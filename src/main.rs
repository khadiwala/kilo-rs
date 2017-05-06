extern crate libc;
extern crate termios;
extern crate ioctl_rs as ioctl;
extern crate time;

use std::env::args;
use std::fs::File;
use std::ops::Sub;
use std::os::unix::io::RawFd;
use std::io::{self, Read, Write, BufRead, BufReader};
use std::cmp::{max, min};
use std::str::from_utf8;

use libc::c_ushort;
use time::{get_time, Timespec};
use termios::*;

const VERSION: &'static str = "0.0.1";
const TABSTOP: usize = 8;

const CLEAR: &'static [u8] = b"\x1b[2J";
const CLEAR_LINE: &'static [u8] = b"\x1b[K";
const SET_CURSOR: &'static [u8] = b"\x1b[H";
const DISABLE_CURSOR: &'static [u8] = b"\x1b[?25l";
const ENABLE_CURSOR: &'static [u8] = b"\x1b[?25h";

#[derive(PartialEq, Eq, Clone, Copy)]
enum Arrow {
    Left,
    Right,
    Up,
    Down,
}

#[derive(PartialEq, Eq)]
enum Special {
    Del,
    Home,
    End,
    Page(Arrow),
}

enum Keypress {
    Ar(Arrow),
    Ch(char),
    Sp(Special),
}

struct RawTerm(Termios);

struct Editor {
    term: RawTerm,
    screenrows: usize,
    screencols: usize,
    cx: usize,
    cy: usize,
    rx: usize,
    rows: Vec<String>,
    render: Vec<String>,
    rowoff: usize,
    coloff: usize,
    filename: String,
    status_msg: String,
    status_time: Timespec,
}


#[repr(C)]
#[derive(Default)]
struct Winsize {
    ws_row: c_ushort, /* rows, in characters */
    ws_col: c_ushort, /* columns, in characters */
    ws_xpixel: c_ushort, /* horizontal size, pixels */
    ws_ypixel: c_ushort, /* vertical size, pixels */
}

fn ioctl_window_size() -> io::Result<(u16, u16)> {
    let mut w: Winsize = Default::default();
    match unsafe { libc::ioctl(libc::STDIN_FILENO, libc::TIOCGWINSZ, &mut w) } {
            0 => Ok((w.ws_row, w.ws_col)),
            _ => Err(io::Error::last_os_error()),
        }
        .and_then(|(row, col)| if col == 0 {
                      Err(io::Error::new(io::ErrorKind::Other, "ioctl error"))
                  } else {
                      Ok((row, col))
                  })
}

fn tty_window_size() -> io::Result<(u16, u16)> {
    io::stdout().write_all(b"\x1b[999C\x1b[999B")?;
    io::stdout().flush()?;
    get_cursor_position()
}

fn get_window_size() -> io::Result<(u16, u16)> {
    ioctl_window_size().or_else(|_| tty_window_size())
}

impl RawTerm {
    fn from(fd: RawFd) -> io::Result<RawTerm> {
        let term = RawTerm(Termios::from_fd(fd)?);
        term.enable_raw()?;
        Ok(term)
    }

    fn enable_raw(&self) -> io::Result<()> {
        let mut raw = self.0;
        raw.c_cflag |= CS8;
        raw.c_iflag &= !(BRKINT | INPCK | ISTRIP | IXON | ICRNL);
        raw.c_oflag &= !(OPOST);
        raw.c_lflag &= !(ECHO | ICANON | ISIG | IEXTEN);

        raw.c_cc[VMIN] = 0;
        raw.c_cc[VTIME] = 1;
        tcsetattr(libc::STDIN_FILENO, TCSANOW, &raw)
    }
}

impl Editor {
    fn from(rt: RawTerm) -> io::Result<Editor> {
        let (rows, cols) = get_window_size()?;
        Ok(Editor {
               term: rt,
               // leave two rows for status
               screenrows: (rows - 2) as usize,
               screencols: cols as usize,
               // current column
               cx: 0,
               // current row
               cy: 0,
               // current column within rendered line
               rx: 0,
               // file contents
               rows: Vec::new(),
               // rendered contents (tabs->spaces)
               render: Vec::new(),
               rowoff: 0,
               coloff: 0,
               filename: "[No name]".to_owned(),
               status_msg: "".to_owned(),
               status_time: Timespec::new(0, 0),
           })
    }

    fn open(&mut self, filename: &str) -> io::Result<()> {
        self.filename = filename.to_owned();
        let f = File::open(filename)?;
        let handle = BufReader::new(f);
        for rline in handle.lines() {
            let line = rline?;
            // count tabs so we only need to make a single allocation
            let tabs = line.as_bytes().iter().filter(|c| **c == b'\t').count();
            let mut rendered: Vec<u8> = Vec::with_capacity(line.len() + tabs * (TABSTOP - 1));
            let mut r_index = 0;
            for c in line.as_bytes() {
                if *c == b'\t' {
                    rendered.push(b' ');
                    r_index += 1;
                    while r_index % TABSTOP != 0 {
                        rendered.push(b' ');
                        r_index += 1;
                    }
                } else {
                    rendered.push(*c);
                    r_index += 1;
                }
            }
            let render_s = std::string::String::from_utf8(rendered)
                .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
            self.render.push(render_s);
            self.rows.push(line);
        }
        Ok(())
    }

    fn move_cursor(&mut self, key: Arrow) {
        match key {
            Arrow::Left => {
                if self.cx != 0 {
                    self.cx -= 1;
                } else if self.cy > 0 {
                    self.cy -= 1;
                    self.cx = self.rows[self.cy].len();
                }
            }
            Arrow::Right => {
                let rowlen = self.rows.get(self.cy).map_or(0, String::len);
                if self.cx < rowlen {
                    self.cx += 1;
                } else if self.cx == rowlen {
                    self.cy += 1;
                    self.cx = 0;
                }
            }
            Arrow::Up => self.cy = if self.cy == 0 { 0 } else { self.cy - 1 },
            Arrow::Down => {
                if self.cy < self.rows.len() {
                    self.cy += 1
                }
            }
        }

        // limit cursor to end of line
        let rowlen = self.rows.get(self.cy).map_or(0, String::len);
        if self.cx > rowlen {
            self.cx = rowlen;
        }
    }

    fn set_status_message(&mut self, msg: String) {
        self.status_msg = msg;
        self.status_time = get_time();
    }

    fn scroll(&mut self) {
        self.rx = if self.cy < self.rows.len() {
            let row = &self.rows[self.cy];
            let xpos = self.cx;
            cx_to_rx(row.as_bytes(), xpos)
        } else {
            0
        };
        // scroll before page
        if self.cy < self.rowoff {
            self.rowoff = self.cy;
        }
        // scroll past page
        if self.cy >= self.rowoff + self.screenrows {
            // one page up from current y pos
            self.rowoff = self.cy - self.screenrows + 1;
        }
        if self.rx < self.coloff {
            self.coloff = self.rx;
        }
        if self.rx >= self.coloff + self.screencols {
            self.coloff = self.rx - self.screencols + 1;
        }
    }

    fn process_keypress(&mut self) -> bool {
        let handle = &mut io::stdin();
        let kp = editor_read_key(handle);
        match kp {
            Keypress::Ar(arrow) => {
                self.move_cursor(arrow);
                true
            }
            Keypress::Ch(c) => c as u8 != ctrled('q'),
            Keypress::Sp(special) => {
                match special {
                    Special::Page(dir) => {
                        match dir {
                            Arrow::Up => self.cy = self.rowoff,
                            Arrow::Down => {
                                self.cy = min(self.rowoff + self.screenrows - 1, self.rows.len())
                            }
                            _ => panic!("illegal paging"),
                        }
                        for _ in 0..self.screenrows {
                            self.move_cursor(dir);
                        }
                    }
                    Special::Home => self.cx = 0,
                    Special::End => {
                        if self.cy < self.rows.len() {
                            self.cx = self.rows[self.cy].len();
                        }
                    }
                    _ => (),
                };
                true
            }
        }
    }

    fn refresh_screen(&mut self) -> io::Result<()> {
        self.scroll();
        let mut v = Vec::new();
        v.extend(DISABLE_CURSOR);
        v.extend(SET_CURSOR);
        v.extend(self.draw_rows());
        v.extend(self.draw_status_bar());
        v.extend(self.draw_message_bar());
        v.extend(to_pos(self.rx + 1 - self.coloff, (self.cy + 1) - self.rowoff));
        v.extend(ENABLE_CURSOR);
        execute(&v)
    }

    fn draw_status_bar(&mut self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        v.extend(b"\x1b[7m");
        let lstatus = format!("{} - {} lines",
                              &self.filename[..min(self.filename.len(), 20)],
                              self.rows.len());
        let rstatus = format!("{}/{}", self.cy + 1, self.rows.len());
        let truncated = &lstatus[0..min(lstatus.len(), (self.screencols - rstatus.len()))];
        v.extend(truncated.as_bytes());
        v.extend(std::iter::repeat(b' ').take(self.screencols - truncated.len() - rstatus.len()));
        v.extend(rstatus.as_bytes());
        v.extend(b"\x1b[m");
        v.extend(b"\r\n");
        v
    }

    fn draw_message_bar(&mut self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        v.extend(b"\x1b[K");
        if !self.status_msg.is_empty() && get_time().sub(self.status_time).num_seconds() < 5 {
            v.extend(self.status_msg.as_bytes());
        }
        v
    }

    fn draw_rows(&mut self) -> Vec<u8> {
        let mut v = Vec::new();
        for y in 0..self.screenrows {
            v.extend(CLEAR_LINE);
            let filerow = self.rowoff + y;
            if filerow >= self.rows.len() {
                if self.rows.is_empty() && y == self.screenrows / 3 {
                    let welcome = format!("Kilo editor -- version {}\r\n", VERSION);
                    let msglen = min(welcome.len(), self.screencols as usize);
                    let padding = ((self.screencols as usize) - msglen) / 2;
                    for i in 0..padding {
                        v.push(if i == 0 { b'~' } else { b' ' });
                    }
                    v.extend(&welcome.as_bytes()[0..msglen]);
                } else {
                    v.extend(b"~\r\n");
                }
            } else {
                let line = &self.render[filerow];
                let available_text = max(line.len() as i32 - self.coloff as i32, 0);
                let len = min(available_text, self.screencols as i32) as usize;
                let start = if len > 0 { self.coloff } else { 0 };
                v.extend(self.render[filerow][start..start + len].as_bytes());
                v.extend(b"\r\n")
            }
        }
        v.extend(CLEAR_LINE);
        // v.extend(b"~");
        v
    }
}

impl Drop for RawTerm {
    fn drop(&mut self) {
        println!("restoring terminal");
        execute(CLEAR).unwrap();
        execute(SET_CURSOR).unwrap();
        tcsetattr(libc::STDIN_FILENO, TCSANOW, &self.0).unwrap();
    }
}

fn ctrled(c: char) -> u8 {
    (c as u8) & 0x1f
}

fn read1(handle: &mut Read) -> Option<u8> {
    let mut buffer: [u8; 1] = [0];
    match handle.take(1).read(&mut buffer) {
        Ok(1) => Some(buffer[0]),
        Ok(0) => None,
        Ok(_) | Err(_) => panic!("error"),
    }
}

fn editor_read_key(handle: &mut Read) -> Keypress {
    let c;
    loop {
        match read1(handle) {
            Some(x) => {
                c = x;
                break;
            }
            None => continue,
        }
    }
    if c == b'\x1b' {
        if let (Some(c1), Some(c2)) = (read1(handle), read1(handle)) {
            match (c1, c2) {
                (b'[', b'0'...b'9') => {
                    if let Some(c3) = read1(handle) {
                        match (c3, c2) {
                            (b'~', b'1') | (b'~', b'7') => return Keypress::Sp(Special::Home),
                            (b'~', b'4') | (b'~', b'8') => return Keypress::Sp(Special::End),
                            (b'~', b'3') => return Keypress::Sp(Special::Del),
                            (b'~', b'5') => return Keypress::Sp(Special::Page(Arrow::Up)),
                            (b'~', b'6') => return Keypress::Sp(Special::Page(Arrow::Down)),
                            (_, _) => (),
                        }
                    }
                }
                (b'[', b'A') => return Keypress::Ar(Arrow::Up),
                (b'[', b'B') => return Keypress::Ar(Arrow::Down),
                (b'[', b'C') => return Keypress::Ar(Arrow::Right),
                (b'[', b'D') => return Keypress::Ar(Arrow::Left),
                (b'[', b'H') | (b'O', b'H') => return Keypress::Sp(Special::Home),
                (b'[', b'F') | (b'O', b'F') => return Keypress::Sp(Special::End),
                _ => (),
            }
        }
    }
    Keypress::Ch(c as char)
}

// terminal commands

fn to_pos(x: usize, y: usize) -> Vec<u8> {
    let cmd = format!("\x1b[{};{}H", y, x);
    cmd.into_bytes()
}

fn execute(v: &[u8]) -> io::Result<()> {
    io::stdout().write_all(v)?;
    io::stdout().flush()
}

fn get_cursor_position() -> io::Result<(u16, u16)> {
    execute(b"\x1b[6n")?;

    let mut vec = Vec::new();

    let stdin = io::stdin();
    let mut handle = stdin.lock();
    handle.read_until(b'R', &mut vec)?;

    //println!("{:?}", &vec);
    //println!("{}", std::str::from_utf8(&vec[2..]).unwrap());
    if vec[0] != 0x1b || vec[1] != b'[' {
        return Err(io::Error::new(io::ErrorKind::Other, "invalid tty response"));
    }
    let dim_str = from_utf8(&vec[2..vec.len() - 1]).unwrap();
    let v: Vec<u16> = dim_str
        .split(';')
        .flat_map(|s| s.parse::<u16>().into_iter())
        .collect();
    if v.len() != 2 {
        return Err(io::Error::new(io::ErrorKind::Other, "parse error with tty dim"));
    }
    Ok((v[0], v[1]))
}

fn cx_to_rx(row: &[u8], cx: usize) -> usize {
    let mut rx = 0;
    for &c in row[0..cx].iter() {
        if c == b'\t' {
            rx += (TABSTOP - 1) - (rx % TABSTOP)
        }
        rx += 1;
    }
    rx
}


fn main() {
    let rawterm = RawTerm::from(libc::STDIN_FILENO).unwrap();
    let mut editor = Editor::from(rawterm).unwrap();
    args()
        .nth(1)
        .map(|filename| editor.open(&filename).unwrap());
    editor.set_status_message("HELP: Ctrl-Q = quit".to_owned());
    loop {
        editor.refresh_screen().unwrap();
        if !editor.process_keypress() {
            break;
        }
    }
}

