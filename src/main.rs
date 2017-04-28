extern crate libc;
extern crate termios;
extern crate ioctl_rs as ioctl;
use std::os::unix::io::RawFd;
use std::io::{self, Read, Write, BufRead};
use libc::c_ushort;

use termios::*;

const VERSION: &'static str = "0.0.1";
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
    screenrows: u16,
    screencols: u16,
    cx: u16,
    cy: u16,
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
            screenrows: rows,
            screencols: cols,
            cx: 0,
            cy: 0,
        })
    }

    fn move_cursor(&mut self, key: Arrow) {
        match key {
            Arrow::Left => self.cx = if self.cx == 0 { 0 } else { self.cx - 1 },
            Arrow::Right => {
                if self.cx != self.screenrows - 1 {
                    self.cx += 1
                }
            }
            Arrow::Up => self.cy = if self.cy == 0 { 0 } else { self.cy - 1 },
            Arrow::Down => {
                if self.cy != self.screencols - 1 {
                    self.cy += 1
                }
            }
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
                        for _ in 0..self.screenrows {
                            self.move_cursor(dir);
                        }
                    }
                    Special::Home => self.cx = 0,
                    Special::End => self.cx = self.screencols,
                    _ => (),
                };
                true
            }
        }
    }

    fn refresh_screen(&mut self) -> io::Result<()> {
        let mut v = Vec::new();
        v.extend(DISABLE_CURSOR);
        v.extend(SET_CURSOR);
        v.extend(self.draw_rows());
        v.extend(to_pos(self.cx, self.cy));
        v.extend(ENABLE_CURSOR);
        execute(&v)
    }

    fn draw_rows(&mut self) -> Vec<u8> {
        let mut v = Vec::new();
        for y in 0..self.screenrows - 1 {
            v.extend(CLEAR_LINE);
            if y == self.screenrows / 3 {
                let welcome = format!("Kilo editor -- version {}\r\n", VERSION);
                let msglen = std::cmp::min(welcome.len(), self.screencols as usize);
                let padding = ((self.screencols as usize) - msglen) / 2;
                for i in 0..padding {
                    v.push(if i == 0 { b'~' } else { b' ' });
                }
                v.extend(&welcome.as_bytes()[0..msglen]);
            } else {
                v.extend(b"~\r\n");
            }
        }
        v.extend(CLEAR_LINE);
        v.extend(b"~");
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

fn to_pos(x: u16, y: u16) -> Vec<u8> {
    let cmd = format!("\x1b[{};{}H", y + 1, x + 1);
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
    let dim_str = std::str::from_utf8(&vec[2..vec.len() - 1]).unwrap();
    let v: Vec<u16> = dim_str.split(';')
        .flat_map(|s| s.parse::<u16>().into_iter())
        .collect();
    if v.len() != 2 {
        return Err(io::Error::new(io::ErrorKind::Other, "parse error with tty dim"));
    }
    Ok((v[0], v[1]))
}


fn main() {
    let rawterm = RawTerm::from(libc::STDIN_FILENO).unwrap();
    let mut editor = Editor::from(rawterm).unwrap();
    loop {
        editor.refresh_screen().unwrap();
        if !editor.process_keypress() {
            break;
        }
    }

}
