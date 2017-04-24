extern crate libc;
extern crate termios;
extern crate ioctl_rs as ioctl;
use std::os::unix::io::RawFd;
use std::io::{self, Read, Write, BufRead};
use libc::c_ushort;

use termios::*;

struct RawTerm(Termios);

struct Term {
    term: RawTerm,
    screenrows: u16,
    screencols: u16,
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
    //Err(io::Error::new(io::ErrorKind::Other, "oh no!"))
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
        let mut raw = self.0.clone();
        raw.c_cflag |= CS8;
        raw.c_iflag &= !(BRKINT | INPCK | ISTRIP | IXON | ICRNL);
        raw.c_oflag &= !(OPOST);
        raw.c_lflag &= !(ECHO | ICANON | ISIG | IEXTEN);

        raw.c_cc[VMIN] = 0;
        raw.c_cc[VTIME] = 1;
        tcsetattr(libc::STDIN_FILENO, TCSANOW, &raw)
    }
}

impl Term {
    fn from(rt: RawTerm) -> io::Result<Term> {
        let (rows, cols) = get_window_size()?;
        Ok(Term {
            term: rt,
            screenrows: rows,
            screencols: cols,
        })
    }
}

impl Drop for RawTerm {
    fn drop(&mut self) {
        println!("restoring terminal");
        clear_term().unwrap();
        tcsetattr(libc::STDIN_FILENO, TCSANOW, &self.0).unwrap();
    }
}

fn ctrled(c: char) -> u8 {
    (c as u8) & 0x1f
}

fn iscntrl(c: char) -> bool {
    unsafe { libc::iscntrl(c as i32) != 0 }
}

fn editor_read_key(handle: &mut Read) -> char {
    let mut buffer: [u8; 1] = [0];
    loop {
        match handle.take(1).read(&mut buffer) {
            Ok(1) => return buffer[0] as char,
            Ok(0) => continue,
            Ok(_) | Err(_) => panic!("error"),
        };
    }
}

fn editor_process_keypress(handle: &mut Read) -> bool {
    let c = editor_read_key(handle);
    // if iscntrl(c) {
    //     print!("{}\r\n", c as u8);
    // } else {
    //     print!("{}({})\r\n", c, c as u8);
    // }
    c as u8 != ctrled('q')
}

fn editor_draw_rows(term: &Term) -> io::Result<()> {
    for _ in 0..term.screenrows - 1 {
        io::stdout().write_all(b"~\r\n")?;
    }
    io::stdout().write_all(b"~")?;
    Ok(())
}
fn editor_refresh_screen(term: &Term) -> io::Result<()> {
    clear_term()?;
    editor_draw_rows(term)?;
    set_cursor()?;
    io::stdout().flush()
}

// terminal commands
fn set_cursor() -> io::Result<()> {
    io::stdout().write_all(b"\x1b[H")?;
    io::stdout().flush()
}

fn clear_term() -> io::Result<()> {
    io::stdout().write_all(b"\x1b[2J")?;
    set_cursor()?;
    io::stdout().flush()
}

fn get_cursor_position() -> io::Result<(u16, u16)> {
    io::stdout().write_all(b"\x1b[6n")?;
    io::stdout().flush()?;

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
    let term = Term::from(rawterm).unwrap();
    loop {
        editor_refresh_screen(&term).unwrap();
        if !editor_process_keypress(&mut io::stdin()) {
            break;
        }
    }

}
