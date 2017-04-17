extern crate libc;
extern crate termios;
use std::os::unix::io::RawFd;
use std::io::{self, Read};

use termios::*;

struct Term(Termios);
impl Drop for Term {
    fn drop(&mut self) {
        println!("restoring terminal");
        tcsetattr(libc::STDIN_FILENO, TCSANOW, &self.0).unwrap();
    }
}
impl Term {
    fn from(fd: RawFd) -> io::Result<Term> {
        Termios::from_fd(fd).map(|t| Term(t))
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

fn ctrled(c: u8) -> u8 {
    c & 0x1f
}

fn iscntrl(c: u8) -> bool {
    unsafe { libc::iscntrl(c as i32) != 0 }
}

fn main() {
    let stdin = io::stdin();
    let mut handle = stdin.lock();

    let term = Term::from(libc::STDIN_FILENO).unwrap();
    term.enable_raw().unwrap();

    let mut buffer: [u8; 1] = [0];
    loop {
        let c = match handle.read_exact(&mut buffer) {
            Ok(_) => buffer[0],
            Err(_) => 0,
        };
        if iscntrl(c) {
            print!("{}\r\n", c);
        } else {
            print!("{}({})\r\n", buffer[0] as char, buffer[0]);
        }
        if c == ctrled('q' as u8) {
            break;
        }
    }
}
