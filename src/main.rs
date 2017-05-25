extern crate libc;
extern crate termios;
extern crate ioctl_rs as ioctl;
extern crate time;

#[macro_use]
extern crate bitflags;

use std::env::args;
use std::fs::File;
use std::ops::Sub;
use std::os::unix::io::RawFd;
use std::io::{self, Read, Write, BufRead, BufReader};
use std::cmp::{max, min};
use std::str::from_utf8;
use std::mem;

use libc::c_ushort;
use time::{get_time, Timespec};
use termios::*;

// editor config
const VERSION: &'static str = "0.0.1";
// Tabs are rendered to spaces
const TABSTOP: usize = 8;
// Issue QUIT_TIMES quits to exit with a dirty file
const QUIT_TIMES: u8 = 3;

// ANSI/VT100 codes
const CLEAR: &'static [u8] = b"\x1b[2J";
const CLEAR_LINE: &'static [u8] = b"\x1b[K";
const SET_CURSOR: &'static [u8] = b"\x1b[H";
const DISABLE_CURSOR: &'static [u8] = b"\x1b[?25l";
const ENABLE_CURSOR: &'static [u8] = b"\x1b[?25h";
const INVERTED_COLOR: &'static [u8] = b"\x1b[7m";
const NORMAL_COLOR: &'static [u8] = b"\x1b[m";
const GET_CURSOR_POS: &'static [u8] = b"\x1b[6n";

// ctrl-key sequences
const SAVE: u8 = (b's' & 0x1f);
const QUIT: u8 = (b'q' & 0x1f);
const FIND: u8 = (b'f' & 0x1f);
const CTRLH: u8 = (b'h' & 0x1f);

// syntax highlighting options
bitflags! {
    flags SynConfig: u8 {
        const HL_NUMBERS  = 0b00000001,
        const HL_STRINGS  = 0b00000010,

        const DISABLED = 0b00000000,
        const RUST_CONFIG = HL_NUMBERS.bits | HL_STRINGS.bits
    }
}

/// Syntax highlighting configuration for rust
const RS_SYNTAX: &Syntax = &Syntax {
    filetype: "rust",
    comment_start: "//",
    filematch: &["rs"],
    flags: RUST_CONFIG,
    // use keywords1 for reserved words/builtins
    keywords1: &["abstract", "alignof", "as", "become", "box", "break", "const", "continue",
                 "crate", "do", "else", "enum", "extern", "false", "final", "fn", "for", "if",
                 "impl", "in", "let", "loop", "macro", "match", "mod", "move", "mut", "offsetof",
                 "override", "priv", "proc", "pub", "pure", "ref", "return", "Self", "self",
                 "sizeof", "static", "struct", "super", "trait", "true", "type", "typeof",
                 "unsafe", "unsized", "use", "virtual", "where", "while", "yield", "bool", "char",
                 "str"],
    // use keywords2 for primitives
    keywords2: &["i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "isize", "usize", "f32",
                 "f64"],
};

/// No highlighting (default)
const NO_SYNTAX: &Syntax = &Syntax {
    filetype: "no ft",
    comment_start: "",
    filematch: &[],
    flags: DISABLED,
    keywords1: &[],
    keywords2: &[],
};

/// To add a new syntax, define a syntax struct and add it here
/// You can configure file extensions, comments, and keywords but not much else
/// Syntax assumes `""`s for strings, and `''`s for characters, and the `0x`/`0b`/`0o` radix
/// prefixes for numeric literals.
/// You can disable these with the `flags` option
const HLDB: [&Syntax; 2] = [RS_SYNTAX, NO_SYNTAX];

/// Configuration for a syntax highlighting type
struct Syntax<'a> {
    comment_start: &'a str, // Prefix for line comments
    filetype: &'a str, // Name that is printed in status messages
    filematch: &'a [&'a str], // Extensions that map to this filetype

    // A list of words that should be highlighted.
    // There are two colors available for highlighting keywords.
    // keywords are highlighted if they are prefixed and suffixed with a seperator
    keywords1: &'a [&'a str],
    keywords2: &'a [&'a str],

    flags: SynConfig, // Highlighting features to enable/disable
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum Highlight {
    Normal,
    Number,
    Strings,
    Comment,
    Keyword1,
    Keyword2,
    Match, // for search highlighting
}
impl Highlight {
    /// Map a syntax color type from the Highlight enum to
    /// an ansi code
    fn color(hl: Highlight) -> u8 {
        match hl {
            Highlight::Number => 31, // red
            Highlight::Match => 34, // blue
            Highlight::Strings => 35, // magenta
            Highlight::Comment => 36, // cyan
            Highlight::Keyword1 => 33, //yellow
            Highlight::Keyword2 => 32, //green
            Highlight::Normal => 37,
        }
    }
}


#[derive(PartialEq, Eq, Clone, Copy)]
enum Arrow {
    Left,
    Right,
    Up,
    Down,
}
enum Keypress {
    Ar(Arrow),
    Page(Arrow),
    Home,
    End,
    Enter,
    Backspace,
    CtrlH,
    Del,
    Save,
    Find,
    Quit,
    Esc,
    Chr(char),
}

/// Use Termios API to switch into raw mode
///
/// Store the original terminal flags and restore them on `drop`
struct RawTerm(Termios);
impl RawTerm {
    /// Switch into raw mode, return a Rawterm object that can be `dropped` to restore
    fn from(fd: RawFd) -> io::Result<RawTerm> {
        let term = RawTerm(Termios::from_fd(fd)?);
        term.enable_raw()?;
        Ok(term)
    }

    /// Enable raw mode
    fn enable_raw(&self) -> io::Result<()> {
        let mut raw = self.0;
        // input - No break, no parity check, no strip char, no start/stop output, No CR to NL
        raw.c_iflag &= !(BRKINT | INPCK | ISTRIP | IXON | ICRNL);
        // output - no post processing
        raw.c_oflag &= !(OPOST);
        // control modes - set 8 bit chars
        raw.c_cflag |= CS8;
        // local modes - echoing off, canonical off, no signal chars (^Z, ^C), no extended functions
        raw.c_lflag &= !(ECHO | ICANON | ISIG | IEXTEN);

        // minimum number of bytes that can be returned
        raw.c_cc[VMIN] = 0;
        // 100ms timeout
        raw.c_cc[VTIME] = 1;

        tcsetattr(libc::STDIN_FILENO, TCSANOW, &raw)
    }
}

/// Restores to the previous `Termios` state on drop
///
/// Additionally, clears any output on the screen and sets curstor to 0,0 using VT100 codes
impl Drop for RawTerm {
    fn drop(&mut self) {
        execute(CLEAR).unwrap();
        execute(SET_CURSOR).unwrap();
        tcsetattr(libc::STDIN_FILENO, TCSANOW, &self.0).unwrap();
    }
}

// populated by libc::ioctl call
#[repr(C)]
#[derive(Default)]
struct Winsize {
    ws_row: c_ushort, // rows, in characters
    ws_col: c_ushort, // columns, in characters
    ws_xpixel: c_ushort, // horizontal size, pixels
    ws_ypixel: c_ushort, // vertical size, pixels
}

/// Get window size using ioctl if it is available
///
/// Uses the TIOCGWINSZ request (Terminal IO Get Window Size)
///
/// # Return value
/// Return the (height, width) of the terminal or an error
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

/// Get window size using vt100 codes
///
/// # Return value
/// Return the (height, width) of the terminal or an error
fn tty_window_size() -> io::Result<(u16, u16)> {
    io::stdout().write_all(b"\x1b[999C\x1b[999B")?;
    io::stdout().flush()?;
    get_cursor_position()
}

/// Get window size
///
/// Uses ioctl if available, otherwise falling back to vt100
///
/// # Return value
/// Return the (height, width) of the terminal or an error
fn get_window_size() -> io::Result<(u16, u16)> {
    ioctl_window_size().or_else(|_| tty_window_size())
}


/// Represents a row of text in the editor
///
/// Contains both the source text and a rendering. Rerenders text on modifications.
struct Row {
    orig: String,
    rendered: String,
    highlights: Vec<Highlight>,
    syntax: &'static Syntax<'static>,
    len: usize,
}

impl Row {
    /// Create a row, usually from some source text
    ///
    /// * The source text of the line
    /// * The Syntax to use to provide syntax highlighting
    fn from(line: String, syntax: &'static Syntax) -> Row {
        let rendered = Row::render(&line);
        let highlights = syntax.highlight(&rendered);
        let len = line.len();
        Row {
            rendered: rendered,
            orig: line,
            highlights: highlights,
            len: len,
            syntax: syntax,
        }
    }

    /// insert a character `c` at `at` and rerender the text
    fn insert_char(&mut self, at: usize, c: char) {
        self.orig.insert(min(at, self.len), c);
        self.update();
    }

    /// delete character at `at` and rerender the text
    fn delete_char(&mut self, at: usize) {
        self.orig.remove(at);
        self.update();
    }

    /// Append a row `r` to this row
    fn push(&mut self, r: &Row) {
        self.orig.push_str(&r.orig);
        self.update();
    }

    /// Split this at `at`, returning ownership of the new `Row` to caller.
    fn split_off(&mut self, at: usize) -> Row {
        let right = self.orig.split_off(at);
        self.update();
        Row::from(right, self.syntax)
    }

    /// Set the Highlight for a subrange of the rendered row
    fn highlight_range(&mut self, hl: Highlight, rstart: usize, rend: usize) {
        for i in rstart..rend {
            self.highlights[i] = hl;
        }
    }

    /// Update derrived structures after modifications to `self.orig`
    fn update(&mut self) {
        self.rendered = Row::render(&self.orig);
        self.highlights = self.syntax.highlight(&self.rendered);
        self.len = self.orig.len();
    }


    /// Translate a position in the original text to a position in the rendered text.
    fn cx_to_rx(&self, cx: usize) -> usize {
        let row = self.orig.as_bytes();
        let mut rx = 0;
        for &c in row[0..cx].iter() {
            if c == b'\t' {
                rx += (TABSTOP - 1) - (rx % TABSTOP)
            }
            rx += 1;
        }
        rx
    }

    /// Translate a position in the rendered text to a position in the original text.
    fn rx_to_cx(&self, rx: usize) -> usize {
        let row = self.orig.as_bytes();
        let mut cur_rx = 0;
        for (i, &c) in row.iter().enumerate() {
            if c == b'\t' {
                cur_rx += (TABSTOP - 1) - (rx % TABSTOP);
            }
            cur_rx += 1;
            if cur_rx > rx {
                return i;
            }
        }
        row.len() - 1
    }

    /// Change source text into what is displated
    ///
    /// Expands tabs into spaces according to TABSTOP
    fn render(line: &str) -> String {
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
        std::string::String::from_utf8(rendered).unwrap()
    }
}

/// A position in the editor.
///
/// Contains geometric cursor position wrt the window and the offsets wrt to the file.
#[derive(Clone, Copy, Default)]
struct Position {
    // current x position
    cx: usize,
    // current y position
    cy: usize,
    // row offset into the file
    rowoff: usize,
    // col offset into the file
    coloff: usize,
}

/// Contains state associated with the editor instance
struct Editor {
    _term: RawTerm,
    screenrows: usize,
    screencols: usize,
    position: Position,
    // current x position in rendered row
    rx: usize,
    rows: Vec<Row>,
    // the name of the file, empty if there isn't one
    filename: String,
    syntax: &'static Syntax<'static>,
    // nonzeo if the file has been modified but not saved
    dirty: usize,
    // number of times we've quit (relevant when we're trying to quit with a dirty file)
    quit_times: u8,
    status_msg: String,
    status_time: Timespec,
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum Direction {
    Forward,
    Backward,
}

impl Direction {
    fn from(a: Arrow) -> Direction {
        match a {
            Arrow::Right | Arrow::Down => Direction::Forward,
            Arrow::Left | Arrow::Up => Direction::Backward,
        }
    }

    /// traverse the iterator backwords or forwards based on the direction
    /// There is surely a way to return an iterator without just making a new vector,
    /// but I can't figure it out
    fn traverse<'a, T, I>(self, it: I) -> Vec<T>
        where I: ExactSizeIterator<Item = T> + DoubleEndedIterator<Item = T>
    {
        match self {
            Direction::Forward => it.collect(),
            Direction::Backward => it.rev().collect(),
        }
    }
}

/// The location of the previous match when searching
struct LastMatch {
    row_index: usize,

    // what the highlight was before
    saved_hl: Vec<Highlight>,
}
impl LastMatch {
    /// take the saved highlight, replacing `self.saved_hl` with an empty vec
    fn take_saved(&mut self) -> Vec<Highlight> {
        mem::replace(&mut self.saved_hl, Vec::new())
    }
}

impl Editor {
    /// Create a Editor struct from a Rawterm struct
    fn from(rt: RawTerm) -> io::Result<Editor> {
        let (rows, cols) = get_window_size()?;
        Ok(Editor {
               _term: rt,
               // leave two rows for status
               screenrows: (rows - 2) as usize,
               screencols: cols as usize,
               position: Default::default(),
               rx: 0,
               rows: Vec::new(),
               filename: String::new(),
               dirty: 0,
               quit_times: QUIT_TIMES,
               status_msg: "".to_owned(),
               status_time: Timespec::new(0, 0),
               syntax: NO_SYNTAX,
           })
    }

    /// Open a file and load all lines into the editor
    fn open(&mut self, filename: &str) -> io::Result<()> {
        self.filename = filename.to_owned();
        self.syntax = Syntax::from(filename);
        let f = File::open(filename)?;
        let handle = BufReader::new(f);
        for rline in handle.lines() {
            let line = rline?;
            self.rows.push(Row::from(line, self.syntax));
        }
        Ok(())
    }

    /// Return a single String with the current text of all rows
    fn rows_to_file(&self) -> String {
        self.rows
            .iter()
            .map(|row| &row.orig)
            .fold(String::new(), |mut s, nxt| {
                s.push_str(nxt);
                s.push('\n');
                s
            })
    }

    /// Save current editor state to a file, prompting for filename if it was not provided.
    ///
    /// # Return Value
    /// The number of bytes saved to `self.filename`, if the save was successful.
    fn save(&mut self) -> io::Result<usize> {
        if self.filename == "" {
            self.filename = self.prompt("Save as: {} (ESC to cancel)", &mut |_, _, _| {})?;
            if self.filename == "" {
                return Ok(0);
            } else {
                self.syntax = Syntax::from(&self.filename);
            }
        }
        let file_content = self.rows_to_file();
        let len = file_content.len();
        let handle = File::create(&self.filename);
        handle?.write_all(file_content.as_bytes())?;

        // only clear dirty if save worked
        self.dirty = 0;
        Ok(len)
    }

    /// Open a prompt and search for user's input.
    fn find(&mut self) {
        let mut direction = Direction::Forward;
        let mut last_match: Option<LastMatch> = None;
        let mut on_keypress = |editor: &mut Editor, partial_input: &str, kp: Keypress| {
            last_match
                .as_mut()
                .map(|lm| { editor.rows[lm.row_index].highlights = lm.take_saved(); });

            match kp {
                Keypress::Enter | Keypress::Esc => return,
                Keypress::Ar(dir) => direction = Direction::from(dir),
                _ => {
                    direction = Direction::Forward;
                    last_match = None;
                }
            }
            Some(partial_input)
                .iter()
                .find(|q| !q.is_empty())
                .and_then(|q| {
                    // there's a non-empty search query

                    // always start forward
                    if last_match.is_none() {
                        direction = Direction::Forward
                    };

                    // start with the line after the current match
                    // relative to the beginning if forward, end if back
                    let current = last_match
                        .as_ref()
                        .map(|lm| match direction {
                                 Direction::Forward => lm.row_index + 1,
                                 Direction::Backward => {
                                     (((editor.rows.len() - 1) as i32) -
                                      (lm.row_index as i32 - 1)) as
                                     usize
                                 }
                             })
                        .unwrap_or(0);

                    // make a pass through the file starting at the current match offset,
                    // looping back around through the file when reaching either end
                    direction
                        .traverse(editor.rows.iter().enumerate())
                        .into_iter()
                        .cycle()
                        .skip(current)
                        .take(editor.rows.len())
                        .flat_map(|(i, row)| row.rendered.find(q).map(|f| (i, f)).into_iter())
                        .next()
                })
                .map(|(rowidx, colidx)| {
                    // Found a match, update cursor position, highlight
                    last_match = Some(LastMatch {
                                          row_index: rowidx,
                                          saved_hl: editor.rows[rowidx].highlights.clone(),
                                      });
                    editor.position.rowoff = editor.rows.len();
                    editor.position.cy = rowidx;
                    let brow = &mut editor.rows[rowidx];
                    editor.position.cx = brow.rx_to_cx(colidx);
                    brow.highlight_range(Highlight::Match, colidx, colidx + partial_input.len());
                });
        };
        // Save the position from before the start of the search
        let initial = self.position;

        let last = self.prompt("Seach: {} (Use ESC/Arrows/Enter)", &mut on_keypress);
        last.ok()
            .iter()
            .find(|s| !s.is_empty())
            .map(|_| ())
            // If the prompt returned empty, the user cancelled the operation,
            // set the cursor back to the original position
            .unwrap_or_else(|| self.position = initial);
    }


    /// Display the prompt to the user and trigger the `callback` on every keypress
    ///
    /// Switches focus to the status bar. A Enter or Esc keypress ends the prompt interaction.
    ///
    /// * prompt string to display in the status bar, must contain one `{}` where the user's input
    ///          will appear as they type
    /// * callback the callback to be triggered on each keypress. The callback will be passed the
    ///            last `Keypress`, the user input so far, and a mutable editor reference since
    ///            this method has mutable ownership of the Editor and a callback may need to
    ///            modify it.
    ///
    /// # Return value
    /// The state of the user's input when Enter was pressed, or empty string if the prompt was
    /// cancelled via Esc
    fn prompt<F>(&mut self, prompt: &str, callback: &mut F) -> io::Result<String>
        where F: FnMut(&mut Editor, &str, Keypress)
    {
        let handle = &mut io::stdin();
        let mut input = String::with_capacity(128);
        loop {
            self.set_status_message(prompt.replace("{}", &input));
            self.refresh_screen()?;

            let keypress = Self::editor_read_key(handle);
            match keypress {
                Keypress::Backspace | Keypress::Del | Keypress::CtrlH => {
                    let input_len = input.len();
                    if input_len > 0 {
                        input.remove(input_len - 1);
                    }
                }
                Keypress::Enter => {
                    if !input.is_empty() {
                        self.set_status_message("".to_string());
                        callback(self, &input, keypress);
                        return Ok(input);
                    }
                }
                Keypress::Esc => {
                    self.set_status_message("".to_string());
                    callback(self, &input, keypress);
                    return Ok(String::new());
                }
                Keypress::Chr(c) => {
                    input.push(c);
                }
                _ => (),
            }
            callback(self, &input, keypress);
        }
    }

    /// insert a char at the current position
    fn insert_char(&mut self, c: char) {
        if self.position.cy == self.rows.len() {
            self.rows.push(Row::from(String::new(), self.syntax))
        }
        self.rows[self.position.cy].insert_char(self.position.cx, c);
        self.position.cx += 1;
        self.dirty += 1;
    }

    /// insert a newline at the current position, which might split
    /// one `Row` into two.
    fn insert_newline(&mut self) {
        if self.position.cy > self.rows.len() {
            return;
        }
        if self.position.cx == 0 {
            self.rows
                .insert(self.position.cy, Row::from(String::new(), self.syntax));
        } else {
            let next = self.rows[self.position.cy].split_off(self.position.cx);
            self.rows.insert(self.position.cy + 1, next);
        }
        self.position.cx = 0;
        self.position.cy += 1;
        self.dirty += 1;
    }

    /// delete a char at the current position
    fn delete_char(&mut self) {
        if self.position.cy == self.rows.len() || (self.position.cx == 0 && self.position.cy == 0) {
            return;
        }
        if self.position.cx > 0 {
            let row = &mut self.rows[self.position.cy];
            row.delete_char(self.position.cx - 1);
            self.position.cx -= 1;
        } else {
            let row = self.rows.remove(self.position.cy);
            let prev = &mut self.rows[self.position.cy - 1];
            self.position.cx = prev.len;
            prev.push(&row);
            self.position.cy -= 1;

        }
        self.dirty += 1;
    }

    /// Move the cursor in the direction of the `Arrow`
    ///
    /// Supports wrapping, for example a right at the end of
    /// a line moves the cursor to the next line
    fn move_cursor(&mut self, key: Arrow) {
        match key {
            Arrow::Left => {
                if self.position.cx != 0 {
                    self.position.cx -= 1;
                } else if self.position.cy > 0 {
                    self.position.cy -= 1;
                    self.position.cx = self.rows[self.position.cy].len;
                }
            }
            Arrow::Right => {
                let rowlen = self.rows.get(self.position.cy).map_or(0, |r| r.len);
                if self.position.cx < rowlen {
                    self.position.cx += 1;
                } else if self.position.cx == rowlen {
                    self.position.cy += 1;
                    self.position.cx = 0;
                }
            }
            Arrow::Up => {
                self.position.cy = if self.position.cy == 0 {
                    0
                } else {
                    self.position.cy - 1
                }
            }
            Arrow::Down => {
                if self.position.cy < self.rows.len() {
                    self.position.cy += 1
                }
            }
        }

        // limit cursor to end of line
        let rowlen = self.rows.get(self.position.cy).map_or(0, |r| r.len);
        if self.position.cx > rowlen {
            self.position.cx = rowlen;
        }
    }

    /// Set that status message that will be drawn in the second to
    /// the last row of the screen
    fn set_status_message(&mut self, msg: String) {
        self.status_msg = msg;
        self.status_time = get_time();
    }

    /// Change thie visible portion of the file
    ///
    /// After processing any movement cursor commands, a call to scroll adjusts the
    /// `rowoff`/`coloff` fields to change if we had moved ahead or behind of what
    /// portion of the file is currently visible.
    fn scroll(&mut self) {
        self.rx = if self.position.cy < self.rows.len() {
            let row = &self.rows[self.position.cy];
            let xpos = self.position.cx;
            row.cx_to_rx(xpos)
        } else {
            0
        };
        // scroll before page
        if self.position.cy < self.position.rowoff {
            self.position.rowoff = self.position.cy;
        }
        // scroll past page
        if self.position.cy >= self.position.rowoff + self.screenrows {
            // one page up from current y pos
            self.position.rowoff = self.position.cy - self.screenrows + 1;
        }
        if self.rx < self.position.coloff {
            self.position.coloff = self.rx;
        }
        if self.rx >= self.position.coloff + self.screencols {
            self.position.coloff = self.rx - self.screencols + 1;
        }
    }

    /// Read a single `Keypress` from stdin and perform the appropriate action
    ///
    /// # Return value
    /// true if the keypress indicated the program should terminate
    fn process_keypress(&mut self) -> bool {
        let handle = &mut io::stdin();
        let kp = Self::editor_read_key(handle);
        match kp {
            // editor commands
            Keypress::Quit => {
                if self.dirty > 0 && self.quit_times > 0 {
                    let quits_left = self.quit_times;
                    let msg = format!("WARNING!!! File has unsaved changes. Press Ctrl-Q {} more \
                                       times to quit.",
                                      quits_left);
                    self.set_status_message(msg);
                    self.quit_times -= 1;
                    return true;
                }
                return false;
            }
            Keypress::Save => {
                match self.save() {
                    Ok(len) => self.set_status_message(format!("{} bytes written to disk", len)),
                    Err(e) => self.set_status_message(format!("Can't save! I/O error: {}", e)),
                };
            }
            Keypress::Find => self.find(),

            // movement
            Keypress::Ar(arrow) => self.move_cursor(arrow),
            Keypress::Page(dir) => {
                match dir {
                    Arrow::Up => self.position.cy = self.position.rowoff,
                    Arrow::Down => {
                        self.position.cy = min(self.position.rowoff + self.screenrows - 1,
                                               self.rows.len())
                    }
                    _ => panic!("illegal paging"),
                }
                for _ in 0..self.screenrows {
                    self.move_cursor(dir);
                }
            }
            Keypress::Home => self.position.cx = 0,
            Keypress::End => {
                if self.position.cy < self.rows.len() {
                    self.position.cx = self.rows[self.position.cy].len;
                }
            }

            // editing
            Keypress::Enter => self.insert_newline(),
            Keypress::Backspace | Keypress::CtrlH => self.delete_char(),
            Keypress::Del => {
                self.move_cursor(Arrow::Right);
                self.delete_char();
            }

            // do nothing with Esc when editing
            Keypress::Esc => (),
            Keypress::Chr(c) => self.insert_char(c),
        };
        self.quit_times = QUIT_TIMES;
        true
    }

    /// Redraw the entire screen
    fn refresh_screen(&mut self) -> io::Result<()> {
        self.scroll();
        let mut v = Vec::new();
        v.extend(DISABLE_CURSOR);
        v.extend(SET_CURSOR);
        v.extend(self.draw_rows());
        v.extend(self.draw_status_bar());
        v.extend(self.draw_message_bar());
        v.extend(to_pos(self.rx + 1 - self.position.coloff,
                        (self.position.cy + 1) - self.position.rowoff));
        v.extend(ENABLE_CURSOR);
        execute(&v)
    }

    /// Return text that should be displayed in the status bar
    fn draw_status_bar(&self) -> Vec<u8> {
        let display_name = if self.filename.is_empty() {
            "[No name]"
        } else {
            &self.filename
        };
        let mut v: Vec<u8> = Vec::new();
        v.extend(INVERTED_COLOR);
        let lstatus = format!("{} - {} lines {}",
                              &display_name[..min(display_name.len(), 20)],
                              self.rows.len(),
                              if self.dirty != 0 { "(modified)" } else { "" });
        let rstatus = format!("{} | {}/{}",
                              self.syntax.filetype,
                              self.position.cy + 1,
                              self.rows.len());
        let truncated = &lstatus[0..min(lstatus.len(), (self.screencols - rstatus.len()))];
        v.extend(truncated.as_bytes());
        // achieve right alignment by padding with whitespace
        v.extend(std::iter::repeat(b' ').take(self.screencols - truncated.len() - rstatus.len()));
        v.extend(rstatus.as_bytes());
        v.extend(NORMAL_COLOR);
        v.extend(b"\r\n");
        v
    }

    /// Return text that should be displayed in the message bar
    ///
    /// The message bar is for prompts or transient messages
    fn draw_message_bar(&mut self) -> Vec<u8> {
        let mut v: Vec<u8> = Vec::new();
        v.extend(CLEAR_LINE);

        // after a status update is made, only draw it for 5 seconds
        if !self.status_msg.is_empty() && get_time().sub(self.status_time).num_seconds() < 5 {
            v.extend(self.status_msg.as_bytes());
        }
        v
    }

    /// Return a single vector of all the row content that should be drawn
    ///
    /// Renders each of the lines in `rows` and applies the specified
    /// color codes for syntax highlighting. If there is no file, lines
    /// appear with `~`
    fn draw_rows(&self) -> Vec<u8> {
        let mut v = Vec::new();
        for y in 0..self.screenrows {
            v.extend(CLEAR_LINE);
            let filerow = self.position.rowoff + y;
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
                let line = &self.rows[filerow].rendered;
                let available_text = max(line.len() as i32 - self.position.coloff as i32, 0);
                let len = min(available_text, self.screencols as i32) as usize;
                let start = if len > 0 { self.position.coloff } else { 0 };

                let visible_line = line[start..start + len].as_bytes();
                let highlights = &self.rows[filerow].highlights[start..start + len];
                let mut current_color = Highlight::color(Highlight::Normal);

                // Add a code for the specified color if we aren't already using that color
                for (&c, &hl) in visible_line.iter().zip(highlights) {
                    let color = Highlight::color(hl);
                    if current_color != color {
                        v.extend(format!("\x1b[{}m", color).as_bytes());
                        current_color = color;
                    }
                    v.push(c)
                }

                // Set back to the normal color at the end of the line
                if current_color != Highlight::color(Highlight::Normal) {
                    v.extend(b"\x1b[39m");
                }
                v.extend(b"\r\n")
            }
        }
        v.extend(CLEAR_LINE);
        v
    }

    /// Grab the next keypress from `handle`
    ///
    /// Polls handle until a keypress is available. If it is
    /// a recognized escape sequence, we return the appropriate keypress
    /// othewise we just return the character `Keypress::Chr()`
    fn editor_read_key(handle: &mut Read) -> Keypress {

        // read a single byte from handle
        fn read1(handle: &mut Read) -> Option<u8> {
            let mut buffer: [u8; 1] = [0];
            match handle.take(1).read(&mut buffer) {
                Ok(1) => Some(buffer[0]),
                Ok(0) => None,
                Ok(_) | Err(_) => panic!("error"),
            }
        }

        // with raw mode we set a read timeout, so the read doesn't block waiting for data
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
                                (b'~', b'1') | (b'~', b'7') => return Keypress::Home,
                                (b'~', b'4') | (b'~', b'8') => return Keypress::End,
                                (b'~', b'3') => return Keypress::Del,
                                (b'~', b'5') => return Keypress::Page(Arrow::Up),
                                (b'~', b'6') => return Keypress::Page(Arrow::Down),
                                (_, _) => (),
                            }
                        }
                    }
                    (b'[', b'A') => return Keypress::Ar(Arrow::Up),
                    (b'[', b'B') => return Keypress::Ar(Arrow::Down),
                    (b'[', b'C') => return Keypress::Ar(Arrow::Right),
                    (b'[', b'D') => return Keypress::Ar(Arrow::Left),
                    (b'[', b'H') | (b'O', b'H') => return Keypress::Home,
                    (b'[', b'F') | (b'O', b'F') => return Keypress::End,
                    _ => (),
                }
            }
            return Keypress::Esc;
        }
        match c {
            127 => Keypress::Backspace,
            b'\r' => Keypress::Enter,
            CTRLH => Keypress::CtrlH,
            QUIT => Keypress::Quit,
            SAVE => Keypress::Save,
            FIND => Keypress::Find,
            _ => Keypress::Chr(c as char),
        }
    }
}


// Syntax highlighting implementation

/// Provides methods for providing color codes for every character in a line
impl<'a> Syntax<'a> {
    /// Take a filename and find the matching syntax object
    ///
    /// # Return value
    /// The first syntax struct in HLDB with a matching extension, or NO_SYNTAX
    fn from(filename: &str) -> &'static Syntax<'static> {
        filename
            .rsplit('.')
            .next()
            .and_then(|ext| {
                HLDB.iter()
                    .map(|&s| s)
                    .find(|syn| syn.filematch.contains(&ext))
            })
            .unwrap_or(NO_SYNTAX)
    }

    /// Whether `ch` is a separator
    ///
    /// Separator characters can mark the beginning/ending
    /// of units of text that can be highlighted
    fn is_separator(ch: char) -> bool {
        ch.is_whitespace() || ",.()+-/*=~%<>[];".contains(ch)
    }

    /// Parse a numeric literal out of line, returning Highlight codes for it.
    ///
    /// Numeric literals can be base10 integral, float, or binary/octal/hex
    /// provided it is prefixed with the appropriate `0x`/`0o`/`0b` prefix
    ///
    /// # Return Value
    /// a `Vec<Highlight>` containing the code for the prefix of the line that is numeric.
    ///
    /// # Examples
    /// ```
    /// assert_eq!(vec![Highlight::Number; 4], highlight_number("1234 test"));
    /// assert_eq!(vec![Highlight::Number; 4], highlight_number("0xCA test"));
    /// assert_eq!(Vec::new(), highlight_number("notnumber 1234 0xCA test"));
    /// ```
    fn highlight_number(line: &str) -> Vec<Highlight> {
        let bs = line.as_bytes();

        // numeric literals all start with a base 10 digit or 0
        let starts_numeric = (bs[0] as char).is_digit(10);
        if bs.len() == 1 || !starts_numeric {
            if (bs[0] as char).is_digit(10) {
                return vec![Highlight::Number];
            }
            return Vec::new();
        }
        let (radix, start) = match (bs[0], bs[1]) {
            (b'0', b'x') => (16, 2),
            (b'0', b'o') => (8, 2),
            (b'0', b'b') => (2, 2),
            _ => (10, 0),
        };

        // true if s has exactly one dot as it's prefix
        // `4.5` is a single numeric literal, however `4..5` (a range)
        // is not
        fn single_dot(s: &[u8]) -> bool {
            s[0] == b'.' && (s.len() < 2 || s[1] != b'.')
        }

        bs.iter()
            .enumerate()
            .take_while(|&(i, b)| {
                let c = *b as char;
                // when i < start, we are in the prefix (ex: `0x`)
                // which has already been validated
                i < start || c.is_digit(radix) || single_dot(&bs[i..])
            })
            .map(|_| Highlight::Number)
            .collect()
    }

    /// Parse a quoted string out of a line, returning Highlight codes for it.
    ///
    /// # Return value
    /// a `Vec<Highlight>` containing the code for the prefix of the line that is the string
    ///
    /// # Examples
    /// ```
    /// assert_eq!(vec![Highlight::Strings; 5], highlight_string("\"hi,\" she said"))
    /// assert_eq!(Vec::new(), highlight_string("no quotes"))
    /// assert_eq!(Vec::new(), highlight_string("'single quotes are not matched'"))
    /// ```
    fn highlight_string(input: &str) -> Vec<Highlight> {
        let line = input.as_bytes();
        let mut h = Vec::new();
        if line.len() < 2 || line[0] != b'\"' {
            return h;
        }
        h.push(Highlight::Strings);
        let mut i = 1;

        // if we encounter \, skip next character (don't check for closing quote)
        let mut escaped = false;
        while i < line.len() {
            h.push(Highlight::Strings);
            match (escaped, line[i]) {
                (false, b'\"') => return h,
                (false, b'\\') => escaped = true,
                (true, _) => escaped = false,
                _ => (),
            }
            i += 1;
        }
        h
    }

    /// Parse a single quoted character out of a line, returning Highlight codes for it.
    ///
    /// # Return value
    /// a `Vec<Highlight>` containing the code for the prefix of the line that is the literal
    ///
    /// # Examples
    /// ```
    /// assert_eq!(vec![Highlight::Strings; 3], highlight_string("'c' is a char"))
    /// assert_eq!(Vec::new(), highlight_string("no chars"))
    /// assert_eq!(vec![Highlight::Strings; 4], highlight_string("'\'' is a char"))
    /// ```
    fn highlight_char_literal(input: &str) -> Vec<Highlight> {
        let line = input.as_bytes();
        // character literal requires at least 3 characters
        if line[0] != b'\'' || line.len() < 3 {
            Vec::new()
        } else {
            let escaped = line[1] == b'\\' && line.len() > 3;
            let close_pos = if escaped { 3 } else { 2 };
            if line[close_pos] == b'\'' {
                vec![Highlight::Strings; close_pos + 1]
            } else {
                Vec::new()
            }
        }
    }

    /// Get the Highlight code to use for every character in `line`
    ///
    /// * `line` the line to highlight
    /// # Return value
    /// A `Vector<Highlight>` with a code for every character in the original `line`
    fn highlight(&self, line: &str) -> Vec<Highlight> {

        // Check if any keyword in keywords is a prefix of the string
        // return Some(match) for the first match
        fn keyword_match<'a>(keywords: &'a [&'a str], remainder: &str) -> Option<&'a str> {
            keywords
                .iter()
                .find(|&kw| &remainder[..min(remainder.len(), kw.len())] == *kw)
                .map(|s| *s)
        }

        // Copy the parsed highlights into existing and return the amount moved. None if
        // parsed was empty
        fn add_parsed(parsed: &[Highlight], existing: &mut [Highlight]) -> Option<usize> {
            let len = parsed.len();
            if len == 0 {
                return None;
            }
            for (muth, h) in existing[..len].iter_mut().zip(parsed.iter()) {
                *muth = *h;
            }
            Some(len)
        }

        let mut highlights = vec![Highlight::Normal; line.len()];
        if self.flags.is_empty() {
            return highlights;
        }
        let bs = line.as_bytes();
        let comment_len = self.comment_start.len();

        let mut prev_sep = true;
        let mut i = 0;
        while i < line.len() {
            // general pattern:
            // try to parse a prefix of the line starting at i
            // if we find something, increment i by the amount that the parser consumed
            // if nothing parses, just increment i by 1
            let c = bs[i] as char;
            if self.flags.contains(HL_STRINGS) {
                if let Some(n) = add_parsed(&Self::highlight_string(&line[i..]),
                                            &mut highlights[i..]) {
                    i += n;
                    prev_sep = false;
                    continue;
                }

                if let Some(n) = add_parsed(&Self::highlight_char_literal(&line[i..]),
                                            &mut highlights[i..]) {
                    i += n;
                    prev_sep = false;
                    continue;
                }
            }
            if self.flags.contains(HL_NUMBERS) && prev_sep {
                if let Some(n) = add_parsed(&Self::highlight_number(&line[i..]),
                                            &mut highlights[i..]) {
                    i += n;
                    prev_sep = false;
                    continue;
                }
            }
            if comment_len > 0 && &line[i..min(i + comment_len, line.len())] == self.comment_start {
                for x in &mut highlights[i..].iter_mut() {
                    *x = Highlight::Comment;
                }
                // line comments set the Highlight for the entire line suffx, so we are done
                break;
            }

            if prev_sep {
                // find if any keyword matched from either list and
                // return the correct highlight code for it
                let keyword_matched = keyword_match(self.keywords1, &line[i..])
                    .map(|k| (k, Highlight::Keyword1))
                    .or_else(|| {
                        keyword_match(self.keywords2, &line[i..]).map(|k| (k, Highlight::Keyword2))
                    });

                if let Some((kw, hl)) = keyword_matched {
                    // keywords must also be suffixed by a seperator, otherwise
                    // words like `fort` would match a `for` keyword
                    if bs.len() > i + kw.len() && Self::is_separator(bs[i + kw.len()] as char) {
                        for x in (&mut highlights[i..i + kw.len()]).iter_mut() {
                            *x = hl;
                        }
                        i += kw.len();
                        prev_sep = false;
                        continue;
                    }
                }
            }
            prev_sep = Self::is_separator(c);
            i += 1;
        }
        highlights
    }
}


// terminal commands

/// Create the control sequence for moving the cursor to the specified x,y position
fn to_pos(x: usize, y: usize) -> Vec<u8> {
    let cmd = format!("\x1b[{};{}H", y, x);
    cmd.into_bytes()
}

/// Write a control sequence to the terminal
fn execute(v: &[u8]) -> io::Result<()> {
    io::stdout().write_all(v)?;
    io::stdout().flush()
}

/// Get the current position of the cursor using vt100
fn get_cursor_position() -> io::Result<(u16, u16)> {
    execute(GET_CURSOR_POS)?;

    // read back answer from terminal
    // the response is supposed to look like 0x1b [24;80R
    let mut vec = Vec::new();
    let stdin = io::stdin();
    let mut handle = stdin.lock();
    handle.read_until(b'R', &mut vec)?;

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


fn main() {
    let rawterm = RawTerm::from(libc::STDIN_FILENO).unwrap();
    let mut editor = Editor::from(rawterm).unwrap();
    args()
        .nth(1)
        .map(|filename| editor.open(&filename).unwrap());
    editor.set_status_message("HELP: Ctrl-S = save | Ctrl-Q = quit | Ctrl-F = find".to_owned());
    editor.refresh_screen().unwrap();
    while editor.process_keypress() {
        editor.refresh_screen().unwrap();
    }
}
