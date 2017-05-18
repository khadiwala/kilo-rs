# kilo-rs
A port of the Kilo text editor to rust

This is a port of [kilo](https://github.com/antirez/kilo), a simple text editor written in < 1000 lines of C that supports search and syntax highlighting. 
This implementation also leaned heavily on [this tutorial](http://viewsourcecode.org/snaptoken/kilo/) which walks through the kilo source.

Usage: kilo `<filename>`

Keys:

    CTRL-S: Save
    CTRL-Q: Quit
    CTRL-F: Find string in file (ESC to exit search, arrows to navigate)

The port supports roughly the same set of features kilo supports, including search and some basic syntax highlighting (but for rust instead of c). Like kilo, it uses no higher level terminal libraries (no curses) and few external dependencies.
