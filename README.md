# enlist
Enlist Recreational Programming Language

# inspirations
This language is largely inspired by Jelly, an awesome golfing language made by PPCG moderator Dennis.

# reasons
Jelly contains some atoms (functions) and quicks (operators) which are two bytes, which sometimes causes it to be beaten by other golfing languages such as 05AB1E and Pyth. Enlist is designed to be as short as possible, especially when working with numbers and lists.

# usage

    enlist f <filename> [args...]: Read from a file using the Enlist codepage

    enlist fu <filename> [args...]: Read from a file using UTF-8

    enlist e <code> [args...]: Read from the second command line input using the Enlist codepage

    enlist eu <code> [args...]: Read from the second command line input using UTF-8

    Append `n` to the flag to output with a trailing newline
