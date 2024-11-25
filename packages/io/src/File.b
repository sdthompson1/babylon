module File

// A simple file I/O library.

import Int;
import String;

interface {

    // ** Types

    // "File" represents a file or file-like object (anything that supports read, write
    // and/or seek operations).
    extern type File (allocated);

    // TODO: we might include error codes, or more detail on errors here?
    datatype IOResult = OK | EOF | Error;


    // ** Reading from a file

    // Read upto num_bytes bytes from file into 'buffer'.
    // Returns the number of bytes actually read, together with a result
    // code (OK, EOF or read error).
    // Note: This will block until at least one byte has been read (or
    // an error or EOF has occurred).
    extern impure function read_bytes(ref file: File,
                                      ref buffer: u8[],
                                      num_bytes: u64): {IOResult, u64}
            = "File_read_bytes";
        requires allocated(file);
        requires num_bytes <= sizeof(buffer);
        ensures allocated(file);
        ensures sizeof(buffer) == old(sizeof(buffer));
        ensures return.0 == OK ==> u64_min(1, num_bytes) <= return.1 <= num_bytes;
        ensures return.0 != OK ==> return.1 == 0;

    // Read an entire line. Lines are delimited by newline bytes ('\n').
    // The line (or as much of it as will fit) will be copied into 'str', and a
    // zero byte appended. (The terminating '\n' character is NOT copied to 'str'.)
    // The second return value is the actual length of the line in the file
    // (which might be greater than strlen(str) if the line had to be truncated
    // to fit the buffer, or if the line contained "null" bytes).
    impure function read_str_ln(ref file: File,
                                ref str: u8[]): {IOResult, u64}
        requires allocated(file);
        requires sizeof(str) >= 1;
        ensures allocated(file);
        ensures sizeof(str) == old(sizeof(str));
        ensures valid_string(str);
        ensures strlen(str) <= return.1;
        ensures return.0 != OK ==> strlen(str) == return.1 == 0;


    // ** Writing to a file

    // Write num_bytes from buffer into file.
    extern impure function write_bytes(ref file: File,
                                       buffer: u8[],
                                       num_bytes: u64): IOResult
            = "File_write_bytes";
        requires allocated(file);
        requires num_bytes <= sizeof(buffer);
        ensures allocated(file);

    // Write bytes from the 'str' upto (but not including) the first zero byte.
    extern impure function write_str(ref file: File,
                                     str: u8[]): IOResult
            = "File_write_str";
        requires allocated(file);
        requires valid_string(str);
        ensures allocated(file);

    // Write from 'str' upto (but not including) the first zero byte. Then append a newline.
    impure function write_str_ln(ref file: File,
                                 str: u8[]): IOResult
        requires allocated(file);
        requires valid_string(str);
        ensures allocated(file);

    // Write the given integer as a string.
    impure function write_i64(ref file: File,
                              num: i64): IOResult
        requires allocated(file);
        ensures allocated(file);

    impure function write_u64(ref file: File,
                              num: u64): IOResult
        requires allocated(file);
        ensures allocated(file);

    // For convenience, we give "write integer" functions for smaller types
    // (i32, u16 and so on), although these just call the 64-bit versions!
    impure function write_i32(ref file: File, num: i32): IOResult
        requires allocated(file);
        ensures allocated(file);
    { return write_i64(file, num); }

    impure function write_i16(ref file: File, num: i16): IOResult
        requires allocated(file);
        ensures allocated(file);
    { return write_i64(file, num); }

    impure function write_i8(ref file: File, num: i8): IOResult
        requires allocated(file);
        ensures allocated(file);
    { return write_i64(file, num); }

    impure function write_u32(ref file: File, num: u32): IOResult
        requires allocated(file);
        ensures allocated(file);
    { return write_u64(file, num); }

    impure function write_u16(ref file: File, num: u16): IOResult
        requires allocated(file);
        ensures allocated(file);
    { return write_u64(file, num); }

    impure function write_u8(ref file: File, num: u8): IOResult
        requires allocated(file);
        ensures allocated(file);
    { return write_u64(file, num); }



    // ** Seeking

    datatype Whence = Begin | Current | End;

    extern impure function seek(ref file: File,
                                offset: i64,
                                whence: Whence): IOResult
            = "File_seek";
        requires allocated(file);
        requires whence == Begin ==> offset >= 0;
        ensures allocated(file);
        ensures return != EOF;


    // ** Closing a file

    extern impure function close(ref file: File): IOResult
            = "File_close";
        requires allocated(file);
        ensures !allocated(file);
        ensures return != EOF;


    // ** Opening disk files

    // The "filename" and "mode" are passed directly to fopen.
    extern impure function open(ref file: File, filename: u8[], mode: u8[]): IOResult
            = "File_open";
        requires !allocated(file);
        requires valid_string(filename);
        requires valid_string(mode);
        ensures allocated(file) <==> return == OK;
        ensures return != EOF;


    // ** Access to stdin, stdout and stderr streams

    extern impure function open_stdin(ref file: File): IOResult
            = "File_open_stdin";
        requires !allocated(file);
        ensures allocated(file) <==> return == OK;
        ensures return != EOF;

    extern impure function open_stdout(ref file: File): IOResult
            = "File_open_stdout";
        requires !allocated(file);
        ensures allocated(file) <==> return == OK;
        ensures return != EOF;

    extern impure function open_stderr(ref file: File): IOResult
            = "File_open_stderr";
        requires !allocated(file);
        ensures allocated(file) <==> return == OK;
        ensures return != EOF;
}

impure function read_str_ln(ref file: File, ref str: u8[]): {IOResult, u64}
    requires allocated(file);
    requires sizeof(str) >= 1;
    ensures allocated(file);
    ensures sizeof(str) == old(sizeof(str));
    ensures valid_string(str);
    ensures strlen(str) <= return.1;
    ensures return.0 != OK ==> strlen(str) == return.1 == 0;
{
    var buf: u8[1];
    var pos: u64 = 0;
    var total_read: u64 = 0;
    var size: u64 = sizeof(str);

    var fuel: u64 = U64_MAX - 1;

    while fuel > 0
        invariant allocated(file);
        invariant sizeof(str) == size;
        invariant pos <= size - 1;
        invariant fuel <= U64_MAX - 1;
        invariant pos <= total_read <= U64_MAX - 1 - fuel;
        decreases fuel;
    {
        // Read at most one byte.
        var r: {IOResult, u64} = read_bytes(file, buf, 1);

        // Examine the result.
        match r.0 {
        case Error =>
            // Zero out the string and return.
            str[0] = 0;
            return {Error, u64(0)};

        case EOF =>
            // If at least one byte read, then treat the string read so
            // far as a complete line; otherwise, return EOF.
            if total_read == 0 {
                str[0] = 0;
                return {EOF, u64(0)};
            } else {
                str[pos] = 0;
                return {OK, total_read};
            }

        case OK =>
            // Since we asked for 1 byte, we must have exactly 1 byte.
            assert r.1 == 1;
            var byte_read = buf[0];

            // If the byte is a newline, we are done.
            if byte_read == 10 {
                str[pos] = 0;
                return {OK, total_read};
            }

            // Otherwise, if there is room, deposit this byte into the buffer.
            if pos < size - 1 {
                str[pos] = byte_read;
                pos = pos + 1;
            }

            // We always increase total_read, whether the byte went into the buffer or not.
            total_read = total_read + 1;
        }

        // Continue looping.
        fuel = fuel - 1;
    }

    // This should never be reached, because U64_MAX is really big.
    str[0] = 0;
    return {Error, u64(0)};
}

impure function write_str_ln(ref file: File, str: u8[]): IOResult
    requires allocated(file);
    requires valid_string(str);
    ensures allocated(file);
{
    var r = write_str(file, str);
    match r {
    case OK =>
        return write_str(file, "\n");
    case _ =>
        return r;
    }
}

impure function write_i64(ref file: File, num: i64): IOResult
    requires allocated(file);
    ensures allocated(file);
{
    var buf: u8[21];
    i64_to_string(num, buf);
    return write_str(file, buf);
}

impure function write_u64(ref file: File, num: u64): IOResult
    requires allocated(file);
    ensures allocated(file);
{
    var buf: u8[21];
    u64_to_string(num, buf);
    return write_str(file, buf);
}
