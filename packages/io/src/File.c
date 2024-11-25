#ifndef _WIN32
#define _FILE_OFFSET_BITS 64
#endif

#include <stdint.h>
#include <stdio.h>
#include <string.h>

enum IOResult {
    IO_OK,
    IO_EOF,
    IO_ERROR
};

enum Whence {
    WHENCE_BEGIN,
    WHENCE_CURRENT,
    WHENCE_END
};

static FILE *file_ptr(char *file)
{
    FILE *ptr;
    memcpy(&ptr, file, sizeof(FILE*));
    return ptr;
}

static char *buffer_ptr(char *buffer)
{
    char *ptr;
    memcpy(&ptr, buffer, sizeof(char*));
    return ptr;
}

void File_read_bytes(uint8_t *ret, char *file, char *buffer, uint64_t num_bytes)
{
    // Preconditions: file is open; buffer size >= num_bytes.
    // Postconditions: returns a pair {IOResult, count}.
    // On OK result, 1 <= count <= num_bytes; on any other result, count = 0.

    FILE *fptr = file_ptr(file);

    uint8_t io_result;
    uint64_t num_read;

    if (num_bytes == 0) {
        // Zero-sized reads cannot generate an error, but they can return
        // EOF if the "end-of-file indicator" is set.
        if (feof(fptr)) {
            io_result = IO_EOF;
        } else {
            io_result = IO_OK;
        }
        num_read = 0;

    } else {
        // Perform the read using fread.
        size_t r = fread(buffer_ptr(buffer),
                         1,
                         num_bytes,
                         fptr);

        if (r < num_bytes && ferror(fptr)) {
            // fread indicated error
            io_result = IO_ERROR;
            num_read = 0;
        } else if (r == 0) {
            // fread indicated EOF and no bytes read
            io_result = IO_EOF;
            num_read = 0;
        } else {
            // fread indicated EOF with at least one byte read (before the EOF),
            // *or*, fread indicated success
            io_result = IO_OK;
            num_read = r;
        }
    }

    *ret = io_result;
    memcpy(ret + 1, &num_read, 8);
}

void File_write_bytes(uint8_t *ret, char *file, char *buffer, uint64_t num_bytes)
{
    // Preconditions: file is open; buffer size >= num_bytes.
    // Returns an IOResult.

    // Note: for fwrite, EOF is not a relevant concept, so this function
    // returns IO_OK or IO_ERROR only.

    if (num_bytes == 0) {
        *ret = IO_OK;
    } else {
        size_t w = fwrite(buffer_ptr(buffer),
                          1,
                          num_bytes,
                          file_ptr(file));

        if (w == num_bytes) {
            *ret = IO_OK;
        } else {
            *ret = IO_ERROR;
        }
    }
}

void File_write_str(uint8_t *ret, char *file, char *buffer)
{
    // Preconditions: file != NULL, buffer contains a null terminated string.
    // Returns an IOResult.

    int r = fputs(buffer_ptr(buffer), file_ptr(file));

    if (r >= 0) {
        *ret = IO_OK;
    } else {
        *ret = IO_ERROR;
    }
}

static int translate_whence(uint8_t whence)
{
    switch (whence) {
    case WHENCE_BEGIN: return SEEK_SET;
    case WHENCE_CURRENT: return SEEK_CUR;
    case WHENCE_END: return SEEK_END;
    default: return SEEK_SET;  // should never happen
    }
}

void File_seek(uint8_t *ret, char *file, int64_t offset, uint8_t whence)
{
    // Preconditions: file is open; if WHENCE_BEGIN then offset >= 0.
    // Returns an IOResult (not IO_EOF).

    int origin = translate_whence(whence);

#ifdef _WIN32
    int r = _fseeki64(file_ptr(file), offset, origin);
#else
    int r = fseeko(file_ptr(file), offset, origin);
#endif

    if (r == 0) {
        *ret = IO_OK;
    } else {
        *ret = IO_ERROR;
    }
}

void File_open(uint8_t *ret, char *file, char *filename_buf, char *mode_buf)
{
    // Preconditions: file points to NULL; filename_buf and mode_buf contain null terminated strings.
    // Postcondition: file points to non-NULL if and only if return is IO_OK. Does not return IO_EOF.

    FILE *f = fopen(buffer_ptr(filename_buf), buffer_ptr(mode_buf));
    if (f == NULL) {
        *ret = IO_ERROR;
    } else {
        memcpy(file, &f, sizeof(FILE*));
        *ret = IO_OK;
    }
}

void File_close(uint8_t *ret, char *file)
{
    // Precondition: file is open.
    // Postcondition: file is closed (no matter the return value).
    // Return value is an IOResult (not IO_EOF).

    // Extract the FILE*
    FILE *f = file_ptr(file);
    FILE *null_file = NULL;
    memcpy(file, &null_file, sizeof(FILE*));

    // Don't do anything if the file was "opened" using open_stdin or open_stdout or open_stderr.
    if (f == stdin || f == stdout || f == stderr) {
        *ret = IO_OK;
        return;
    }

    // Close the file.
    int r = fclose(f);

    if (r == 0) {
        *ret = IO_OK;
    } else {
        *ret = IO_ERROR;
    }
}

void File_open_stdin(uint8_t *ret, char *file)
{
    memcpy(file, &stdin, sizeof(FILE*));
    *ret = IO_OK;
}

void File_open_stdout(uint8_t *ret, char *file)
{
    memcpy(file, &stdout, sizeof(FILE*));
    *ret = IO_OK;
}

void File_open_stderr(uint8_t *ret, char *file)
{
    memcpy(file, &stderr, sizeof(FILE*));
    *ret = IO_OK;
}
