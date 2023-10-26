// Module for working with C-style strings.

// Currently just contains a predicate to determine if a u8[] array
// is a valid C-style string, which is to say, it contains a NUL
// character somewhere within it.

module CString

interface {
    ghost function valid_c_string(s: u8[]): bool
    {
        return exists (idx:u64) idx < sizeof(s) && s[idx] == 0;
    }
}
