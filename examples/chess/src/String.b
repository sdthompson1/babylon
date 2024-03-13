// Module for working with strings.

// Currently just contains a predicate to determine if a u8[] array
// is a valid string, which is to say, it contains a null character
// somewhere within it.

module String

interface {
    ghost function valid_string(s: u8[]): bool
    {
        return exists (idx:u64) idx < sizeof(s) && s[idx] == 0;
    }
}
