// Simple function to display a message box.
// Typically used for showing error messages.

module MessageBox

import String;

interface {
    extern function message_box(msg: u8[])
        requires sizeof(msg) == 0 || valid_string(msg);
}
