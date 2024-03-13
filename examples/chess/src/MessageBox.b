// Simple function to display a message box.
// Typically used for showing error messages.

module MessageBox

import IO;
import String;

interface {
    extern function message_box(ref io: IO, msg: u8[])
        requires valid_string(msg);
}
