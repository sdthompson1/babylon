// Simple function to display a message box.
// Typically used for showing error messages.

module MessageBox

import CString;
import IO;

interface {
    extern function message_box(ref io: IO, msg: u8[])
        requires valid_c_string(msg);
}
