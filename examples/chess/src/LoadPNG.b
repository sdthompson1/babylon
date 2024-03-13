// PNG image loader (this is basically just a wrapper around the stb_image library).

module LoadPNG

import IO;
import Result;
import String;

interface {
    type RGBA = {r: u8, g: u8, b: u8, a: u8};

    // Loads RGBA data in [row,col] order.
    extern function load_png(ref io: IO,
                             filename: u8[],
                             ref pixels: RGBA[*,*],
                             ref result: Result<{}>)
        requires valid_string(filename);
        requires !allocated(pixels);
        requires !allocated(result);
        
        ensures valid_c_result<{}>(result);
        ensures is_ok<{}>(result) <==> allocated(pixels);
}
