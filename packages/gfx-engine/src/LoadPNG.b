// This is a small (optional) helper module that allows loading a
// PNG file from disk. It may be useful for creating the pixel arrays
// required by GfxEngine.create_texture.

// At the moment this is basically just a wrapper around the stb_image
// public domain C library. See stb_image.h.

module LoadPNG

import Either;
import String;

interface {
    type RGBA = {r: u8, g: u8, b: u8, a: u8};

    // Loads RGBA data in [row,col] order.
    extern function load_png(filename: u8[],
                             ref result: Either<u8[*], RGBA[*,*]>)
        requires valid_string(filename);
        requires !allocated(result);

        ensures match result {
            case Left(err_msg) =>
                valid_string(err_msg) || sizeof(err_msg) == 0
            case Right(pixels) =>
                true
        };
}
