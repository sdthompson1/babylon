// load_texture function

// This is placed in its own module -- originally I had it in ChessMain but
// that didn't work because the verification of ChessMain.load_textures failed.

// The reason for the failure seems to be that the verifier tries to
// expand out all the calls to load_texture in ChessMain.load_textures,
// using the full definition of load_texture, which then creates a huge
// function which is too big for the verifier to analyse.

// If we put load_texture in a separate module, so that the verifier can
// only see the interface (with the pre and post conditions), not the
// full definition, then it works.

// In future it would be good if there were mechanisms for showing or hiding
// particular definitions when invoking the verifier (a bit like "using" in
// Isabelle); that would provide an alternative way of solving the problem.

module LoadTexture

import GameEngine;
import IO;
import MemAlloc;
import Result;

interface {
    const HIGHEST_TEXTURE_NUM = 16;

    function load_texture(ref mem: Mem,
                          ref io: IO,
                          ref engine: GameEngine,
                          ref result: Result<{}>,
                          texture_num: TextureNum,
                          filename: u8[])

        requires texture_num <= HIGHEST_TEXTURE_NUM;

        requires sizeof(filename) > u64(0);
        requires filename[sizeof(filename) - u64(1)] == 0;

        requires valid_engine(engine);
        requires !engine_state(engine).textures[texture_num];

        requires valid_c_result<{}>(result);

        // if result is error initially, we do not attempt the load
        ensures is_error<{}>(old(result)) ==> result == old(result);

        // if result is ok, then the texture has loaded
        ensures is_ok<{}>(result) ==> engine_state(engine)
            == set_texture(old(engine_state(engine)), texture_num);

        // if result is error, then the engine state is unchanged
        ensures is_error<{}>(result) ==> engine_state(engine)
            == old(engine_state(engine));

        ensures valid_engine(engine);
        ensures valid_c_result<{}>(result);    
}

import CString;
import LoadPNG;
import Maybe;
import StringBuffer;

function load_texture(ref mem: Mem,
                      ref io: IO,
                      ref engine: GameEngine,
                      ref result: Result<{}>,
                      texture_num: TextureNum,
                      filename: u8[])

    requires texture_num <= HIGHEST_TEXTURE_NUM;

    requires valid_c_string(filename);
    
    requires valid_engine(engine);
    requires !engine_state(engine).textures[texture_num];

    requires valid_c_result<{}>(result);

    ensures is_error<{}>(old(result)) ==> result == old(result);

    ensures is_ok<{}>(result) ==> engine_state(engine)
        == set_texture(old(engine_state(engine)), texture_num);

    ensures is_error<{}>(result) ==> engine_state(engine)
        == old(engine_state(engine));

    ensures valid_engine(engine);
    ensures valid_c_result<{}>(result);    
{
    if is_error<{}>(result) {
        // Do not attempt the load
        return;
    }

    var img: LoadPNG.RGBA[,];
    var load_png_result: Result<{}>;
    load_png(io, filename, img, load_png_result);
    
    match load_png_result {
    case Error(ref msg) =>
        // Try to make a new err msg, if we can allocate space for it

        var MAX_ERR_MSG_LEN = u64(1024);
        var sb: StringBuffer;
        var resize_result = resize_string_buffer(mem, sb, MAX_ERR_MSG_LEN);
        
        if !resize_result {
            // no memory, just use the original error message.
            swap sb.buf, msg;

        } else {
            // we allocated a buffer, write the new message into it.
            append_string(sb, "Failed to load ");
            append_c_string(sb, filename);
            append_string(sb, ":\n");
            append_c_string(sb, msg);
            null_terminate(sb);
            var free_result = resize_array<u8>(mem, msg, 0);
        }

        // Now we have to get sb.buf into an error Result.
        // This is slightly awkward unfortunately - we have to swap it into place.
        var empty_string: u8[];
        result = Error<{}>(empty_string);
        match result {
        case Error(ref err_msg) => swap err_msg, sb.buf;
        }

    case Ok({}) =>
        // The load was successful, now let's send the pixel data to the GameEngine.
        create_texture(engine, texture_num, img, result);
        
        // Free the pixel array as it's no longer needed.
        var free_result = resize_2d_array<LoadPNG.RGBA>(mem, img, 0, 0);
    }
}
