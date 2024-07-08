// A simple 2D game engine.

module GameEngine

import IO;
import Limits;
import Maybe;
import MemAlloc;  // for 'default'
import Result;
import String;

interface {

    // Types:


    // ** The GameEngine itself.

    // Note: The "default" value of an extern type is the C null pointer value.
    // A GameEngine is considered "allocated" if it is NOT a null pointer (i.e. "not default").
    
    extern type GameEngine (allocated_if_not_default);


    // ** Graphics related types

    type TextureNum = u32;
    const MAX_TEXTURES: u32 = 1000000;

    type RGBA = {r: u8, g: u8, b: u8, a: u8};

    type Rectangle = {x: u32, y: u32, width: u32, height: u32};

    datatype BlendMode =
        BlendMode_None          // dst = src
      | BlendMode_Blend;        // dstRGB = srcRGB * srcA + dstRGB * (1-srcA)
                                //   dstA =      1 * srcA +   dstA * (1-srcA)

    // ** Event types
    
    datatype MouseButton =
          UnknownButton
        | LeftButton
        | MiddleButton
        | RightButton;

    datatype Event =
        AppQuitRequested
        
      | WindowHidden                   // Window is now (completely) invisible
      | WindowShown                    // Window is now (at least partly) visible
      | WindowSizeChanged {new_width: u32, new_height: u32}
      | WindowRequiresRedraw           // Window corrupted, needs redraw.

      | MouseEnteredWindow
      | MouseLeftWindow
      | MouseMoved { x: u32, y: u32 }
      | MousePressed { x: u32, y: u32, button: MouseButton }
      | MouseReleased { x: u32, y: u32, button: MouseButton };


    
    // "Ghost" types/functions:

    type EngineState = {
        textures: bool [],     // which textures are loaded
        blend_mode: BlendMode,
        colour: RGBA
    };

    ghost function engine_state(g: GameEngine): EngineState;

    ghost function valid_engine_state(s: EngineState): bool
    {
        return sizeof(s.textures) == u64(MAX_TEXTURES);
    }

    ghost function valid_engine(g: GameEngine): bool
    {
        return allocated(g) && valid_engine_state(engine_state(g));
    }

    // true if the given state is the initial engine state
    ghost function initial_engine_state(s: EngineState): bool
    {
        return valid_engine_state(s)
            && forall (i: TextureNum) i < MAX_TEXTURES ==> !s.textures[i]
            && s.blend_mode == BlendMode_None
            && s.colour == {r = u8(255), g = u8(255), b = u8(255), a = u8(255)};
    }

    // theorem: the initial_engine_state is a valid_engine_state
    ghost function initial_state_is_valid(s: EngineState)
        requires initial_engine_state(s);
        ensures valid_engine_state(s);
    {}

    ghost function set_texture(s: EngineState, texture_num: TextureNum): EngineState
        requires valid_engine_state(s);
        requires texture_num < MAX_TEXTURES;
    {
        var new_state = s;
        new_state.textures[texture_num] = true;
        return new_state;
    }

    ghost function clear_texture(s: EngineState, texture_num: TextureNum): EngineState
        requires valid_engine_state(s);
        requires texture_num < MAX_TEXTURES;
    {
        var new_state = s;
        new_state.textures[texture_num] = false;
        return new_state;
    }

        

    // Game Engine API:

    // ** Init/shutdown functions

    // Create a new GameEngine. This will open a window on the screen.
    extern function new_engine(ref io: IO,
                               ref engine: GameEngine,
                               title: u8[],
                               width: u32,
                               height: u32,
                               ref result: Result<{}>)
        requires !allocated(engine);
        requires valid_string(title);
        requires !allocated(result);
        
        ensures valid_c_result(result);
        ensures Result.is_error(result) ==> !allocated(engine);
        ensures Result.is_ok(result) ==>
            allocated(engine) &&
            initial_engine_state(engine_state(engine));


    // Shut down a GameEngine. The window will be closed.
    // (If any textures are still loaded, they will be unloaded automatically.)
    extern function free_engine(ref engine: GameEngine)
        requires valid_engine(engine);
        ensures !allocated(engine);


    // ** Texture loading

    // Create a texture. The caller decides the TextureNum, which must not already
    // be in use.
    // Although any TextureNum (upto MAX_TEXTURES) is allowed, it is better to use
    // small TextureNums (sequentially from zero if possible), as the C implementation
    // will use less memory in this case.
    // Note: 'pixels' array is accessed in [row,col] (or [y,x]) order.
    extern function create_texture(ref engine: GameEngine,
                                   texture_num: TextureNum,
                                   pixels: RGBA[,],
                                   ref result: Result<{}>)
        // engine valid
        requires valid_engine(engine);

        // texture num in range
        requires texture_num < MAX_TEXTURES;

        // texture not already loaded
        requires !engine_state(engine).textures[texture_num];

        requires !allocated(result);

        ensures valid_c_result<{}>(result);
        ensures valid_engine(engine);

        // on failure, state unchanged
        ensures !Result.is_ok<{}>(result) ==>
            engine_state(engine) == old(engine_state(engine));

        // on success, texture becomes loaded
        ensures Result.is_ok<{}>(result) ==> engine_state(engine)
            == set_texture( old(engine_state(engine)), texture_num );


    // Destroy a texture. This always succeeds.
    extern function destroy_texture(ref engine: GameEngine,
                                    texture_num: TextureNum)
        // engine valid
        requires valid_engine(engine);

        // texture num in range
        requires texture_num < MAX_TEXTURES;

        // this texture was previously loaded
        requires engine_state(engine).textures[texture_num];

        // afterwards, the texture becomes unloaded
        ensures valid_engine(engine);
        ensures engine_state(engine) ==
            clear_texture( old(engine_state(engine)), texture_num );
    

    // ** Set blending and colour state

    // The blend state affects all draw operations (including textures)
    // apart from clear_screen.
    extern function set_blend_mode(ref engine: GameEngine,
                                   blend_mode: BlendMode)
        requires valid_engine(engine);
        ensures valid_engine(engine);
        ensures engine_state(engine) ==
            { old(engine_state(engine)) with blend_mode = blend_mode };

    // The colour state affects all drawing operations e.g.
    //  - for clear screen, it sets the colour to clear to
    //  - for rectangle drawing, it sets the colour of the rectangle (and alpha if
    //    blending is enabled)
    //  - for texture drawing, it sets a colour and alpha modulation
    extern function set_colour(ref engine: GameEngine,
                               colour: RGBA)
        requires valid_engine(engine);
        ensures valid_engine(engine);
        ensures engine_state(engine) ==
            { old(engine_state(engine)) with colour = colour };


    // ** Clear screen

    // This should be called at the start of each frame (before any
    // other drawing operations).

    extern function clear_screen(ref engine: GameEngine)
        requires valid_engine(engine);
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));


    // ** Drawing textures onto the screen

    // Copy a texture onto the screen.
    // If src_rect is Nothing the entire texture will be drawn, otherwise
    // only the part of the texture indicated by src_rect will be drawn.
    // The top-left of the destination rectangle will be at (x,y) on the screen.
    extern function draw_texture(ref engine: GameEngine,
                                 texture_num: TextureNum,
                                 src_rect: Maybe<Rectangle>,
                                 x: u32,
                                 y: u32)
        // engine must be valid
        requires valid_engine(engine);

        // texture_num must be in range
        requires texture_num < MAX_TEXTURES;

        // the texture must be loaded
        requires engine_state(engine).textures[texture_num];

        // the engine state is unchanged
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));
    

    // ** Other drawing operations

    // Draw a filled rectangle
    extern function fill_rectangle(ref engine: GameEngine,
                                   rect: Rectangle)
        requires valid_engine(engine);
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));


    // ** Present image

    // This must be called at the end of each frame to submit the
    // final image to the display.
    extern function present(ref engine: GameEngine)
        requires valid_engine(engine);
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));


    // ** Events

    // This function will block until the next incoming event arrives.
    extern function wait_event(ref engine: GameEngine): Event
        requires valid_engine(engine);
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));

}
