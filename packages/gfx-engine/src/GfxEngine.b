module GfxEngine

// from coretypes
import Either;
import Maybe;
import String;

// from gfx-engine
import Key;

interface {

    // ** Types

    extern type GfxEngine (allocated);

    type TextureNum = u32;
    const MAX_TEXTURES: u32 = 1000000;

    type RGBA = {r: u8, g: u8, b: u8, a: u8};

    type Rectangle = {x: i32, y: i32, width: i32, height: i32};

    datatype BlendMode =
        BlendMode_None          // dst = src
      | BlendMode_Blend;        // dstRGB = srcRGB * srcA + dstRGB * (1-srcA)
                                //   dstA =      1 * srcA +   dstA * (1-srcA)

    datatype MouseButton =
          UnknownButton
        | LeftButton
        | MiddleButton
        | RightButton;

    datatype Event =
        AppQuitRequested
        
      | WindowHidden                   // Window is now (completely) invisible
      | WindowShown                    // Window is now (at least partly) visible
      | WindowSizeChanged {new_width: i32, new_height: i32}
      | WindowRequiresRedraw           // Window corrupted, needs redraw.

      | MouseEnteredWindow
      | MouseLeftWindow
      | MouseMoved { x: i32, y: i32 }
      | MousePressed { x: i32, y: i32, button: MouseButton }
      | MouseReleased { x: i32, y: i32, button: MouseButton }

      | KeyPressed { key: Key }
      | KeyReleased { key: Key };


    
    // ** Engine State (ghost type/functions)

    type EngineState = {
        textures: bool [],     // which textures are loaded
        blend_mode: BlendMode,
        colour: RGBA,
        clip_rect: Maybe<Rectangle>,
        window_open: bool
    };

    ghost function engine_state(g: GfxEngine): EngineState;
        requires allocated(g);

    ghost function valid_engine_state(s: EngineState): bool
    {
        return sizeof(s.textures) == MAX_TEXTURES;
    }

    ghost function valid_engine(g: GfxEngine): bool
    {
        return allocated(g) && valid_engine_state(engine_state(g));
    }

    // true if the given state is the initial engine state
    ghost function initial_engine_state(s: EngineState): bool
    {
        return valid_engine_state(s)
            && (forall (i: TextureNum) i < MAX_TEXTURES ==> !s.textures[i])
            && s.blend_mode == BlendMode_None
            && s.colour == {r = u8(255), g = u8(255), b = u8(255), a = u8(255)}
            && s.clip_rect == Nothing
            && !s.window_open;
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


    // ** Helper Functions

    function rgb(r: u8, g: u8, b: u8): RGBA {
        return {r=r, g=g, b=b, a=u8(255)};
    }
    
    function rgba(r: u8, g: u8, b: u8, a: u8): RGBA {
        return {r=r, g=g, b=b, a=a};
    }

    function point_in_rect(x: i64, y: i64, rect: Rectangle): bool
    {
        return i64(rect.x) <= x < i64(rect.x) + i64(rect.width)
            && i64(rect.y) <= y < i64(rect.y) + i64(rect.height);
    }


    // ** Init/Shutdown

    // Create a new GfxEngine.
    // Sets 'result' to either Left(error_message) or Right(new_engine).
    extern impure function new_engine(ref result: Either<u8[*], GfxEngine>)
        requires !allocated(result);
        ensures match result {
            case Left(err_msg) =>
                valid_string(err_msg) || sizeof(err_msg) == 0
            case Right(engine) =>
                valid_engine(engine) && initial_engine_state(engine_state(engine))
            };

    // Shut down a GfxEngine.
    // (If the window is open, it will be automatically closed.)
    extern function free_engine(ref engine: GfxEngine)
        requires valid_engine(engine);
        ensures !allocated(engine);


    // ** Window Operations

    // Open the graphics window at a given size.
    // (For simplicity, only one window is allowed at a time currently.)
    extern impure function open_window(ref engine: GfxEngine,
                                       title: u8[],
                                       width: u32,
                                       height: u32,
                                       ref result: Either<u8[*], {}>)
        requires valid_engine(engine);
        requires !engine_state(engine).window_open;
        requires valid_string(title);
        requires !allocated(result);
        ensures valid_engine(engine);
        ensures match result {
            case Left(err_msg) =>
                (valid_string(err_msg) || sizeof(err_msg) == 0)
                && engine == old(engine);
            case Right{} => engine_state(engine) ==
                { old(engine_state(engine)) with window_open = true, clip_rect = Nothing }
        };

    // Close the graphics window.
    // (If any textures exist, they will be automatically freed.)
    extern function close_window(ref engine: GfxEngine)
        requires valid_engine(engine);
        requires engine_state(engine).window_open;
        ensures valid_engine(engine);
        ensures sizeof(engine_state(engine).textures) == MAX_TEXTURES;
        ensures forall (i: u64) i < MAX_TEXTURES ==> !engine_state(engine).textures[i];
        ensures engine_state(engine).blend_mode == old(engine_state(engine).blend_mode);
        ensures engine_state(engine).colour == old(engine_state(engine).colour);
        ensures engine_state(engine).clip_rect == Nothing;
        ensures !engine_state(engine).window_open;

    // Get desktop resolution. This might be useful for choosing
    // an initial window size.
    // (On error, returns 0,0.)
    extern impure function get_desktop_resolution(ref engine: GfxEngine): {u32, u32}
        requires valid_engine(engine);
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));


    // ** Texture Loading

    // Note: These functions require the window to be open, because (at least in SDL)
    // we cannot create textures before knowing the pixel format of the window.


    // Create a texture. The caller decides the TextureNum, which must not
    // already be in use.

    // Although any TextureNum (up to MAX_TEXTURES) is allowed, it is better to
    // use small TextureNums (sequentially from zero) if possible, as the C
    // implementation will use less memory in this case.

    // Note: the 'pixels' array is accessed in [row,col] or [y,x] order.

    extern impure function create_texture(ref engine: GfxEngine,
                                          texture_num: TextureNum,
                                          pixels: RGBA[,],
                                          ref result: Either<u8[*], {}>)
        // engine valid
        requires valid_engine(engine);
        requires engine_state(engine).window_open;

        // texture num in range, and not already loaded
        requires texture_num < MAX_TEXTURES;
        requires !engine_state(engine).textures[texture_num];

        requires !allocated(result);

        ensures valid_engine(engine);

        ensures match result {
            case Left(err_msg) =>
                // On failure, engine state is unchanged
                (valid_string(err_msg) || sizeof(err_msg) == 0)
                && engine == old(engine);
                
            case Right{} => engine_state(engine) ==
                set_texture( old(engine_state(engine)), texture_num );
        };


    // Destroy a texture. This always succeeds.

    extern function destroy_texture(ref engine: GfxEngine,
                                    texture_num: TextureNum)
        // engine valid
        requires valid_engine(engine);
        requires engine_state(engine).window_open;

        // texture num in range, and was previously loaded
        requires texture_num < MAX_TEXTURES;
        requires engine_state(engine).textures[texture_num];

        // afterwards, the texture becomes unloaded
        ensures valid_engine(engine);
        ensures engine_state(engine) ==
            clear_texture( old(engine_state(engine)), texture_num );


    // ** Set rendering state (blending, colour, clipping)

    // The blend state affects all draw operations (including textures)
    // except for clear_screen.
    extern function set_blend_mode(ref engine: GfxEngine,
                                   blend_mode: BlendMode)
        requires valid_engine(engine);
        ensures valid_engine(engine);
        ensures engine_state(engine) ==
            { old(engine_state(engine)) with blend_mode = blend_mode };

    // The colour state affects all drawing operations e.g.
    //  - for clear_screen, it sets the colour to clear to;
    //  - for rectangle drawing, it sets the colour of the rectangle
    //    (and alpha, if blending is enabled);
    //  - for texture drawing, it sets a colour and alpha modulation.
    extern function set_colour(ref engine: GfxEngine,
                               colour: RGBA)
        requires valid_engine(engine);
        ensures valid_engine(engine);
        ensures engine_state(engine) ==
            { old(engine_state(engine)) with colour = colour };

    // If a clip rectangle is set, then all drawing operations (except
    // clear_screen) are clipped to the intersection of the given
    // rectangle and the window itself.
    // Setting to 'Nothing' disables clipping.
    extern function set_clip_rect(ref engine: GfxEngine, rect: Maybe<Rectangle>)
        requires valid_engine(engine);
        requires engine_state(engine).window_open;
        ensures valid_engine(engine);
        ensures engine_state(engine) ==
            { old(engine_state(engine)) with clip_rect = rect };


    // ** Clear screen

    // This should be called at the start of each frame, before any
    // other drawing operations.

    extern function clear_screen(ref engine: GfxEngine)
        requires valid_engine(engine);
        requires engine_state(engine).window_open;
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));


    // ** Drawing ("blitting") textures onto the screen

    // Copy a texture onto the screen.

    // If src_rect is Nothing, the entire texture will be drawn, otherwise
    // only the part of the texture indicated by src_rect will be drawn.
    // (src_rect will be clipped to the actual size of the texture.)

    // The top-left of the destination rectangle will be at (x,y) on the
    // screen. (x,y are signed to allow for partially-off-screen drawing
    // and clipping.)

    datatype FlipMode = Flip_None | Flip_Horiz | Flip_Vert | Flip_Both;

    extern function draw_texture(ref engine: GfxEngine,
                                 texture_num: TextureNum,
                                 src_rect: Maybe<Rectangle>,
                                 x: i32,
                                 y: i32,
                                 flip: FlipMode)
        // engine valid
        requires valid_engine(engine);
        requires engine_state(engine).window_open;

        // texture_num in range, and texture loaded
        requires texture_num < MAX_TEXTURES;
        requires engine_state(engine).textures[texture_num];

        // the engine state is unchanged.
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));


    // ** Other drawing operations

    // Draw a filled rectangle
    extern function fill_rectangle(ref engine: GfxEngine,
                                   rect: Rectangle)
        requires valid_engine(engine);
        requires engine_state(engine).window_open;
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));

    // Draw a rectangle outline (1 pixel wide)
    extern function outline_rectangle(ref engine: GfxEngine,
                                      rect: Rectangle)
        requires valid_engine(engine);
        requires engine_state(engine).window_open;
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));


    // ** Present image

    // This must be called at the end of each frame to submit the final
    // image to the display.

    extern function present(ref engine: GfxEngine)
        requires valid_engine(engine);
        requires engine_state(engine).window_open;
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));


    // ** Events

    // This function will pop one event from the queue if available, or
    // return Nothing otherwise. It does not block.
    extern impure function poll_event(ref engine: GfxEngine): Maybe<Event>
        requires valid_engine(engine);
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));

    // This function will block until the next incoming event arrives.
    extern impure function wait_event(ref engine: GfxEngine): Event
        requires valid_engine(engine);
        ensures valid_engine(engine);
        ensures engine_state(engine) == old(engine_state(engine));
}
