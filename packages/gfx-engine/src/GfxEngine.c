
//--------------------------------------------------------------
// Includes

#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <SDL2/SDL.h>


//--------------------------------------------------------------
// Enums

enum BlendMode {
    BLEND_MODE_NONE,
    BLEND_MODE_BLEND
};

enum MouseButtonTag {
    UNKNOWN_BUTTON,
    LEFT_BUTTON,
    MIDDLE_BUTTON,
    RIGHT_BUTTON
};

enum EventTag {
    APP_QUIT_REQUESTED,
    WINDOW_HIDDEN,
    WINDOW_SHOWN,
    WINDOW_SIZE_CHANGED,
    WINDOW_REQUIRES_REDRAW,
    MOUSE_ENTERED_WINDOW,
    MOUSE_LEFT_WINDOW,
    MOUSE_MOVED,
    MOUSE_PRESSED,
    MOUSE_RELEASED,
    KEY_PRESSED,
    KEY_RELEASED
};


//--------------------------------------------------------------
// Engine state

struct Texture {
    SDL_Texture *texture;
    int width, height;
    enum BlendMode blend_mode;
    uint8_t colour[4];  // rgba
};

struct GfxEngine {
    SDL_Window *window;
    SDL_Renderer *renderer;

    struct Texture *texture_array;
    uint32_t texture_array_size;

    enum BlendMode blend_mode;
    uint8_t colour[4];  // rgba
    bool draw_state_modified;
};


//--------------------------------------------------------------
// Error message helpers

static void make_string_3(char *u8_array,
                          const char *string1,
                          const char *string2,
                          const char *string3)
{
    uint64_t len1 = string1 ? strlen(string1) : 0;
    uint64_t len2 = string2 ? strlen(string2) : 0;
    uint64_t len3 = string3 ? strlen(string3) : 0;

    uint64_t len = len1 + len2 + len3 + 1;

    char *ptr = malloc(len);
    if (ptr == NULL) {
        memset(u8_array, 0, sizeof(char*) + 8);
    } else {
        memcpy(u8_array, &ptr, sizeof(ptr));
        memcpy(u8_array + sizeof(ptr), &len, 8);
        if (string1) memcpy(ptr, string1, len1);
        if (string2) memcpy(ptr + len1, string2, len2);
        if (string3) memcpy(ptr + len1 + len2, string3, len3);
        ptr[len - 1] = 0;
    }
}

static void make_string(char *u8_array, const char *string)
{
    make_string_3(u8_array, string, NULL, NULL);
}

static void make_sdl_error_string(char *u8_array, const char *prefix)
{
    make_string_3(u8_array, prefix, ": ", SDL_GetError());
}


//--------------------------------------------------------------
// Init and shutdown

// requires: 'result' points to an unallocated "Either" object
// ensures (success case):
//   result[0] == 1, result[1] onwards is a valid GfxEngine* pointer
// ensures (failure case):
//   result[0] == 0, result[1] onwards is either {NULL, 0} or {p, len}
//     where p points to an allocated error message string
void new_engine(char *result)
{
    // Do not allow multiple engines to exist simultaneously
    if (SDL_WasInit(0)) {
        result[0] = 0;
        make_string(&result[1], "GfxEngine already created");
        return;
    }

    // Allocate memory for the GfxEngine struct
    struct GfxEngine *engine = malloc(sizeof(struct GfxEngine));
    if (engine == NULL) {
        result[0] = 0;
        make_string(&result[1], "malloc failed");
        return;
    }

    // Init SDL
    if (SDL_Init(SDL_INIT_EVENTS | SDL_INIT_VIDEO) != 0) {
        free(engine);
        result[0] = 0;
        make_sdl_error_string(&result[1], "SDL_Init failed");
        return;
    }

    // Setup initial engine state
    engine->window = NULL;
    engine->renderer = NULL;
    engine->texture_array = NULL;
    engine->texture_array_size = 0;
    engine->blend_mode = BLEND_MODE_NONE;
    memset(&engine->colour[0], 255, 4);   // set initial colour to white
    engine->draw_state_modified = true;  // force state update on first draw

    // Return result
    result[0] = 1;
    void *ptr = (void*)engine;
    memcpy(&result[1], &ptr, sizeof(ptr));
}

void close_window(void **gfx_engine);

// requires: *gfx_engine != NULL
// ensures: *gfx_engine = NULL
void free_engine(void **gfx_engine)
{
    struct GfxEngine *engine = (struct GfxEngine *) *gfx_engine;

    // Automatically close the window if required.
    if (engine->window) {
        close_window(gfx_engine);
    }

    // Close down SDL.
    SDL_Quit();

    // Free memory.
    free(engine->texture_array);
    free(engine);

    // Ensure postcondition is satisfied.
    *gfx_engine = NULL;
}


//--------------------------------------------------------------
// Window operations

// requires: *gfx_engine valid, window not open, title valid string,
//           err_msg points to {NULL, 0}
// ensures (success case): window now open, result[0] == 1
// ensures (failure case): gfx engine unchanged, result[0] == 0,
//     rest of result contains err msg descriptor or {NULL, 0}
void open_window(void **gfx_engine,
                 char *title_u8_array,
                 uint32_t width,
                 uint32_t height,
                 char *result)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;

    // Open a window.
    const char *title;
    memcpy(&title, title_u8_array, sizeof(char*));

    const int sdl_flags = SDL_WINDOW_ALLOW_HIGHDPI | SDL_WINDOW_RESIZABLE;

    engine->window = SDL_CreateWindow(title,
                                      SDL_WINDOWPOS_UNDEFINED,
                                      SDL_WINDOWPOS_UNDEFINED,
                                      width,
                                      height,
                                      sdl_flags);

    if (engine->window == NULL) {
        result[0] = 0;
        make_sdl_error_string(&result[1], "SDL_CreateWindow failed");
        return;
    }

    // Create renderer.
    engine->renderer = SDL_CreateRenderer(engine->window,
                                          -1,  // use first available renderer
                                          0);  // no flags
    if (engine->renderer == NULL) {
        result[0] = 0;
        make_sdl_error_string(&result[1], "SDL_CreateRenderer failed");
        SDL_DestroyWindow(engine->window);
        engine->window = NULL;
        return;
    }

    // Ensure clip rect is unset initially (it should be, but this will make sure).
    // (Note: errors ignored.)
    SDL_RenderSetClipRect(engine->renderer, NULL);

    // Force state update on first draw.
    engine->draw_state_modified = true;

    // Success.
    result[0] = 1;
}

void destroy_texture(void **gfx_engine, uint32_t texture_num);

// requires: *gfx_engine valid, window open
// ensures: all textures freed, clip rect unset, other state unchanged, window closed.
void close_window(void **gfx_engine)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;

    // Automatically free all textures if required.
    for (uint32_t index = 0; index < engine->texture_array_size; ++index) {
        if (engine->texture_array[index].texture) {
            destroy_texture(gfx_engine, index);
        }
    }

    // Destroy the SDL renderer and window objects.
    SDL_DestroyRenderer(engine->renderer);
    engine->renderer = NULL;

    SDL_DestroyWindow(engine->window);
    engine->window = NULL;
}

// requires: *gfx_engine valid
// returns: {u32, u32} (on error returns 0, 0)
void get_desktop_resolution(char *ret, void **gfx_engine)
{
    // note: this doesn't actually use the gfx_engine at all
    SDL_DisplayMode mode;
    int err = SDL_GetDesktopDisplayMode(0,      // display index
                                        &mode);
    if (err) {
        memset(ret, 0, 8);
    } else {
        uint32_t w = mode.w;
        uint32_t h = mode.h;
        memcpy(ret, &w, 4);
        memcpy(ret + 4, &h, 4);
    }
}


//--------------------------------------------------------------
// Texture loading

// requires: *gfx_engine valid, window open, texture not previously used, err_msg {NULL, 0}
// ensures (return 0): engine state unchanged, err_msg valid string or {NULL, 0}
// ensures (return 1): texture becomes loaded, other state unchanged, err_msg unchanged
void create_texture(void **gfx_engine,
                    uint32_t texture_num,
                    char *pixels,
                    char *result)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;

    // Grow the texture array if required.
    if (texture_num >= engine->texture_array_size) {
        uint32_t new_size = engine->texture_array_size * 2;
        if (new_size < 10) {
            new_size = 10;
        }
        if (texture_num >= new_size) {
            new_size = texture_num + 1;
        }

        struct Texture *new_array = realloc(engine->texture_array,
                                            new_size * sizeof(struct Texture));
        if (new_array == NULL) {
            result[0] = 0;
            make_string(&result[1], "failed to expand texture array");
            return;
        }

        engine->texture_array = new_array;

        for (uint32_t i = engine->texture_array_size; i < new_size; ++i) {
            engine->texture_array[i].texture = NULL;
        }

        engine->texture_array_size = new_size;
    }

    // Read values from the array descriptor.
    char *pixel_data;
    uint64_t width, height;
    memcpy(&pixel_data, pixels, sizeof(char*));
    memcpy(&height, pixels + sizeof(char*), 8);     // first array index is "y"
    memcpy(&width, pixels + sizeof(char*) + 8, 8);  // second array index is "x"

    // SDL represents width and height as int, which might not be able
    // to store the array size that we have been given.
    if (width > INT_MAX || height > INT_MAX) {
        result[0] = 0;
        make_string(&result[1], "texture too big");
        return;
    }

    // Create the SDL texture object
    int bpp;
    Uint32 rmask, gmask, bmask, amask;
    SDL_PixelFormatEnumToMasks(SDL_PIXELFORMAT_RGBA32, &bpp, &rmask, &gmask, &bmask, &amask);

    SDL_Surface *surface = SDL_CreateRGBSurfaceFrom(pixel_data,
                                                    width,
                                                    height,
                                                    bpp,
                                                    width * 4,
                                                    rmask,
                                                    gmask,
                                                    bmask,
                                                    amask);
    if (surface == NULL) {
        result[0] = 0;
        make_string(&result[1], "SDL_CreateRGBSurfaceFrom failed");
        return;
    }

    SDL_Texture *texture = SDL_CreateTextureFromSurface(engine->renderer, surface);
    SDL_FreeSurface(surface);
    if (texture == NULL) {
        result[0] = 0;
        make_string(&result[1], "SDL_CreateTextureFromSurface failed");
        return;
    }

    // Create the Texture struct and set initial blend and colour states.
    struct Texture *tx = &engine->texture_array[texture_num];
    tx->texture = texture;
    tx->width = width;
    tx->height = height;
    tx->blend_mode = BLEND_MODE_NONE;
    tx->colour[0] = tx->colour[1] = tx->colour[2] = tx->colour[3] = 255;

    SDL_SetTextureBlendMode(texture, SDL_BLENDMODE_NONE);
    SDL_SetTextureColorMod(texture, 255, 255, 255);
    SDL_SetTextureAlphaMod(texture, 255);

    // Success
    result[0] = 1;
}

// requires: *gfx_engine valid, window open, texture is in use
// ensures: texture is now free, no other state changes
void destroy_texture(void **gfx_engine, uint32_t texture_num)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;
    SDL_DestroyTexture(engine->texture_array[texture_num].texture);
    engine->texture_array[texture_num].texture = NULL;
}


//--------------------------------------------------------------
// Render state setting

// requires: valid engine
// ensures: blend state changed, no other changes
void set_blend_mode(void **gfx_engine, uint8_t* blend_mode)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;
    engine->blend_mode = *blend_mode;
    engine->draw_state_modified = true;
}

// requires: valid engine; colour points to a struct of four uint8_t's (rgba)
// ensures: draw colour changed, no other changes
void set_colour(void **gfx_engine, const char *colour)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;
    memcpy(&engine->colour[0], colour, 4);
    engine->draw_state_modified = true;
}

// helper for set_clip_rect
static void copy_rect_to_sdl_rect(SDL_Rect *r, const char *rect)
{
    int32_t x, y;
    int32_t w, h;
    memcpy(&x, rect, 4);
    memcpy(&y, rect + 4, 4);
    memcpy(&w, rect + 8, 4);
    memcpy(&h, rect + 12, 4);
    // We assume that int32_t will fit into a C 'int' value without overflow.
    // (We also assume that SDL does something sensible in the event that negative
    // values are passed for width and/or height!)
    r->x = x;
    r->y = y;
    r->w = w;
    r->h = h;
}

// requires: valid engine, window open, rect points to a Maybe<Rectangle>
// ensures: clip rect changed, no other changes
void set_clip_rect(void **gfx_engine, const char *maybe_rect)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;
    uint8_t tag = maybe_rect[0];
    if (tag == 0) {
        SDL_RenderSetClipRect(engine->renderer, NULL);
    } else {
        SDL_Rect r;
        copy_rect_to_sdl_rect(&r, maybe_rect + 1);
        SDL_RenderSetClipRect(engine->renderer, &r);
    }
}

static SDL_BlendMode get_sdl_blend_mode(const struct GfxEngine *engine)
{
    switch (engine->blend_mode) {
    case BLEND_MODE_NONE: return SDL_BLENDMODE_NONE;
    case BLEND_MODE_BLEND: return SDL_BLENDMODE_BLEND;
    }

    // To prevent compiler warning:
    return SDL_BLENDMODE_NONE;
}

// This sets the colour and blend mode for rendering the given texture_num.
// (It is assumed that the clip rect is loaded into the SDL_Renderer at all times,
// so this doesn't need to be explicitly set; and we have no other relevant SDL
// render state to set.)
static void setup_texture_state(struct GfxEngine *engine, uint32_t texture_num)
{
    struct Texture *t = &engine->texture_array[texture_num];

    if (engine->colour[0] != t->colour[0]
    || engine->colour[1] != t->colour[1]
    || engine->colour[2] != t->colour[2]) {
        SDL_SetTextureColorMod(t->texture,
                               engine->colour[0],
                               engine->colour[1],
                               engine->colour[2]);
        t->colour[0] = engine->colour[0];
        t->colour[1] = engine->colour[1];
        t->colour[2] = engine->colour[2];
    }

    if (engine->colour[3] != t->colour[3]) {
        SDL_SetTextureAlphaMod(t->texture, engine->colour[3]);
        t->colour[3] = engine->colour[3];
    }

    if (engine->blend_mode != t->blend_mode) {
        SDL_SetTextureBlendMode(t->texture, get_sdl_blend_mode(engine));
        t->blend_mode = engine->blend_mode;
    }
}

// The same, but sets up state for line/rectangle drawing operations
// rather than texture rendering.
static void setup_draw_state(struct GfxEngine *engine)
{
    if (engine->draw_state_modified) {
        SDL_SetRenderDrawColor(engine->renderer,
                               engine->colour[0],
                               engine->colour[1],
                               engine->colour[2],
                               engine->colour[3]);
        SDL_SetRenderDrawBlendMode(engine->renderer,
                                   get_sdl_blend_mode(engine));
        engine->draw_state_modified = false;
    }
}


//--------------------------------------------------------------
// Rendering operations

// requires: valid engine, window open
// ensures: no state changes
void clear_screen(void **gfx_engine)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;
    setup_draw_state(engine);
    SDL_RenderClear(engine->renderer);
}

// requires: valid engine, window open, texture_num is loaded
// ensures: no state changes
void draw_texture(void **gfx_engine,
                  uint32_t texture_num,
                  const char *src_rect,   // Maybe<Rectangle>
                  int32_t x,
                  int32_t y,
                  const uint8_t *flip_mode)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;

    setup_texture_state(engine, texture_num);

    SDL_Rect r_from;
    SDL_Rect r_to;

    r_to.x = x;
    r_to.y = y;

    if (*src_rect == 1) {
        // "Just" (setup r_from using src_rect)
        copy_rect_to_sdl_rect(&r_from, src_rect + 1);
        r_to.w = r_from.w;
        r_to.h = r_from.h;
    } else {
        // "Nothing" (leave r_from unset)
        r_to.w = engine->texture_array[texture_num].width;
        r_to.h = engine->texture_array[texture_num].height;
    }

    bool flip_x = (*flip_mode & 1) != 0;
    bool flip_y = (*flip_mode & 2) != 0;

    SDL_RenderCopyEx(engine->renderer,
                     engine->texture_array[texture_num].texture,
                     *src_rect ? &r_from : NULL,
                     &r_to,
                     0.0,   // rotation angle
                     NULL,  // rotation centre point
                     (flip_x ? SDL_FLIP_HORIZONTAL : 0)
                     | (flip_y ? SDL_FLIP_VERTICAL : 0));
}

// requires: engine valid, window open
// ensures: no state changes
void fill_rectangle(void **gfx_engine, const char *rect)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;
    setup_draw_state(engine);

    SDL_Rect dest_rect;
    copy_rect_to_sdl_rect(&dest_rect, rect);

    SDL_RenderFillRect(engine->renderer, &dest_rect);
}

// requires: engine valid, window open
// ensures: no state changes
void outline_rectangle(void **gfx_engine, const char *rect)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;
    setup_draw_state(engine);

    SDL_Rect dest_rect;
    copy_rect_to_sdl_rect(&dest_rect, rect);

    SDL_RenderDrawRect(engine->renderer, &dest_rect);
}

// requires: engine valid, window open
// ensures: no state changes
void present(void **gfx_engine)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;
    SDL_RenderPresent(engine->renderer);
}


//--------------------------------------------------------------
// Events

static int translate_key(SDL_Keycode sym)
{
    switch (sym) {
    case SDLK_0: return 0;
    case SDLK_1: return 1;
    case SDLK_2: return 2;
    case SDLK_3: return 3;
    case SDLK_4: return 4;
    case SDLK_5: return 5;
    case SDLK_6: return 6;
    case SDLK_7: return 7;
    case SDLK_8: return 8;
    case SDLK_9: return 9;

    case SDLK_a: return 10;
    case SDLK_b: return 11;
    case SDLK_c: return 12;
    case SDLK_d: return 13;
    case SDLK_e: return 14;
    case SDLK_f: return 15;
    case SDLK_g: return 16;
    case SDLK_h: return 17;
    case SDLK_i: return 18;
    case SDLK_j: return 19;
    case SDLK_k: return 20;
    case SDLK_l: return 21;
    case SDLK_m: return 22;
    case SDLK_n: return 23;
    case SDLK_o: return 24;
    case SDLK_p: return 25;
    case SDLK_q: return 26;
    case SDLK_r: return 27;
    case SDLK_s: return 28;
    case SDLK_t: return 29;
    case SDLK_u: return 30;
    case SDLK_v: return 31;
    case SDLK_w: return 32;
    case SDLK_x: return 33;
    case SDLK_y: return 34;
    case SDLK_z: return 35;

    case SDLK_SPACE: return 36;
    case SDLK_RETURN: return 37;
    case SDLK_BACKSPACE: return 38;
    case SDLK_DELETE: return 39;
    case SDLK_TAB: return 40;

    case SDLK_LSHIFT: return 41;
    case SDLK_RSHIFT: return 42;

    case SDLK_UP: return 43;
    case SDLK_DOWN: return 44;
    case SDLK_LEFT: return 45;
    case SDLK_RIGHT: return 46;

    case SDLK_ESCAPE: return 47;
    case SDLK_F1: return 48;
    case SDLK_F2: return 49;
    case SDLK_F3: return 50;
    case SDLK_F4: return 51;
    case SDLK_F5: return 52;
    case SDLK_F6: return 53;
    case SDLK_F7: return 54;
    case SDLK_F8: return 55;
    case SDLK_F9: return 56;
    case SDLK_F10: return 57;
    case SDLK_F11: return 58;
    case SDLK_F12: return 59;

    default: return -1;
    }
}

static void fill_event_x_y(char *event, int x, int y)
{
    // event[0] is the tag; we assume the next eight bytes are two
    // consecutive i32 values, which are filled in by this function.
    int32_t x32 = x;
    int32_t y32 = y;
    memcpy(event + 1, &x32, 4);
    memcpy(event + 5, &y32, 4);
}

static bool translate_sdl_event(char *event,
                                const SDL_Event *sdl_event,
                                struct GfxEngine *engine)
{
    switch (sdl_event->type) {
    case SDL_QUIT:
        *event = APP_QUIT_REQUESTED;
        return true;

    case SDL_WINDOWEVENT:
        switch (sdl_event->window.event) {
        case SDL_WINDOWEVENT_HIDDEN:
            *event = WINDOW_HIDDEN;
            return true;

        case SDL_WINDOWEVENT_SHOWN:
            *event = WINDOW_SHOWN;
            return true;

        case SDL_WINDOWEVENT_SIZE_CHANGED:
            *event = WINDOW_SIZE_CHANGED;

            // Get width/height from the renderer, this should give the exact pixel size
            // even on high dpi displays
            int w, h;
            if (SDL_GetRendererOutputSize(engine->renderer, &w, &h) != 0) {
                // in the event of errors, give a size of zero to the app.
                w = h = 0;
            }
            fill_event_x_y(event, w, h);
            return true;

        case SDL_WINDOWEVENT_EXPOSED:
            *event = WINDOW_REQUIRES_REDRAW;
            return true;

        case SDL_WINDOWEVENT_ENTER:
            *event = MOUSE_ENTERED_WINDOW;
            return true;

        case SDL_WINDOWEVENT_LEAVE:
            *event = MOUSE_LEFT_WINDOW;
            return true;

        default:
            return false;
        }

    case SDL_MOUSEMOTION:
        *event = MOUSE_MOVED;
        fill_event_x_y(event, sdl_event->motion.x, sdl_event->motion.y);
        return true;

    case SDL_MOUSEBUTTONDOWN:
    case SDL_MOUSEBUTTONUP:
        if (sdl_event->type == SDL_MOUSEBUTTONDOWN) {
            *event = MOUSE_PRESSED;
        } else {
            *event = MOUSE_RELEASED;
        }
        fill_event_x_y(event, sdl_event->button.x, sdl_event->button.y);

        switch (sdl_event->button.button) {
        case SDL_BUTTON_LEFT: event[9] = LEFT_BUTTON; break;
        case SDL_BUTTON_MIDDLE: event[9] = MIDDLE_BUTTON; break;
        case SDL_BUTTON_RIGHT: event[9] = RIGHT_BUTTON; break;
        default: event[9] = UNKNOWN_BUTTON; break;
        }

        return true;

    case SDL_KEYDOWN:
    case SDL_KEYUP:
        if (sdl_event->key.repeat) {
            // Ignore auto-repeats
            return false;
        }
        if (sdl_event->type == SDL_KEYDOWN) {
            *event = KEY_PRESSED;
        } else {
            *event = KEY_RELEASED;
        }
        int key = translate_key(sdl_event->key.keysym.sym);
        if (key < 0) {
            return false;
        }
        event[1] = (uint8_t)key;
        return true;

    default:
        return false;
    }
}

// requires: valid engine, window open
// ensures: no state change. maybe_event is set to a valid Maybe<Event>.
void poll_event(char *maybe_event, void **gfx_engine)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;

    SDL_Event ev;

    while (true) {
        int sdl_result = SDL_PollEvent(&ev);
        if (sdl_result == 0) {
            // No more events are pending
            *maybe_event = 0;  // "Nothing"
            return;

        } else if (translate_sdl_event(maybe_event + 1, &ev, engine)) {
            // We found a valid event that can be returned to the caller
            *maybe_event = 1;  // "Just"
            return;
        }

        // Else: we found an event, but it is not one that the
        // GfxEngine reports, so we should just ignore it and continue
        // looping (as there might be another event that we can
        // return).
    }
}

// requires: valid engine, window open
// ensures: no state change. event is set to a valid Event.
void wait_event(char *event, void **gfx_engine)
{
    struct GfxEngine *engine = (struct GfxEngine*) *gfx_engine;

    SDL_Event ev;

    while (true) {
        int sdl_result = SDL_WaitEvent(&ev);
        if (sdl_result == 0) {
            // Error while waiting for events.
            // This shouldn't happen. Convert it to APP_QUIT_REQUESTED if it does!
            *event = APP_QUIT_REQUESTED;
            return;
        } else if (translate_sdl_event(event, &ev, engine)) {
            return;
        }
    }
}
