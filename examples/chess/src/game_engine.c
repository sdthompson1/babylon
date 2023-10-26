// This is the C implementation of the simple game engine defined in
// GameEngine.b.

#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <SDL2/SDL.h>

#include "common_types.h"


//--------------------------------------------------------------

// Types


// datatype BlendMode = BlendMode_None | BlendMode_Blend
enum BlendModeTag {
    BLEND_MODE_NONE,
    BLEND_MODE_BLEND
};

struct BlendMode {
    uint8_t tag;
};

// type Rectangle = {x:u32, y:u32, width:u32, height:u32}
struct Rectangle {
    uint32_t x;
    uint32_t y;
    uint32_t width;
    uint32_t height;
};


// datatype Maybe<T> = Nothing | Just(T)
struct __attribute__((__packed__)) MaybeRectangle {
    uint8_t tag;
    struct Rectangle rect;
};


// datatype MouseButton = UnknownButton | LeftButton | ...
enum MouseButtonTag {
    UNKNOWN_BUTTON,
    LEFT_BUTTON,
    MIDDLE_BUTTON,
    RIGHT_BUTTON
};

// type {new_width:u32, new_height:u32}
struct WindowSizeRecord {
    uint32_t new_width;
    uint32_t new_height;
};

// type {x:u32, y:u32, button:MouseButton}
struct __attribute__((__packed__)) MouseInfo {
    uint32_t x;
    uint32_t y;
    uint8_t button;
};

// datatype Event = AppQuitRequested | WindowHidden | ...
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
    MOUSE_RELEASED
};

struct __attribute__((__packed__)) Event {
    uint8_t tag;
    union {
        struct WindowSizeRecord size_info;
        struct MouseInfo mouse_info;
    };
};


//--------------------------------------------------------------

// Engine state

struct Texture {
    SDL_Texture *texture;
    int width, height;
    enum BlendModeTag blend_mode;
    struct RGBA colour;
};

struct GameEngine {
    SDL_Window *window;
    SDL_Renderer *renderer;

    struct Texture *texture_array;
    uint32_t texture_array_size;

    enum BlendModeTag blend_mode;
    struct RGBA colour;
    bool draw_state_modified;
};

struct __attribute__((__packed__)) MaybeGameEngine {
    uint8_t tag;
    uint64_t value;
};


//--------------------------------------------------------------
// SDL error message helper

struct String make_sdl_error_string(const char *prefix)
{
    return make_string_3(prefix, ": ", SDL_GetError());
}


//--------------------------------------------------------------
// Init and shutdown

void new_engine(void *io,
                struct MaybeGameEngine *maybe_engine,
                const struct String *title,
                uint32_t width,
                uint32_t height,
                struct Result *result)
{
    struct GameEngine *engine = NULL;

    // To avoid confusion, we only allow new_engine to be successfully called once.
    static bool engine_created = false;
    if (engine_created) {
        result->error_string = make_string("GameEngine already created");
        goto return_error;
    }

    // Allocate memory that we need.
    engine = calloc(sizeof(struct GameEngine), 1);
    if (engine == NULL) {
        result->error_string = make_string("malloc failed");
        goto return_error;
    }

    // Init SDL.
    if (SDL_Init(SDL_INIT_EVENTS | SDL_INIT_VIDEO) != 0) {
        result->error_string = make_sdl_error_string("SDL_Init failed");
        goto return_error;
    }

    // Open a window.
    const int sdl_flags = SDL_WINDOW_ALLOW_HIGHDPI | SDL_WINDOW_RESIZABLE;

    engine->window = SDL_CreateWindow(title->data,
                                      SDL_WINDOWPOS_UNDEFINED,
                                      SDL_WINDOWPOS_UNDEFINED,
                                      width,
                                      height,
                                      sdl_flags);

    if (engine->window == NULL) {
        result->error_string = make_sdl_error_string("SDL_CreateWindow failed");
        goto quit_sdl;
    }

    // Create renderer.
    engine->renderer = SDL_CreateRenderer(engine->window, -1, 0);
    if (engine->renderer == NULL) {
        result->error_string = make_sdl_error_string("SDL_CreateRenderer failed");
        goto close_window;
    }

    // Setup initial engine state.
    engine->blend_mode = BLEND_MODE_NONE;
    engine->colour.r = engine->colour.g = engine->colour.b = engine->colour.a = 255;

    // Also set draw_state_modified to true, this will force us to
    // update the SDL render states, the first time we draw something.
    engine->draw_state_modified = true;

    // Return result
    engine_created = true;
    maybe_engine->tag = MAYBE_JUST;
    maybe_engine->value = (uint64_t)engine;
    result->tag = RESULT_OK;
    return;


    // Error handling code (goto-chain)
    // Assumption is that result->error_string has been set.
  close_window:
    SDL_DestroyWindow(engine->window);

  quit_sdl:
    SDL_Quit();

  return_error:
    free(engine);
    result->tag = RESULT_ERROR;
}

void destroy_texture(struct GameEngine **engine, uint32_t texture_num);

void free_engine(struct MaybeGameEngine *maybe_engine)
{
    struct GameEngine *engine = (struct GameEngine *) maybe_engine->value;

    for (uint32_t index = 0; index < engine->texture_array_size; ++index) {
        if (engine->texture_array[index].texture) {
            destroy_texture(&engine, index);
        }
    }

    SDL_DestroyRenderer(engine->renderer);
    SDL_DestroyWindow(engine->window);
    SDL_Quit();

    free(engine->texture_array);
    free(engine);

    maybe_engine->tag = MAYBE_NOTHING;
}


//--------------------------------------------------------------
// Texture loading

void create_texture(struct GameEngine **engine_ptr,
                    uint32_t texture_num,
                    const struct Array2 *pixels,
                    struct Result *result)
{
    struct GameEngine *engine = *engine_ptr;

    // Grow the texture array if required.
    if (texture_num >= engine->texture_array_size) {
        uint32_t new_size = engine->texture_array_size * 2;
        if (new_size < 10) {
            new_size = 10;
        }
        if (texture_num >= new_size) {
            new_size = texture_num + 1;
        }

        struct Texture * new_array = realloc(engine->texture_array,
                                             new_size * sizeof(struct Texture));
        if (new_array == NULL) {
            result->tag = RESULT_ERROR;
            result->error_string = make_string("failed to expand texture array");
            return;
        }

        engine->texture_array = new_array;

        for (uint32_t i = engine->texture_array_size; i < new_size; ++i) {
            engine->texture_array[i].texture = NULL;
        }

        engine->texture_array_size = new_size;
    }

    // SDL represents width and height as int, which might not be able
    // to store a u32 value.
    if (pixels->num_elements_0 > INT_MAX || pixels->num_elements_1 > INT_MAX) {
        result->tag = RESULT_ERROR;
        result->error_string = make_string("texture too big");
        return;
    }

    // Create the SDL texture object
    int bpp;
    Uint32 rmask, gmask, bmask, amask;
    SDL_PixelFormatEnumToMasks(SDL_PIXELFORMAT_RGBA32, &bpp, &rmask, &gmask, &bmask, &amask);

    SDL_Surface *surface = SDL_CreateRGBSurfaceFrom(pixels->data,
                                                    pixels->num_elements_1,
                                                    pixels->num_elements_0,
                                                    bpp,
                                                    pixels->num_elements_1 * 4,
                                                    rmask,
                                                    gmask,
                                                    bmask,
                                                    amask);
    if (surface == NULL) {
        result->tag = RESULT_ERROR;
        result->error_string = make_string("SDL_CreateRGBSurfaceFrom failed");
        return;
    }

    SDL_Texture *texture = SDL_CreateTextureFromSurface(engine->renderer, surface);
    SDL_FreeSurface(surface);
    if (texture == NULL) {
        result->tag = RESULT_ERROR;
        result->error_string = make_string("SDL_CreateTextureFromSurface failed");
        return;
    }

    // Create the struct Texture object and set initial blend and colour states.
    struct Texture *tx = &engine->texture_array[texture_num];
    tx->texture = texture;
    tx->width = pixels->num_elements_1;
    tx->height = pixels->num_elements_0;
    tx->blend_mode = BLEND_MODE_NONE;
    tx->colour.r = tx->colour.g = tx->colour.b = tx->colour.a = 255;

    SDL_SetTextureBlendMode(texture, SDL_BLENDMODE_NONE);
    SDL_SetTextureColorMod(texture, 255, 255, 255);
    SDL_SetTextureAlphaMod(texture, 255);

    result->tag = RESULT_OK;
}

void destroy_texture(struct GameEngine **engine_ptr, uint32_t texture_num)
{
    struct GameEngine *engine = *engine_ptr;
    SDL_DestroyTexture(engine->texture_array[texture_num].texture);
    engine->texture_array[texture_num].texture = NULL;
}


//--------------------------------------------------------------
// Render state setting

void set_blend_mode(struct GameEngine **engine_ptr, const struct BlendMode *mode)
{
    struct GameEngine *engine = *engine_ptr;
    engine->blend_mode = mode->tag;
    engine->draw_state_modified = true;
}

void set_colour(struct GameEngine **engine_ptr, const struct RGBA *colour)
{
    struct GameEngine *engine = *engine_ptr;
    engine->colour = *colour;
    engine->draw_state_modified = true;
}

static SDL_BlendMode get_sdl_blend_mode(const struct GameEngine *engine)
{
    switch (engine->blend_mode) {
    case BLEND_MODE_NONE: return SDL_BLENDMODE_NONE;
    case BLEND_MODE_BLEND: return SDL_BLENDMODE_BLEND;
    }

    // to prevent a compiler warning
    return SDL_BLENDMODE_NONE;
}

static void setup_texture_state(struct GameEngine *engine,
                                uint32_t texture_num)
{
    struct Texture *t = &engine->texture_array[texture_num];

    if (engine->colour.r != t->colour.r
    || engine->colour.g != t->colour.g
    || engine->colour.b != t->colour.b) {
        SDL_SetTextureColorMod(t->texture,
                               engine->colour.r,
                               engine->colour.g,
                               engine->colour.b);
        t->colour.r = engine->colour.r;
        t->colour.g = engine->colour.g;
        t->colour.b = engine->colour.b;
    }

    if (engine->colour.a != t->colour.a) {
        SDL_SetTextureAlphaMod(t->texture, engine->colour.a);
        t->colour.a = engine->colour.a;
    }

    if (engine->blend_mode != t->blend_mode) {
        SDL_SetTextureBlendMode(t->texture, get_sdl_blend_mode(engine));
        t->blend_mode = engine->blend_mode;
    }
}

static void setup_draw_state(struct GameEngine *engine)
{
    if (engine->draw_state_modified) {
        SDL_SetRenderDrawColor(engine->renderer,
                               engine->colour.r,
                               engine->colour.g,
                               engine->colour.b,
                               engine->colour.a);
        SDL_SetRenderDrawBlendMode(engine->renderer,
                                   get_sdl_blend_mode(engine));
        engine->draw_state_modified = false;
    }
}


//--------------------------------------------------------------
// Rendering operations

void clear_screen(struct GameEngine **engine_ptr)
{
    struct GameEngine *engine = *engine_ptr;
    setup_draw_state(engine);
    SDL_RenderClear(engine->renderer);
}

void draw_texture(struct GameEngine **engine_ptr,
                  uint32_t texture_num,
                  struct MaybeRectangle *src_rect,
                  uint32_t x,
                  uint32_t y)
{
    struct GameEngine *engine = *engine_ptr;

    setup_texture_state(engine, texture_num);

    SDL_Rect r_from;
    SDL_Rect r_to;

    r_to.x = x;
    r_to.y = y;

    if (src_rect->tag == MAYBE_JUST) {
        r_from.x = src_rect->rect.x;
        r_from.y = src_rect->rect.y;
        r_from.w = src_rect->rect.width;
        r_from.h = src_rect->rect.height;
        r_to.w = r_from.w;
        r_to.h = r_from.h;
    } else {
        r_to.w = engine->texture_array[texture_num].width;
        r_to.h = engine->texture_array[texture_num].height;
    }

    SDL_RenderCopy(engine->renderer,
                   engine->texture_array[texture_num].texture,
                   src_rect->tag == MAYBE_JUST ? &r_from : NULL,
                   &r_to);
}

void fill_rectangle(struct GameEngine **engine_ptr, struct Rectangle *rect)
{
    struct GameEngine *engine = *engine_ptr;

    setup_draw_state(engine);
    struct SDL_Rect dest_rect = { rect->x, rect->y, rect->width, rect->height };
    SDL_RenderFillRect(engine->renderer, &dest_rect);
}

void present(struct GameEngine **engine_ptr)
{
    struct GameEngine *engine = *engine_ptr;
    SDL_RenderPresent(engine->renderer);
}


//--------------------------------------------------------------
// Events

static bool translate_sdl_event(struct Event *result,
                                const SDL_Event *sdl_event,
                                SDL_Renderer *renderer)
{
    switch (sdl_event->type) {
    case SDL_QUIT:
        result->tag = APP_QUIT_REQUESTED;
        return true;

    case SDL_WINDOWEVENT:
        switch (sdl_event->window.event) {
        case SDL_WINDOWEVENT_HIDDEN:
            result->tag = WINDOW_HIDDEN;
            return true;

        case SDL_WINDOWEVENT_SHOWN:
            result->tag = WINDOW_SHOWN;
            return true;

        case SDL_WINDOWEVENT_SIZE_CHANGED:
            result->tag = WINDOW_SIZE_CHANGED;

            // get width/height from the renderer, this should give the exact pixel size
            // even on high dpi displays
            int w, h;
            if (SDL_GetRendererOutputSize(renderer, &w, &h) != 0) {
                // in the event of errors, give a size of zero to the app.
                w = h = 0;
            }
            result->size_info.new_width = w;
            result->size_info.new_height = h;
            break;

        case SDL_WINDOWEVENT_EXPOSED:
            result->tag = WINDOW_REQUIRES_REDRAW;
            break;

        case SDL_WINDOWEVENT_ENTER:
            result->tag = MOUSE_ENTERED_WINDOW;
            break;

        case SDL_WINDOWEVENT_LEAVE:
            result->tag = MOUSE_LEFT_WINDOW;
            break;

        default:
            return false;
        }

    case SDL_MOUSEMOTION:
        result->tag = MOUSE_MOVED;
        result->mouse_info.x = sdl_event->motion.x;
        result->mouse_info.y = sdl_event->motion.y;
        return true;

    case SDL_MOUSEBUTTONDOWN:
    case SDL_MOUSEBUTTONUP:
        if (sdl_event->type == SDL_MOUSEBUTTONDOWN) {
            result->tag = MOUSE_PRESSED;
        } else {
            result->tag = MOUSE_RELEASED;
        }
        result->mouse_info.x = sdl_event->button.x;
        result->mouse_info.y = sdl_event->button.y;

        switch (sdl_event->button.button) {
        case SDL_BUTTON_LEFT: result->mouse_info.button = LEFT_BUTTON; break;
        case SDL_BUTTON_MIDDLE: result->mouse_info.button = MIDDLE_BUTTON; break;
        case SDL_BUTTON_RIGHT: result->mouse_info.button = RIGHT_BUTTON; break;
        default: result->mouse_info.button = UNKNOWN_BUTTON; break;
        }

        return true;

    default:
        return false;
    }
}

void wait_event(struct Event *result, struct GameEngine **engine_ptr)
{
    struct GameEngine *engine = *engine_ptr;

    SDL_Event ev;

    while (true) {
        int sdl_result = SDL_WaitEvent(&ev);
        if (sdl_result == 0) {
            // This shouldn't happen. Convert it to APP_QUIT_REQUESTED if it does!
            result->tag = APP_QUIT_REQUESTED;
            return;
        } else if (translate_sdl_event(result, &ev, engine->renderer)) {
            return;
        }
    }
}
