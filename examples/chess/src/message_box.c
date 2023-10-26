// Message box function, as defined in MessageBox.b

#include "common_types.h"

#include <SDL2/SDL.h>

void message_box(void *io, struct String *msg)
{
    // precondition: msg->data is a nul-terminated string
    SDL_ShowSimpleMessageBox(SDL_MESSAGEBOX_INFORMATION, "Information", msg->data, NULL);
}
