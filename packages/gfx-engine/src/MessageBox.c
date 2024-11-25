// Message box function, as defined in MessageBox.b

#include <SDL2/SDL.h>

#include <string.h>

void message_box(const char *msg)
{
    const char *str;
    memcpy(&str, msg, sizeof(char*));
    if (str == NULL) {
        str = "Unknown Error";
    }
    SDL_ShowSimpleMessageBox(SDL_MESSAGEBOX_INFORMATION, "Message", str, NULL);
}
