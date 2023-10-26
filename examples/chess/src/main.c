// C "main" function that just calls ChessMain.main_prog.

#include <SDL2/SDL.h>

extern void ChessMain_main_prog(void *mem, void *io);

int main()
{
    // We need to pass Mem and IO objects to ChessMain.main_prog.
    // The actual value of these is irrelevant -- we can just pass zero.
    ChessMain_main_prog(0, 0);
    return 0;
}
