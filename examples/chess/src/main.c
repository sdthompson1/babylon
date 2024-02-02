// C "main" function that just calls ChessMain.main_prog.

#include <SDL2/SDL.h>

extern void ChessMainz_main_prog(void *mem, void *io);

int main()
{
    // We need to pass Mem and IO objects to ChessMain.main_prog.
    // The actual value of these is irrelevant -- we can just pass zero.
    // Note that due to the way function names are encoded by the Babylon compiler,
    // "ChessMain.main_prog" becomes "ChessMainz_main_prog".
    ChessMainz_main_prog(0, 0);
    return 0;
}
