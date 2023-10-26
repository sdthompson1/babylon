// Main program for the chess demo.

module ChessMain

import IO;
import MemAlloc;

interface {
    // This entry point is called by the C "main" function.
    // (Since there is no way to create IO or Mem objects in the
    // language, C gives us one of each.)
    function main_prog(ref mem: Mem, ref io: IO);
}

import ChessLogic;
import CString;
import GameEngine;
import Int;
import Limits;
import LoadTexture;
import Maybe;
import MessageBox;
import Result;

// Texture numbers
function piece_texture_num(p: Piece): TextureNum
{
    return match p {
    case {Black,Pawn} => 0
    case {Black,Knight} => 1
    case {Black,Bishop} => 2
    case {Black,Rook} => 3
    case {Black,Queen} => 4
    case {Black,King} => 5
    case {White,Pawn} => 6
    case {White,Knight} => 7
    case {White,Bishop} => 8
    case {White,Rook} => 9
    case {White,Queen} => 10
    case {White,King} => 11
    };
}
const TX_SELECTED = 12;
const TX_POSSIBLE_MOVE = 13;
const TX_CHECK = 14;
const TX_CHECKMATE_MSG = 15;
const TX_STALEMATE_MSG = 16;

// Square colours and sizes
const DARK_SQUARE_COL: GameEngine.RGBA = {r=u8(134), g=u8(172), b=u8(191), a=u8(255)};
const LIGHT_SQUARE_COL: GameEngine.RGBA = {r=u8(178), g=u8(218), b=u8(237), a=u8(255)};
const SQUARE_PIXEL_SIZE = 60;
const MARGIN = 25;
const CHECKMATE_MSG_WIDTH = 300;
const CHECKMATE_MSG_HEIGHT = 100;
const CHECKMATE_MSG_X = MARGIN + SQUARE_PIXEL_SIZE*4 - CHECKMATE_MSG_WIDTH/2;
const CHECKMATE_MSG_Y = MARGIN + SQUARE_PIXEL_SIZE*4 - CHECKMATE_MSG_HEIGHT/2;


ghost function textures_loaded(engine: GameEngine): bool
{
    return valid_engine(engine)
      && forall (i: u32) i <= HIGHEST_TEXTURE_NUM ==>
           engine_state(engine).textures[i];
}

function load_textures(ref mem: Mem,
                       ref io: IO,
                       ref engine: GameEngine,
                       ref result: Result<{}>)
    requires valid_engine(engine);
    requires forall (i:u32) i <= HIGHEST_TEXTURE_NUM ==> !engine_state(engine).textures[i];
    requires result == Ok<{}>{};
    ensures valid_engine(engine);
    ensures valid_c_result<{}>(result);
    ensures is_ok<{}>(result) ==> textures_loaded(engine);
{
    load_texture(mem, io, engine, result, piece_texture_num({Black,Pawn}), "images/black_pawn.png\0");
    load_texture(mem, io, engine, result, piece_texture_num({Black,Knight}), "images/black_knight.png\0");
    load_texture(mem, io, engine, result, piece_texture_num({Black,Bishop}), "images/black_bishop.png\0");
    load_texture(mem, io, engine, result, piece_texture_num({Black,Rook}), "images/black_rook.png\0");
    load_texture(mem, io, engine, result, piece_texture_num({Black,Queen}), "images/black_queen.png\0");
    load_texture(mem, io, engine, result, piece_texture_num({Black,King}), "images/black_king.png\0");

    load_texture(mem, io, engine, result, piece_texture_num({White,Pawn}), "images/white_pawn.png\0");
    load_texture(mem, io, engine, result, piece_texture_num({White,Knight}), "images/white_knight.png\0");
    load_texture(mem, io, engine, result, piece_texture_num({White,Bishop}), "images/white_bishop.png\0");
    load_texture(mem, io, engine, result, piece_texture_num({White,Rook}), "images/white_rook.png\0");
    load_texture(mem, io, engine, result, piece_texture_num({White,Queen}), "images/white_queen.png\0");
    load_texture(mem, io, engine, result, piece_texture_num({White,King}), "images/white_king.png\0");

    load_texture(mem, io, engine, result, TX_SELECTED, "images/selected.png\0");
    load_texture(mem, io, engine, result, TX_POSSIBLE_MOVE, "images/possible_move.png\0");
    load_texture(mem, io, engine, result, TX_CHECK, "images/check.png\0");

    load_texture(mem, io, engine, result, TX_CHECKMATE_MSG, "images/checkmate.png\0");
    load_texture(mem, io, engine, result, TX_STALEMATE_MSG, "images/stalemate.png\0");
}


// Our "UI state" consists of:
//  - the current position
//  - a selected square (possibly)
//  - some cached information:
//     - the legal moves from the selected square
//     - whether the position is check
//     - current game status (InProgress, Checkmate or Stalemate)
// The UI state is valid if the values themselves are valid
// (e.g. valid_position(pos)) and the cached information correctly
// corresponds to the actual position.
ghost function valid_ui_state(pos: Position,
                              selected: Maybe<Square>,
                              legal_moves: bool[,],
                              check: bool,
                              status: GameStatus): bool
{
    if !valid_position(pos) { return false; }
    if sizeof(legal_moves) != board_size { return false; }
    
    if check != is_check(pos) { return false; }
    if status != game_status(pos) { return false; }
    
    match selected {
    case Just(from) =>
        if !valid_square(from) { return false; }
        if !(forall (sq:Square) valid_square(sq) ==>
                legal_moves[sq.x, sq.y] == is_legal_move(pos, from, sq)) {
            return false;
        }
    case _ =>
    }

    return true;
}



// Converting square positions to/from pixel coordinates:

function square_pixel_position(sq: Square): {i32, i32}
    requires valid_square(sq);
{
    return {MARGIN + SQUARE_PIXEL_SIZE * sq.x,
            MARGIN + SQUARE_PIXEL_SIZE * (y_size - 1 - sq.y)};
}

function pixel_pos_to_square(x: u32, y: u32): Maybe<Square>
    ensures is_just<Square>(return) ==> valid_square(from_just<Square>(return));
{
    if x >= MARGIN && y >= MARGIN {
        var sq = { x = i32((x - MARGIN) / SQUARE_PIXEL_SIZE),
                   y = y_size - 1 - i32((y - MARGIN) / SQUARE_PIXEL_SIZE) };
        if valid_square(sq) {
            return Just<Square>(sq);
        }
    }
    return Nothing<Square>;
}


// Draw the checkerboard pattern
function draw_board(ref engine: GameEngine)
    requires textures_loaded(engine);
    requires engine_state(engine).blend_mode == BlendMode_None;
    ensures textures_loaded(engine);
{
    ghost var old_state = engine_state(engine);

    var sq = first_square();
    while !iteration_done(sq)
        invariant valid_square(sq) || iteration_done(sq);
        invariant textures_loaded(engine);
        decreases square_number(sq);
    {
        var pixel_pos = square_pixel_position(sq);

        // (0,0) (a1) is a dark square, as are all squares where x+y is even.
        var dark = if ((sq.x + sq.y) & 1) == 1 then false else true;

        set_colour(engine, if dark then DARK_SQUARE_COL else LIGHT_SQUARE_COL);
        fill_rectangle(engine, {x=u32(pixel_pos.0),
                                y=u32(pixel_pos.1),
                                width=u32(SQUARE_PIXEL_SIZE),
                                height=u32(SQUARE_PIXEL_SIZE)});

        next_square(sq);
    }
}

// Draw the pieces on the board.
// Also draw a "glow" effect under the king, if in check.
function draw_pieces(ref engine: GameEngine, pos: Position, check: bool)
    requires textures_loaded(engine);
    requires valid_position(pos);
    requires check == is_check(pos);
    requires engine_state(engine).colour == {r=u8(255), g=u8(255), b=u8(255), a=u8(255)};
    requires engine_state(engine).blend_mode == BlendMode_Blend;
    ensures engine_state(engine) == old(engine_state(engine));
{
    ghost var old_state = engine_state(engine);

    var sq = first_square();
    while !iteration_done(sq)
        invariant valid_square(sq) || iteration_done(sq);
        invariant engine_state(engine) == old_state;
        decreases square_number(sq);
    {
        var pixel_pos = square_pixel_position(sq);

        match pos.board[sq.x, sq.y] {
        case Just(p) =>

            if check {
                match p {
                case {c, King} =>
                    // Draw check highlight effect
                    if same_colour(c, pos.turn) {
                        draw_texture(engine, TX_CHECK, Nothing<Rectangle>, pixel_pos.0, pixel_pos.1);
                    }
                case _ =>
                }
            }

            // Draw the piece
            draw_texture(engine, piece_texture_num(p), Nothing<Rectangle>, pixel_pos.0, pixel_pos.1);

        case Nothing =>
        }

        next_square(sq);
    }
}

// Draw the red dots on the legal moves for the selected piece
function draw_legal_moves(ref engine: GameEngine,
                          legal_moves: bool[,])
    requires textures_loaded(engine);
    requires sizeof(legal_moves) == board_size;
    requires engine_state(engine).colour == {r=u8(255), g=u8(255), b=u8(255), a=u8(255)};
    requires engine_state(engine).blend_mode == BlendMode_Blend;
    ensures engine_state(engine) == old(engine_state(engine));
{
    ghost var old_state = engine_state(engine);

    var sq = first_square();
    while !iteration_done(sq)
        invariant valid_square(sq) || iteration_done(sq);
        invariant engine_state(engine) == old_state;
        decreases square_number(sq);
    {
        if legal_moves[sq.x, sq.y] {
            // Draw a dot on this square
            var pixel_pos = square_pixel_position(sq);
            draw_texture(engine, TX_POSSIBLE_MOVE, Nothing<Rectangle>, pixel_pos.0, pixel_pos.1);
        }
        next_square(sq);
    }
}

// Draw the entire display.
function draw(ref engine: GameEngine,
              pos: Position,
              selected: Maybe<Square>,
              legal_moves: bool[,],
              check: bool,
              status: GameStatus,
              status_acknowledged: bool)
    requires textures_loaded(engine);
    requires valid_ui_state(pos, selected, legal_moves, check, status);
    ensures textures_loaded(engine);
{
    var black: GameEngine.RGBA = {r=u8(0), g=u8(0), b=u8(0), a=u8(255)};
    var white: GameEngine.RGBA = {r=u8(255), g=u8(255), b=u8(255), a=u8(255)};

    assert check == is_check(pos);

    // Clear the screen to black.
    set_colour(engine, black);
    set_blend_mode(engine, BlendMode_None);
    clear_screen(engine);

    // Draw the checkerboard
    draw_board(engine);

    // Draw the pieces
    set_colour(engine, white);
    set_blend_mode(engine, BlendMode_Blend);
    draw_pieces(engine, pos, check);

    // Draw a box around the selected piece, if any
    match selected {
    case Nothing =>
    case Just(sq) =>
        var pixel_pos = square_pixel_position(sq);
        draw_texture(engine, TX_SELECTED, Nothing<Rectangle>, pixel_pos.0, pixel_pos.1);
        draw_legal_moves(engine, legal_moves);
    }

    assert engine_state(engine).colour == white;
    if !status_acknowledged {
        match status {
        case Checkmate =>
            draw_texture(engine, TX_CHECKMATE_MSG, Nothing<Rectangle>, CHECKMATE_MSG_X, CHECKMATE_MSG_Y);
            
        case Stalemate =>
            draw_texture(engine, TX_STALEMATE_MSG, Nothing<Rectangle>, CHECKMATE_MSG_X, CHECKMATE_MSG_Y);
            
        case _ =>
        }
    }

    // Present the frame.
    present(engine);
}


// Utility function to check if two Maybe<Square>'s are equal
function maybe_sq_equal(lhs: Maybe<Square>, rhs: Maybe<Square>): bool
{
    match lhs {
    case Nothing => return is_nothing<Square>(rhs);
    case Just(lhs_sq) =>
        match rhs {
        case Nothing => return false;
        case Just(rhs_sq) =>
            return lhs_sq.x == rhs_sq.x && lhs_sq.y == rhs_sq.y;
        }
    }
}

function game_over_status(status: GameStatus): bool
{
    return match status {
    case Checkmate => true
    case Stalemate => true
    case InProgress => false
    };
}

// React to a mouse click.
function handle_mouse_click(x: u32,
                            y: u32,
                            ref pos: Position,
                            ref scratch_pos: Position,
                            ref selected: Maybe<Square>,
                            ref legal_moves: bool[,],
                            ref check: bool,
                            ref status: GameStatus,
                            ref status_acknowledged: bool,
                            ref requires_redraw: bool)
    requires valid_ui_state(pos, selected, legal_moves, check, status);
    requires sizeof(scratch_pos.board) == board_size;
    ensures valid_ui_state(pos, selected, legal_moves, check, status);
    ensures sizeof(scratch_pos.board) == board_size;
{
    if game_over_status(status) {
        if !status_acknowledged {
            if x >= CHECKMATE_MSG_X && x < CHECKMATE_MSG_X + CHECKMATE_MSG_WIDTH
            && y >= CHECKMATE_MSG_Y && y < CHECKMATE_MSG_Y + CHECKMATE_MSG_HEIGHT {
                status_acknowledged = true;
                requires_redraw = true;
            }
        }
        return;
    }

    // By default, just try to select the new square
    var clicked_square = pixel_pos_to_square(x, y);

    // Did we click on the chessboard, while a piece is selected?
    match ({clicked_square, selected}) {
    case {Just(to), Just(from)} =>
    
        // Is it legal to move here?
        // If so, make the move, and return immediately
        if legal_moves[to.x, to.y] {
            make_move(pos, from, to);
            selected = Nothing<Square>;
            check = is_check(pos);
            status = get_game_status(pos, scratch_pos);
            requires_redraw = true;
            return;
        }

        // Are we clicking on the same piece that was already selected?
        // If so, then un-select it
        if to.x == from.x && to.y == from.y {
            clicked_square = Nothing<Square>;
        }
    case _ =>
    }

    // Allow selecting our own pieces only
    match clicked_square {
    case Just(sq) =>
        if !has_piece_of_colour(pos, pos.turn, sq) {
            clicked_square = Nothing<Square>;
        }
    case _ =>
    }

    // "selected" should now change to "clicked_square".
    // If this is a change, then redraw the display.
    if !maybe_sq_equal(selected, clicked_square) {
        match clicked_square {
        case Just(sq) =>
            get_legal_moves_from(pos, scratch_pos, sq, legal_moves);
        case _ =>
        }
        selected = clicked_square;
        requires_redraw = true;
    }
}


// Run the main program. This is called once all memory has been allocated
// and the GameEngine has been started. No runtime errors (e.g. memory
// allocation failures) are possible beyond this point (at least in theory!).
function run_prog(ref engine: GameEngine,
                  ref pos: Position,            // memory for current position
                  ref scratch_pos: Position,    // memory for a scratch position
                  ref legal_moves: bool[,])     // memory for storing legal move targets
    requires textures_loaded(engine);
    requires valid_position(pos);
    requires sizeof(scratch_pos.board) == board_size;
    requires sizeof(legal_moves) == board_size;
    ensures textures_loaded(engine);
{
    setup_initial_position(pos);

    var check: bool = is_check(pos);
    var status: GameStatus = get_game_status(pos, scratch_pos);
    var status_acknowledged = false;

    var requires_redraw = true;
    var selected: Maybe<Square> = Nothing<Square>;

    // "Fuel" is a hack to allow us to write an infinite loop.
    // Even if 10^12 loop iterations are done per second (unlikely!), it will take over
    // 200 years for the fuel to run out. So we should be safe :)
    // In future we should figure out some more elegant way to allow infinite loops
    // (without compromising logical consistency).
    var fuel: u64 = U64_MAX;
    
    while fuel > u64(0)
        invariant textures_loaded(engine);
        invariant valid_ui_state(pos, selected, legal_moves, check, status);
        invariant sizeof(scratch_pos.board) == board_size;

        decreases fuel;
    {
        if requires_redraw {
            draw(engine, pos, selected, legal_moves, check, status, status_acknowledged);
            assert textures_loaded(engine);
        }

        assert textures_loaded(engine);

        var ev = wait_event(engine);
        match ev {
        case AppQuitRequested =>
            return;

        case WindowRequiresRedraw =>
            requires_redraw = true;

        case MousePressed(m) =>
            handle_mouse_click(m.x, m.y, pos, scratch_pos,
                               selected, legal_moves, check, status,
                               status_acknowledged,
                               requires_redraw);

        case _ =>
            // ignore
        }

        fuel = fuel - u64(1);
    }
}


// Entry point.
// Allocate all required memory and start the GameEngine.
// If this was successful, then transfer control to run_prog
// (during which no further runtime errors should be possible).
// Otherwise, display a message box and exit.
function main_prog(ref mem: Mem, ref io: IO)
{
    var xsize = SQUARE_PIXEL_SIZE * x_size + 2 * MARGIN;
    var ysize = SQUARE_PIXEL_SIZE * y_size + 2 * MARGIN;

    ref title = "Chess Demo\0";

    var results = {Ok<{}>{}, Nothing<GameEngine>};
    
    new_engine(io, results.1, title, xsize, ysize, results.0);

    match results {
    case {Error(ref msg), _} =>
        // GameEngine failed to start. Show message and exit.
        message_box(io, msg);
        var ok = resize_array<u8>(mem, msg, 0);

    case {Ok({}), Just(ref engine)} =>
        var tex_result: Result<{}>;
        load_textures(mem, io, engine, tex_result);

        match tex_result {
        case Error(ref msg) =>
            // Textures failed to load. Show message and exit.
            message_box(io, msg);
            var ok = resize_array<u8>(mem, msg, 0);

        case Ok(_) =>
            // Allocate arrays needed
            var pos: Position;
            var ok: bool = resize_2d_array<Maybe<Piece> >(mem, pos.board, x_size, y_size);

            var scratch_pos: Position;
            if ok {
                ok = resize_2d_array<Maybe<Piece> >(mem, scratch_pos.board, x_size, y_size);
            }

            var legal_moves: bool[,];
            if ok {
                ok = resize_2d_array<bool>(mem, legal_moves, x_size, y_size);
            }

            if ok {
                // Array allocation successful - Run the program!
                run_prog(engine, pos, scratch_pos, legal_moves);

            } else {
                // Array allocation failed - Show error message
                ref msg = "Failed to allocate arrays\0";
                message_box(io, msg);
            }

            // Free the arrays
            ok = resize_2d_array<Maybe<Piece> >(mem, pos.board, 0, 0);
            ok = resize_2d_array<Maybe<Piece> >(mem, scratch_pos.board, 0, 0);
            ok = resize_2d_array<bool>(mem, legal_moves, 0, 0);
        }

        // Shut down the GameEngine.
        free_engine(results.1);
    }
}
