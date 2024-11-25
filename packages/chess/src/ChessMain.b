// Main program for the chess demo.

module ChessMain

interface {
    impure function main();
}

import Array;
import ChessLogic;
import Either;
import GfxEngine;
import Int;
import qualified LoadPNG;
import Maybe;
import MessageBox;
import String;
import StringBuffer;

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
const HIGHEST_TEXTURE_NUM = 16;

// PNG file names for each texture num.
// (The case numbers should be kept consistent with the above constants!)
const PNG_FILENAME_MAX = 30;
function png_filename(n: TextureNum, ref buf: u8[PNG_FILENAME_MAX])
    requires n <= HIGHEST_TEXTURE_NUM;
    ensures valid_string(buf);
{
    match n {
    case 0 => strcpy(buf, "images/black_pawn.png");
    case 1 => strcpy(buf, "images/black_knight.png");
    case 2 => strcpy(buf, "images/black_bishop.png");
    case 3 => strcpy(buf, "images/black_rook.png");
    case 4 => strcpy(buf, "images/black_queen.png");
    case 5 => strcpy(buf, "images/black_king.png");
    case 6 => strcpy(buf, "images/white_pawn.png");
    case 7 => strcpy(buf, "images/white_knight.png");
    case 8 => strcpy(buf, "images/white_bishop.png");
    case 9 => strcpy(buf, "images/white_rook.png");
    case 10 => strcpy(buf, "images/white_queen.png");
    case 11 => strcpy(buf, "images/white_king.png");
    case 12 => strcpy(buf, "images/selected.png");
    case 13 => strcpy(buf, "images/possible_move.png");
    case 14 => strcpy(buf, "images/check.png");
    case 15 => strcpy(buf, "images/checkmate.png");
    case 16 => strcpy(buf, "images/stalemate.png");
    };
}

// Square colours and sizes
const DARK_SQUARE_COL: GfxEngine.RGBA = {r=u8(134), g=u8(172), b=u8(191), a=u8(255)};
const LIGHT_SQUARE_COL: GfxEngine.RGBA = {r=u8(178), g=u8(218), b=u8(237), a=u8(255)};
const SQUARE_PIXEL_SIZE = 60;
const MARGIN = 25;
const CHECKMATE_MSG_WIDTH = 300;
const CHECKMATE_MSG_HEIGHT = 100;
const CHECKMATE_MSG_X = MARGIN + SQUARE_PIXEL_SIZE*4 - CHECKMATE_MSG_WIDTH/2;
const CHECKMATE_MSG_Y = MARGIN + SQUARE_PIXEL_SIZE*4 - CHECKMATE_MSG_HEIGHT/2;


ghost function textures_loaded(engine: GfxEngine): bool
{
    return valid_engine(engine)
      && engine_state(engine).window_open
      && (forall (i: u32) i <= HIGHEST_TEXTURE_NUM ==>
            engine_state(engine).textures[i]);
}

impure function load_texture(ref engine: GfxEngine,
                             texture_num: TextureNum,
                             filename: u8[],
                             ref result: Either<u8[*], {}>)

    requires texture_num <= HIGHEST_TEXTURE_NUM;

    requires valid_string(filename);
    
    requires valid_engine(engine);
    requires engine_state(engine).window_open;
    requires !engine_state(engine).textures[texture_num];

    requires !allocated(result);

    ensures valid_engine(engine);
    ensures match result {
        case Left(err_msg) =>
            (valid_string(err_msg) || sizeof(err_msg) == 0)
            && engine_state(engine) == old(engine_state(engine));
        case Right{} =>
            engine_state(engine) == set_texture(old(engine_state(engine)), texture_num);
        };
{
    var img_result: Either<u8[*], RGBA[*,*]>;
    LoadPNG.load_png(filename, img_result);

    match img_result {
    case Left(ref err_msg) =>
        // Try to make a new err msg, if we can allocate space for it

        var MAX_ERR_MSG_LEN = u64(1024);
        var sb: StringBuffer;
        var alloc_result = alloc_string_buffer(sb, MAX_ERR_MSG_LEN);

        if alloc_result {
            // we allocated a buffer, write the new message into it.
            append_string(sb, "Failed to load ");
            append_string(sb, filename);
            if sizeof(err_msg) != 0 {
                append_string(sb, ":\n");
                append_string(sb, err_msg);
            }
            null_terminate(sb);
            swap sb.buf, err_msg;
            free_string_buffer(sb);
        }

        // TODO: This could be tidied up if we were allowed to return
        // allocated values from functions.
        var d: Either<u8[*], {}>;
        result = d;
        match result {
        case Left(ref msg) => swap msg, err_msg;
        }

    case Right(ref img) =>
        // The load was successful, now let's send the pixel data to the GfxEngine.
        create_texture(engine, texture_num, img, result);

        // Free the pixel array as it's no longer needed.
        free_2d_array(img);
    }
}

impure function load_textures(ref engine: GfxEngine, ref result: Either<u8[*], {}>)
    requires valid_engine(engine);
    requires engine_state(engine).window_open;
    requires forall (i:u32) i <= HIGHEST_TEXTURE_NUM ==> !engine_state(engine).textures[i];
    requires !allocated(result);
    ensures valid_engine(engine);
    ensures engine_state(engine).window_open;
    ensures match result {
        case Left(err_msg) =>
            (valid_string(err_msg) || sizeof(err_msg) == 0)
        case Right{} =>
            textures_loaded(engine)
        };
{
    hide load_texture;

    var i: TextureNum = 0;
    while i <= HIGHEST_TEXTURE_NUM
        invariant i <= HIGHEST_TEXTURE_NUM + 1;
        invariant valid_engine(engine);
        invariant engine_state(engine).window_open;
        invariant forall (j: u32) j < i ==>
            engine_state(engine).textures[j];
        invariant forall (j: u32) i <= j <= HIGHEST_TEXTURE_NUM ==>
            !engine_state(engine).textures[j];
        invariant !allocated(result);
        decreases ~i;
    {
        var buf: u8[PNG_FILENAME_MAX];
        png_filename(i, buf);
        load_texture(engine, i, buf, result);
        if is_left(result) {
            return;  // failure
        }
        i = i + 1;
    }
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

function pixel_pos_to_square(x: i32, y: i32): Maybe<Square>
    ensures is_just<Square>(return) ==> valid_square(from_just<Square>(return));
{
    if x >= MARGIN && y >= MARGIN {
        var sq = { x = i32((x - MARGIN) / SQUARE_PIXEL_SIZE),
                   y = y_size - 1 - i32((y - MARGIN) / SQUARE_PIXEL_SIZE) };
        if valid_square(sq) {
            return Just(sq);
        }
    }
    return Nothing;
}


// Draw the checkerboard pattern
function draw_board(ref engine: GfxEngine)
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
        fill_rectangle(engine, {x = pixel_pos.0,
                                y = pixel_pos.1,
                                width = SQUARE_PIXEL_SIZE,
                                height = SQUARE_PIXEL_SIZE});

        next_square(sq);
    }
}

// Draw the pieces on the board.
// Also draw a "glow" effect under the king, if in check.
function draw_pieces(ref engine: GfxEngine, pos: Position, check: bool)
    requires textures_loaded(engine);
    requires valid_position(pos);
    requires check == is_check(pos);
    requires engine_state(engine).colour == {r=u8(255), g=u8(255), b=u8(255), a=u8(255)};
    requires engine_state(engine).blend_mode == BlendMode_Blend;
    ensures valid_engine(engine);
    ensures engine_state(engine) == old(engine_state(engine));
{
    ghost var old_state = engine_state(engine);

    var sq = first_square();
    while !iteration_done(sq)
        invariant valid_square(sq) || iteration_done(sq);
        invariant valid_engine(engine);
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
                        draw_texture(engine, TX_CHECK, Nothing, pixel_pos.0, pixel_pos.1,
                                     Flip_None);
                    }
                case _ =>
                }
            }

            // Draw the piece
            draw_texture(engine, piece_texture_num(p), Nothing, pixel_pos.0, pixel_pos.1, Flip_None);

        case Nothing =>
        }

        next_square(sq);
    }
}

// Draw the red dots on the legal moves for the selected piece
function draw_legal_moves(ref engine: GfxEngine,
                          legal_moves: bool[,])
    requires textures_loaded(engine);
    requires sizeof(legal_moves) == board_size;
    requires engine_state(engine).colour == {r=u8(255), g=u8(255), b=u8(255), a=u8(255)};
    requires engine_state(engine).blend_mode == BlendMode_Blend;
    ensures valid_engine(engine);
    ensures engine_state(engine) == old(engine_state(engine));
{
    ghost var old_state = engine_state(engine);

    var sq = first_square();
    while !iteration_done(sq)
        invariant valid_square(sq) || iteration_done(sq);
        invariant valid_engine(engine);
        invariant engine_state(engine) == old_state;
        decreases square_number(sq);
    {
        if legal_moves[sq.x, sq.y] {
            // Draw a dot on this square
            var pixel_pos = square_pixel_position(sq);
            draw_texture(engine, TX_POSSIBLE_MOVE, Nothing, pixel_pos.0, pixel_pos.1, Flip_None);
        }
        next_square(sq);
    }
}

// Draw the entire display.
function draw(ref engine: GfxEngine,
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
    var black: GfxEngine.RGBA = {r=u8(0), g=u8(0), b=u8(0), a=u8(255)};
    var white: GfxEngine.RGBA = {r=u8(255), g=u8(255), b=u8(255), a=u8(255)};

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
        draw_texture(engine, TX_SELECTED, Nothing, pixel_pos.0, pixel_pos.1, Flip_None);
        draw_legal_moves(engine, legal_moves);
    }

    assert engine_state(engine).colour == white;
    if !status_acknowledged {
        match status {
        case Checkmate =>
            draw_texture(engine, TX_CHECKMATE_MSG, Nothing, CHECKMATE_MSG_X, CHECKMATE_MSG_Y, Flip_None);
            
        case Stalemate =>
            draw_texture(engine, TX_STALEMATE_MSG, Nothing, CHECKMATE_MSG_X, CHECKMATE_MSG_Y, Flip_None);
            
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
function handle_mouse_click(x: i32,
                            y: i32,
                            ref pos: Position,
                            ref selected: Maybe<Square>,
                            ref legal_moves: bool[,],
                            ref check: bool,
                            ref status: GameStatus,
                            ref status_acknowledged: bool,
                            ref requires_redraw: bool)
    requires valid_ui_state(pos, selected, legal_moves, check, status);
    ensures valid_ui_state(pos, selected, legal_moves, check, status);
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
            selected = Nothing;
            check = is_check(pos);
            status = get_game_status(pos);
            requires_redraw = true;
            return;
        }

        // Are we clicking on the same piece that was already selected?
        // If so, then un-select it
        if to.x == from.x && to.y == from.y {
            clicked_square = Nothing;
        }
    case _ =>
    }

    // Allow selecting our own pieces only
    match clicked_square {
    case Just(sq) =>
        if !has_piece_with_colour(pos, pos.turn, sq) {
            clicked_square = Nothing;
        }
    case _ =>
    }

    // "selected" should now change to "clicked_square".
    // If this is a change, then redraw the display.
    if !maybe_sq_equal(selected, clicked_square) {
        match clicked_square {
        case Just(sq) =>
            get_legal_moves_from(pos, sq, legal_moves);
        case _ =>
        }
        selected = clicked_square;
        requires_redraw = true;
    }
}


// Run the main program. This is called once all memory has been allocated
// and the GfxEngine has been started. No runtime errors (e.g. memory
// allocation failures) are possible beyond this point (at least in theory!).
impure function run_prog(ref engine: GfxEngine)
    requires textures_loaded(engine);
    ensures textures_loaded(engine);
{
    var pos: Position;
    setup_initial_position(pos);

    var legal_moves: bool[x_size, y_size];

    var check: bool = is_check(pos);
    var status: GameStatus = get_game_status(pos);
    var status_acknowledged = false;

    var requires_redraw = true;
    var selected: Maybe<Square> = Nothing;

    // "Fuel" is a hack to allow us to write an infinite loop.
    // Even if 10^12 loop iterations are done per second (unlikely!), it will take over
    // 200 years for the fuel to run out. So we should be safe :)
    // In future we should figure out some more elegant way to allow infinite loops
    // (without compromising logical consistency).
    var fuel: u64 = U64_MAX;

    while fuel > u64(0)
        invariant textures_loaded(engine);
        invariant valid_ui_state(pos, selected, legal_moves, check, status);

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
            handle_mouse_click(m.x, m.y, pos,
                               selected, legal_moves, check, status,
                               status_acknowledged,
                               requires_redraw);

        case _ =>
            // ignore
        }

        fuel = fuel - u64(1);

        hide handle_mouse_click;  // for proving the invariant
        hide draw;
    }
}


// Entry point.
// Allocate all required memory and start the GfxEngine.
// If this was successful, then transfer control to run_prog
// (during which no further runtime errors should be possible).
// Otherwise, display a message box and exit.
impure function main()
{
    var xsize = SQUARE_PIXEL_SIZE * x_size + 2 * MARGIN;
    var ysize = SQUARE_PIXEL_SIZE * y_size + 2 * MARGIN;

    ref title = "Chess Demo";

    var engine_result: Either<u8[*], GfxEngine>;
    new_engine(engine_result);

    match engine_result {
    case Left(ref err_msg) =>
        message_box(err_msg);
        free_array(err_msg);

    case Right(ref engine) =>

        var result: Either<u8[*], {}>;
        open_window(engine, title, xsize, ysize, result);

        match result {
        case Left(ref err_msg) =>
            message_box(err_msg);
            free_array(err_msg);

        case Right(_) =>
            load_textures(engine, result);

            match result {
            case Left(ref err_msg) =>
                close_window(engine);
                message_box(err_msg);
                free_array(err_msg);

            case Right(_) =>
                run_prog(engine);
            }
        }
        
        free_engine(engine);
    }
}
