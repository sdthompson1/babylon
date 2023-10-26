// "Game logic" for the chess demo.

module ChessLogic

import Limits;
import Maybe;

interface {
    // Types
    datatype PieceType = Pawn | Knight | Bishop | Rook | Queen | King;
    datatype Colour = White | Black;
    type Piece = {Colour, PieceType};
    type Board = Maybe<Piece> [,];
    type Square = {x:i32, y:i32};

    type Position = {
        board: Board,
        turn: Colour,
        en_passant: Maybe<Square>,
        castle_kingside_white: bool,
        castle_queenside_white: bool,
        castle_kingside_black: bool,
        castle_queenside_black: bool
    };


    // Constants
    const x_size: i32 = 8;
    const y_size: i32 = 8;
    const board_size: {u64, u64} = {u64(x_size), u64(y_size)};
    

    // Some helper functions
    
    function same_colour(a: Colour, b: Colour): bool
    {
        match {a,b} {
        case {White,White} => return true;
        case {Black,Black} => return true;
        case _ => return false;
        }
    }

    function opposite(col: Colour): Colour
    {
        match col {
        case Black => return White;
        case White => return Black;
        }
    }
    
    function valid_square(sq: Square): bool
    {
        return 0 <= sq.x < x_size && 0 <= sq.y < y_size;
    }

    // Conditions for a position to be valid: board has correct size,
    // and en_passant is reasonable.
    // Note we do not check other conditions (e.g. that there exist
    // two kings on the board) as that would probably be harder to
    // do proofs for.
    ghost function valid_position(pos: Position): bool
    {
        return sizeof(pos.board) == board_size
          && (match pos.en_passant {
                 case Nothing => true
                 case Just{x=x, y=y} =>
                     0 <= x < x_size && (y == 2 || y == y_size - 3)
              });
    }

    function has_piece_of_colour(pos: Position, col: Colour, sq: Square): bool
        requires valid_position(pos);
        requires valid_square(sq);
    {
        match pos.board[sq.x, sq.y] {
        case Nothing =>
            return false;
        case Just{col2, _} =>
            return same_colour(col, col2);
        }
    }


    // This function sets up the initial chess position.
    // The caller first has to allocate the memory for the board.
    
    function setup_initial_position(ref pos: Position)
        requires sizeof(pos.board) == board_size;
        ensures valid_position(pos);


    // Functions to calculate legal chess moves.

    ghost function is_legal_move(pos: Position,
                                 from: Square,
                                 to: Square): bool
        requires valid_position(pos);
        requires valid_square(from);
        requires valid_square(to);

    function compute_is_legal_move(pos: Position,
                                   ref scratch_pos: Position,
                                   from: Square,
                                   to: Square): bool
        requires valid_position(pos);
        requires sizeof(scratch_pos.board) == board_size;
        requires valid_square(from);
        requires valid_square(to);
        ensures sizeof(scratch_pos.board) == board_size;
        ensures return == is_legal_move(pos, from, to);

    function get_legal_moves_from(pos: Position,
                                  ref scratch_pos: Position,
                                  from: Square,
                                  ref to: bool[,])
        requires valid_position(pos);
        requires sizeof(scratch_pos.board) == board_size;
        requires valid_square(from);
        requires sizeof(to) == board_size;
        ensures sizeof(scratch_pos.board) == board_size;
        ensures sizeof(to) == board_size;
        ensures forall (sq:Square) valid_square(sq) ==>
            to[sq.x, sq.y] == is_legal_move(pos, from, sq);


    // Functions to determine whether the current player is in check,
    // and whether the game is over.

    function is_check(pos: Position): bool
        requires valid_position(pos);

    datatype GameStatus = InProgress | Checkmate | Stalemate;

    ghost function game_status(pos: Position): GameStatus
        requires valid_position(pos);
    {
        if exists (sq1: Square) exists (sq2: Square)
              valid_square(sq1) && valid_square(sq2) &&
                is_legal_move(pos, sq1, sq2) {
            return InProgress;
        } else if is_check(pos) {
            return Checkmate;
        } else {
            return Stalemate;
        }
    }

    function get_game_status(pos: Position,
                             ref scratch_pos: Position): GameStatus
        requires valid_position(pos);
        requires sizeof(scratch_pos.board) == board_size;
        ensures sizeof(scratch_pos.board) == board_size;
        ensures return == game_status(pos);    


    // This function will execute a move, updating the position,
    // and flipping the current player (pos.turn) to the opposite
    // player.

    function make_move(ref pos: Position, from: Square, to: Square)
        requires valid_position(pos);
        requires valid_square(from);
        requires valid_square(to);
        requires is_legal_move(pos, from, to);
        ensures valid_position(pos);


    // These functions allow iterating through all the squares on the
    // chessboard in order.
    // (Using these is less painful than using two nested while-loops!)

    function first_square(): Square
        ensures valid_square(return);

    function next_square(ref sq: Square)
        requires valid_square(sq);
        ensures valid_square(sq) || iteration_done(sq);
        ensures square_number(sq) < square_number(old(sq));

    function iteration_done(sq: Square): bool;

    // this value decreases when next_square is called
    ghost function square_number(sq: Square): i32
        requires valid_square(sq) || iteration_done(sq);

    // true if lhs is visited before rhs in the iteration
    ghost function before(lhs: Square, rhs: Square): bool;
}


// Some more helper functions

function abs(x: i32): i32
    requires x != I32_MIN;
{
    if x < 0 {
        return -x;
    } else {
        return x;
    }
}

function sgn(x: i32): i32
{
    if x < 0 {
        return -1;
    } else if x == 0 {
        return 0;
    } else {
        return 1;
    }
}


// Implementation of the iteration functions

function first_square(): Square
    ensures valid_square(return);
{
    return {x=0, y=0};
}

function next_square(ref sq: Square)
    requires valid_square(sq);
    ensures valid_square(sq) || (iteration_done(sq) && sq.x == 0);
    ensures square_number(sq) < square_number(old(sq));
{
    sq.x = sq.x + 1;
    if sq.x == x_size {
        sq.x = 0;
        sq.y = sq.y + 1;
    }
}

function iteration_done(sq: Square): bool
{
    return sq.y == y_size;
}

// this value decreases when next_square is called
ghost function square_number(sq: Square): i32
    requires valid_square(sq) || iteration_done(sq);
{
    if iteration_done(sq) {
        return -x_size * y_size;
    } else {
        return -(sq.x + x_size * sq.y);
    }
}

// true if lhs is visited before rhs in the iteration
ghost function before(lhs: Square, rhs: Square): bool
{
    return lhs.y < rhs.y ||
        (lhs.y == rhs.y && lhs.x < rhs.x);
}



// Make an identical copy of a Position
function copy_position(ref dest: Position, src: Position)
    requires valid_position(src);
    requires sizeof(dest.board) == board_size;
    ensures dest == src;
{
    var sq = first_square();
    while !iteration_done(sq)
        invariant valid_square(sq) || iteration_done(sq);
        invariant sizeof(dest.board) == board_size;
        invariant forall (other: Square)
            valid_square(other) && before(other, sq) ==>
                dest.board[other.x, other.y] == src.board[other.x, other.y];
        decreases square_number(sq);
    {
        dest.board[sq.x, sq.y] = src.board[sq.x, sq.y];
        next_square(sq);
    }
    
    dest.castle_kingside_white = src.castle_kingside_white;
    dest.castle_queenside_white = src.castle_queenside_white;
    dest.castle_kingside_black = src.castle_kingside_black;
    dest.castle_queenside_black = src.castle_queenside_black;
    
    dest.en_passant = src.en_passant;
    dest.turn = src.turn;
}



// The initial chess position
function setup_initial_position(ref pos: Position)
    requires sizeof(pos.board) == board_size;
    ensures valid_position(pos);
{
    // Setup all ranks except the first and last
    var sq: Square = first_square();
    while !iteration_done(sq)
        invariant valid_square(sq) || iteration_done(sq);
        invariant sizeof(pos.board) == board_size;
        decreases square_number(sq);
    {
        if sq.y == 1 {
            pos.board[sq.x, sq.y] = Just<Piece>{White, Pawn};
        } else if sq.y == y_size - 2 {
            pos.board[sq.x, sq.y] = Just<Piece>{Black, Pawn};
        } else {
            pos.board[sq.x, sq.y] = Nothing<Piece>;
        }
        next_square(sq);
    }

    // Now setup the first and last ranks
    pos.board[0,0] = Just<Piece> {White, Rook};
    pos.board[1,0] = Just<Piece> {White, Knight};
    pos.board[2,0] = Just<Piece> {White, Bishop};
    pos.board[3,0] = Just<Piece> {White, Queen};
    pos.board[4,0] = Just<Piece> {White, King};
    pos.board[5,0] = Just<Piece> {White, Bishop};
    pos.board[6,0] = Just<Piece> {White, Knight};
    pos.board[7,0] = Just<Piece> {White, Rook};

    var y = y_size - 1;
    pos.board[0,y] = Just<Piece> {Black, Rook};
    pos.board[1,y] = Just<Piece> {Black, Knight};
    pos.board[2,y] = Just<Piece> {Black, Bishop};
    pos.board[3,y] = Just<Piece> {Black, Queen};
    pos.board[4,y] = Just<Piece> {Black, King};
    pos.board[5,y] = Just<Piece> {Black, Bishop};
    pos.board[6,y] = Just<Piece> {Black, Knight};
    pos.board[7,y] = Just<Piece> {Black, Rook};

    // Setup remaining state variables - White to go first.
    pos.turn = White;
    pos.en_passant = Nothing<Square>;
    pos.castle_kingside_white = true;
    pos.castle_queenside_white = true;
    pos.castle_kingside_black = true;
    pos.castle_queenside_black = true;
}


// This next function calculates whether a move is a "pseudo legal"
// chess move.
// A "pseudo legal move" is a move that obeys all of the rules of 
// chess, *except* that checks are ignored -- i.e. the move might
// be moving into check (or in the case of castling, it might be
// castling into, out of or through check).

function is_pseudo_legal_move(pos: Position,
                              from: Square,
                              to: Square,
                              turn: Colour): bool
    requires valid_position(pos);
    requires valid_square(from);
    requires valid_square(to);
{
    // The "from" square must contain a piece
    match pos.board[from.x, from.y] {
    case Nothing =>
        return false;

    case Just{col, piece_type} =>
        // The piece must be my colour
        if !same_colour(col, turn) {
            return false;

        // The "to" square must NOT contain a piece of my colour
        } else if has_piece_of_colour(pos, col, to) {
            return false;

        } else {
            // Check the specific rules for this piece type
            match piece_type {
            case Pawn => return legal_pawn_move(pos, from, to, turn);
            case Knight => return legal_knight_move(pos, from, to);
            case Bishop => return legal_bishop_move(pos, from, to);
            case Rook => return legal_rook_move(pos, from, to);
            case Queen => return legal_queen_move(pos, from, to);
            case King => return legal_king_move(pos, from, to);
            }
        }
    }
}

// These legal_xxx_move functions are called by is_pseudo_legal_move.
// That function has already checked that the "from" square contains a piece
// of the correct type, and the "to" square is empty or contains a capturable piece.
// Therefore, only the remaining rules for each piece type (e.g. rooks move
// vertically or horizontally, bishops move diagonally) must be tested.

function legal_pawn_move(pos: Position,
                         from: Square,
                         to: Square,
                         turn: Colour): bool
    requires valid_position(pos);
    requires valid_square(from);
    requires valid_square(to);
{
    var dy = match turn {
        case White => 1
        case Black => -1
    };

    if (from.x == to.x) {
        // Move within same file.

        // The target space must be empty (i.e. capturing not allowed)
        if (is_just<Piece>(pos.board[to.x, to.y])) {
            return false;
        }

        // The "to.y" position must be correct. There are two cases:
        
        if (from.y == 1 && to.y == 3 && dy == 1)
        || (from.y == y_size - 2 && to.y == y_size - 4 && dy == -1) {
            // Two-space initial move.
            // Valid if the intermediate space is also empty.
            return is_nothing<Piece>(pos.board[from.x, from.y + dy]);
            
        } else if to.y == from.y + dy {
            // One-space move. Always valid.
            return true;
            
        } else {
            // Some other vertical move; not allowed.
            return false;
        }
        
    } else if (from.x == to.x + 1 || from.x == to.x - 1) {
        // Move to an adjacent file.
        // Allowed if "to.y" is correct (for a diagonal capturing move)
        // and the target square contains a piece (OR the target square is
        // the en passant capture square).
        if to.y == from.y + dy {
            if is_just<Piece>(pos.board[to.x, to.y]) {
                return true;
            }
            match pos.en_passant {
            case Just{x=target_x, y=target_y} =>
                if to.x == target_x && to.y == target_y {
                    return true;
                }
            case _ =>
            }
        }
        return false;
        
    } else {
        return false;
    }
}

function legal_knight_move(pos: Position, from: Square, to: Square): bool
    requires valid_position(pos);
    requires valid_square(from);
    requires valid_square(to);
{
    var diff_x = abs(from.x - to.x);
    var diff_y = abs(from.y - to.y);
    return (diff_x == 1 && diff_y == 2) || (diff_x == 2 && diff_y == 1);
}

// Helper function for bishop and rook moves:
// Determines if all squares in between "from" and "to" are empty.
function squares_between_are_empty(pos: Position,
                                   from: Square,
                                   to: Square,
                                   dx: i32,
                                   dy: i32): bool
    requires valid_position(pos);
    requires valid_square(from);
    requires valid_square(to);
    requires -1 <= dx <= 1;
    requires -1 <= dy <= 1;
    requires !(dx == 0 && dy == 0);
{
    var sq = {x = from.x + dx,
              y = from.y + dy};
    
    while valid_square(sq) && (sq.x != to.x || sq.y != to.y)
        decreases -(sq.x * dx + sq.y * dy);
    {
        if is_just<Piece>(pos.board[sq.x, sq.y]) {
            return false;
        }
        sq.x = sq.x + dx;
        sq.y = sq.y + dy;
    }
    
    return true;
}

function legal_bishop_move(pos: Position, from: Square, to: Square): bool
    requires valid_position(pos);
    requires valid_square(from);
    requires valid_square(to);
    requires from != to;
{
    var dx = (to.x - from.x);
    var dy = (to.y - from.y);
    if abs(dx) == abs(dy) {
        return squares_between_are_empty(pos, from, to, sgn(dx), sgn(dy));
    } else {
        return false;
    }
}

function legal_rook_move(pos: Position, from: Square, to: Square): bool
    requires valid_position(pos);
    requires valid_square(from);
    requires valid_square(to);
    requires from != to;
{
    var dx = sgn(to.x - from.x);
    var dy = sgn(to.y - from.y);
    if dx == 0 || dy == 0 {
        return squares_between_are_empty(pos, from, to, dx, dy);
    } else {
        return false;
    }
}

// A queen move is just a combination of rook and bishop moves
function legal_queen_move(pos: Position, from: Square, to: Square): bool
    requires valid_position(pos);
    requires valid_square(from);
    requires valid_square(to);
    requires from != to;
{
    return legal_bishop_move(pos, from, to) || legal_rook_move(pos, from, to);
}

function legal_king_move(pos: Position, from: Square, to: Square): bool
    requires valid_position(pos);
    requires valid_square(from);
    requires valid_square(to);
{
    var dx = abs(to.x - from.x);
    var dy = abs(to.y - from.y);

    if dx == 2 && dy == 0 {
        // Castling attempt
        var can_castle: bool;
        if same_colour(pos.turn, White) {
            if to.x > from.x {
                can_castle = pos.castle_kingside_white;
            } else {
                can_castle = pos.castle_queenside_white;
            }
        } else {
            if to.x > from.x {
                can_castle = pos.castle_kingside_black;
            } else {
                can_castle = pos.castle_queenside_black;
            }
        }
        if !can_castle {
            return false;
        }

        // the squares between king and rook must be free.
        // Note: this code assumes that from.x==4, which is not actually implied
        // by valid_position(pos), however, it will be true in all real chess games
        // (because the "castle" flag would be false if the king had moved from its
        // starting position).
        if to.x > from.x {
            // kingside castling. squares at x=5, 6 must be free.
            if is_just<Piece>(pos.board[5, from.y])
            || is_just<Piece>(pos.board[6, from.y]) {
                return false;
            }
        } else {
            // queenside castling. squares at x=1, 2, 3 must be free.
            if is_just<Piece>(pos.board[3, from.y])
            || is_just<Piece>(pos.board[2, from.y])
            || is_just<Piece>(pos.board[1, from.y]) {
                return false;
            }
        }

        return true;
    }

    return -1 <= dx <= 1 && -1 <= dy <= 1;
}


// Now we bring in the concept of "check".

// First we need a function which returns the position of the king.

// This returns "Maybe", although in real chess games we would expect
// it to always return Just (rather than Nothing) as there should always
// be one king of each colour on the board!

// (If we wanted to be more clever, we could make "there exists a king of
// each colour" a part of the conditions for a valid_position. Then we would
// have to prove that this invariant is maintained by any legal chess move.
// In return, we would be able to have find_king return Square instead of
// Maybe<Square>.)

function find_king(pos: Position, colour: Colour): Maybe<Square>
    requires valid_position(pos);
    ensures match return {
        case Nothing => true
        case Just(sq) =>
            valid_square(sq)
            && pos.board[sq.x,sq.y] == Just<Piece>{colour, King}
    };
{
    var sq = first_square();
    while !iteration_done(sq)
        invariant valid_square(sq) || iteration_done(sq);
        decreases square_number(sq);
    {
        match pos.board[sq.x, sq.y] {
        case Just<Piece>{king_col, King} =>
            if same_colour(king_col, colour) {
                return Just<Square>(sq);
            }
        case _ =>
        }
        next_square(sq);
    }
    return Nothing<Square>;
}


// A position is "in check" if there exists a pseudo legal move (see above)
// which can take the current player's king.

function is_check(pos: Position): bool
    requires valid_position(pos);
{
    var opponent = opposite(pos.turn);

    match find_king(pos, pos.turn) {
    case Nothing =>
    case Just(king_pos) =>
        // If a move from any square to king_pos is legal, then it's check.
        var sq = first_square();
        while !iteration_done(sq)
            invariant valid_square(sq) || iteration_done(sq);
            decreases square_number(sq);
        {
            if is_pseudo_legal_move(pos, sq, king_pos, opponent) {
                return true;
            }
            next_square(sq);
        }
    }
    
    return false;
}


// Now we can define a "legal" move as a pseudo legal move which does not
// put the player making the move in check. (In the case of castling we also
// have to confirm the player is not castling out of or through check.)

function is_castling_move(pos: Position, from: Square, to: Square): bool
    requires valid_position(pos);
    requires valid_square(from);
    requires valid_square(to);
{
    return match pos.board[from.x, from.y] {
        case Just {_, King} =>
            abs(to.x - from.x) == 2    // a 2-space king move is castling
        case _ =>
            false
        };
}

function castling_through_check(pos: Position,
                                ref scratch_pos: Position,
                                from: Square,
                                to: Square): bool
    requires valid_position(pos);
    requires scratch_pos == pos;
    requires valid_square(from);
    requires valid_square(to);
    requires (pos.board[from.x, from.y] == Just<Piece>{pos.turn, King});

    ensures return ==> sizeof(scratch_pos.board) == board_size;
    ensures !return ==> scratch_pos == pos;
{
    // We will move the king one space towards "to" on the scratch board, and
    // see if the resulting position is check.

    var modified_to = {x=from.x + sgn(to.x - from.x), y=to.y};

    assert scratch_pos == pos;

    scratch_pos.board[from.x, from.y] = Nothing<Piece>;

    var backup = scratch_pos.board[modified_to.x, modified_to.y];
    scratch_pos.board[modified_to.x, modified_to.y] = Just<Piece>{pos.turn, King};

    if is_check(scratch_pos) {
        return true;
    }

    // Put the scratch board back how it was originally
    scratch_pos.board[modified_to.x, modified_to.y] = backup;
    scratch_pos.board[from.x, from.y] = Just<Piece>{pos.turn, King};
    return false;
}

// Compute whether a move is a legal move
function real_compute_is_legal_move(pos: Position,
                                    ref scratch_pos: Position,
                                    from: Square,
                                    to: Square): bool
    requires valid_position(pos);
    requires sizeof(scratch_pos.board) == board_size;
    requires valid_square(from);
    requires valid_square(to);
    ensures sizeof(scratch_pos.board) == board_size;
{
    // First of all, it must be a pseudo-legal move.
    if !is_pseudo_legal_move(pos, from, to, pos.turn) {
        return false;
    }

    // If we are castling, confirm we are not trying to castle out of check.
    var castling = is_castling_move(pos, from, to);
    if castling && is_check(pos) {
        // Trying to castle out of check
        return false;
    }

    // Now copy our position to the scratch board
    copy_position(scratch_pos, pos);

    // If we are castling, confirm we are not trying to castle through check.
    if castling {
        var bad = castling_through_check(pos, scratch_pos, from, to);
        if bad {
            return false;
        }
    }

    // Execute the move on the scratch position (but not changing the
    // current player)
    assert scratch_pos == pos;
    make_move_internal(scratch_pos, from, to);

    // The move is legal iff the new position is not check.
    return !is_check(scratch_pos);
}

ghost function is_legal_move(pos: Position, from: Square, to: Square): bool
    requires valid_position(pos);
    requires valid_square(from);
    requires valid_square(to);
{
    var pos2 = pos;
    var result = real_compute_is_legal_move(pos, pos2, from, to);
    return result;
}

// This just calls real_compute_is_legal_move
function compute_is_legal_move(pos: Position,
                               ref scratch_pos: Position,
                               from: Square,
                               to: Square): bool
    requires valid_position(pos);
    requires sizeof(scratch_pos.board) == board_size;
    requires valid_square(from);
    requires valid_square(to);
    ensures sizeof(scratch_pos.board) == board_size;
    ensures return == is_legal_move(pos, from, to);
{
    var result = real_compute_is_legal_move(pos, scratch_pos, from, to);
    return result;
}


// This function computes all the legal moves from a given square.
// It is used by the UI to highlight the possible moves after a
// piece is clicked on.

// It doesn't do anything fancy, it just loops through all the
// squares on the board and calls "compute_is_legal_move" for each.

function get_legal_moves_from(pos: Position,
                              ref scratch_pos: Position,
                              from: Square,
                              ref to: bool[,])
    requires valid_position(pos);
    requires sizeof(scratch_pos.board) == board_size;
    requires valid_square(from);
    requires sizeof(to) == board_size;
    ensures sizeof(scratch_pos.board) == board_size;
    ensures sizeof(to) == board_size;
    ensures forall (sq:Square) valid_square(sq) ==>
        to[sq.x, sq.y] == is_legal_move(pos, from, sq);
{
    var sq = first_square();
    while !iteration_done(sq)
        invariant sizeof(scratch_pos.board) == board_size;
        invariant sizeof(to) == board_size;
        invariant valid_square(sq) || iteration_done(sq);
        invariant forall (other:Square)
            valid_square(other) && before(other, sq) ==>
                to[other.x, other.y] == is_legal_move(pos, from, other);
        decreases square_number(sq);
    {
        to[sq.x, sq.y] = compute_is_legal_move(pos, scratch_pos, from, sq);
        next_square(sq);
    }
}


// This function executes a move, updating the position.
// However, the current player (pos.turn) is not changed.

function make_move_internal(ref pos: Position, from: Square, to: Square)
    requires valid_position(pos);
    requires valid_square(from);
    requires valid_square(to);
    requires is_pseudo_legal_move(pos, from, to, pos.turn);
    ensures valid_position(pos);
{
    // Update castling and en passant flags
    var old_en_passant = pos.en_passant;
    pos.en_passant = Nothing<Square>;
    
    match pos.board[from.x,from.y] {
    case Just{White,Rook} =>
        if from.y == 0 {
            if from.x == 0 {
                pos.castle_queenside_white = false;
            } else if from.x == x_size - 1 {
                pos.castle_kingside_white = false;
            }
        }
    case Just{White,King} =>
        pos.castle_queenside_white = false;
        pos.castle_kingside_white = false;
        
    case Just{Black,Rook} =>
        if from.y == y_size - 1 {
            if from.x == 0 {
                pos.castle_queenside_black = false;
            } else if from.x == x_size - 1 {
                pos.castle_kingside_black = false;
            }
        }
    case Just{Black,King} =>
        pos.castle_queenside_black = false;
        pos.castle_kingside_black = false;
        
    case Just{White,Pawn} =>
        if from.y == 1 && to.y == 3 {
            pos.en_passant = Just<Square>{x = to.x, y = 2};
        }
    case Just{Black,Pawn} =>
        if from.y == y_size - 2 && to.y == y_size - 4 {
            pos.en_passant = Just<Square>{x = to.x, y = y_size - 3};
        }
        
    case _ =>
    }


    // Move the piece
    pos.board[to.x, to.y] = pos.board[from.x, from.y];
    pos.board[from.x, from.y] = Nothing<Piece>;


    // Handle castling, en passant captures, and pawn promotion.
    match pos.board[to.x, to.y] {
    case Just{col, King} =>
        // King move -- if movement was 2 spaces in x, then we are castling,
        // so move the rook as well.
        if abs(to.x - from.x) == 2 {
            var old_rook_x = if to.x > from.x then x_size - 1 else 0;
            var new_rook_x = from.x + sgn(to.x - from.x);
            pos.board[new_rook_x, to.y] = Just<Piece>{col, Rook};
            pos.board[old_rook_x, to.y] = Nothing<Piece>;
        }

    case Just{col, Pawn} =>
        // Pawn move

        // Check for en passant capture.
        match old_en_passant {
        case Just{x=target_x, y=target_y} =>
            if to.x == target_x && to.y == target_y {
                match col {
                case White =>
                    pos.board[to.x, to.y - 1] = Nothing<Piece>;
                case Black =>
                    pos.board[to.x, to.y + 1] = Nothing<Piece>;
                }
            }
        case _ =>
        }

        // Check for pawn promotion.
        // Currently we only support promotion to Queen.
        if to.y == y_size - 1 || to.y == 0 {
            pos.board[to.x, to.y] = Just<Piece>{col, Queen};
        }

    case _ =>
    }
}


// This does everything make_move_internal does, and also flips
// pos.turn over to the other player.

function make_move(ref pos: Position, from: Square, to: Square)
    requires valid_position(pos);
    requires valid_square(from);
    requires valid_square(to);
    requires is_legal_move(pos, from, to);
    ensures valid_position(pos);
{
    make_move_internal(pos, from, to);
    assert valid_position(pos);
    
    pos.turn = opposite(pos.turn);
}


// Determining whether the game is over

function exists_legal_move_from(pos: Position,
                                ref scratch_pos: Position,
                                from: Square): bool
    requires valid_position(pos);
    requires sizeof(scratch_pos.board) == board_size;
    requires valid_square(from);
    ensures return <==> exists (to: Square)
        valid_square(to) && is_legal_move(pos, from, to);
    ensures sizeof(scratch_pos.board) == board_size;
{
    var to = first_square();
    while !iteration_done(to)
        invariant valid_square(to) || iteration_done(to);
        invariant forall (other_to: Square)
            valid_square(other_to) && before(other_to, to) ==>
                !is_legal_move(pos, from, other_to);
        invariant sizeof(scratch_pos.board) == board_size;
        decreases square_number(to);
    {
        var legal = compute_is_legal_move(pos, scratch_pos, from, to);
        if legal {
            return true;
        }
        next_square(to);
    }
    
    return false;
}

function get_game_status(pos: Position,
                         ref scratch_pos: Position): GameStatus
    requires valid_position(pos);
    requires sizeof(scratch_pos.board) == board_size;
    ensures sizeof(scratch_pos.board) == board_size;
    ensures return == game_status(pos);    
{
    var from = first_square();
    while !iteration_done(from)
        invariant valid_square(from) || iteration_done(from);
        invariant forall (other_from: Square)
            valid_square(other_from) && before(other_from, from) ==>
                !exists (to: Square) valid_square(to) && is_legal_move(pos, other_from, to);
        invariant sizeof(scratch_pos.board) == board_size;                
        decreases square_number(from);
    {
        var legal = exists_legal_move_from(pos, scratch_pos, from);
        if legal {
            return InProgress;
        }

        ghost var old_from = from;
        next_square(from);

        assert forall (other_from: Square)
            valid_square(other_from) && before(other_from, from) ==>
                other_from == old_from || before(other_from, old_from);
    }

    if is_check(pos) {
        return Checkmate;
    } else {
        return Stalemate;
    }
}
