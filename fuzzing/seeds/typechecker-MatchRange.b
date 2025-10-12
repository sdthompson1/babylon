module Main
interface {}

const test_i8: bool =
  match (i8(100)) {
    case -100 => true    // OK
    case  110 => true    // OK
    case 1000 => true    // Error
    case _ => true
  };

const test_u8: bool =
  match (u8(100)) {
    case 20 => true    // OK
    case 2000 => true  // Error
    case -1 => true    // Error
    case _ => true
  };

const test_i16: bool =
  match (i16(100)) {
    case 25000 => true   // OK
    case -99999 => true  // Error
    case _ => true
  };

const test_u16: bool =
  match (u16(100)) {
    case 40000 => true  // OK
    case -1 => true     // Error
    case _ => true
  };
