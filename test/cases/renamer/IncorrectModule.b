module IncorrectModule
interface {
  const x: i32 = 1;
  const y: x.T = 100;    // "Incorrect use as module" error
  const z: M.T = 200;    // "Not in scope: M" error
}
