module TraitDuplicate

interface {}

// Error: Copy listed twice
datatype DType<a: Copy + Copy> = DType;

// Error: Default listed twice
type Typedef<a: Default + Copy + Default> = a;

// Error: Move listed twice
function f<a: Move + Default + Move>() {}
