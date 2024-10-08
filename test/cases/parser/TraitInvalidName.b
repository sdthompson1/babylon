module TraitInvalidName

interface {}

function f<T: NonExistentTrait>() {}
