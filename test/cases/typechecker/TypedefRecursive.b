module TypedefRecursive
interface {}

type Bad = Bad;

type Bad1 = Bad2;
type Bad2 = Bad1;
