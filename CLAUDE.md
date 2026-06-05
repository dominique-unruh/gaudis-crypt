# subtask 1
We want to define `glob A` with intended semantics being all global variables of A, or alternatively the part of state which `A` can potentially modify.

Here is the plan:

- Define a structure Getter with elements get.
- Let structure Lens inherit from Getter.
- Define Lens.toGetter (or as a coercion)
- Define LensRange.global_getter : LensRange m -> Getter <some type>
- Define Program.range : Program s a -> LensRange m
- Define Program.range' (progs : a -> Program s b) := Sup of all (progs x).range (for convenience)
 
And then you have glob A := A.range.global_getter or A.range'.global_getter, depending on the type.

# subtask 2
Our goal is to develop enough theory to prove the following theorem (roughly):

Theorem: forall Adv, L. If Adv inRange L.range,
then there exists Adv' such that Adv = L(Adv')

L() :: Program c a -> Program s a  for any lens of type Lens c s

L(Adv') defined as:
do
  inner_st := L.get st
  inner_st' <- Adv' inner_st
  st := lens.set inner_st' st
