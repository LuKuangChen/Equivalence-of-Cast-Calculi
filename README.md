# Equivalence of Cast Calculi

This repo aims at helping people to develop new cast representations and to prove their correctness.

The package [equivalence-of-cast-calculi](./equivalence-of-cast-calculi) contains necessary semantic definition and theorems.
To get started, one must pick a blame strategy. We currently support only Lazy D and Lazy UD.
Assuming one has picked the Lazy UD strategy, they should create an Agda module and import the 
[equivalence-of-cast-calculi/NewLazyUDCastADT](./equivalence-of-cast-calculi/NewLazyUDCastADT) module,
implement a Cast ADT (said `C`),
prove that `C` is a Lazy UD Cast ADT.
To show that `S(C)` is equivalent to `R(LD)`, they will need `theorem-LazyD-CastADT-correct-part-1` and `theorem-LazyD-CastADT-correct-part-1`, which
are all provided by the [NewLazyUDCastADT](./equivalence-of-cast-calculi/NewLazyUDCastADT) module.

For illustration, please refer to [illustration](./illustration). There each file applies our framework to a known cast representation.
We recommand starting with [coercions in normal form](./illustration/LazyUDCoercionsInNormalForm.agda) if you are familiar with this name.
Otherwise [Lazy UD hypercoercions](illustration/LazyUDHypercoercions.agda) might be a good choice.
