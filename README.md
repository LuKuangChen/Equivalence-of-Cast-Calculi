# Equivalence of Cast Calculi

This repo comes with [Kuang-Chen Lu's master's thesis](https://lukuangchen.github.io/Downloads/thesis-of-KuangChen.pdf).

This repo aims at helping people to develop new cast representations and to prove their correctness.

The package [equivalence-of-cast-calculi](./equivalence-of-cast-calculi) contains necessary semantic definition and theorems.
To get started, a user must pick a blame strategy. Currently only Lazy D and Lazy UD blame strategy are supported.

If a user want to prove a Lazy UD cast representation is correct, the user should
1. create an Agda module and import the [equivalence-of-cast-calculi/NewLazyUDCastADT](./equivalence-of-cast-calculi/NewLazyUDCastADT) module;
2. define a Cast ADT (said `c`);
3. prove that `c` is a Lazy UD Cast ADT.

For illustration, please refer to [illustration](./illustration). There each file applies our framework to a known cast representation.
We recommand starting with [coercions in normal form](./illustration/LazyUDCoercionsInNormalForm.agda) if you know coercions.
Otherwise, [Lazy UD hypercoercions](illustration/LazyUDHypercoercions.agda) is recommanded because 
this cast representation is described in details in our paper.
