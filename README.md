# Equivalence of Cast Calculi

This repo comes with [Kuang-Chen Lu's master's thesis](https://lukuangchen.github.io/Downloads/thesis-of-KuangChen.pdf).

I assume you, the reader, already know

* what *gradual typing* is,
* that *structural* (rather than *nominal*) gradual typing can incur terrible runtime overhead because of casts
* that we can optimize some overhead away by representing casts more compactly with cast calculi/representations

When my thesis was written (2020), the most well-known cast calculi are *coercions* and *threesomes*.

There are two major contributions of my thesis (as well as this repo):

* an Agda library that helps you (formally) (1) defines a cast calculus, and (2) prove that your calculus is correct (explained in the thesis and below).
* hypercoercion, a new kind of cast calculi that seem to be better than known ones (explained in the thesis)

## What do you mean by a (cast) calculus is correct?

It means that using the cast calculus to (hopefully) optimize runtime *does not change the (dynamic) semantics of language*.
More specifically, programs that raise cast errors will still error with the same error messages (i.e., blame labels),
and programs that produce other results will still produce the same results.

## How can this library help me defines a cast calculus?

It defines the collection of functions that you must implement for any kind of cast calculus.

In other words, it defines the abstract data type (ADT) for cast (calculi).

## How can this library help me proof the correctness of my cast calculus?

Usually, to proof correctness, one must proof that a dynamic semantics using the cast calculus is equivalent to the
referential (and hence not optimized) dynamic semantics. For brievity,
let's call them *optimized semantics* and *referential semantics* respectively.

So, usually, one needs to define the referential semantics and a optimized semantics, and prove the equivalence of the
two semantics. This is a non-trivial amount of work. Futhermore, if you are proving multiple cast calculi, a considerable
portion of the work will be repeatitive -- your optimized semantics would be almost identical except for the places that
really involve casts.

Given these observation, I capture the interaction between optimized semantics and cast calculus as an ADT. Now, rather than
proving properties of the optimized semantics, you only need to proof properties about the ADT. The library provides functions
that turn the ADT proofs to the proofs about semantics.

## How to use this library?

You should follow the examples in [illustration](./illustration).
There, each file applies our framework to a known cast representation.
We recommand starting with [coercions in normal form](./illustration/LazyUDCoercionsInNormalForm.agda) if you know coercions.
Otherwise, [Lazy UD hypercoercions](illustration/LazyUDHypercoercions.agda) is recommanded because 
this cast representation is described in details in my thesis.
