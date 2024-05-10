# Equivalence of Cast Calculi

This repo comes with [Kuang-Chen Lu's master's thesis](https://lukuangchen.github.io/Downloads/thesis-of-KuangChen.pdf).

I assume you, the reader, already know

* what *gradual typing* is,
* why casts in *structural* (rather than *nominal*) gradual typing can incur terrible runtime overhead
* that we can optimize some overhead away by representing casts more compactly with cast calculi/representations

When my thesis was written (2020), the most well-known cast calculi were *coercion* and *threesome*.

There are two major contributions of my thesis (as well as this repo):

* An Agda library that helps you (formally) (1) define a cast calculus, and (2) prove that your calculus is correct (explained in the thesis and below).
* Hypercoercion, a new kind of cast calculi that seems to be better than known ones (explained in the thesis)

## What do you mean by a (cast) calculus is correct?

It means that using the cast calculus to (hopefully) optimize runtime *does not change the (dynamic) semantics*.
More specifically, programs that raise cast errors will still error with the same error messages (i.e., blame labels),
and programs that produce other results will still produce the same results.

## How can this library help me define a cast calculus?

It defines the collection of functions that you must implement for any kind of cast calculus.

In other words, it defines the abstract data type (ADT) for cast (calculi).

## How can this library help me prove the correctness of my cast calculus?

Usually, to prove correctness, one needs to define the referential semantics and an optimized semantics, and prove the equivalence of the
two semantics. This is a non-trivial amount of work. Furthermore, if you are proving multiple cast calculi, a considerable
portion of the work will be repetitive -- your optimized semantics would be almost identical except for the places that
really involve casts.

Given these observations, I capture the interaction between optimized semantics and cast calculus as an ADT. Now, rather than
proving properties of the optimized semantics, you only need to prove properties about the ADT. The library provides functions
that turn the ADT proofs into the proof about semantics.

## How to use this library?

You should follow the examples in the [illustration](./illustration) folder.
There, each file applies our framework to a known cast representation.
I recommend starting with [coercions in normal form](./illustration/LazyUDCoercionsInNormalForm.agda) if you know coercion.
Otherwise, [Lazy UD hypercoercions](illustration/LazyUDHypercoercions.agda) are recommended because
this cast representation is described in detail in my thesis.

Check the [equivalence-of-cast-calculi](./equivalence-of-cast-calculi) folder for things like the semantics, the ADT, properties, and theorems.
