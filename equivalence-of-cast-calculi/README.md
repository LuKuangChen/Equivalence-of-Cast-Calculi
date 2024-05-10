# Inventory

* [./C](./C) defines blame strategies (only Lazy D and Lazy UD are supported) and the referential semantics. (This machine is named as `R(B)` in my thesis.)
* [./S](./S) defines the CastADT (i.e., the ADT for cast calculi) and the optimized semantics.
* [./Bisimulation/LazyDCastADT.agda](./Bisimulation/LazyDCastADT.agda) defines the required properties for a Lazy D cast calculus.
* [./Bisimulation/LazyUDCastADT.agda](./Bisimulation/LazyUDCastADT.agda) defines the required properties for a Lazy UD cast calculus.
* [./Theorems.agda](./Theorems.agda) defines the theorems: an optimized semantics using a Lazy(U)D CastADT is equivalent to the Lazy (U)D referential semantics
* [./GTLC.agda](./GTLC.agda) defines the flavor of Gradually Typed Lambda Calculus used in this formalization.
* [./CastInsertion.agda](./CastInsertion.agda) compile GTLC to Core Calculus (defined in [./CC.agda](./CC.agda)) by making casts explicit.

Other files provide auxiliary definitions.
