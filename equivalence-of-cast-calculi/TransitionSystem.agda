module equivalence-of-cast-calculi.TransitionSystem where

open import equivalence-of-cast-calculi.Chain
  using (Chain)
  using ([]; _∷_; _++_) public
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- A *system* is a deterministic transition system, which includes
--   - a set of states
--   - a transition relation
--   - a theorem saying that final state cannot transition
--   - a theorem saying that the transition relation is deterministic

record System (State : Set) : Set₁ where
  field
    _—→_ : State → State → Set
    Final : State → Set
    final-progressing-absurd : ∀ {s t}
      → Final s
      → (s —→ t)
      → ⊥
    deterministic : ∀ {s t1 t2}
      → s —→ t1
      → s —→ t2
      → t1 ≡ t2

  _—→*_ : State → State → Set
  _—→*_ S T = Chain _—→_ S T

  record _—→+_ (s s' : State) : Set where
    constructor _∷_
    field
      {t} : State
      x  : s —→  t
      xs : t —→* s'

  data Prefix : {s1 s2 s3 : State} → (s1 —→* s2) → (s1 —→* s3) → Set where
    zero : ∀ {s1 s3}
      → {xs : s1 —→* s3}
      → Prefix [] xs

    suc : ∀ {s0 s1 s2 s3}
      → {x : s0 —→ s1}
      → {y : s0 —→ s1}
      → {xs : s1 —→* s2}
      → {ys : s1 —→* s3}
      → Prefix xs ys
      → Prefix (x ∷ xs) (y ∷ ys)

open System using (_∷_) public
