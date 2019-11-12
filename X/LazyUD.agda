open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module X.LazyUD
  (Label : Set)
  where

open import Types
open import BlameStrategies using (LazyUDInjectable)
open import X.Values Label LazyUDInjectable
open import X.Cast Label

open import Relation.Nullary using (yes; no)

project : Val * → Label → (Q : PreType) → Ground Q → CastResult (` Q)
project (dyn P Pg v) l Q Qg with (` P) ≡? (` Q)
... | yes refl = succ v
... | no ¬p = fail l

apply-cast : ∀ {S T} → Val S → Cast S T → CastResult T
apply-cast v (it l * *) = succ v
apply-cast v (it l (` P) *) with ground? P
... | yes Pg = succ (dyn P Pg v)
... | no ¬Pg = succ (dyn _ (ground-Ground P)
                    (proxy v (it l (` P) (` ground P)) (ground-⌣ P)))
apply-cast v (it l (` P) (` Q)) with (` P) ⌣? (` Q)
... | yes p = succ (proxy v (it l (` P) (` Q)) p)
... | no ¬p = fail l
apply-cast v (it l * (` Q)) with ground? Q
apply-cast v (it l .* (` Q)) | yes Qg = project v l Q Qg
apply-cast v (it l .* (` Q)) | no ¬Qg
  = project v l (ground Q) (ground-Ground Q) >>= λ u →
    succ (proxy u (it l (` ground Q) (` Q)) (⌣sym (ground-⌣ Q)))
