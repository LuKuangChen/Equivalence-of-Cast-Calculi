open import Relation.Nullary using (Dec; yes; no)

module X.LazyD
  (Label : Set)
  where

open import Types
open import BlameStrategies using (LazyDInjectable)

open import Data.Unit using (tt)

open import X.Cast Label
open import X.Values Label LazyDInjectable

open import Relation.Nullary using (yes; no)

apply-cast' : ∀ {P Q} → Val (` P) → Cast (` P) (` Q) → CastResult (` Q)
apply-cast' v (it l (` P) (` Q)) with (` P) ⌣? (` Q)
... | yes p = succ (proxy v (it l (` P) (` Q)) p)
... | no ¬p = fail l

apply-cast : ∀ {S T} → Val S → Cast S T → CastResult T
apply-cast v (it l * *) = succ v
apply-cast v (it l (` P) *) = succ (dyn P tt v)
apply-cast v (it l (` P) (` Q)) = apply-cast' v (it l (` P) (` Q))
apply-cast (dyn P I v) (it l * (` Q)) = apply-cast' v (it l (` P) (` Q))

