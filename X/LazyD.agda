open import Relation.Nullary using (Dec; yes; no)

module X.LazyD
  (Label : Set)
  where

open import Types

record Injectable (P : PreType) : Set where

open import X.Cast Label
open import X.Values Label Injectable

open import Relation.Nullary using (yes; no)

project : Val * → Label → (P : PreType) → CastResult (` P)
project (dyn P _ v) l Q with (` P) ⌣? (` Q)
project (dyn P _ v) l Q | yes p = succ (cast v l p)
project (dyn P _ v) l Q | no ¬p = fail l

do-cast : (T S : Type) → Label → Val S → CastResult T
do-cast * * l v = succ v
do-cast * (` P) l v = succ (dyn P _ v)
do-cast (` Q) * l v = project v l Q
do-cast (` Q) (` P) l v with (` P) ⌣? (` Q)
do-cast (` Q) (` P) l v | yes p = succ (cast v l p)
do-cast (` Q) (` P) l v | no ¬p = fail l

apply-cast : ∀ {S T} → Val S → Cast S T → CastResult T
apply-cast v (it l S T) = do-cast T S l v

