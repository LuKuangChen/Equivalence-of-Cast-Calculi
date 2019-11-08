open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module X.LazyUD
  (Label : Set)
  where

open import Types
open import X.Values Label Ground

open import Relation.Nullary using (yes; no)

project : Val * → Label → (Q : PreType) → Ground Q → CastResult (` Q)
project (dyn P _ v) l Q _ with (` P) ≡? (` Q)
project (dyn P _ v) l Q _ | yes refl = succ v
project (dyn P _ v) l Q _ | no ¬p = fail l

do-cast : (T S : Type) → Label → Val S → CastResult T
do-cast * * l v = succ v
do-cast * (` P) l v with ground? P
do-cast * (` P) l v | yes Pg = succ (dyn P Pg v)
do-cast * (` P) l v | no ¬Pg = succ (dyn _ (ground-Ground P) (cast v l (ground-⌣ P)))
do-cast (` Q) * l v with ground? Q
do-cast (` Q) * l v | yes Qg = project v l Q Qg
do-cast (` Q) * l v | no ¬Qg
  = project v l (ground Q) (ground-Ground Q) >>= λ u →
    succ (cast u l (⌣symm (ground-⌣ Q)))
do-cast (` Q) (` P) l v with (` P) ⌣? (` Q)
do-cast (` Q) (` P) l v | yes P⌣Q = succ (cast v l P⌣Q)
do-cast (` Q) (` P) l v | no ¬P⌣Q = fail l

open import X.Cast Label

apply-cast : ∀ {S T} → Val S → Cast S T → CastResult T
apply-cast v (it l S T) = do-cast T S l v
