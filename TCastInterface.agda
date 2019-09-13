open import Types

module TCastInterface
  (Label : Set)
  where
open import Relation.Nullary using (Dec; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import TCast Label
open import Terms Label
open import Vals Label Cast

mk-id : ∀ T → Cast T T
mk-id T = id

mk-cast : Label → ∀ T1 T2 → Cast T1 T2
mk-cast l T1 T2 = cast l T2

mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
mk-seq c1 c2 = seq c1 c2

do-cast : Label → (T1 T2 : Type) → Val T1 → CastResult T2
do-cast l T1 T2 v with T1 ⌣? T2
do-cast l .⋆ .⋆ v | yes ⋆⌣⋆ = succ v
do-cast l .⋆ .(` P) (inj P₁ v) | yes (⋆⌣P P) = do-cast l (` P₁) (` P) v
do-cast l .(` P) .⋆ v | yes (P⌣⋆ P) = succ (inj P v)
do-cast l .(` U) .(` U) v | yes ⌣U = succ v
do-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22)) (fun env c₁ b c₂) | yes ⌣⇒ =
  succ (fun env (seq (mk-cast l T21 T11) c₁) b (seq c₂ (mk-cast l T12 T22)))
do-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22)) (cons v₁ c₁ v₂ c₂) | yes ⌣⊗ =
  succ (cons v₁ (seq c₁ (mk-cast l T11 T21)) v₂ ((seq c₂ (mk-cast l T12 T22))))
do-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22)) (inl v) | yes ⌣⊕ =
  do-cast l T11 T21 v >>= λ u →
  succ (inl u)
do-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22)) (inr v) | yes ⌣⊕ =
  do-cast l T12 T22 v >>= λ u →
  succ (inr u)
do-cast l T1 T2 v | no ¬p = fail l

apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val T1 → CastResult T2
apply-cast id v = succ v
apply-cast (cast l T2) v = do-cast l _ T2 v
apply-cast (seq c c₁) v =
  apply-cast c v >>= λ u →
  apply-cast c₁ u
