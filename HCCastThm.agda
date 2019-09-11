module HCCastThm
  (Label : Set)
  where

open import Types

import HCCast
module HCCastLabel = HCCast Label
open HCCastLabel

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong-app; subst)
open import Relation.Nullary using (Dec; yes; no)


mutual
  lem-seq-id-l : ∀ T1 → ∀ {T2} → (c : Cast T1 T2) → mk-seq (mk-id T1) c ≡ c
  lem-seq-id-l ⋆ id⋆
    = refl
  lem-seq-id-l ⋆ (↷ h b t)
    = refl
  lem-seq-id-l (` U) (↷ ε U t)
    = refl
  lem-seq-id-l (` (T₁ ⇒ T₂)) (↷ ε (c₁ ⇒ c₂) t)
    rewrite lem-seq-id-r T₁ c₁ | lem-seq-id-l T₂ c₂
    = refl
  lem-seq-id-l (` (T₁ ⊗ T₂)) (↷ ε (c₁ ⊗ c₂) t)
    rewrite lem-seq-id-l T₁ c₁ | lem-seq-id-l T₂ c₂
    = refl
  lem-seq-id-l (` (T₁ ⊕ T₂)) (↷ ε (c₁ ⊕ c₂) t)
    rewrite lem-seq-id-l T₁ c₁ | lem-seq-id-l T₂ c₂
    = refl
    
  lem-seq-id-r : ∀ T2 → ∀ {T1} → (c : Cast T1 T2) → mk-seq c (mk-id T2) ≡ c
  lem-seq-id-r ⋆ id⋆
    = refl
  lem-seq-id-r T (↷ h b (⊥ l))
    = refl
  lem-seq-id-r ⋆ (↷ h b ‼)
    = refl
  lem-seq-id-r (` U) (↷ h U ε)
    = refl
  lem-seq-id-r (` (T₁ ⇒ T₂)) (↷ h (c₁ ⇒ c₂) ε)
    rewrite lem-seq-id-l T₁ c₁ | lem-seq-id-r T₂ c₂
    = refl
  lem-seq-id-r (` (T₁ ⊗ T₂)) (↷ h (c₁ ⊗ c₂) ε)
    rewrite lem-seq-id-r T₁ c₁ | lem-seq-id-r T₂ c₂
    = refl
  lem-seq-id-r (` (T₁ ⊕ T₂)) (↷ h (c₁ ⊕ c₂) ε)
    rewrite lem-seq-id-r T₁ c₁ | lem-seq-id-r T₂ c₂
    = refl

mk-seq-is-seq : ∀ {T1 T2 T3}
  → (ℓ : Label)
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  -------------------
  → mk-seq c1 c2 ≡ seq ℓ c1 c2
mk-seq-is-seq ℓ id⋆ id⋆ = refl
mk-seq-is-seq ℓ id⋆ (↷ (⁇ l) b t) = refl
mk-seq-is-seq ℓ (↷ h b (⊥ l)) c2 = refl
mk-seq-is-seq ℓ (↷ h U ε) (↷ ε U t) = refl
mk-seq-is-seq ℓ (↷ h (c₁ ⇒ c₂) ε) (↷ ε (c₃ ⇒ c₄) t)
  rewrite mk-seq-is-seq ℓ c₃ c₁ | mk-seq-is-seq ℓ c₂ c₄
  = refl
mk-seq-is-seq ℓ (↷ h (c₁ ⊗ c₂) ε) (↷ ε (c₃ ⊗ c₄) t)
  rewrite mk-seq-is-seq ℓ c₁ c₃ | mk-seq-is-seq ℓ c₂ c₄
  = refl
mk-seq-is-seq ℓ (↷ h (c₁ ⊕ c₂) ε) (↷ ε (c₃ ⊕ c₄) t)
  rewrite mk-seq-is-seq ℓ c₁ c₃ | mk-seq-is-seq ℓ c₂ c₄
  = refl
mk-seq-is-seq ℓ (↷ h b ‼) id⋆ = refl
mk-seq-is-seq ℓ (↷ h b ‼) (↷ (⁇ l) b₁ t) = refl

seq-assoc : ∀ {T1 T2 T3 T4 T5 T6}
  → (ℓ1 : Label)
  → (ℓ2 : Label)
  → (c1 : Cast T1 T2)
  → (c2 : Cast T3 T4)
  → (c3 : Cast T5 T6)
  -------------------
  → seq ℓ2 (seq ℓ1 c1 c2) c3 ≡ seq ℓ1 c1 (seq ℓ2 c2 c3)
seq-assoc ℓ1 ℓ2 id⋆ id⋆ id⋆ = refl
seq-assoc ℓ1 ℓ2 id⋆ id⋆ (↷ ε b t) = refl
seq-assoc ℓ1 ℓ2 id⋆ id⋆ (↷ (⁇ l) b t) = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε b (⊥ l)) c3 = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ (⁇ l₁) b (⊥ l)) c3 = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε b ε) id⋆ = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε b ‼) id⋆ = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε b ε) (↷ h b₁ t₁) with b ⌣? b₁
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε .U ε) (↷ ε .U t₁) | yes ⌣U = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε .U ε) (↷ (⁇ l) .U t₁) | yes ⌣U = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε .(c₁ ⇒ c₂) ε) (↷ ε .(c₃ ⇒ c₄) t₁) | yes (⌣⇒ c₁ c₂ c₃ c₄) = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε .(c₁ ⇒ c₂) ε) (↷ (⁇ l) .(c₃ ⇒ c₄) t₁) | yes (⌣⇒ c₁ c₂ c₃ c₄) = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε .(c₁ ⊗ c₂) ε) (↷ ε .(c₃ ⊗ c₄) t₁) | yes (⌣⊗ c₁ c₂ c₃ c₄) = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε .(c₁ ⊗ c₂) ε) (↷ (⁇ l) .(c₃ ⊗ c₄) t₁) | yes (⌣⊗ c₁ c₂ c₃ c₄) = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε .(c₁ ⊕ c₂) ε) (↷ ε .(c₃ ⊕ c₄) t₁) | yes (⌣⊕ c₁ c₂ c₃ c₄) = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε .(c₁ ⊕ c₂) ε) (↷ (⁇ l) .(c₃ ⊕ c₄) t₁) | yes (⌣⊕ c₁ c₂ c₃ c₄) = refl
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε b ε) (↷ h b₁ t₁) | no ¬p = {!!}
seq-assoc ℓ1 ℓ2 id⋆ (↷ ε b ‼) (↷ h b₁ t₁) with b ⌣? b₁
... | r = {!!}
seq-assoc ℓ1 ℓ2 id⋆ (↷ (⁇ l) b ε) c3 = {!!}
seq-assoc ℓ1 ℓ2 id⋆ (↷ (⁇ l) b ‼) c3 = {!!}
seq-assoc ℓ1 ℓ2 (↷ h b (⊥ l)) c2 c3 = refl
seq-assoc ℓ1 ℓ2 (↷ h b ε) c2 c3 = {!!}
seq-assoc ℓ1 ℓ2 (↷ h b ‼) c2 c3 = {!!}

-- seq-assoc : ∀ {T1 T2 T3 T4}
--   → (c1 : Cast T1 T2)
--   → (c2 : Cast T2 T3)
--   → (c3 : Cast T3 T4)
--   -------------------
--   → mk-seq (mk-seq c1 c2) c3 ≡ mk-seq c1 (mk-seq c2 c3)
-- seq-assoc id⋆ c2 c3 = refl
-- seq-assoc (↷ h b (⊥ l)) c2 c3 = refl
-- seq-assoc (↷ h U ε) (↷ ε U (⊥ l)) c3 = refl
-- seq-assoc (↷ h U ε) (↷ ε U ε) (↷ ε U t) = refl
-- seq-assoc (↷ h U ε) (↷ ε U ‼) id⋆ = refl
-- seq-assoc (↷ h U ε) (↷ ε U ‼) (↷ (⁇ l) U t) = refl
-- seq-assoc (↷ h U ε) (↷ ε U ‼) (↷ (⁇ l) (c₁ ⇒ c₂) t) = refl
-- seq-assoc (↷ h U ε) (↷ ε U ‼) (↷ (⁇ l) (c₁ ⊗ c₂) t) = refl
-- seq-assoc (↷ h U ε) (↷ ε U ‼) (↷ (⁇ l) (c₁ ⊕ c₂) t) = refl
-- seq-assoc (↷ h (c₁ ⇒ c₂) ε) (↷ ε (c₃ ⇒ c₄) (⊥ l)) c3 = refl
-- seq-assoc (↷ h (c₁ ⇒ c₂) ε) (↷ ε (c₃ ⇒ c₄) ε) (↷ ε (c₅ ⇒ c₆) t)
--   rewrite seq-assoc c₅ c₃ c₁ | seq-assoc c₂ c₄ c₆
--   = refl
-- seq-assoc (↷ h (c₁ ⇒ c₂) ε) (↷ ε (c₃ ⇒ c₄) ‼) id⋆ = refl
-- seq-assoc (↷ h (c₁ ⇒ c₂) ε) (↷ ε (c₃ ⇒ c₄) ‼) (↷ (⁇ l) U t) = refl
-- seq-assoc (↷ h (c₁ ⇒ c₂) ε) (↷ ε (c₃ ⇒ c₄) ‼) (↷ (⁇ l) (c₅ ⇒ c₆) t)
--   = {!!}
-- seq-assoc (↷ h (c₁ ⇒ c₂) ε) (↷ ε (c₃ ⇒ c₄) ‼) (↷ (⁇ l) (c₅ ⊗ c₆) t) = refl
-- seq-assoc (↷ h (c₁ ⇒ c₂) ε) (↷ ε (c₃ ⇒ c₄) ‼) (↷ (⁇ l) (c₅ ⊕ c₆) t) = refl
-- seq-assoc (↷ h (c₁ ⊗ c₂) ε) (↷ ε (c₃ ⊗ c₄) t) c3 = {!!}
-- seq-assoc (↷ h (c₁ ⊕ c₂) ε) (↷ ε (c₃ ⊕ c₄) t) c3 = {!!}
-- seq-assoc (↷ h b ‼) c2 c3 = {!!}
