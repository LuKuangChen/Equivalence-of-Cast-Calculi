{-# OPTIONS --allow-unsolved-metas #-}
open import Types

module HCCastInterface
  (Label : Set)
  where
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Variables
open import HCCast Label
open import Terms Label
open import Vals Label Cast

mutual
  seq : ∀ {T1 T2 T3 T4}
    → Label
    → Cast T1 T2
    → Cast T3 T4
  ----------------
    → Cast T1 T4
  seq ℓ id⋆ id⋆
    = id⋆
  seq ℓ id⋆ (↷ ε r)
    = ↷ (⁇ ℓ) r
  seq ℓ id⋆ (↷ (⁇ l) r)
    = ↷ (⁇ l) r
  seq ℓ (↷ h (rest b (fail l))) c2
    = ↷ h (rest b (fail l))
  seq ℓ (↷ h (rest b (last t))) id⋆
    = ↷ h (rest b (last ‼))
  seq ℓ (↷ h (rest b (last t))) (↷ ε r)
    = ↷ h (ext-rest ℓ b r)
  seq ℓ (↷ h (rest b (last t))) (↷ (⁇ l) r)
    = ↷ h (ext-rest l b r)

  ext-rest : ∀ {P1 P2 P3 T1}
    → Label
    → Body P1 P2
    → Rest P3 T1
  ----------------
    → Rest P1 T1
  ext-rest {P2 = P2} {P3 = P3} ℓ b (rest b₁ t) with (` P2) ⌣? (` P3)
  ext-rest ℓ U (rest U t) | yes ⌣U
    = rest U t
  ext-rest ℓ (c₁ ⇒ c₂) (rest (c₃ ⇒ c₄) t) | yes ⌣⇒
    = rest ((seq ℓ c₃ c₁) ⇒ (seq ℓ c₂ c₄)) t
  ext-rest ℓ (c₁ ⊗ c₂) (rest (c₃ ⊗ c₄) t) | yes ⌣⊗
    = rest ((seq ℓ c₁ c₃) ⊗ (seq ℓ c₂ c₄)) t
  ext-rest ℓ (c₁ ⊕ c₂) (rest (c₃ ⊕ c₄) t) | yes ⌣⊕
    = rest ((seq ℓ c₁ c₃) ⊕ (seq ℓ c₂ c₄)) t
  ext-rest ℓ b (rest b₁ t) | no ¬p = rest b (fail ℓ)

mutual
  user-ext-rest : ∀ {P1 P2 T1}
    → Body P1 P2
    → Rest P2 T1
    ----------------
    → Rest P1 T1
  user-ext-rest U (rest U t)
    = rest U t
  user-ext-rest (c₁ ⇒ c₂) (rest (c₃ ⇒ c₄) t)
    = rest ((mk-seq c₃ c₁) ⇒ (mk-seq c₂ c₄)) t
  user-ext-rest (c₁ ⊗ c₂) (rest (c₃ ⊗ c₄) t)
    = rest ((mk-seq c₁ c₃) ⊗ (mk-seq c₂ c₄)) t
  user-ext-rest (c₁ ⊕ c₂) (rest (c₃ ⊕ c₄) t)
    = rest ((mk-seq c₁ c₃) ⊕ (mk-seq c₂ c₄)) t
    
  mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
  mk-seq id⋆ c2
    = c2
  mk-seq (↷ h (rest b (fail l))) c2
    = ↷ h (rest b (fail l))
  mk-seq (↷ h (rest b (last ‼))) id⋆ = ↷ h (rest b (last ‼))
  mk-seq (↷ h (rest b (last ‼))) (↷ (⁇ l) r) = ↷ h (ext-rest l b r)
  mk-seq (↷ h (rest b (last ε))) (↷ ε r) = ↷ h (user-ext-rest b r)

mutual
  mk-id : ∀ T → Cast T T
  mk-id ⋆
    = id⋆
  mk-id (` P)
    = ↷ ε (rest (mk-id-body P) (last ε))

  mk-id-body : ∀ P → Body P P
  mk-id-body U
    = U
  mk-id-body (T₁ ⇒ T₂)
    = mk-id T₁ ⇒ mk-id T₂
  mk-id-body (T₁ ⊗ T₂)
    = mk-id T₁ ⊗ mk-id T₂
  mk-id-body (T₁ ⊕ T₂)
    = mk-id T₁ ⊕ mk-id T₂

mk-cast : Label → ∀ T1 T2 → Cast T1 T2
mk-cast l T1 T2 = seq l (mk-id T1) (mk-id T2)
-- mk-cast ℓ T1 T2 with T1 ⌣? T2
-- mk-cast ℓ .⋆ .⋆ | yes ⋆⌣⋆ = id⋆
-- mk-cast ℓ .⋆ .(` P) | yes (⋆⌣P P)
--   = ↷ (⁇ ℓ) (rest (mk-id-body P) (last ε))
-- mk-cast ℓ .(` P) .⋆ | yes (P⌣⋆ P)
--   = ↷     ε (rest (mk-id-body P) (last ‼))
-- mk-cast ℓ .(` U) .(` U) | yes ⌣U
--   = ↷ ε (rest U (last ε))
-- mk-cast ℓ (` (T11 ⇒ T12)) (` (T21 ⇒ T22)) | yes ⌣⇒
--   = ↷ ε (rest (mk-cast ℓ T21 T11 ⇒ mk-cast ℓ T12 T22) (last ε))
-- mk-cast ℓ (` (T11 ⊗ T12)) (` (T21 ⊗ T22)) | yes ⌣⊗
--   = ↷ ε (rest (mk-cast ℓ T11 T21 ⊗ mk-cast ℓ T12 T22) (last ε))
-- mk-cast ℓ (` (T11 ⊕ T12)) (` (T21 ⊕ T22)) | yes ⌣⊕
--   = ↷ ε (rest (mk-cast ℓ T11 T21 ⊕ mk-cast ℓ T12 T22) (last ε))
-- mk-cast ℓ ⋆ ⋆ | no ¬p
--   = ⊥-elim (¬p ⋆⌣⋆)
-- mk-cast ℓ ⋆ (` P) | no ¬p
--   = ⊥-elim (¬p (⋆⌣P P))
-- mk-cast ℓ (` P) T2 | no ¬p
--   = ↷ ε (rest (mk-id-body P) (fail ℓ))

apply-last : ∀ {P T} → Last P T → Val (` P) → Val T
apply-last ε v = v
apply-last ‼ v = (inj _ v)

apply-tail : ∀ {P T} → Tail P T → Val (` P) → CastResult T
apply-tail (fail l) v = fail l
apply-tail (last t) v = succ (apply-last t v)

mutual

  apply-rest : ∀ {P T} → Rest P T → Val (` P) → CastResult T
  apply-rest (rest b t) v
    = apply-body b v >>= λ u →
      apply-tail t u

  apply-body : ∀ {P Q} → Body P Q → Val (` P) → CastResult (` Q)
  apply-body U sole
    = succ sole
  apply-body (c₁ ⇒ c₂) (fun E c₃ b c₄)
    = succ (fun E (mk-seq c₁ c₃) b (mk-seq c₄ c₂))
  apply-body (c₁ ⊗ c₂) (cons v₁ c₃ v₂ c₄)
    = succ (cons v₁ (mk-seq c₃ c₁) v₂ (mk-seq c₄ c₂))
  apply-body (c₁ ⊕ c₂) (inl v)
    = apply-cast c₁ v >>= λ u →
      succ (inl u)
  apply-body (c₁ ⊕ c₂) (inr v)
    = apply-cast c₂ v >>= λ u →
      succ (inr u)
  
  apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val T1 → CastResult T2
  apply-cast id⋆ v
    = succ v
  apply-cast (↷ (⁇ l) r) (inj P v)
    = apply-rest (ext-rest l (mk-id-body P) r) v
  apply-cast (↷ ε r) v
    = apply-rest r v
      
mutual
  seq-id-l : ∀ {T1 T2} → (c : Cast T1 T2) → mk-seq (mk-id T1) c ≡ c
  seq-id-l id⋆ = refl
  seq-id-l (↷ (⁇ l) r) = refl
  seq-id-l (↷ ε (rest U t)) = refl
  seq-id-l (↷ ε (rest (c₁ ⇒ c₂) t)) rewrite seq-id-r c₁ | seq-id-l c₂ = refl
  seq-id-l (↷ ε (rest (c₁ ⊗ c₂) t)) rewrite seq-id-l c₁ | seq-id-l c₂ = refl
  seq-id-l (↷ ε (rest (c₁ ⊕ c₂) t)) rewrite seq-id-l c₁ | seq-id-l c₂ = refl
  
  seq-id-r : ∀ {T1 T2} → (c : Cast T1 T2) → mk-seq c (mk-id T2) ≡ c
  seq-id-r id⋆ = refl
  seq-id-r (↷ h (rest b (fail l))) = refl
  seq-id-r (↷ h (rest b (last ‼))) = refl
  seq-id-r (↷ h (rest U (last ε))) = refl
  seq-id-r (↷ h (rest (c₁ ⇒ c₂) (last ε))) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
  seq-id-r (↷ h (rest (c₁ ⊗ c₂) (last ε))) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
  seq-id-r (↷ h (rest (c₁ ⊕ c₂) (last ε))) rewrite seq-id-r c₁ | seq-id-r c₂ = refl

lem-id : ∀ T
  → (v : Val T)  
  -----------------------------
  → apply-cast (mk-id T) v ≡ succ v
lem-id ⋆ v = refl
lem-id (` U) sole = refl
lem-id (` (T₁ ⇒ T₂)) (fun env c₁ b c₂) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
lem-id (` (T₁ ⊗ T₂)) (cons v₁ c₁ v₂ c₂) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
lem-id (` (T₁ ⊕ T₂)) (inl v) rewrite lem-id T₁ v = refl
lem-id (` (T₁ ⊕ T₂)) (inr v) rewrite lem-id T₂ v = refl

lem-seq : ∀ {T1 T2 T3}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → (v : Val T1)
  --------------------
  → apply-cast (mk-seq c1 c2) v ≡ apply-cast c1 v >>= λ u → apply-cast c2 u
lem-seq id⋆ c2 v = refl
lem-seq (↷ h (rest b (fail l))) c2 v = {!!}
lem-seq (↷ h (rest b (last ‼))) id⋆ v = sym (>>=-succ _)
lem-seq (↷ h (rest b (last ‼))) (↷ (⁇ l) r) v = {!!}
lem-seq (↷ (⁇ l) (rest b (last ε))) (↷ ε r) v = {!!}
lem-seq (↷ ε (rest b (last ε))) (↷ ε r) v rewrite >>=-succ (apply-body b v) = {!!}

lem-cast-¬⌣ : ∀ {T1 T2}
  → (l : Label)
  → ¬ (T1 ⌣ T2)
  → (v : Val T1)
  → apply-cast (mk-cast l T1 T2) v ≡ fail l
lem-cast-¬⌣ {⋆} {⋆} l ¬p v = ⊥-elim (¬p ⋆⌣⋆)
lem-cast-¬⌣ {⋆} {` P} l ¬p v = ⊥-elim (¬p (⋆⌣P P))
lem-cast-¬⌣ {` P} {⋆} l ¬p v = ⊥-elim (¬p (P⌣⋆ P))
lem-cast-¬⌣ {` P} {` P₁} l ¬p v with (` P) ⌣? (` P₁)
lem-cast-¬⌣ {` P} {` P₁} l ¬p v | yes p = ⊥-elim (¬p p)
lem-cast-¬⌣ {` P} {` P₁} l ¬p v | no ¬p₁
  rewrite sym (>>=-succ (apply-body (mk-id-body P) v))
        | lem-id (` P) v
  = refl

lem-cast-id⋆ : ∀ l
  → (v : Val ⋆)
  → apply-cast (mk-cast l ⋆ ⋆) v ≡ succ v
lem-cast-id⋆ l v = refl

lem-cast-inj : ∀ {P}
  → (l : Label)
  → (v : Val (` P))  
  → apply-cast (mk-cast l (` P) ⋆) v ≡ succ (inj P v)
lem-cast-inj {P} l v
  rewrite sym (>>=-succ (apply-body (mk-id-body P) v))
        | lem-id (` P) v
  = refl

lem-cast-proj : ∀ l P P₁ v
  → apply-cast (mk-cast l ⋆ (` P)) (inj P₁ v) ≡ apply-cast (mk-cast l (` P₁) (` P)) v
lem-cast-proj l P P₁ v with (` P₁) ⌣? (` P)
lem-cast-proj l .U .U v | yes ⌣U = refl
lem-cast-proj l .(_ ⇒ _) .(_ ⇒ _) v | yes ⌣⇒ = refl
lem-cast-proj l .(_ ⊗ _) .(_ ⊗ _) v | yes ⌣⊗ = refl
lem-cast-proj l .(_ ⊕ _) .(_ ⊕ _) v | yes ⌣⊕ = refl
lem-cast-proj l P P₁ v | no ¬p = refl

lem-cast-U : 
    (l : Label)
  → apply-cast (mk-cast l (` U) (` U)) sole ≡ succ sole
lem-cast-U l = refl

lem-cast-⇒ : ∀ T11 T12 T21 T22
  → ∀ {S T}
  → (l : Label)
  → {Γ : Context}
  → (E : Env Γ)
  → (c₁ : Cast T11 S)
  → (b : (Γ , S) ⊢ T)
  → (c₂ : Cast T T12)
  → apply-cast (mk-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22))) (fun E c₁ b c₂) ≡
    succ (fun E (mk-seq (mk-cast l T21 T11) c₁) b (mk-seq c₂ (mk-cast l T12 T22)))
lem-cast-⇒ T11 T12 T21 T22 l E c₁ b c₂ = refl

lem-cast-⊗ : ∀ T01 T02 T11 T12 T21 T22
  → (l : Label)
  → (v₁ : Val T01)
  → (v₂ : Val T02)
  → (c₁ : Cast T01 T11)
  → (c₂ : Cast T02 T12)
  → apply-cast (mk-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22))) (cons v₁ c₁ v₂ c₂) ≡
    succ (cons v₁ (mk-seq c₁ (mk-cast l T11 T21)) v₂ (mk-seq c₂ (mk-cast l T12 T22)))
lem-cast-⊗ T01 T02 T11 T12 T21 T22 l v₁ v₂ c₁ c₂ = refl
    
lem-cast-⊕-l : ∀ T11 T12 T21 T22
  → (l : Label)
  → (v : Val T11)
  → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inl v) ≡
    apply-cast (mk-cast l T11 T21) v >>= λ u →
    succ (inl u)
lem-cast-⊕-l T11 T12 T21 T22 l v
  = >>=-succ _

lem-cast-⊕-r : ∀ T11 T12 T21 T22
  → (l : Label)
  → (v : Val T12)
  → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inr v) ≡
    apply-cast (mk-cast l T12 T22) v >>= λ u →
    succ (inr u)
lem-cast-⊕-r T11 T12 T21 T22 l v
  = >>=-succ _
