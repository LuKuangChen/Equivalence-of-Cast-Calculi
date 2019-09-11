open import Types

module HCCastInterface
  (Label : Set)
  where
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Variables
open import HCCast Label
open import Terms Label
open import Vals Label Cast

mutual
  seq : Label → ∀ {T1 T2 T3 T4} → Cast T1 T2 → Cast T3 T4 →
    Cast T1 T4
  -- here ℓ is the label that associates with all casts in the middle
  seq ℓ id⋆ id⋆ =
    id⋆
  seq ℓ id⋆ (↷ ε b t) =
    ↷ (⁇ ℓ) b t
  seq ℓ id⋆ (↷ (⁇ l) b t) =
    ↷ (⁇ l) b t
  seq ℓ (↷ h b (⊥ l)) c2 =
    ↷ h b (⊥ l)
  -- now t is either ε or ⁇
  seq ℓ (↷ h b t) id⋆ =
    ↷ h b ‼
  seq ℓ (↷ h b t) (↷ ε b₁ t₁) =
    seq-body ℓ h b b₁ t₁
  seq ℓ (↷ h b t) (↷ (⁇ l) b₁ t₁) =
    seq-body l h b b₁ t₁
  
  seq-body : ∀ {T1 T2 P1 P2 P3 P4}
    → Label
    → Head P1 T1
    → Body P1 P2
    → Body P3 P4
    → Tail P4 T2
    -------------
    → Cast T1 T2
  seq-body {P2 = P2} {P3 = P3} ℓ h b b₁ t with (` P2) ⌣? (` P3)
  seq-body ℓ h U U t | yes ⌣U = ↷ h U t
  seq-body ℓ h (c₁ ⇒ c₂) (c₃ ⇒ c₄) t | yes ⌣⇒ =
    ↷ h (seq ℓ c₃ c₁ ⇒ seq ℓ c₂ c₄) t
  seq-body ℓ h (c₁ ⊗ c₂) (c₃ ⊗ c₄) t | yes ⌣⊗ =
    ↷ h (seq ℓ c₁ c₃ ⊗ seq ℓ c₂ c₄) t
  seq-body ℓ h (c₁ ⊕ c₂) (c₃ ⊕ c₄) t | yes ⌣⊕ =
    ↷ h (seq ℓ c₁ c₃ ⊕ seq ℓ c₂ c₄) t
  seq-body ℓ h b b₁ t | no ¬p = ↷ h b (⊥ ℓ)

mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
mk-seq id⋆ c =
  c
mk-seq (↷ h b (⊥ l)) c2 =
  ↷ h b (⊥ l)
mk-seq (↷ h U ε) (↷ ε U t) =
  ↷ h U t
mk-seq (↷ h (c₁ ⇒ c₂) ε) (↷ ε (c₃ ⇒ c₄) t) =
  ↷ h (mk-seq c₃ c₁ ⇒ mk-seq c₂ c₄) t
mk-seq (↷ h (c₁ ⊗ c₂) ε) (↷ ε (c₃ ⊗ c₄) t) =
  ↷ h (mk-seq c₁ c₃ ⊗ mk-seq c₂ c₄) t
mk-seq (↷ h (c₁ ⊕ c₂) ε) (↷ ε (c₃ ⊕ c₄) t) =
  ↷ h (mk-seq c₁ c₃ ⊕ mk-seq c₂ c₄) t
mk-seq (↷ h b ‼) id⋆ =
  ↷ h b ‼
mk-seq (↷ h b ‼) (↷ (⁇ l) b₁ t) =
  seq-body l h b b₁ t

mk-id : ∀ T → Cast T T
mk-id ⋆ = id⋆
mk-id (` U) = ↷ ε U ε
mk-id (` (T₁ ⇒ T₂)) = ↷ ε (mk-id T₁ ⇒ mk-id T₂) ε
mk-id (` (T₁ ⊗ T₂)) = ↷ ε (mk-id T₁ ⊗ mk-id T₂) ε
mk-id (` (T₁ ⊕ T₂)) = ↷ ε (mk-id T₁ ⊕ mk-id T₂) ε

mk-cast : Label → ∀ T1 T2 → Cast T1 T2
mk-cast ℓ T1 T2 = seq ℓ (mk-id T1) (mk-id T2)
-- mk-cast ℓ ⋆ ⋆ = id⋆
-- mk-cast ℓ ⋆ (` U) = ↷ (⁇ ℓ) U ε
-- mk-cast ℓ ⋆ (` (T₁ ⇒ T₂)) = ↷ (⁇ ℓ) (mk-cast ℓ T₁ T₂ ⇒ mk-cast ℓ T₁ T₂) ε
-- mk-cast ℓ ⋆ (` (T₁ ⊗ T₂)) = ↷ (⁇ ℓ) (mk-cast ℓ T₂ T₁ ⊗ mk-cast ℓ T₁ T₂) ε
-- mk-cast ℓ ⋆ (` (T₁ ⊕ T₂)) = ↷ (⁇ ℓ) (mk-cast ℓ T₂ T₁ ⊕ mk-cast ℓ T₁ T₂) ε
-- mk-cast ℓ (` U) ⋆ = ↷ ε U ‼
-- mk-cast ℓ (` (T₁ ⇒ T₂)) ⋆ = ↷ ε (mk-cast ℓ T₂ T₁ ⇒ mk-cast ℓ T₂ T₁) ‼
-- mk-cast ℓ (` (T₁ ⊗ T₂)) ⋆ = ↷ ε (mk-cast ℓ T₁ T₂ ⊗ mk-cast ℓ T₂ T₁) ‼
-- mk-cast ℓ (` (T₁ ⊕ T₂)) ⋆ = ↷ ε (mk-cast ℓ T₁ T₂ ⊕ mk-cast ℓ T₂ T₁) ‼
-- mk-cast ℓ (` U) (` U) = ↷ ε U ε
-- mk-cast ℓ (` (T₁ ⇒ T₂)) (` (T₃ ⇒ T₄)) = ↷ ε (mk-cast ℓ T₃ T₁ ⇒ mk-cast ℓ T₂ T₄) ε
-- mk-cast ℓ (` (T₁ ⊗ T₂)) (` (T₃ ⊗ T₄)) = ↷ ε (mk-cast ℓ T₁ T₃ ⊗ mk-cast ℓ T₂ T₄) ε
-- mk-cast ℓ (` (T₁ ⊕ T₂)) (` (T₃ ⊕ T₄)) = ↷ ε (mk-cast ℓ T₁ T₃ ⊕ mk-cast ℓ T₂ T₄) ε
-- mk-cast ℓ (` U) (` P₁) = ↷ ε U (⊥ ℓ)
-- mk-cast ℓ (` (T₁ ⇒ T₂)) (` P₁) = ↷ ε (mk-id T₁ ⇒ mk-id T₂) (⊥ ℓ)
-- mk-cast ℓ (` (T₁ ⊗ T₂)) (` P₁) = ↷ ε (mk-id T₁ ⊗ mk-id T₂) (⊥ ℓ)
-- mk-cast ℓ (` (T₁ ⊕ T₂)) (` P₁) = ↷ ε (mk-id T₁ ⊕ mk-id T₂) (⊥ ℓ)

apply-tail : ∀ {P T} → Tail P T → Val (` P) → CastResult T
apply-tail ε v = succ v
apply-tail ‼ v = succ (inj _ v)
apply-tail (⊥ l) v = fail l

apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val T1 → CastResult T2
apply-cast id⋆ v =
  succ v
apply-cast (↷ ε U t) sole =
  apply-tail t sole
apply-cast (↷ ε (c₁ ⇒ c₂) t) (fun E c₃ b c₄) =
  apply-tail t (fun E (mk-seq c₁ c₃) b (mk-seq c₄ c₂))
apply-cast (↷ ε (c₁ ⊗ c₂) t) (cons v₁ v₂) =
  apply-cast c₁ v₁ >>= λ u₁ →
  apply-cast c₂ v₂ >>= λ u₂ →
  apply-tail t (cons u₁ u₂)
apply-cast (↷ ε (c₁ ⊕ c₂) t) (inl v) =
  apply-cast c₁ v >>= λ u →
  apply-tail t (inl u)
apply-cast (↷ ε (c₁ ⊕ c₂) t) (inr v) =
  apply-cast c₂ v >>= λ u →
  apply-tail t (inr u)
apply-cast (↷ {P = P1} (⁇ l) b t) (inj P2 v) =
  apply-cast (mk-seq (mk-cast l (` P2) (` P1)) (↷ ε b t)) v

mutual
  seq-id-l : ∀ {T1 T2} → (c : Cast T1 T2) → mk-seq (mk-id T1) c ≡ c
  seq-id-l id⋆ = refl
  seq-id-l (↷ (⁇ l) b t) = refl
  seq-id-l (↷ ε U t) = refl
  seq-id-l (↷ ε (c₁ ⇒ c₂) t) rewrite seq-id-r c₁ | seq-id-l c₂ = refl
  seq-id-l (↷ ε (c₁ ⊗ c₂) t) rewrite seq-id-l c₁ | seq-id-l c₂ = refl
  seq-id-l (↷ ε (c₁ ⊕ c₂) t) rewrite seq-id-l c₁ | seq-id-l c₂ = refl
  
  seq-id-r : ∀ {T1 T2} → (c : Cast T1 T2) → mk-seq c (mk-id T2) ≡ c
  seq-id-r id⋆ = refl
  seq-id-r (↷ h b (⊥ l)) = refl
  seq-id-r (↷ h b ‼) = refl
  seq-id-r (↷ h U ε) = refl
  seq-id-r (↷ h (c₁ ⇒ c₂) ε) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
  seq-id-r (↷ h (c₁ ⊗ c₂) ε) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
  seq-id-r (↷ h (c₁ ⊕ c₂) ε) rewrite seq-id-r c₁ | seq-id-r c₂ = refl

lem-id : ∀ T
  → (v : Val T)  
  -----------------------------
  → apply-cast (mk-id T) v ≡ succ v
lem-id ⋆ v = refl
lem-id (` U) sole = refl
lem-id (` (T₁ ⇒ T₂)) (fun env c₁ b c₂) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
lem-id (` (T₁ ⊗ T₂)) (cons v₁ v₂) rewrite lem-id T₁ v₁ | lem-id T₂ v₂ =  refl
lem-id (` (T₁ ⊕ T₂)) (inl v) rewrite lem-id T₁ v = refl
lem-id (` (T₁ ⊕ T₂)) (inr v) rewrite lem-id T₂ v = refl

lem-seq : ∀ {T1 T2 T3}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → (v : Val T1)
  --------------------
  → apply-cast (mk-seq c1 c2) v ≡ apply-cast c1 v >>= λ u → apply-cast c2 u
lem-seq id⋆ c2 v = refl
lem-seq (↷ (⁇ l) b t) c2 v = {!!}
lem-seq (↷ ε b t) c2 v = {!!}

lem-cast-¬⌣ : ∀ {T1 T2}
  → (l : Label)
  → ¬ (T1 ⌣ T2)
  → (v : Val T1)
  → apply-cast (mk-cast l T1 T2) v ≡ fail l
lem-cast-¬⌣ l ¬p v = {!!}

lem-cast-id⋆ : ∀ l
  → (v : Val ⋆)
  → apply-cast (mk-cast l ⋆ ⋆) v ≡ succ v
lem-cast-id⋆ l v = refl

lem-cast-inj : ∀ {P}
  → (l : Label)
  → (v : Val (` P))  
  → apply-cast (mk-cast l (` P) ⋆) v ≡ succ (inj P v)
lem-cast-inj l v = {!!}

lem-cast-proj : ∀ l P P₁ v
  → apply-cast (mk-cast l ⋆ (` P)) (inj P₁ v) ≡ apply-cast (mk-cast l (` P₁) (` P)) v
lem-cast-proj l P P₁ v = {!!}

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

lem-cast-⊗ : ∀ T11 T12 T21 T22
  → (l : Label)
  → (v : Val T11)
  → (v₁ : Val T12)
  → apply-cast (mk-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22))) (cons v v₁) ≡
    apply-cast (mk-cast l T11 T21) v >>= λ u →
    apply-cast (mk-cast l T12 T22) v₁ >>= λ u₁ →
    succ (cons u u₁)
lem-cast-⊗ T11 T12 T21 T22 l v v₁ = refl
    
lem-cast-⊕-l : ∀ T11 T12 T21 T22
  → (l : Label)
  → (v : Val T11)
  → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inl v) ≡
    apply-cast (mk-cast l T11 T21) v >>= λ u →
    succ (inl u)
lem-cast-⊕-l T11 T12 T21 T22 l v = refl

lem-cast-⊕-r : ∀ T11 T12 T21 T22
  → (l : Label)
  → (v : Val T12)
  → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inr v) ≡
    apply-cast (mk-cast l T12 T22) v >>= λ u →
    succ (inr u)
lem-cast-⊕-r T11 T12 T21 T22 l v = refl
