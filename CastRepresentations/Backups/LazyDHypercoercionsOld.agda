module CastRepresentations.LazyDHypercoercions (Label : Set) where
open import Types
open import Variables using (Context)
open import Terms Label
open import Cast Label using (_⟹[_]_) renaming (Cast to SrcCast)
open import S.CastADT Label
open import S.LazyDCastADT Label
open import Error using (Error; return; raise; _>>=_; _>=>_; >>=-return)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

open import X.BlameStrategies Label using (BlameStrategy; LazyDBS)
open BlameStrategy LazyDBS

data Head : PreType → Type → Set where
  ⁇ : ∀ {P} → (l : Label) → Head P *
  ε : ∀ {P} → Head P (` P)

data Last (P : PreType) : Type → Set where
  ‼ : Last P *
  ε : Last P (` P)

data Tail (P : PreType) : Type → Set where
  fail : ∀ {T}
    → (l : Label)
    → Tail P T
  last : ∀ {T}
    → (t : Last P T)
    → Tail P T

mutual
  data Cast : Type → Type → Set where
    id* : Cast * *
    ↷ : ∀ {A P B}
      → (h : Head P A)
      → (r : Rest P B)
      → Cast A B

  data Rest : PreType → Type → Set where
    rest : ∀ {P Q B}
      → (b : Body P Q)
      → (t : Tail Q B)
      → Rest P B
    
  data Body : PreType → PreType → Set where
    B : Body B B
    _⇒_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S2 S1) →
      (c₂ : Cast T1 T2) →
      Body (S1 ⇒ T1) (S2 ⇒ T2)
    _⊗_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S1 S2) →
      (c₂ : Cast T1 T2) →
      Body (S1 ⊗ T1) (S2 ⊗ T2)
    -- _⊕_ : ∀ {S1 S2 T1 T2} →
    --   (c₁ : Cast S1 S2) →
    --   (c₂ : Cast T1 T2) →
    --   Body (S1 ⊕ T1) (S2 ⊕ T2)

GapP : PreType → PreType → Set
GapP P1 P2 = P1 ≡ P2 ⊎ Label

GapT : Type → Type → Set
GapT T1 T2 = T1 ≡ T2 ⊎ Label

ℓ-dom : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⇒ T2) (T3 ⇒ T4)
  → GapT T3 T1
ℓ-dom (inj₁ refl) = inj₁ refl
ℓ-dom (inj₂ l) = inj₂ l

ℓ-cod : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⇒ T2) (T3 ⇒ T4)
  → GapT T2 T4
ℓ-cod (inj₁ refl) = inj₁ refl
ℓ-cod (inj₂ l) = inj₂ l

ℓ-car : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊗ T2) (T3 ⊗ T4)
  → GapT T1 T3
ℓ-car (inj₁ refl) = inj₁ refl
ℓ-car (inj₂ l) = inj₂ l

ℓ-cdr : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊗ T2) (T3 ⊗ T4)
  → GapT T2 T4
ℓ-cdr (inj₁ refl) = inj₁ refl
ℓ-cdr (inj₂ l) = inj₂ l

-- ℓ-inl : ∀ {T1 T2 T3 T4}
--   → GapP (T1 ⊕ T2) (T3 ⊕ T4)
--   → GapT T1 T3
-- ℓ-inl (inj₁ refl) = inj₁ refl
-- ℓ-inl (inj₂ l) = inj₂ l

-- ℓ-inr : ∀ {T1 T2 T3 T4}
--   → GapP (T1 ⊕ T2) (T3 ⊕ T4)
--   → GapT T2 T4
-- ℓ-inr (inj₁ refl) = inj₁ refl
-- ℓ-inr (inj₂ l) = inj₂ l

mutual
  seq : ∀ {T1 T2 T3 T4}
    → Cast T1 T2
    → T2 ≡ T3 ⊎ Label
    → Cast T3 T4
  ----------------
    → Cast T1 T4
  seq id* ℓ id* = id*
  seq id* ℓ (↷ (⁇ l) r) = ↷ (⁇ l) r
  seq id* ℓ (↷ ε r)
    with ℓ
  ... | inj₁ ()
  ... | inj₂ l = ↷ (⁇ l) r
  seq (↷ h (rest b (fail l)))    ℓ c2        = ↷ h (rest b (fail l))
  seq (↷ h (rest b (last t)))    ℓ id*       = ↷ h (rest b (last ‼))
  seq (↷ h1 (rest b1 (last t1))) ℓ (↷ h2 r2) = ↷ h1 (seq-rest b1 t1 ℓ h2 r2)

  seq-rest : ∀ {P1 P2 P3 T1 T2 T3}
    → (b1 : Body P1 P2)
    → (t1 : Last P2 T1)
    → (ℓ : GapT T1 T2)
    → (h2 : Head P3 T2)
    → (r2 : Rest P3 T3)
    → Rest P1 T3
  seq-rest {P2 = P1} b1 t1 ℓ h2 (rest {P = P2} b2 t2)
    with (` P1) ⌣? (` P2)
  ... | yes p = rest (seq-m (link h2 ℓ t1) p b1 b2) t2
  ... | no ¬p
    with (link h2 ℓ t1)
  ... | inj₁ refl = ⊥-elim (¬p (⌣refl _))
  ... | inj₂ l = rest b1 (fail l)

  seq-m : ∀ {P1 P2 P3 P4}
    → P2 ≡ P3 ⊎ Label
    → (` P2) ⌣ (` P3)
    → Body P1 P2
    → Body P3 P4
    ---
    → Body P1 P4
  seq-m ℓ ⌣B B B = B
  seq-m ℓ ⌣⇒ (c₁ ⇒ c₂) (c₃ ⇒ c₄) = seq c₃ (ℓ-dom ℓ) c₁ ⇒ seq c₂ (ℓ-cod ℓ) c₄
  seq-m ℓ ⌣⊗ (c₁ ⊗ c₂) (c₃ ⊗ c₄) = seq c₁ (ℓ-car ℓ) c₃ ⊗ seq c₂ (ℓ-cdr ℓ) c₄
  -- seq-m ℓ ⌣⊕ (c₁ ⊕ c₂) (c₃ ⊕ c₄) = seq c₁ (ℓ-inl ℓ) c₃ ⊕ seq c₂ (ℓ-inr ℓ) c₄
  
  link : ∀ {Q P T1 T2}
    → (h : Head P T2)
    → (ℓ : T1 ≡ T2 ⊎ Label)
    → (t : Last Q T1)
    -----------------
    → Q ≡ P ⊎ Label
  link (⁇ l) ℓ t = inj₂ l
  link ε (inj₁ refl) ε = inj₁ refl
  link ε (inj₂ l)    t = inj₂ l

mutual
  mk-id : ∀ T → Cast T T
  mk-id *
    = id*
  mk-id (` P)
    = ↷ ε (rest (mk-id-body P) (last ε))

  mk-id-body : ∀ P → Body P P
  mk-id-body B
    = B
  mk-id-body (T₁ ⇒ T₂)
    = mk-id T₁ ⇒ mk-id T₂
  mk-id-body (T₁ ⊗ T₂)
    = mk-id T₁ ⊗ mk-id T₂
  -- mk-id-body (T₁ ⊕ T₂)
  --   = mk-id T₁ ⊕ mk-id T₂

mk-cast : ∀ {T1 T2} → SrcCast T1 T2 → Cast T1 T2
mk-cast (T1 ⟹[ l ] T2) = seq (mk-id T1) (inj₂ l) (mk-id T2)

mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
mk-seq c1 c2 = seq c1 (inj₁ refl) c2

open import S.Values Label Injectable Cast
  
module AlternativeApplyCast where

  CastResult : Type → Set
  CastResult T = Error Label (Value T)
 
  apply-body : ∀ {P1 P2 P3}
    → P1 ≡ P2 ⊎ Label
    → Body P2 P3
    → Value (` P1)
    → CastResult (` P3)
  apply-body {P1} {P2} ℓ b v with (` P1) ⌣? (` P2)
  apply-body {.B} {.B} ℓ B b | yes ⌣B = return b
  apply-body {.(_ ⇒ _)} {.(_ ⇒ _)} ℓ (c₃ ⇒ c₄) (lam⟨ c₁ ⇒ c₂ ⟩ e env) | yes ⌣⇒
    = return (lam⟨ seq c₃ (ℓ-dom ℓ) c₁ ⇒ seq c₂ (ℓ-cod ℓ) c₄ ⟩ e env)
  apply-body {.(_ ⊗ _)} {.(_ ⊗ _)} ℓ (c₃ ⊗ c₄) (cons⟨ c₁ ⊗ c₂ ⟩ v₁ v₂) | yes ⌣⊗ = return (cons⟨ seq c₁ (ℓ-car ℓ) c₃ ⊗ seq c₂ (ℓ-cdr ℓ) c₄ ⟩ v₁ v₂)
  apply-body {P1} {.P1} (inj₁ refl) b v | no ¬p = ⊥-elim (¬p (⌣refl (` P1)))
  apply-body {P1} {P2} (inj₂ l) b v | no ¬p = raise l
  
  apply-tail : ∀ {P T} → Tail P T → Value (` P) → CastResult T
  apply-tail (fail l) v = raise l
  apply-tail (last ‼) v = return (dyn _ _ v)
  apply-tail (last ε) v = return v

  apply-rest : ∀ {P1 P2 T}
    → GapP P1 P2
    → Rest P2 T
    → Value (` P1)
    ---
    → CastResult T
  apply-rest ℓ (rest b t) v = apply-body ℓ b v >>= apply-tail t

  apply-cast : ∀ {T1 T2}
    → Cast T1 T2
    → Value T1
    ---
    → CastResult T2
  apply-cast id* v = return v
  apply-cast (↷ (⁇ l) r) (dyn _ _ v) = apply-rest (inj₂ l) r v
  apply-cast (↷ ε r) v = apply-rest (inj₁ refl) r v

open AlternativeApplyCast public

-- mutual
--   lem-id-body : ∀ P
--     → (v : Value (` P))  
--     -----------------------------
--     → apply-body (inj₁ refl) (mk-id-body P) v ≡ return v
--   lem-id-body B sole = refl
--   lem-id-body (T₁ ⇒ T₂) (lam⟨ c₁ ⇒ c₂ ⟩ e env) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
--   lem-id-body (T₁ ⊗ T₂) (cons v c₁ v₁ c₂) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
--   -- lem-id-body (T₁ ⊕ T₂) (inl v c) rewrite seq-id-r c = refl
--   -- lem-id-body (T₁ ⊕ T₂) (inr v c) rewrite seq-id-r c = refl

--   lem-id : ∀ T
--     → (v : Value T)  
--     -----------------------------
--     → apply-cast (mk-id T) v ≡ return v
--   lem-id * v = refl
--   lem-id (` B) sole = refl
--   lem-id (` (T₁ ⇒ T₂)) (lam⟨ c₁ ⇒ c₂ ⟩ e env) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
--   lem-id (` (T₁ ⊗ T₂)) (cons v c₁ v₁ c₂) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
--   -- lem-id (` (T₁ ⊕ T₂)) (inl v c) rewrite seq-id-r c = refl
--   -- lem-id (` (T₁ ⊕ T₂)) (inr v c) rewrite seq-id-r c = refl

lem-seq-raise : ∀ {P1 P2 P3 T1 T2}
  → (v : Value (` P1))
  → (ℓ : GapP P1 P2)
  → (b : Body P2 P3)
  → (l : Label)
  → (f : Value T1 → CastResult T2)
  ---
  → (apply-body ℓ b v >>= (λ v → raise l)) ≡
    ((apply-body ℓ b v >>= (λ v → raise l)) >>= f)
lem-seq-raise v ℓ b l f with apply-body ℓ b v
lem-seq-raise v ℓ b l f | return v₁ = refl
lem-seq-raise v ℓ b l f | raise l₁ = refl

lem-apply-body-refl : ∀ {P1 P2}
  → (v : Value (` P1))
  → (b : Body P1 P2)
  → ∃[ u ](apply-body (inj₁ refl) b v ≡ return u)
lem-apply-body-refl {P1} v b with (` P1) ⌣? (` P1)
lem-apply-body-refl {.B} sole B | yes ⌣B = sole , refl
lem-apply-body-refl {.(_ ⇒ _)} (lam⟨ c₁ ⇒ c₂ ⟩ e env) (c₃ ⇒ c₄) | yes ⌣⇒
  = lam⟨ seq c₃ (inj₁ refl) c₁ ⇒ seq c₂ (inj₁ refl) c₄ ⟩ e env , refl
lem-apply-body-refl {.(_ ⊗ _)} (cons v c₁ v₁ c₂) (c₃ ⊗ c₄) | yes ⌣⊗
  = cons v (seq c₁ (inj₁ refl) c₃) v₁ (seq c₂ (inj₁ refl) c₄) , refl
-- lem-apply-body-refl {.(_ ⊕ _)} (inl v c) (c₁ ⊕ c₂) | yes ⌣⊕ = inl v (seq c (inj₁ refl) c₁) , refl
-- lem-apply-body-refl {.(_ ⊕ _)} (inr v c) (c₁ ⊕ c₂) | yes ⌣⊕ = inr v (seq c (inj₁ refl) c₂) , refl
lem-apply-body-refl {P1} v b | no ¬p = ⊥-elim (¬p (⌣refl _))

lem-apply-body-⌣ : ∀ {P0 P1 P2}
  → (v : Value (` P0))
  → (ℓ : GapP P0 P1)
  → (p : (` P0) ⌣ (` P1))
  → (b : Body P1 P2)
  → ∃[ u ](apply-body ℓ b v ≡ return u)
lem-apply-body-⌣ {.B} {.B} sole ℓ ⌣B B = sole , refl
lem-apply-body-⌣ {.(_ ⇒ _)} {.(_ ⇒ _)} (lam⟨ c₁ ⇒ c₂ ⟩ e env) ℓ ⌣⇒ (c₃ ⇒ c₄) = ? -- lam⟨ seq c₃ _ c₁ ⇒ seq c₂ _ c₄⟩ e env , refl
lem-apply-body-⌣ {.(_ ⊗ _)} {.(_ ⊗ _)} (cons v c₁ v₁ c₂) ℓ ⌣⊗ (c₃ ⊗ c₄) = cons v (seq c₁ _ c₃) v₁ (seq c₂ _ c₄) , refl
-- lem-apply-body-⌣ {.(_ ⊕ _)} {.(_ ⊕ _)} (inl v c) ℓ ⌣⊕ (c₁ ⊕ c₂) = inl v (seq c _ c₁) , refl
-- lem-apply-body-⌣ {.(_ ⊕ _)} {.(_ ⊕ _)} (inr v c) ℓ ⌣⊕ (c₁ ⊕ c₂) = inr v (seq c _ c₂) , refl

lem-seq' : ∀ {P1 P2 P3 P4 P5 T1 T2}
  → (v : Value (` P1))
  → (ℓ : GapP P1 P2)
  → (b1 : Body P2 P3)
  → (t1 : Last P3 T1)
  → (h2 : Head P4 T1)
  → (b2 : Body P4 P5)
  → (t2 : Tail P5 T2)
  → apply-rest ℓ
      (seq-rest b1 t1 (inj₁ refl) h2 (rest b2 t2))
      v
    ≡
    ((apply-body ℓ b1 v >>= apply-tail (last t1)) >>=
      apply-cast (↷ h2 (rest b2 t2)))
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 with (` P3) ⌣? (` P4)
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | yes p with t1 | h2
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | yes p | ‼ | ⁇ l with (` P1) ⌣? (` P2)
lem-seq' {.B} {.B} {.B} {.B} sole ℓ B t1 h2 B t2 | yes ⌣B | ‼ | ⁇ l | yes ⌣B = refl
-- lem-seq' {.(_ ⇒ _)} {.(_ ⇒ _)} {.(_ ⇒ _)} {.(_ ⇒ _)} (fun env c₁ b c₂) ℓ (c₃ ⇒ c₄) t1 h2 (c₅ ⇒ c₆) t2 | yes ⌣⇒ | ‼ | ⁇ l | yes ⌣⇒
--   rewrite seq-assoc c₅ (inj₂ l) c₃ (ℓ-dom ℓ) c₁ | seq-assoc c₂ (ℓ-cod ℓ) c₄ (inj₂ l) c₆
--   = refl
lem-seq' {.(_ ⊗ _)} {.(_ ⊗ _)} {.(_ ⊗ _)} {.(_ ⊗ _)} (cons v c₁ v₁ c₂) ℓ (c₃ ⊗ c₄) t1 h2 (c₅ ⊗ c₆) t2 | yes ⌣⊗ | ‼ | ⁇ l | yes ⌣⊗
  rewrite seq-assoc c₁ (ℓ-car ℓ) c₃ (inj₂ l) c₅ | seq-assoc c₂ (ℓ-cdr ℓ) c₄ (inj₂ l) c₆
  = refl
-- lem-seq' {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} (inl v c) ℓ (c₁ ⊕ c₂) t1 h2 (c₃ ⊕ c₄) t2 | yes ⌣⊕ | ‼ | ⁇ l | yes ⌣⊕
--   rewrite seq-assoc c (ℓ-inl ℓ) c₁ (inj₂ l) c₃
--   = refl
-- lem-seq' {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} (inr v c) ℓ (c₁ ⊕ c₂) t1 h2 (c₃ ⊕ c₄) t2 | yes ⌣⊕ | ‼ | ⁇ l | yes ⌣⊕
--   rewrite seq-assoc c (ℓ-inr ℓ) c₂ (inj₂ l) c₄
--   = refl
lem-seq' {P1} {.P1} {P3} {P4} v (inj₁ refl) b1 t1 h2 b2 t2 | yes p | ‼ | ⁇ l | no ¬p = (⊥-elim (¬p (⌣refl (` P1))))
lem-seq' {P1} {P2} {P3} {P4} v (inj₂ y) b1 t1 h2 b2 t2 | yes p | ‼ | ⁇ l | no ¬p = refl
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | yes p | ε | ε with (` P1) ⌣? (` P2)
-- lem-seq' {.(_ ⇒ _)} {.(_ ⇒ _)} {.(_ ⇒ _)} {.(_ ⇒ _)} (fun env c₁ b c₂) ℓ (c₃ ⇒ c₄) t1 h2 (c₅ ⇒ c₆) t2 | yes ⌣⇒ | ε | ε | yes ⌣⇒
--   rewrite seq-assoc c₅ (inj₁ refl) c₃ (ℓ-dom ℓ) c₁ | seq-assoc c₂ (ℓ-cod ℓ) c₄ (inj₁ refl) c₆
--   = refl
lem-seq' {.B} {.B} {.B} {.B} sole ℓ B t1 h2 B t2 | yes ⌣B | ε | ε | yes ⌣B = refl
lem-seq' {.(_ ⊗ _)} {.(_ ⊗ _)} {.(_ ⊗ _)} {.(_ ⊗ _)} (cons v c₁ v₁ c₂) ℓ (c₃ ⊗ c₄) t1 h2 (c₅ ⊗ c₆) t2 | yes ⌣⊗ | ε | ε | yes ⌣⊗
  rewrite seq-assoc c₁ (ℓ-car ℓ) c₃ (inj₁ refl) c₅ | seq-assoc c₂ (ℓ-cdr ℓ) c₄ (inj₁ refl) c₆
  = refl
-- lem-seq' {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} (inl v c) ℓ (c₁ ⊕ c₂) t1 h2 (c₃ ⊕ c₄) t2 | yes ⌣⊕ | ε | ε | yes ⌣⊕
--   rewrite seq-assoc c (ℓ-inl ℓ) c₁ (inj₁ refl) c₃
--   = refl
-- lem-seq' {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} (inr v c) ℓ (c₁ ⊕ c₂) t1 h2 (c₃ ⊕ c₄) t2 | yes ⌣⊕ | ε | ε | yes ⌣⊕
--   rewrite seq-assoc c (ℓ-inr ℓ) c₂ (inj₁ refl) c₄
--   = refl
lem-seq' {P1} {.P1} {P3} {P3} v (inj₁ refl) b1 t1 h2 b2 t2 | yes p | ε | ε | no ¬p = (⊥-elim (¬p (⌣refl (` P1))))
lem-seq' {P1} {P2} {P3} {P3} v (inj₂ y) b1 t1 h2 b2 t2 | yes p | ε | ε | no ¬p = refl
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p with t1 | h2
... | ε | ε = (⊥-elim (¬p (⌣refl (` P3))))
... | ‼ | ⁇ l with apply-body ℓ b1 v
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p | ‼ | ⁇ l | return v₁ with (` P3) ⌣? (` P4)
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p | ‼ | ⁇ l | return v₁ | yes p = ⊥-elim (¬p p)
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p | ‼ | ⁇ l | return v₁ | no ¬p₁ = refl
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p | ‼ | ⁇ l | raise l₁ = refl

lem-seq : ∀ {T1 T2 T3}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → (v : Value T1)
  --------------------
  → apply-cast (mk-seq c1 c2) v ≡ apply-cast c1 v >>= λ u → apply-cast c2 u
lem-seq id* id* v = refl
lem-seq id* (↷ (⁇ l) r) v = refl
lem-seq (↷ h (rest b (last ‼))) id* v = sym (>>=-return _)
lem-seq (↷ (⁇ l₁) (rest b (raise l))) c2 (dyn P v) = lem-seq-raise v (inj₂ l₁) b l _
lem-seq (↷ ε (rest b (raise l))) c2 v = lem-seq-raise v _ b l _
lem-seq (↷ (⁇ l) (rest {Q = P1} b (last t))) (↷ h₁ (rest {_} b₁ t₁)) (dyn P v) = lem-seq' v (inj₂ l) b t h₁ b₁ t₁
lem-seq (↷ ε (rest {Q = P1} b (last t))) (↷ h₁ (rest {_} b₁ t₁)) v = lem-seq' v (inj₁ refl) b t h₁ b₁ t₁

-- lem-cast-¬⌣ : ∀ {T1 T2}
--   → (l : Label)
--   → ¬ (T1 ⌣ T2)
--   → (v : Value T1)
--   → apply-cast (mk-cast l T1 T2) v ≡ raise l
-- lem-cast-¬⌣ {*} {*} l ¬p v = ⊥-elim (¬p *⌣*)
-- lem-cast-¬⌣ {*} {` P} l ¬p v = ⊥-elim (¬p (*⌣P P))
-- lem-cast-¬⌣ {` P} {*} l ¬p v = ⊥-elim (¬p (P⌣* P))
-- lem-cast-¬⌣ {` P} {` P₁} l ¬p v with (` P) ⌣? (` P₁)
-- lem-cast-¬⌣ {` P} {` P₁} l ¬p v | yes p = ⊥-elim (¬p p)
-- lem-cast-¬⌣ {` P} {` P₁} l ¬p v | no ¬p₁
--   rewrite sym (>>=-return (apply-body (inj₁ refl) (mk-id-body P) v))
--         | lem-id (` P) v
--   = refl

-- lem-cast-id* : ∀ l
--   → (v : Value *)
--   → apply-cast (mk-cast l * *) v ≡ return v
-- lem-cast-id* l v = refl

-- lem-cast-dyn : ∀ {P}
--   → (l : Label)
--   → (v : Value (` P))  
--   → apply-cast (mk-cast l (` P) *) v ≡ return (dyn P v)
-- lem-cast-dyn {P} l v
--   rewrite sym (>>=-return (apply-body (inj₁ refl) (mk-id-body P) v))
--         | lem-id (` P) v
--   = refl

-- lem-seq2-id : ∀ {T1 T2 T3 T4}
--   → (c1 : Cast T1 T2)
--   → (ℓ : GapT T2 T3)
--   → (c2 : Cast T3 T4)
--   → seq c1 (inj₁ refl) (seq (mk-id T2) ℓ c2)
--     ≡ seq c1 ℓ c2
-- lem-seq2-id c1 ℓ c2
--   rewrite sym (seq-assoc c1 (inj₁ refl) (mk-id _) ℓ c2) | seq-id-r c1
--   = refl

-- lem-cast-proj : ∀ l P P₁ v
--   → apply-cast (mk-cast l * (` P)) (dyn P₁ v) ≡ apply-cast (mk-cast l (` P₁) (` P)) v
-- lem-cast-proj l P P₁ v with (` P₁) ⌣? (` P)
-- lem-cast-proj l .B .B sole | yes ⌣B = refl
-- -- lem-cast-proj l (T1 ⇒ T2) (T3 ⇒ T4) (fun env c₁ b c₂) | yes ⌣⇒
-- --   rewrite seq-id-l (seq (mk-id T1) (inj₂ l) c₁)
-- --         | seq-assoc (mk-id T1) (inj₂ l) (mk-id T3) (inj₁ refl) c₁
-- --         | seq-id-l c₁
-- --         | seq-id-r (seq c₂ (inj₂ l) (mk-id T2))
-- --         | sym (seq-assoc c₂ (inj₁ refl) (mk-id T4) (inj₂ l) (mk-id T2))
-- --         | seq-id-r c₂
-- --   = refl
-- lem-cast-proj l (T1 ⊗ T2) (T3 ⊗ T4) (cons v c₁ v₁ c₂) | yes ⌣⊗
--   rewrite lem-seq2-id c₁ (inj₂ l) (mk-id T1) | lem-seq2-id c₂ (inj₂ l) (mk-id T2)
--   = refl
-- -- lem-cast-proj l (T1 ⊕ T2) (T3 ⊕ T4) (inl v c₁) | yes ⌣⊕
-- --   rewrite lem-seq2-id c₁ (inj₂ l) (mk-id T1)
-- --   = refl
-- -- lem-cast-proj l (T1 ⊕ T2) (T3 ⊕ T4) (inr v c₂) | yes ⌣⊕
-- --   rewrite lem-seq2-id c₂ (inj₂ l) (mk-id T2)
-- --   = refl
-- lem-cast-proj l P P₁ v | no ¬p rewrite lem-id-body P₁ v = refl

-- lem-cast-B : ∀ l v
--   → apply-cast (mk-cast l (` B) (` B)) v ≡ return v
-- lem-cast-B l = refl

-- lem-cast-⇒ : ∀ T11 T12 T21 T22
--   → ∀ {S T}
--   → (l : Label)
--   → {Γ : Context}
--   → (E : Env Γ)
--   → (c₁ : Cast T11 S)
--   → (b : (Γ , S) ⊢ T)
--   → (c₂ : Cast T T12)
--   → apply-cast (mk-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22))) (lam⟨ c₁ ⇒ c₂ ⟩ b E) ≡
--     return (lam⟨ mk-seq (mk-cast l T21 T11) c₁ ⇒ (mk-seq c₂ (mk-cast l T12 T22)) ⟩ b E)
-- lem-cast-⇒ T11 T12 T21 T22 l E c₁ b c₂ = refl

-- lem-cast-⊗ : ∀ T01 T02 T11 T12 T21 T22
--   → (l : Label)
--   → (v₁ : Value T01)
--   → (v₂ : Value T02)
--   → (c₁ : Cast T01 T11)
--   → (c₂ : Cast T02 T12)
--   → apply-cast (mk-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22))) (cons v₁ c₁ v₂ c₂) ≡
--     return (cons v₁ (mk-seq c₁ (mk-cast l T11 T21)) v₂ (mk-seq c₂ (mk-cast l T12 T22)))
-- lem-cast-⊗ T01 T02 T11 T12 T21 T22 l v₁ v₂ c₁ c₂ = refl
    
-- -- lem-cast-⊕-l : ∀ T T11 T12 T21 T22
-- --   → (l : Label)
-- --   → (v : Value T)
-- --   → (c : Cast T T11)
-- --   → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inl v c) ≡
-- --     return (inl v (mk-seq c (mk-cast l T11 T21)))
-- -- lem-cast-⊕-l T T11 T12 T21 T22 l v c = refl

-- -- lem-cast-⊕-r : ∀ T T11 T12 T21 T22
-- --   → (l : Label)
-- --   → (v : Value T)
-- --   → (c : Cast T T12)
-- --   → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inr v c) ≡
-- --     return (inr v (mk-seq c (mk-cast l T12 T22)))
-- -- lem-cast-⊕-r T T11 T12 T21 T22 l v c = refl

-- cast-adt : CastADT
-- cast-adt
--   = record
--     { Cast = Cast
--     ; mk-cast = mk-cast
--     ; mk-seq = mk-seq
--     ; mk-id = mk-id
--     ; apply-cast = apply-cast
--     }
-- cast-adt-LazyD : LazyD cast-adt
-- cast-adt-LazyD
--   = record
--     { lem-id = lem-id
--     ; lem-seq = lem-seq
--     ; lem-cast-¬⌣ = lem-cast-¬⌣
--     ; lem-cast-id* = lem-cast-id*
--     ; lem-cast-dyn = lem-cast-dyn
--     ; lem-cast-proj = lem-cast-proj
--     ; lem-cast-B = lem-cast-B
--     ; lem-cast-⇒ = lem-cast-⇒
--     ; lem-cast-⊗ = lem-cast-⊗
--     -- ; lem-cast-⊕-l = lem-cast-⊕-l
--     -- ; lem-cast-⊕-r = lem-cast-⊕-r
--     }
-- -- cast-adt-monoid : Monoid cast-adt
-- -- cast-adt-monoid
-- --   = record
-- --     { lem-id-l = seq-id-l
-- --     ; lem-id-r = seq-id-r
-- --     ; lem-assoc = λ c1 c2 c3 → seq-assoc c1 _ c2 _ c3
-- --     }

-- -- lem-cast-id-is-id : ∀ l T →
-- --   mk-cast l T T ≡ mk-id T
-- -- lem-cast-id-is-id l * = refl
-- -- lem-cast-id-is-id l (` B) = refl
-- -- lem-cast-id-is-id l (` (T₁ ⇒ T₂))
-- --   rewrite lem-cast-id-is-id l T₁ | lem-cast-id-is-id l T₂ = refl
-- -- lem-cast-id-is-id l (` (T₁ ⊗ T₂))
-- --   rewrite lem-cast-id-is-id l T₁ | lem-cast-id-is-id l T₂ = refl
-- -- lem-cast-id-is-id l (` (T₁ ⊕ T₂))
-- --   rewrite lem-cast-id-is-id l T₁ | lem-cast-id-is-id l T₂ = refl

-- -- cast-adt-cast-id-is-id : CastIdIsId cast-adt
-- -- cast-adt-cast-id-is-id
-- --   = record { lem-cast-id-is-id = lem-cast-id-is-id }
