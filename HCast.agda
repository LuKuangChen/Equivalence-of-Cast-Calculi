module HCast (Label : Set) where
open import Types
open import Variables
open import Terms Label

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

data Head (P : PreType) : Type → Set where
  ⁇ : (l : Label) → Head P ⋆
  ε : Head P (` P)

data Last (P : PreType) : Type → Set where
  ‼ : Last P ⋆
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
    id⋆ : Cast ⋆ ⋆
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
    U : Body U U
    _⇒_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S2 S1) →
      (c₂ : Cast T1 T2) →
      Body (S1 ⇒ T1) (S2 ⇒ T2)
    _⊗_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S1 S2) →
      (c₂ : Cast T1 T2) →
      Body (S1 ⊗ T1) (S2 ⊗ T2)
    _⊕_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S1 S2) →
      (c₂ : Cast T1 T2) →
      Body (S1 ⊕ T1) (S2 ⊕ T2)

mutual
  seq : ∀ {T1 T2 T3 T4}
    → Cast T1 T2
    → T2 ≡ T3 ⊎ Label
    → Cast T3 T4
  ----------------
    → Cast T1 T4
  seq id⋆ (inj₁ refl) id⋆ = id⋆
  seq id⋆ (inj₁ refl) (↷ (⁇ l) r) = ↷ (⁇ l) r
  seq id⋆ (inj₂ l') id⋆ = id⋆
  seq id⋆ (inj₂ l') (↷ (⁇ l) r) = ↷ (⁇ l) r
  seq id⋆ (inj₂ l') (↷ ε r) = ↷ (⁇ l') r
  seq (↷ h r) ℓ c2 = ↷ h (seq' r ℓ c2)

  seq' : ∀ {P1 T1 T2 T3}
    → Rest P1 T1
    → T1 ≡ T2 ⊎ Label
    → Cast T2 T3
  ----------------
    → Rest P1 T3
  seq' (rest b (fail l)) ℓ c = rest b (fail l)
  seq' (rest b (last t)) ℓ id⋆ = rest b (last ‼)
  seq' (rest b (last t)) ℓ (↷ (⁇ l) r) = ext-rest (inj₂ l) b r
  seq' (rest b (last t)) ℓ (↷ ε r) with ℓ
  seq' (rest b (last ε)) ℓ (↷ ε r) | inj₁ refl = ext-rest (inj₁ refl) b r
  seq' (rest b (last t)) ℓ (↷ ε r) | inj₂ l = ext-rest (inj₂ l) b r

  ext-rest : ∀ {P1 P2 P3 T1}
    → P2 ≡ P3 ⊎ Label
    → Body P1 P2
    → Rest P3 T1
  ----------------
    → Rest P1 T1
  ext-rest (inj₁ refl) U (rest U t) = rest U t
  ext-rest (inj₁ refl) (c₁ ⇒ c₂) (rest (c₃ ⇒ c₄) t) = rest ((seq c₃ (inj₁ refl) c₁) ⇒ (seq c₂ (inj₁ refl) c₄)) t
  ext-rest (inj₁ refl) (c₁ ⊗ c₂) (rest (c₃ ⊗ c₄) t) = rest ((seq c₁ (inj₁ refl) c₃) ⊗ (seq c₂ (inj₁ refl) c₄)) t
  ext-rest (inj₁ refl) (c₁ ⊕ c₂) (rest (c₃ ⊕ c₄) t) = rest ((seq c₁ (inj₁ refl) c₃) ⊕ (seq c₂ (inj₁ refl) c₄)) t
  ext-rest {P2 = P2} {P3 = P3} (inj₂ l) b r with (` P2) ⌣? (` P3)
  ext-rest {P2 = .U} {.U} (inj₂ l) U (rest U t) | yes ⌣U = rest U t
  ext-rest {P2 = .(_ ⇒ _)} {.(_ ⇒ _)} (inj₂ l) (c₁ ⇒ c₂) (rest (c₃ ⇒ c₄) t) | yes ⌣⇒ = rest ((seq c₃ (inj₂ l) c₁) ⇒ (seq c₂ (inj₂ l) c₄)) t
  ext-rest {P2 = .(_ ⊗ _)} {.(_ ⊗ _)} (inj₂ l) (c₁ ⊗ c₂) (rest (c₃ ⊗ c₄) t) | yes ⌣⊗ = rest ((seq c₁ (inj₂ l) c₃) ⊗ (seq c₂ (inj₂ l) c₄)) t
  ext-rest {P2 = .(_ ⊕ _)} {.(_ ⊕ _)} (inj₂ l) (c₁ ⊕ c₂) (rest (c₃ ⊕ c₄) t) | yes ⌣⊕ = rest ((seq c₁ (inj₂ l) c₃) ⊕ (seq c₂ (inj₂ l) c₄)) t
  ext-rest {P2 = P2} {P3} (inj₂ l) b (rest b₁ t) | no ¬p = rest b (fail l)

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
mk-cast l T1 T2 = seq (mk-id T1) (inj₂ l) (mk-id T2)

mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
mk-seq c1 c2 = seq c1 (inj₁ refl) c2

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

seq-id⋆-l : ∀ {T}
  → (ℓ : ⋆ ≡ ⋆ ⊎ Label)
  → (c : Cast ⋆ T) → seq id⋆ ℓ c ≡ c
seq-id⋆-l (inj₁ refl) id⋆ = refl
seq-id⋆-l (inj₁ refl) (↷ (⁇ l) r) = refl
seq-id⋆-l (inj₂ y) id⋆ = refl
seq-id⋆-l (inj₂ y) (↷ (⁇ l) r) = refl

mutual
  seq-assoc : ∀ {T1 T2 T3 T4 T5 T6}
    → (c1 : Cast T1 T2)
    → (ℓ1 : T2 ≡ T3 ⊎ Label)
    → (c2 : Cast T3 T4)
    → (ℓ2 : T4 ≡ T5 ⊎ Label)
    → (c3 : Cast T5 T6)
    → seq (seq c1 ℓ1 c2) ℓ2 c3 ≡ seq c1 ℓ1 (seq c2 ℓ2 c3)
  seq-assoc id⋆ (inj₁ refl) c2 ℓ2 c3
    rewrite seq-id⋆-l (inj₁ refl) c2 | seq-id⋆-l (inj₁ refl) (seq c2 ℓ2 c3)
    = refl
  seq-assoc id⋆ (inj₂ l) id⋆ ℓ2 c3
    rewrite seq-id⋆-l (inj₂ l) (seq id⋆ ℓ2 c3)
    = refl
  seq-assoc id⋆ (inj₂ l) (↷ (⁇ l₁) r) ℓ2 c3
    rewrite seq-id⋆-l (inj₂ l) (seq (↷ (⁇ l₁) r) ℓ2 c3)
    = refl
  seq-assoc id⋆ (inj₂ l) (↷ ε (rest b (fail l₁))) ℓ2 c3 = refl
  seq-assoc id⋆ (inj₂ l) (↷ ε (rest b (last t))) ℓ2 c3 = refl
  seq-assoc (↷ h (rest b (fail l))) ℓ1 c2 ℓ2 c3 = refl
  seq-assoc (↷ h (rest b (last t))) ℓ1 id⋆ (inj₁ refl) id⋆ = refl
  seq-assoc (↷ h (rest b (last t))) ℓ1 id⋆ (inj₁ refl) (↷ (⁇ l) (rest b₁ t₁)) = refl
  seq-assoc (↷ h (rest b (last t))) ℓ1 id⋆ (inj₂ l) id⋆ = refl
  seq-assoc (↷ h (rest b (last t))) ℓ1 id⋆ (inj₂ l) (↷ (⁇ l₁) (rest b₁ t₁)) = refl
  seq-assoc (↷ h (rest b (last t))) ℓ1 id⋆ (inj₂ l) (↷ ε (rest b₁ t₁)) = refl
  seq-assoc (↷ h (rest b (last t))) ℓ1 (↷ h₁ (rest b₁ (fail l))) ℓ2 c3 = {!!}
  seq-assoc (↷ h (rest b (last t))) ℓ1 (↷ (⁇ l) (rest b₁ (last t₁))) ℓ2 id⋆ = {!!}
  seq-assoc (↷ h (rest b (last t))) ℓ1 (↷ ε (rest b₁ (last t₁))) ℓ2 id⋆ with ℓ1
  seq-assoc (↷ h (rest U (last ε))) ℓ1 (↷ ε (rest U (last t₁))) ℓ2 id⋆ | inj₁ refl = refl
  seq-assoc (↷ h (rest (c₁ ⇒ c₂) (last ε))) ℓ1 (↷ ε (rest (c₃ ⇒ c₄) (last t₁))) ℓ2 id⋆ | inj₁ refl = refl
  seq-assoc (↷ h (rest (c₁ ⊗ c₂) (last ε))) ℓ1 (↷ ε (rest (c₃ ⊗ c₄) (last t₁))) ℓ2 id⋆ | inj₁ refl = refl
  seq-assoc (↷ h (rest (c₁ ⊕ c₂) (last ε))) ℓ1 (↷ ε (rest (c₃ ⊕ c₄) (last t₁))) ℓ2 id⋆ | inj₁ refl = refl
  seq-assoc (↷ h (rest {Q = Q} b (last t))) ℓ1 (↷ ε (rest {P = P} b₁ (last t₁))) ℓ2 id⋆ | inj₂ l with (` Q) ⌣? (` P)
  seq-assoc (↷ h (rest {Q = .U} U (last t))) ℓ1 (↷ ε (rest U (last t₁))) ℓ2 id⋆ | inj₂ l | yes ⌣U = refl
  seq-assoc (↷ h (rest {Q = .(_ ⇒ _)} (c₁ ⇒ c₂) (last t))) ℓ1 (↷ ε (rest (c₃ ⇒ c₄) (last t₁))) ℓ2 id⋆ | inj₂ l | yes ⌣⇒ = refl
  seq-assoc (↷ h (rest {Q = .(_ ⊗ _)} (c₁ ⊗ c₂) (last t))) ℓ1 (↷ ε (rest (c₃ ⊗ c₄) (last t₁))) ℓ2 id⋆ | inj₂ l | yes ⌣⊗ = refl
  seq-assoc (↷ h (rest {Q = .(_ ⊕ _)} (c₁ ⊕ c₂) (last t))) ℓ1 (↷ ε (rest (c₃ ⊕ c₄) (last t₁))) ℓ2 id⋆ | inj₂ l | yes ⌣⊕ = refl
  seq-assoc (↷ h (rest {Q = Q} b (last t))) ℓ1 (↷ ε (rest b₁ (last t₁))) ℓ2 id⋆ | inj₂ l | no ¬p = refl
  seq-assoc (↷ h (rest b (last t))) ℓ1 (↷ h₁ (rest b₁ (last t₁))) ℓ2 (↷ h₂ (rest b₂ t₂)) rewrite seq'-assoc h₁ ℓ1 h₂ ℓ2 b t b₁ t₁ b₂ t₂ = refl

  seq'-assoc : ∀ {P1 P2 P3 P4 P5 P6 T1 T2 T3 T4 T5}
    → (h₁ : Head P3 T2)
    → (ℓ1 : T1 ≡ T2 ⊎ Label)
    → (h₂ : Head P5 T4)
    → (ℓ2 : T3 ≡ T4 ⊎ Label)
    → (b : Body P1 P2)
    → (t : Last P2 T1)
    → (b₁ : Body P3 P4)
    → (t₁ : Last P4 T3)
    → (b₂ : Body P5 P6)
    → (t₂ : Tail P6 T5)
    → (seq' (seq' (rest b (last t)) ℓ1 (↷ h₁ (rest b₁ (last t₁)))) ℓ2 (↷ h₂ (rest b₂ t₂))) ≡
      (seq' (rest b (last t)) ℓ1 (↷ h₁ (seq' (rest b₁ (last t₁)) ℓ2 (↷ h₂ (rest b₂ t₂)))))
  seq'-assoc (⁇ l) ℓ1 h2 ℓ2 b t b₁ t₁ b₂ t₂ = seq'-ext (inj₂ l) b b₁ h2 ℓ2 t₁ b₂ t₂
  seq'-assoc ε (inj₁ refl) h2 ℓ2 b ε b₁ t₁ b₂ t₂ = seq'-ext (inj₁ refl) b b₁ h2 ℓ2 t₁ b₂ t₂
  seq'-assoc ε (inj₂ y) h2 ℓ2 b t b₁ t₁ b₂ t₂ = seq'-ext (inj₂ y) b b₁ h2 ℓ2 t₁ b₂ t₂

  seq'-ext : ∀ {P1 P2 P3 P4 P5 P6 T3 T4 T5}
    → (ℓ : P2 ≡ P3 ⊎ Label)
    → (b : Body P1 P2)
    → (b₁ : Body P3 P4)
    → (h2 : Head P5 T4)
    → (ℓ2 : T3 ≡ T4 ⊎ Label)
    → (t₁ : Last P4 T3)
    → (b₂ : Body P5 P6)
    → (t₂ : Tail P6 T5)
    → seq' (ext-rest ℓ b (rest b₁ (last t₁))) ℓ2 (↷ h2 (rest b₂ t₂)) ≡
      ext-rest ℓ b (seq' (rest b₁ (last t₁)) ℓ2 (↷ h2 (rest b₂ t₂)))
  seq'-ext (inj₁ refl) U U (⁇ l) ℓ2 t₁ b₂ t₂ = seq'-ext-U (inj₁ refl) b₂ t₂ l
  seq'-ext (inj₁ refl) U U ε (inj₁ refl) ε U t₂ = refl
  seq'-ext (inj₁ refl) U U ε (inj₂ y) t₁ b₂ t₂ = seq'-ext-U (inj₁ refl) b₂ t₂ y
  seq'-ext (inj₁ refl) (c₁ ⇒ c₂) (c₃ ⇒ c₄) (⁇ l) ℓ2 t₁ b₂ t₂ = {!!}
  seq'-ext (inj₁ refl) (c₁ ⇒ c₂) (c₃ ⇒ c₄) ε (inj₁ refl) ε (c₅ ⇒ c₆) t₂ = {!!}
  seq'-ext (inj₁ refl) (c₁ ⇒ c₂) (c₃ ⇒ c₄) ε (inj₂ y) t₁ b₂ t₂ = {!!}
  seq'-ext (inj₁ refl) (c₁ ⊗ c₂) b₁ h2 ℓ2 t₁ b₂ t₂ = {!!}
  seq'-ext (inj₁ refl) (c₁ ⊕ c₂) b₁ h2 ℓ2 t₁ b₂ t₂ = {!!}
  seq'-ext {P2 = P2} {P3 = P3} (inj₂ y) b b₁ h2 ℓ2 t₁ b₂ t₂ with (` P2) ⌣? (` P3)
  seq'-ext {P2 = .U} {.U} (inj₂ y) U U (⁇ l) ℓ2 t₁ b₂ t₂ | yes ⌣U = seq'-ext-U (inj₂ y) b₂ t₂ l
  seq'-ext {P2 = .U} {.U} (inj₂ y) U U ε (inj₁ refl) ε U t₂ | yes ⌣U = refl
  seq'-ext {P2 = .U} {.U} (inj₂ y) U U ε (inj₂ y₁) t₁ b₂ t₂ | yes ⌣U = seq'-ext-U (inj₂ y) b₂ t₂ y₁
  seq'-ext {P2 = .(_ ⇒ _)} {.(_ ⇒ _)} (inj₂ y) (c₁ ⇒ c₂) (c₃ ⇒ c₄) (⁇ l) ℓ2 t₁ b₂ t₂ | yes ⌣⇒ = {!!}
  seq'-ext {P2 = .(_ ⇒ _)} {.(_ ⇒ _)} (inj₂ y) (c₁ ⇒ c₂) (c₃ ⇒ c₄) ε (inj₁ refl) ε (c₅ ⇒ c₆) t₂ | yes ⌣⇒ = {!!}
  seq'-ext {P2 = .(_ ⇒ _)} {.(_ ⇒ _)} (inj₂ y) (c₁ ⇒ c₂) (c₃ ⇒ c₄) ε (inj₂ y₁) t₁ b₂ t₂ | yes ⌣⇒ = {!!}
  seq'-ext {P2 = .(_ ⊗ _)} {.(_ ⊗ _)} (inj₂ y) b b₁ h2 ℓ2 t₁ b₂ t₂ | yes ⌣⊗ = {!!}
  seq'-ext {P2 = .(_ ⊕ _)} {.(_ ⊕ _)} (inj₂ y) b b₁ h2 ℓ2 t₁ b₂ t₂ | yes ⌣⊕ = {!!}
  seq'-ext {P2 = P2} {P3} (inj₂ y) b b₁ h2 ℓ2 t₁ b₂ t₂ | no ¬p with seq' (rest b₁ (last t₁)) ℓ2 (↷ h2 (rest b₂ t₂))
  seq'-ext {P2 = P2} {P3} (inj₂ y) b b₁ h2 ℓ2 t₁ b₂ t₂ | no ¬p | rest b₃ t = refl

  seq'-ext-U : ∀ {P5 P6 T5}
    → (ℓ : U ≡ U ⊎ Label)
    → (b₂ : Body P5 P6)
    → (t₂ : Tail P6 T5)
    → (l : Label)
    → ext-rest (inj₂ l) U (rest b₂ t₂) ≡
      ext-rest ℓ U (ext-rest (inj₂ l) U (rest b₂ t₂))
  seq'-ext-U {P5} (inj₁ refl) b₂ t₂ l with (` U) ⌣? (` P5)
  seq'-ext-U {.U} (inj₁ refl) U t₂ l | yes ⌣U = refl
  seq'-ext-U {P5} (inj₁ refl) b₂ t₂ l | no ¬p = refl
  seq'-ext-U {P5} (inj₂ y) b₂ t₂ l with (` U) ⌣? (` P5)
  seq'-ext-U {.U} (inj₂ y) U t₂ l | yes ⌣U = refl
  seq'-ext-U {P5} (inj₂ y) b₂ t₂ l | no ¬p = refl

open import Vals Label Cast

apply-tail : ∀ {P T} → Tail P T → Val (` P) → CastResult T
apply-tail (fail l) v = fail l
apply-tail (last ‼) v = succ (inj _ v)
apply-tail (last ε) v = succ v

mutual
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
      
  apply-rest : ∀ {P T} → Rest P T → Val (` P) → CastResult T
  apply-rest (rest b t) v
    = apply-body b v >>= λ u →
      apply-tail t u
  
  apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val T1 → CastResult T2
  apply-cast id⋆ v
    = succ v
  apply-cast (↷ (⁇ l) r) (inj P v)
    = apply-rest (ext-rest (inj₂ l) (mk-id-body P) r) v
  apply-cast (↷ ε r) v
    = apply-rest r v

mutual
  lem-id-body : ∀ P
    → (v : Val (` P))  
    -----------------------------
    → apply-body (mk-id-body P) v ≡ succ v
  lem-id-body U sole = refl
  lem-id-body (T₁ ⇒ T₂) (fun env c₁ b c₂) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
  lem-id-body (T₁ ⊗ T₂) (cons v₁ c₁ v₂ c₂) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
  lem-id-body (T₁ ⊕ T₂) (inl v) rewrite lem-id T₁ v = refl
  lem-id-body (T₁ ⊕ T₂) (inr v) rewrite lem-id T₂ v = refl
  
  lem-id : ∀ T
    → (v : Val T)  
    -----------------------------
    → apply-cast (mk-id T) v ≡ succ v
  lem-id ⋆ v = refl
  lem-id (` P) v rewrite lem-id-body P v = refl

lem-seq : ∀ {T1 T2 T3}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → (v : Val T1)
  --------------------
  → apply-cast (mk-seq c1 c2) v ≡ apply-cast c1 v >>= λ u → apply-cast c2 u
lem-seq id⋆ id⋆ v = refl
lem-seq id⋆ (↷ (⁇ l) r) v = refl
lem-seq (↷ (⁇ l) (rest b t)) c2 (inj _ v) = {!!}
lem-seq (↷ ε (rest b (fail l))) c2 v with apply-body b v
lem-seq (↷ ε (rest b (fail l))) c2 v | succ v₁ = refl
lem-seq (↷ ε (rest b (fail l))) c2 v | fail l₁ = refl
lem-seq (↷ ε (rest b (last ‼))) id⋆ v = sym (>>=-succ _)
lem-seq (↷ ε (rest {Q = Q} b (last ‼))) (↷ (⁇ l) (rest {P = P} b₁ t)) v with (` Q) ⌣? (` P)
lem-seq (↷ ε (rest {Q = _} U (last ‼))) (↷ (⁇ l) (rest {_} U t)) sole | yes ⌣U = refl
lem-seq (↷ ε (rest {Q = _} (c₁ ⇒ c₂) (last ‼))) (↷ (⁇ l) (rest {_} (c₃ ⇒ c₄) t)) (fun env c₅ b c₆) | yes ⌣⇒
  rewrite seq-assoc c₃ (inj₂ l) (mk-id _) (inj₁ refl) (seq c₁ (inj₁ refl) c₅)
        | seq-assoc c₃ (inj₂ l) c₁ (inj₁ refl) c₅
        | seq-id-l (seq c₁ (inj₁ refl) c₅)
        | sym (seq-assoc (seq c₆ (inj₁ refl) c₂) (inj₁ refl) (mk-id _) (inj₂ l) c₄)
        | seq-id-r (seq c₆ (inj₁ refl) c₂)
        | seq-assoc c₆ (inj₁ refl) c₂ (inj₂ l) c₄
  = refl
lem-seq (↷ ε (rest {Q = _} (c₁ ⊗ c₂) (last ‼))) (↷ (⁇ l) (rest {_} (c₃ ⊗ c₄) t)) (cons v c₅ v₁ c₆) | yes ⌣⊗
  rewrite seq-assoc c₅ (inj₁ refl) c₁ (inj₁ refl) (seq (mk-id _) (inj₂ l) c₃)
        | sym (seq-assoc c₁ (inj₁ refl) (mk-id _) (inj₂ l) c₃)
        | seq-id-r c₁
        | sym (seq-assoc (seq c₆ (inj₁ refl) c₂) (inj₁ refl) (mk-id _) (inj₂ l) c₄)
        | seq-id-r (seq c₆ (inj₁ refl) c₂)
        | seq-assoc c₆ (inj₁ refl) c₂ (inj₂ l) c₄
  = refl
lem-seq (↷ ε (rest {Q = _} b (last ‼))) (↷ (⁇ l) (rest {_} b₁ t)) v | yes ⌣⊕ = {!!} -- I am very sure I can solve this
lem-seq (↷ ε (rest {Q = Q} b (last ‼))) (↷ (⁇ l) (rest {P = P} b₁ t)) v | no ¬p
  with apply-body b v
... | fail l1 = refl
... | succ v1
  with (` Q) ⌣? (` P)
... | yes p1 = ⊥-elim (¬p p1)
... | no ¬p1
  rewrite lem-id-body Q v1
  = refl
lem-seq (↷ ε (rest b (last ε))) (↷ ε (rest {P = P} b₁ t)) v with (` P) ⌣? (` P)
lem-seq (↷ ε (rest U (last ε))) (↷ ε (rest U t)) sole | yes ⌣U = refl
lem-seq (↷ ε (rest (c₁ ⇒ c₂) (last ε))) (↷ ε (rest (c₃ ⇒ c₄) t)) (fun env c₅ b c₆) | yes ⌣⇒
  rewrite seq-assoc c₃ (inj₁ refl) c₁ (inj₁ refl) c₅ | seq-assoc c₆ (inj₁ refl) c₂ (inj₁ refl) c₄
  = refl
lem-seq (↷ ε (rest (c₁ ⊗ c₂) (last ε))) (↷ ε (rest (c₃ ⊗ c₄) t)) (cons v₁ c₅ v₂ c₆) | yes ⌣⊗
  rewrite seq-assoc c₅ (inj₁ refl) c₁ (inj₁ refl) c₃ | seq-assoc c₆ (inj₁ refl) c₂ (inj₁ refl) c₄
  = refl
lem-seq (↷ ε (rest (c₁ ⊕ c₂) (last ε))) (↷ ε (rest (c₃ ⊕ c₄) t)) v | yes ⌣⊕ with v
lem-seq (↷ ε (rest (c₁ ⊕ c₂) (last ε))) (↷ ε (rest (c₃ ⊕ c₄) t)) v | yes ⌣⊕ | inl u
  rewrite lem-seq c₁ c₃ u
  with apply-cast c₁ u
... | fail l = refl
... | succ u1
  with apply-cast c₃ u1
... | fail l = refl
... | succ u2 = refl
lem-seq (↷ ε (rest (c₁ ⊕ c₂) (last ε))) (↷ ε (rest (c₃ ⊕ c₄) t)) v | yes ⌣⊕ | inr u
  rewrite lem-seq c₂ c₄ u
  with apply-cast c₂ u
... | fail l = refl
... | succ u1
  with apply-cast c₄ u1
... | fail l = refl
... | succ u2 = refl
lem-seq (↷ ε (rest b (last ε))) (↷ ε (rest {_} b₁ t)) v | no ¬p = ⊥-elim (¬p (⌣refl _))

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
