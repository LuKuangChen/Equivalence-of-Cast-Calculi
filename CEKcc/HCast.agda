module CEKcc.HCast (Label : Set) where
open import Types
open import Variables
open import Terms Label
open import CEKcc.CastRep Label

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

data Head : PreType → Type → Set where
  ⁇ : ∀ {P} → (l : Label) → Head P ⋆
  ε : ∀ {P} → Head P (` P)

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
  seq' (rest b (last t)) ℓ (↷ h r) = ext-rest (link h ℓ t) b r

  link : ∀ {Q P T1 T2}
    → (h : Head P T2)
    → (ℓ : T1 ≡ T2 ⊎ Label)
    → (t : Last Q T1)
    -----------------
    → Q ≡ P ⊎ Label
  link (⁇ l) ℓ t = inj₂ l
  link ε (inj₁ refl) ε = inj₁ refl
  link ε (inj₂ y) t = inj₂ y

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
  ext-rest {P2 = .(_ ⇒ _)} {.(_ ⇒ _)} (inj₂ l) (c₁ ⇒ c₂) (rest (c₃ ⇒ c₄) t) | yes ⌣⇒
    = rest ((seq c₃ (inj₂ l) c₁) ⇒ (seq c₂ (inj₂ l) c₄)) t
  ext-rest {P2 = .(_ ⊗ _)} {.(_ ⊗ _)} (inj₂ l) (c₁ ⊗ c₂) (rest (c₃ ⊗ c₄) t) | yes ⌣⊗
    = rest ((seq c₁ (inj₂ l) c₃) ⊗ (seq c₂ (inj₂ l) c₄)) t
  ext-rest {P2 = .(_ ⊕ _)} {.(_ ⊕ _)} (inj₂ l) (c₁ ⊕ c₂) (rest (c₃ ⊕ c₄) t) | yes ⌣⊕
    = rest ((seq c₁ (inj₂ l) c₃) ⊕ (seq c₂ (inj₂ l) c₄)) t
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
  seq-assoc (↷ h (rest b (last t))) ℓ1 (↷ h₁ (rest b₁ (fail l))) ℓ2 c3 with (link h₁ ℓ1 t)
  seq-assoc (↷ h (rest U (last t))) ℓ1 (↷ h₁ (rest U (fail l))) ℓ2 c3 | inj₁ refl = refl
  seq-assoc (↷ h (rest (c₁ ⇒ c₂) (last t))) ℓ1 (↷ h₁ (rest (c₃ ⇒ c₄) (fail l))) ℓ2 c3 | inj₁ refl = refl
  seq-assoc (↷ h (rest (c₁ ⊗ c₂) (last t))) ℓ1 (↷ h₁ (rest (c₃ ⊗ c₄) (fail l))) ℓ2 c3 | inj₁ refl = refl
  seq-assoc (↷ h (rest (c₁ ⊕ c₂) (last t))) ℓ1 (↷ h₁ (rest (c₃ ⊕ c₄) (fail l))) ℓ2 c3 | inj₁ refl = refl
  seq-assoc (↷ h (rest {Q = Q} b (last t))) ℓ1 (↷ h₁ (rest {P = P} b₁ (fail l))) ℓ2 c3 | inj₂ y with (` Q) ⌣? (` P)
  seq-assoc (↷ h (rest {Q = .U} U (last t))) ℓ1 (↷ h₁ (rest U (fail l))) ℓ2 c3 | inj₂ y | yes ⌣U = refl
  seq-assoc (↷ h (rest {Q = .(_ ⇒ _)} (c₁ ⇒ c₂) (last t))) ℓ1 (↷ h₁ (rest (c₃ ⇒ c₄) (fail l))) ℓ2 c3 | inj₂ y | yes ⌣⇒ = refl
  seq-assoc (↷ h (rest {Q = .(_ ⊗ _)} (c₁ ⊗ c₂) (last t))) ℓ1 (↷ h₁ (rest (c₃ ⊗ c₄) (fail l))) ℓ2 c3 | inj₂ y | yes ⌣⊗ = refl
  seq-assoc (↷ h (rest {Q = .(_ ⊕ _)} (c₁ ⊕ c₂) (last t))) ℓ1 (↷ h₁ (rest (c₃ ⊕ c₄) (fail l))) ℓ2 c3 | inj₂ y | yes ⌣⊕ = refl
  seq-assoc (↷ h (rest {Q = Q} b (last t))) ℓ1 (↷ h₁ (rest b₁ (fail l))) ℓ2 c3 | inj₂ y | no ¬p = refl
  seq-assoc (↷ h (rest {Q = Q} b (last t))) ℓ1 (↷ (⁇ l) (rest {P = P} b₁ (last t₁))) ℓ2 id⋆ with (` Q) ⌣? (` P)
  seq-assoc (↷ h (rest {Q = .U} U (last t))) ℓ1 (↷ (⁇ l) (rest {_} U (last t₁))) ℓ2 id⋆ | yes ⌣U = refl
  seq-assoc (↷ h (rest {Q = .(_ ⇒ _)} (c₁ ⇒ c₂) (last t))) ℓ1 (↷ (⁇ l) (rest {_} (c₃ ⇒ c₄) (last t₁))) ℓ2 id⋆ | yes ⌣⇒ = refl
  seq-assoc (↷ h (rest {Q = .(_ ⊗ _)} (c₁ ⊗ c₂) (last t))) ℓ1 (↷ (⁇ l) (rest {_} (c₃ ⊗ c₄) (last t₁))) ℓ2 id⋆ | yes ⌣⊗ = refl
  seq-assoc (↷ h (rest {Q = .(_ ⊕ _)} (c₁ ⊕ c₂) (last t))) ℓ1 (↷ (⁇ l) (rest {_} (c₃ ⊕ c₄) (last t₁))) ℓ2 id⋆ | yes ⌣⊕ = refl
  seq-assoc (↷ h (rest {Q = Q} b (last t))) ℓ1 (↷ (⁇ l) (rest {_} b₁ (last t₁))) ℓ2 id⋆ | no ¬p = refl
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
  seq-assoc (↷ h (rest b (last t))) ℓ1 (↷ h₁ (rest b₁ (last t₁))) ℓ2 (↷ h₂ (rest b₂ t₂)) = cong (↷ h) (seq'-assoc (link h₁ ℓ1 t) b b₁ t₁ ℓ2 h₂ b₂ t₂)
  
  seq'-assoc : ∀ {P P₁ P₂ Q Q₁ Q₂ T4 T5 T6 }
    → ∀ ℓ1
    → (b : Body P₂ Q)
    → (b₁    : Body P₁ Q₁)
    → (t₁    : Last Q₁ T4)
    → (ℓ2 : T4 ≡ T5 ⊎ Label)
    → (h₂    : Head P T5)
    → (b₂    : Body P Q₂)
    → (t₂    : Tail Q₂ T6)
    → seq' (ext-rest ℓ1 b (rest b₁ (last t₁))) ℓ2 (↷ h₂ (rest b₂ t₂)) ≡
      ext-rest ℓ1 b (ext-rest (link h₂ ℓ2 t₁) b₁ (rest b₂ t₂))
  seq'-assoc (inj₁ refl) U U t₁ ℓ2 h₂ b₂ t₂ = seq'-assoc-U (link h₂ ℓ2 t₁) (inj₁ refl) b₂ t₂
  ---
  seq'-assoc (inj₁ refl) (c₁ ⇒ c₂) (c₃ ⇒ c₄) t₁ ℓ2 h₂ b₂ t₂ with (link h₂ ℓ2 t₁)
  seq'-assoc (inj₁ refl) (c₁ ⇒ c₂) (c₃ ⇒ c₄) t₁ ℓ2 h₂ (c₅ ⇒ c₆) t₂ | inj₁ refl
    rewrite seq-assoc c₅ (inj₁ refl) c₃ (inj₁ refl) c₁ | seq-assoc c₂ (inj₁ refl) c₄ (inj₁ refl) c₆
    = refl
  seq'-assoc {P = P} {Q₁ = (T1 ⇒ T2)} (inj₁ refl) (c₁ ⇒ c₂) (c₃ ⇒ c₄) t₁ ℓ2 h₂ b₂ t₂ | inj₂ y with (` (T1 ⇒ T2)) ⌣? (` P)
  seq'-assoc {.(_ ⇒ _)} (inj₁ refl) (c₁ ⇒ c₂) (c₃ ⇒ c₄) t₁ ℓ2 h₂ (c₅ ⇒ c₆) t₂ | inj₂ y | yes ⌣⇒ 
    rewrite seq-assoc c₅ (inj₂ y) c₃ (inj₁ refl) c₁ | seq-assoc c₂ (inj₁ refl) c₄ (inj₂ y) c₆
    = refl
  seq'-assoc {P} (inj₁ refl) (c₁ ⇒ c₂) (c₃ ⇒ c₄) t₁ ℓ2 h₂ b₂ t₂ | inj₂ y | no ¬p = refl
  ---
  seq'-assoc (inj₁ refl) (c₁ ⊗ c₂) (c₃ ⊗ c₄) t₁ ℓ2 h₂ b₂ t₂ with (link h₂ ℓ2 t₁)
  seq'-assoc (inj₁ refl) (c₁ ⊗ c₂) (c₃ ⊗ c₄) t₁ ℓ2 h₂ (c₅ ⊗ c₆) t₂ | inj₁ refl
    rewrite seq-assoc c₁ (inj₁ refl) c₃ (inj₁ refl) c₅ | seq-assoc c₂ (inj₁ refl) c₄ (inj₁ refl) c₆
    = refl
  seq'-assoc {P = P} {Q₁ = (T1 ⊗ T2)} (inj₁ refl) (c₁ ⊗ c₂) (c₃ ⊗ c₄) t₁ ℓ2 h₂ b₂ t₂ | inj₂ y with (` (T1 ⊗ T2)) ⌣? (` P)
  seq'-assoc {.(_ ⊗ _)} (inj₁ refl) (c₁ ⊗ c₂) (c₃ ⊗ c₄) t₁ ℓ2 h₂ (c₅ ⊗ c₆) t₂ | inj₂ y | yes ⌣⊗ 
    rewrite seq-assoc c₁ (inj₁ refl) c₃ (inj₂ y) c₅ | seq-assoc c₂ (inj₁ refl) c₄ (inj₂ y) c₆
    = refl
  seq'-assoc {P} (inj₁ refl) (c₁ ⊗ c₂) (c₃ ⊗ c₄) t₁ ℓ2 h₂ b₂ t₂ | inj₂ y | no ¬p = refl
  ---
  seq'-assoc (inj₁ refl) (c₁ ⊕ c₂) (c₃ ⊕ c₄) t₁ ℓ2 h₂ b₂ t₂ with (link h₂ ℓ2 t₁)
  seq'-assoc (inj₁ refl) (c₁ ⊕ c₂) (c₃ ⊕ c₄) t₁ ℓ2 h₂ (c₅ ⊕ c₆) t₂ | inj₁ refl
    rewrite seq-assoc c₁ (inj₁ refl) c₃ (inj₁ refl) c₅ | seq-assoc c₂ (inj₁ refl) c₄ (inj₁ refl) c₆
    = refl
  seq'-assoc {P = P} {Q₁ = (T1 ⊕ T2)} (inj₁ refl) (c₁ ⊕ c₂) (c₃ ⊕ c₄) t₁ ℓ2 h₂ b₂ t₂ | inj₂ y with (` (T1 ⊕ T2)) ⌣? (` P)
  seq'-assoc {.(_ ⊕ _)} (inj₁ refl) (c₁ ⊕ c₂) (c₃ ⊕ c₄) t₁ ℓ2 h₂ (c₅ ⊕ c₆) t₂ | inj₂ y | yes ⌣⊕ 
    rewrite seq-assoc c₁ (inj₁ refl) c₃ (inj₂ y) c₅ | seq-assoc c₂ (inj₁ refl) c₄ (inj₂ y) c₆
    = refl
  seq'-assoc {P} (inj₁ refl) (c₁ ⊕ c₂) (c₃ ⊕ c₄) t₁ ℓ2 h₂ b₂ t₂ | inj₂ y | no ¬p = refl
  ---
  seq'-assoc {P₁ = P₁} {Q = Q} (inj₂ y) b b₁ t₁ ℓ2 h₂ b₂ t₂ with (` Q) ⌣? (` P₁)
  seq'-assoc {P₁ = .U} {Q = .U} (inj₂ y) U U t₁ ℓ2 h₂ b₂ t₂ | yes ⌣U = seq'-assoc-U (link h₂ ℓ2 t₁) (inj₂ y) b₂ t₂
  ---
  seq'-assoc {P₁ = .(_ ⇒ _)} {Q = .(_ ⇒ _)} (inj₂ y) (c₁ ⇒ c₂) (c₃ ⇒ c₄) t₁ ℓ2 h₂ b₂ t₂ | yes ⌣⇒ with (link h₂ ℓ2 t₁)
  seq'-assoc {_} {.(_ ⇒ _)} {_} {.(_ ⇒ _)} (inj₂ y) (c₁ ⇒ c₂) (c₃ ⇒ c₄) t₁ ℓ2 h₂ (c₅ ⇒ c₆) t₂ | yes ⌣⇒ | inj₁ refl
    rewrite seq-assoc c₅ (inj₁ refl) c₃ (inj₂ y) c₁ | seq-assoc c₂ (inj₂ y) c₄ (inj₁ refl) c₆
    = refl
  seq'-assoc {P = P} {Q₁ = (T1 ⇒ T2)} (inj₂ y) (c₁ ⇒ c₂) (c₃ ⇒ c₄) t₁ ℓ2 h₂ b₂ t₂ | yes ⌣⇒ | inj₂ y₁ with (` (T1 ⇒ T2)) ⌣? (` P)
  seq'-assoc {.(_ ⇒ _)} {.(_ ⇒ _)} {_} {.(_ ⇒ _)} (inj₂ y) (c₁ ⇒ c₂) (c₃ ⇒ c₄) t₁ ℓ2 h₂ (c₅ ⇒ c₆) t₂ | yes ⌣⇒ | inj₂ y₁ | yes ⌣⇒
    rewrite seq-assoc c₅ (inj₂ y₁) c₃ (inj₂ y) c₁ | seq-assoc c₂ (inj₂ y) c₄ (inj₂ y₁) c₆
    = refl
  seq'-assoc {P} {.(_ ⇒ _)} {_} {.(_ ⇒ _)} (inj₂ y) (c₁ ⇒ c₂) (c₃ ⇒ c₄) t₁ ℓ2 h₂ b₂ t₂ | yes ⌣⇒ | inj₂ y₁ | no ¬p = refl
  ---
  ---
  seq'-assoc {P₁ = .(_ ⊗ _)} {Q = .(_ ⊗ _)} (inj₂ y) (c₁ ⊗ c₂) (c₃ ⊗ c₄) t₁ ℓ2 h₂ b₂ t₂ | yes ⌣⊗ with (link h₂ ℓ2 t₁)
  seq'-assoc {_} {.(_ ⊗ _)} {_} {.(_ ⊗ _)} (inj₂ y) (c₁ ⊗ c₂) (c₃ ⊗ c₄) t₁ ℓ2 h₂ (c₅ ⊗ c₆) t₂ | yes ⌣⊗ | inj₁ refl
    rewrite seq-assoc c₁ (inj₂ y) c₃ (inj₁ refl) c₅ | seq-assoc c₂ (inj₂ y) c₄ (inj₁ refl) c₆
    = refl
  seq'-assoc {P = P} {Q₁ = (T1 ⊗ T2)} (inj₂ y) (c₁ ⊗ c₂) (c₃ ⊗ c₄) t₁ ℓ2 h₂ b₂ t₂ | yes ⌣⊗ | inj₂ y₁ with (` (T1 ⊗ T2)) ⌣? (` P)
  seq'-assoc {.(_ ⊗ _)} {.(_ ⊗ _)} {_} {.(_ ⊗ _)} (inj₂ y) (c₁ ⊗ c₂) (c₃ ⊗ c₄) t₁ ℓ2 h₂ (c₅ ⊗ c₆) t₂ | yes ⌣⊗ | inj₂ y₁ | yes ⌣⊗
    rewrite seq-assoc c₁ (inj₂ y) c₃ (inj₂ y₁) c₅ | seq-assoc c₂ (inj₂ y) c₄ (inj₂ y₁) c₆
    = refl
  seq'-assoc {P} {.(_ ⊗ _)} {_} {.(_ ⊗ _)} (inj₂ y) (c₁ ⊗ c₂) (c₃ ⊗ c₄) t₁ ℓ2 h₂ b₂ t₂ | yes ⌣⊗ | inj₂ y₁ | no ¬p = refl
  ---
  ---
  seq'-assoc {P₁ = .(_ ⊕ _)} {Q = .(_ ⊕ _)} (inj₂ y) (c₁ ⊕ c₂) (c₃ ⊕ c₄) t₁ ℓ2 h₂ b₂ t₂ | yes ⌣⊕ with (link h₂ ℓ2 t₁)
  seq'-assoc {_} {.(_ ⊕ _)} {_} {.(_ ⊕ _)} (inj₂ y) (c₁ ⊕ c₂) (c₃ ⊕ c₄) t₁ ℓ2 h₂ (c₅ ⊕ c₆) t₂ | yes ⌣⊕ | inj₁ refl
    rewrite seq-assoc c₁ (inj₂ y) c₃ (inj₁ refl) c₅ | seq-assoc c₂ (inj₂ y) c₄ (inj₁ refl) c₆
    = refl
  seq'-assoc {P = P} {Q₁ = (T1 ⊕ T2)} (inj₂ y) (c₁ ⊕ c₂) (c₃ ⊕ c₄) t₁ ℓ2 h₂ b₂ t₂ | yes ⌣⊕ | inj₂ y₁ with (` (T1 ⊕ T2)) ⌣? (` P)
  seq'-assoc {.(_ ⊕ _)} {.(_ ⊕ _)} {_} {.(_ ⊕ _)} (inj₂ y) (c₁ ⊕ c₂) (c₃ ⊕ c₄) t₁ ℓ2 h₂ (c₅ ⊕ c₆) t₂ | yes ⌣⊕ | inj₂ y₁ | yes ⌣⊕
    rewrite seq-assoc c₁ (inj₂ y) c₃ (inj₂ y₁) c₅ | seq-assoc c₂ (inj₂ y) c₄ (inj₂ y₁) c₆
    = refl
  seq'-assoc {P} {.(_ ⊕ _)} {_} {.(_ ⊕ _)} (inj₂ y) (c₁ ⊕ c₂) (c₃ ⊕ c₄) t₁ ℓ2 h₂ b₂ t₂ | yes ⌣⊕ | inj₂ y₁ | no ¬p = refl
  ---
  seq'-assoc {P₁ = P₁} {Q = Q} (inj₂ y) b b₁ t₁ ℓ2 h₂ b₂ t₂ | no ¬p with ext-rest (link h₂ ℓ2 t₁) b₁ (rest b₂ t₂)
  seq'-assoc {P₁ = P₁} {Q = Q} (inj₂ y) b b₁ t₁ ℓ2 h₂ b₂ t₂ | no ¬p | rest b₃ t = refl

  seq'-assoc-U : ∀ {P1 P2 T1}
    → ∀ ℓ1 ℓ2
    → (b : Body P1 P2)
    → (t : Tail P2 T1)
    → ext-rest ℓ1 U (rest b t) ≡
      ext-rest ℓ2 U (ext-rest ℓ1 U (rest b t))
  seq'-assoc-U ℓ1 ℓ2 b t with ext-rest ℓ1 U (rest b t)
  seq'-assoc-U ℓ1 (inj₁ refl) b t | rest U t₁ = refl
  seq'-assoc-U ℓ1 (inj₂ y) b t | rest U t₁ = refl

open import CEKcc.Values Label Cast

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
  apply-body (c₁ ⊕ c₂) (inl v c)
    = succ (inl v (mk-seq c c₁))
  apply-body (c₁ ⊕ c₂) (inr v c)
    = succ (inr v (mk-seq c c₂))
    
  apply-rest : ∀ {P T} → Rest P T → Val (` P) → CastResult T
  apply-rest (rest b t) v
    = apply-body b v >>= λ u →
      apply-tail t u

  apply-head : ∀ {P T} → Head P T → Val T → CastResult (` P)
  apply-head {P = Q} (⁇ l) (inj P v) with (` P) ⌣? (` Q)
  apply-head {.U} (⁇ l) (inj .U sole) | yes ⌣U = succ sole
  apply-head {(T1 ⇒ T2)} (⁇ l) (inj _ (fun env c₁ b c₂)) | yes ⌣⇒
    = succ (fun env (seq (mk-id T1) (inj₂ l) c₁) b (seq c₂ (inj₂ l) (mk-id T2)))
  apply-head {.(_ ⊗ _)} (⁇ l) (inj _ (cons v₁ c₁ v₂ c₂)) | yes ⌣⊗
    = succ (cons v₁ (mk-seq c₁ (mk-cast l _ _)) v₂ (mk-seq c₂ (mk-cast l _ _)))
  apply-head {.(_ ⊕ _)} (⁇ l) (inj _ (inl v c)) | yes ⌣⊕
    = succ (inl v (mk-seq c (mk-cast l _ _)))
  apply-head {.(_ ⊕ _)} (⁇ l) (inj _ (inr v c)) | yes ⌣⊕
    = succ (inr v (mk-seq c (mk-cast l _ _)))
  apply-head {Q} (⁇ l) (inj P v) | no ¬p = fail l
  apply-head ε v = succ v
  
  apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val T1 → CastResult T2
  apply-cast id⋆ v
    = succ v
  apply-cast (↷ h r) v
    = apply-head h v >>= λ u →
      apply-rest r u

mutual
  lem-id-body : ∀ P
    → (v : Val (` P))  
    -----------------------------
    → apply-body (mk-id-body P) v ≡ succ v
  lem-id-body U sole = refl
  lem-id-body (T₁ ⇒ T₂) (fun env c₁ b c₂) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
  lem-id-body (T₁ ⊗ T₂) (cons v₁ c₁ v₂ c₂) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
  lem-id-body (T₁ ⊕ T₂) (inl v c) rewrite seq-id-r c = refl
  lem-id-body (T₁ ⊕ T₂) (inr v c) rewrite seq-id-r c = refl
  
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
lem-seq (↷ h (rest b t)) c2 v with apply-head h v
lem-seq (↷ h (rest b (fail l))) c2 v | succ v₁ with apply-body b v₁
lem-seq (↷ h (rest b (fail l))) c2 v | succ v₁ | succ v₂ = refl
lem-seq (↷ h (rest b (fail l))) c2 v | succ v₁ | fail l₁ = refl
lem-seq (↷ h (rest b (last t))) id⋆ v | succ v₁ with apply-body b v₁
lem-seq (↷ h (rest b (last ‼))) id⋆ v | succ v₁ | succ v₂ = refl
lem-seq (↷ h (rest b (last t))) id⋆ v | succ v₁ | fail l = refl
lem-seq (↷ h (rest {Q = P1} b (last ‼))) (↷ {P = P2} (⁇ l) (rest b₁ t)) v | succ v₁ with (` P1) ⌣? (` P2)
lem-seq (↷ h (rest {Q = .U} U (last ‼))) (↷ {P = .U} (⁇ l) (rest U t)) v | succ sole | yes ⌣U = refl
lem-seq (↷ h (rest {Q = .(_ ⇒ _)} (c₁ ⇒ c₂) (last ‼))) (↷ {P = (T3 ⇒ T4)} (⁇ l) (rest (c₃ ⇒ c₄) t)) v | succ (fun env c₅ b c₆) | yes ⌣⇒
  rewrite seq-assoc (mk-id T3) (inj₂ l) (mk-id _) (inj₁ refl) (mk-seq c₁ c₅)
        | seq-id-l (seq c₁ (inj₁ refl) c₅)
        | sym (seq-assoc c₃ (inj₁ refl) (mk-id T3) (inj₂ l) (seq c₁ (inj₁ refl) c₅))
        | seq-id-r c₃
        | seq-assoc c₃ (inj₂ l) c₁ (inj₁ refl) c₅
        | seq-assoc c₆ (inj₁ refl) c₂ (inj₂ l) (mk-id T4)
        | seq-assoc c₆ (inj₁ refl) (seq c₂ (inj₂ l) (mk-id T4)) (inj₁ refl) c₄
        | seq-assoc c₂ (inj₂ l) (mk-id T4) (inj₁ refl) c₄
        | seq-id-l c₄
  = refl
lem-seq (↷ h (rest {Q = (T1 ⊗ T2)} (c₁ ⊗ c₂) (last ‼))) (↷ {P = (T3 ⊗ T4)} (⁇ l) (rest (c₃ ⊗ c₄) t)) v | succ (cons v₁ c₅ v₂ c₆) | yes ⌣⊗
  rewrite sym (seq-assoc (mk-seq c₅ c₁) (inj₁ refl) (mk-id T1) (inj₂ l) (mk-id T3))
        | seq-id-r (seq c₅ (inj₁ refl) c₁)
        | seq-assoc (seq c₅ (inj₁ refl) c₁) (inj₂ l) (mk-id T3) (inj₁ refl) c₃
        | seq-id-l c₃
        | seq-assoc c₅ (inj₁ refl) c₁ (inj₂ l) c₃
        --
        | sym (seq-assoc (mk-seq c₆ c₂) (inj₁ refl) (mk-id T2) (inj₂ l) (mk-id T4))
        | seq-id-r (seq c₆ (inj₁ refl) c₂)
        | seq-assoc (seq c₆ (inj₁ refl) c₂) (inj₂ l) (mk-id T4) (inj₁ refl) c₄
        | seq-id-l c₄
        | seq-assoc c₆ (inj₁ refl) c₂ (inj₂ l) c₄
  = refl
lem-seq (↷ h (rest {Q = (T1 ⊕ T2)} (c₁ ⊕ c₂) (last ‼))) (↷ {P = (T3 ⊕ T4)} (⁇ l) (rest (c₃ ⊕ c₄) t)) v | succ (inl v₁ c₅) | yes ⌣⊕
  rewrite sym (seq-assoc (mk-seq c₅ c₁) (inj₁ refl) (mk-id T1) (inj₂ l) (mk-id T3))
        | seq-id-r (seq c₅ (inj₁ refl) c₁)
        | seq-assoc (seq c₅ (inj₁ refl) c₁) (inj₂ l) (mk-id T3) (inj₁ refl) c₃
        | seq-id-l c₃
        | seq-assoc c₅ (inj₁ refl) c₁ (inj₂ l) c₃
  = refl
lem-seq (↷ h (rest {Q = (T1 ⊕ T2)} (c₁ ⊕ c₂) (last ‼))) (↷ {P = (T3 ⊕ T4)} (⁇ l) (rest (c₃ ⊕ c₄) t)) v | succ (inr v₁ c₆) | yes ⌣⊕
  rewrite sym (seq-assoc (mk-seq c₆ c₂) (inj₁ refl) (mk-id T2) (inj₂ l) (mk-id T4))
        | seq-id-r (seq c₆ (inj₁ refl) c₂)
        | seq-assoc (seq c₆ (inj₁ refl) c₂) (inj₂ l) (mk-id T4) (inj₁ refl) c₄
        | seq-id-l c₄
        | seq-assoc c₆ (inj₁ refl) c₂ (inj₂ l) c₄
  = refl
lem-seq (↷ h (rest {Q = P1} b (last ‼))) (↷ {P = P2} (⁇ l) (rest b₁ t)) v | succ v₁ | no ¬p with apply-body b v₁
lem-seq (↷ h (rest {Q = P1} b (last ‼))) (↷ {P = P2} (⁇ l) (rest b₁ t)) v | succ v₁ | no ¬p | succ v₂ with (` P1) ⌣? (` P2)
lem-seq (↷ h (rest {Q = P1} b (last ‼))) (↷ {P = P2} (⁇ l) (rest b₁ t)) v | succ v₁ | no ¬p | succ v₂ | yes p = ⊥-elim (¬p p)
lem-seq (↷ h (rest {Q = P1} b (last ‼))) (↷ {P = P2} (⁇ l) (rest b₁ t)) v | succ v₁ | no ¬p | succ v₂ | no ¬p₁ = refl
lem-seq (↷ h (rest {Q = P1} b (last ‼))) (↷ {P = P2} (⁇ l) (rest b₁ t)) v | succ v₁ | no ¬p | fail l₁ = refl
lem-seq (↷ h (rest U (last ε))) (↷ ε (rest U t)) v | succ sole = refl
lem-seq (↷ h (rest (c₁ ⇒ c₂) (last ε))) (↷ ε (rest (c₃ ⇒ c₄) t)) v | succ (fun env c₅ b c₆)
  rewrite seq-assoc c₃ (inj₁ refl) c₁ (inj₁ refl) c₅
        | seq-assoc c₆ (inj₁ refl) c₂ (inj₁ refl) c₄
  = refl
lem-seq (↷ h (rest (c₁ ⊗ c₂) (last ε))) (↷ ε (rest (c₃ ⊗ c₄) t)) v | succ (cons v₁ c₅ v₂ c₆)
  rewrite seq-assoc c₅ (inj₁ refl) c₁ (inj₁ refl) c₃
        | seq-assoc c₆ (inj₁ refl) c₂ (inj₁ refl) c₄
  = refl
lem-seq (↷ h (rest (c₁ ⊕ c₂) (last ε))) (↷ ε (rest (c₃ ⊕ c₄) t)) v | succ (inl v₁ c)
  rewrite seq-assoc c (inj₁ refl) c₁ (inj₁ refl) c₃
  = refl
lem-seq (↷ h (rest (c₁ ⊕ c₂) (last ε))) (↷ ε (rest (c₃ ⊕ c₄) t)) v | succ (inr v₁ c)
  rewrite seq-assoc c (inj₁ refl) c₂ (inj₁ refl) c₄
  = refl
lem-seq (↷ h (rest b t)) c2 v | fail l = refl

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
lem-cast-proj l .U .U sole | yes ⌣U = refl
lem-cast-proj l (T1 ⇒ T2) (T3 ⇒ T4) (fun env c₁ b c₂) | yes ⌣⇒
  rewrite seq-id-l (seq (mk-id T1) (inj₂ l) c₁)
        | seq-assoc (mk-id T1) (inj₂ l) (mk-id T3) (inj₁ refl) c₁
        | seq-id-l c₁
        | seq-id-r (seq c₂ (inj₂ l) (mk-id T2))
        | sym (seq-assoc c₂ (inj₁ refl) (mk-id T4) (inj₂ l) (mk-id T2))
        | seq-id-r c₂
  = refl
lem-cast-proj l (T1 ⊗ T2) (T3 ⊗ T4) (cons v c₁ v₁ c₂) | yes ⌣⊗
  rewrite seq-id-r (seq c₁ (inj₁ refl) (seq (mk-id T3) (inj₂ l) (mk-id T1)))
        | seq-id-r (seq c₂ (inj₁ refl) (seq (mk-id T4) (inj₂ l) (mk-id T2)))
  = refl
lem-cast-proj l (T1 ⊕ T2) (T3 ⊕ T4) (inl v c₁) | yes ⌣⊕
  rewrite seq-id-r (seq c₁ (inj₁ refl) (seq (mk-id T3) (inj₂ l) (mk-id T1)))
  = refl
lem-cast-proj l (T1 ⊕ T2) (T3 ⊕ T4) (inr v c₂) | yes ⌣⊕
  rewrite seq-id-r (seq c₂ (inj₁ refl) (seq (mk-id T4) (inj₂ l) (mk-id T2)))
  = refl
lem-cast-proj l P P₁ v | no ¬p rewrite lem-id-body P₁ v = refl

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
    
lem-cast-⊕-l : ∀ T T11 T12 T21 T22
  → (l : Label)
  → (v : Val T)
  → (c : Cast T T11)
  → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inl v c) ≡
    succ (inl v (mk-seq c (mk-cast l T11 T21)))
lem-cast-⊕-l T T11 T12 T21 T22 l v c = refl

lem-cast-⊕-r : ∀ T T11 T12 T21 T22
  → (l : Label)
  → (v : Val T)
  → (c : Cast T T12)
  → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inr v c) ≡
    succ (inr v (mk-seq c (mk-cast l T12 T22)))
lem-cast-⊕-r T T11 T12 T21 T22 l v c = refl

cast-rep : CastRep
cast-rep = record
             { Cast = Cast
             ; mk-cast = mk-cast
             ; mk-seq = mk-seq
             ; mk-id = mk-id
             ; apply-cast = apply-cast
             ; lem-id = lem-id
             ; lem-seq = lem-seq
             ; lem-cast-¬⌣ = lem-cast-¬⌣
             ; lem-cast-id⋆ = lem-cast-id⋆
             ; lem-cast-inj = lem-cast-inj
             ; lem-cast-proj = lem-cast-proj
             ; lem-cast-U = lem-cast-U
             ; lem-cast-⇒ = lem-cast-⇒
             ; lem-cast-⊗ = lem-cast-⊗
             ; lem-cast-⊕-l = lem-cast-⊕-l
             ; lem-cast-⊕-r = lem-cast-⊕-r
             }
