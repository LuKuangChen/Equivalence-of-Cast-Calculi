module Types where
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Data.Product using (Σ; _×_ ; Σ-syntax; ∃-syntax; _,_)
open import Data.Vec using (Vec; replicate; []; _∷_; map)

-- infix 100 _⊕_

module AlternativeType where
  open import Data.Vec using (Vec; replicate; []; _∷_; map)
  open import Data.Nat using (ℕ)

  infix  99 `_
  infix 101 _·_
  infix 100 _⇒_
  infix 100 _⊗_

  data TypeOp : Set where
    `B : TypeOp
    `⊗ : TypeOp
    `⇒ : TypeOp
  
  _≟op_ : (o1 o2 : TypeOp) → Dec (o1 ≡ o2)
  `⊗ ≟op `⊗ = yes refl
  `⊗ ≟op `⇒ = no (λ ())
  `⇒ ≟op `⊗ = no (λ ())
  `⇒ ≟op `⇒ = yes refl
  `B ≟op `B = yes refl
  `B ≟op `⊗ = no (λ ())
  `B ≟op `⇒ = no (λ ())
  `⊗ ≟op `B = no (λ ())
  `⇒ ≟op `B = no (λ ())
  
  arity : TypeOp → ℕ
  arity `B = 0
  arity `⊗ = 2
  arity `⇒ = 2
  
  mutual
    record PreType : Set where
      inductive
      constructor _·_
      field
        op : TypeOp
        T* : Vec Type (arity op)
  
    data Type : Set where
      *  : Type
      `_ : PreType → Type
  
  data Polarity : Set where
    ⊝ : Polarity
    ⊕ : Polarity
  
  polarity : (op : TypeOp) → Vec Polarity (arity op)
  polarity `B = []
  polarity `⊗ = ⊕ ∷ ⊕ ∷ []
  polarity `⇒ = ⊝ ∷ ⊕ ∷ []
  
  choose : {A : Set} → Polarity → A → A → A
  choose ⊝ a b = a
  choose ⊕ a b = b

  pattern B       = `B · []
  pattern _⇒_ S T = `⇒ · (S ∷ T ∷ [])
  pattern _⊗_ S T = `⊗ · (S ∷ T ∷ [])

open AlternativeType public


-- mutual
--   data Type : Set where
--     * : Type
--     `_ : (P : PreType) → Type
    
--   data PreType : Set where
--     B : PreType
--     _⇒_ : (S T : Type) → PreType
--     _⊗_ : (S T : Type) → PreType
--     -- _⊕_ : (S T : Type) → PreType

data Tag : PreType → Set where
  `B : Tag B
  `⇒ : ∀ {T1 T2} → Tag (T1 ⇒ T2)
  `⊗ : ∀ {T1 T2} → Tag (T1 ⊗ T2)

tag : ∀ P → Tag P
tag B = `B
tag (S ⇒ T) = `⇒
tag (S ⊗ T) = `⊗

tag-unique : ∀ {P} → (t1 : Tag P) → (t2 : Tag P) → t1 ≡ t2
tag-unique `B `B = refl
tag-unique `⇒ `⇒ = refl
tag-unique `⊗ `⊗ = refl

data Same : PreType → Set where
  same : ∀ P → Same P

data Ground : PreType → Set where
  `B : Ground (B)
  `⇒ : Ground (* ⇒ *)
  `⊗ : Ground (* ⊗ *)
  -- `⊕ : Ground (* ⊕ *)

ground-unique : ∀ {P} → (G H : Ground P) → G ≡ H
ground-unique `B `B = refl
ground-unique `⇒ `⇒ = refl
ground-unique `⊗ `⊗ = refl

op→ground : TypeOp → PreType
op→ground op = op · replicate *

op→ground-Ground : ∀ op → Ground (op→ground op)
op→ground-Ground `B = `B
op→ground-Ground `⊗ = `⊗
op→ground-Ground `⇒ = `⇒

inv-ground : ∀ {P} → Ground P → ∃[ o ](P ≡ o · (replicate *))
inv-ground `B = `B , refl
inv-ground `⇒ = `⇒ , refl
inv-ground `⊗ = `⊗ , refl

unground : ∀ {P} → Ground P → PreType
unground {P} gP = P

unground' : ∀ {P} → Ground P → PreType
unground' `B = B
unground' `⇒ = * ⇒ *
unground' `⊗ = * ⊗ *

lem-unground : ∀ {P} → (gP : Ground P) → unground gP ≡ unground' gP
lem-unground `B = refl
lem-unground `⇒ = refl
lem-unground `⊗ = refl

ground? : (P : PreType) → Dec (Ground P)
ground? B = yes `B
ground? (* ⇒ *) = yes `⇒
ground? (* ⇒ (` P)) = no λ ()
ground? ((` P) ⇒ T₂) = no (λ ())
ground? (* ⊗ *) = yes `⊗
ground? (* ⊗ (` P)) = no (λ ())
ground? ((` P) ⊗ T) = no (λ ())
-- ground? (* ⊕ *) = yes `⊕
-- ground? (* ⊕ (` P)) = no (λ ())
-- ground? ((` P) ⊕ T) = no (λ ())

_≟_ : (T1 T2 : Type) → Dec (T1 ≡ T2)
* ≟ * = yes refl
* ≟ (` P) = no (λ ())
(` P) ≟ * = no (λ ())
(` B) ≟ (` B) = yes refl
(` B) ≟ (` (T₁ ⇒ T₂)) = no (λ ())
(` B) ≟ (` (T₁ ⊗ T₂)) = no (λ ())
-- (` B) ≟ (` (T₁ ⊕ T₂)) = no (λ ())
(` (T₁ ⇒ T₂)) ≟ (` B) = no (λ ())
(` (T₁ ⇒ T₂)) ≟ (` (T₃ ⇒ T₄)) with T₁ ≟ T₃ | T₂ ≟ T₄
((` (T₁ ⇒ T₂)) ≟ (` (.T₁ ⇒ .T₂))) | yes refl | yes refl = yes refl
((` (T₁ ⇒ T₂)) ≟ (` (.T₁ ⇒ T₄))) | yes refl | no ¬p = no λ { refl → ¬p refl }
((` (T₁ ⇒ T₂)) ≟ (` (T₃ ⇒ T₄))) | no ¬p | p2 = no λ { refl → ¬p refl }
(` (T₁ ⇒ T₂)) ≟ (` (T₃ ⊗ T₄)) = no (λ ())
-- (` (T₁ ⇒ T₂)) ≟ (` (T₃ ⊕ T₄)) = no (λ ())
(` (T₁ ⊗ T₂)) ≟ (` B) = no (λ ())
(` (T₁ ⊗ T₂)) ≟ (` (T₃ ⇒ T₄)) = no (λ ())
(` (T₁ ⊗ T₂)) ≟ (` (T₃ ⊗ T₄)) with T₁ ≟ T₃ | T₂ ≟ T₄
((` (T₁ ⊗ T₂)) ≟ (` (.T₁ ⊗ .T₂))) | yes refl | yes refl = yes refl
((` (T₁ ⊗ T₂)) ≟ (` (.T₁ ⊗ T₄))) | yes refl | no ¬p = no λ { refl → ¬p refl }
((` (T₁ ⊗ T₂)) ≟ (` (T₃ ⊗ T₄))) | no ¬p | p2 = no λ { refl → ¬p refl }
-- (` (T₁ ⊗ T₂)) ≟ (` (T₃ ⊕ T₄)) = no (λ ())
-- (` (T₁ ⊕ T₂)) ≟ (` B) = no (λ ())
-- (` (T₁ ⊕ T₂)) ≟ (` (T₃ ⇒ T₄)) = no (λ ())
-- (` (T₁ ⊕ T₂)) ≟ (` (T₃ ⊗ T₄)) = no (λ ())
-- (` (T₁ ⊕ T₂)) ≟ (` (T₃ ⊕ T₄)) with T₁ ≟ T₃ | T₂ ≟ T₄
-- ((` (T₁ ⊕ T₂)) ≟ (` (T₃ ⊕ T₄))) | yes refl | yes refl = yes refl
-- ((` (T₁ ⊕ T₂)) ≟ (` (T₃ ⊕ T₄))) | yes refl | no ¬p = no λ { refl → ¬p refl }
-- ((` (T₁ ⊕ T₂)) ≟ (` (T₃ ⊕ T₄))) | no ¬p | p2 = no λ { refl → ¬p refl }
                                                                      
-- consistency

data _~_ : (T1 T2 : Type) → Set where
  *~* : * ~ *
  *~P : ∀ P → * ~ (` P)
  P~* : ∀ P → (` P) ~ *
  ~B : (` B) ~ (` B)
  ~⇒ : ∀ {T1 T2 T3 T4}
    → T1 ~ T3
    → T2 ~ T4
    → (` T1 ⇒ T2) ~ (` T3 ⇒ T4)
  ~⊗ : ∀ {T1 T2 T3 T4}
    → T1 ~ T3
    → T2 ~ T4
    → (` T1 ⊗ T2) ~ (` T3 ⊗ T4)
  -- ~⊕ : ∀ {T1 T2 T3 T4}
  --   → T1 ~ T3
  --   → T2 ~ T4
  --   → (` T1 ⊕ T2) ~ (` T3 ⊕ T4)

-- shallow consistency

data _⌣_ : (T1 T2 : Type) → Set where
  *⌣* : * ⌣ *
  *⌣P : ∀ P → * ⌣ (` P)
  P⌣* : ∀ P → (` P) ⌣ *
  ⌣B : (` B) ⌣ (` B)
  ⌣⇒ : ∀ {T1 T2 T3 T4} → (` T1 ⇒ T2) ⌣ (` T3 ⇒ T4)
  ⌣⊗ : ∀ {T1 T2 T3 T4} → (` T1 ⊗ T2) ⌣ (` T3 ⊗ T4)
  -- ⌣⊕ : ∀ {T1 T2 T3 T4} → (` T1 ⊕ T2) ⌣ (` T3 ⊕ T4)

_⌣?_ : ∀ T1 T2 → Dec (T1 ⌣ T2)
* ⌣? * = yes *⌣*
* ⌣? (` P) = yes (*⌣P P)
(` P) ⌣? * = yes (P⌣* P)
(` B) ⌣? (` B) = yes ⌣B
(` B) ⌣? (` (T₁ ⇒ T₂)) = no (λ ())
(` B) ⌣? (` (T₁ ⊗ T₂)) = no (λ ())
-- (` B) ⌣? (` (T₁ ⊕ T₂)) = no (λ ())
(` (T₁ ⇒ T₂)) ⌣? (` B) = no (λ ())
(` (T₁ ⇒ T₂)) ⌣? (` (T₃ ⇒ T₄)) = yes ⌣⇒
(` (T₁ ⇒ T₂)) ⌣? (` (T₃ ⊗ T₄)) = no (λ ())
-- (` (T₁ ⇒ T₂)) ⌣? (` (T₃ ⊕ T₄)) = no (λ ())
(` (T₁ ⊗ T₂)) ⌣? (` B) = no (λ ())
(` (T₁ ⊗ T₂)) ⌣? (` (T₃ ⇒ T₄)) = no (λ ())
(` (T₁ ⊗ T₂)) ⌣? (` (T₃ ⊗ T₄)) = yes ⌣⊗
-- (` (T₁ ⊗ T₂)) ⌣? (` (T₃ ⊕ T₄)) = no (λ ())
-- (` (T₁ ⊕ T₂)) ⌣? (` B) = no (λ ())
-- (` (T₁ ⊕ T₂)) ⌣? (` (T₃ ⇒ T₄)) = no (λ ())
-- (` (T₁ ⊕ T₂)) ⌣? (` (T₃ ⊗ T₄)) = no (λ ())
-- (` (T₁ ⊕ T₂)) ⌣? (` (T₃ ⊕ T₄)) = yes ⌣⊕

⌣trans : ∀ {P1 P2 P3} → (` P1) ⌣ (` P2) → (` P2) ⌣ (` P3) → (` P1) ⌣ (` P3)
⌣trans ⌣B ⌣B = ⌣B
⌣trans ⌣⇒ ⌣⇒ = ⌣⇒
⌣trans ⌣⊗ ⌣⊗ = ⌣⊗

⌣refl : ∀ T → T ⌣ T
⌣refl * = *⌣*
⌣refl (` B) = ⌣B
⌣refl (` (T₁ ⇒ T₂)) = ⌣⇒
⌣refl (` (T₁ ⊗ T₂)) = ⌣⊗
-- ⌣refl (` (T₁ ⊕ T₂)) = ⌣⊕

⌣sym : ∀ {S T} → S ⌣ T → T ⌣ S
⌣sym *⌣* = *⌣*
⌣sym (*⌣P P) = P⌣* P
⌣sym (P⌣* P) = *⌣P P
⌣sym ⌣B = ⌣B
⌣sym ⌣⇒ = ⌣⇒
⌣sym ⌣⊗ = ⌣⊗
-- ⌣sym ⌣⊕ = ⌣⊕

⌣unique : ∀ {T1 T2}
  → (p1 p2 : T1 ⌣ T2)
  ---
  → p1 ≡ p2
⌣unique *⌣* *⌣* = refl
⌣unique (*⌣P P) (*⌣P .P) = refl
⌣unique (P⌣* P) (P⌣* .P) = refl
⌣unique ⌣B ⌣B = refl
⌣unique ⌣⇒ ⌣⇒ = refl
⌣unique ⌣⊗ ⌣⊗ = refl
-- ⌣unique ⌣⊕ ⌣⊕ = refl

shallow : ∀ {S T} → S ~ T → S ⌣ T
shallow *~* = *⌣*
shallow (*~P P) = *⌣P P
shallow (P~* P) = P⌣* P
shallow ~B = ⌣B
shallow (~⇒ p p₁) = ⌣⇒
shallow (~⊗ p p₁) = ⌣⊗
-- shallow (~⊕ p p₁) = ⌣⊕

ground : PreType → PreType
ground B = B
ground (T₁ ⇒ T₂) = * ⇒ *
ground (S ⊗ T) = * ⊗ *
-- ground (S ⊕ T) = * ⊕ *

ground-Ground : ∀ P → Ground (ground P)
ground-Ground B = `B
ground-Ground (T₁ ⇒ T₂) = `⇒
ground-Ground (S ⊗ T) = `⊗
-- ground-Ground (S ⊕ T) = `⊕

ground-⌣ : ∀ P → (` P) ⌣ (` (ground P))
ground-⌣ B = ⌣B
ground-⌣ (T₁ ⇒ T₂) = ⌣⇒
ground-⌣ (S ⊗ T) = ⌣⊗
-- ground-⌣ (S ⊕ T) = ⌣⊕

_≟G_ : ∀ {P Q} → Ground P → Ground Q → Dec (P ≡ Q)
_≟G_ `B `B = yes refl
_≟G_ `B `⇒ = no (λ ())
_≟G_ `B `⊗ = no (λ ())
_≟G_ `⇒ `B = no (λ ())
_≟G_ `⇒ `⇒ = yes refl
_≟G_ `⇒ `⊗ = no (λ ())
_≟G_ `⊗ `B = no (λ ())
_≟G_ `⊗ `⇒ = no (λ ())
_≟G_ `⊗ `⊗ = yes refl

ground-≡ : ∀ {P Q} → Ground P → Ground Q → (` P) ⌣ (` Q) → P ≡ Q
ground-≡ `B `B P⌣Q = refl
ground-≡ `⇒ `⇒ P⌣Q = refl
ground-≡ `⊗ `⊗ P⌣Q = refl

ground-≢ : ∀ {P Q} → Ground P → Ground Q → ¬ (` P) ⌣ (` Q) → ¬ (` P) ≡ (` Q)
ground-≢ `B `B ¬P⌣Q = ⊥-elim (¬P⌣Q ⌣B)
ground-≢ `B `⇒ ¬P⌣Q = λ ()
ground-≢ `B `⊗ ¬P⌣Q = λ ()
ground-≢ `⇒ `B ¬P⌣Q = λ ()
ground-≢ `⇒ `⇒ ¬P⌣Q = λ _ → ¬P⌣Q ⌣⇒
ground-≢ `⇒ `⊗ ¬P⌣Q = λ ()
ground-≢ `⊗ `B ¬P⌣Q = λ ()
ground-≢ `⊗ `⇒ ¬P⌣Q = λ ()
ground-≢ `⊗ `⊗ ¬P⌣Q = λ _ → ¬P⌣Q ⌣⊗

¬⌣-¬ground⌣ : ∀ {P Q} → ¬ (` P) ⌣ (` Q) → ¬ (` ground P) ⌣ (` ground Q)
¬⌣-¬ground⌣ {B} {B} ¬P⌣Q = λ _ → ¬P⌣Q ⌣B
¬⌣-¬ground⌣ {B} {S ⇒ T} ¬P⌣Q = λ ()
¬⌣-¬ground⌣ {B} {S ⊗ T} ¬P⌣Q = λ ()
¬⌣-¬ground⌣ {S ⇒ T} {B} ¬P⌣Q = λ ()
¬⌣-¬ground⌣ {S ⇒ T} {S₁ ⇒ T₁} ¬P⌣Q = λ _ → ¬P⌣Q ⌣⇒
¬⌣-¬ground⌣ {S ⇒ T} {S₁ ⊗ T₁} ¬P⌣Q = λ ()
¬⌣-¬ground⌣ {S ⊗ T} {B} ¬P⌣Q = λ ()
¬⌣-¬ground⌣ {S ⊗ T} {S₁ ⇒ T₁} ¬P⌣Q = λ ()
¬⌣-¬ground⌣ {S ⊗ T} {S₁ ⊗ T₁} ¬P⌣Q = λ _ → ¬P⌣Q ⌣⊗

-- subtype

data _≤_ : Type → Type → Set where

  *≤* : * ≤ *
  
  P≤* : ∀ P → (` P) ≤ *
  
  ≤B : (` B) ≤ (` B)
  
  ≤⇒ : ∀ {T1 T2 T3 T4}
    → T3 ≤ T1
    → T2 ≤ T4
    ---
    → (` T1 ⇒ T2) ≤ (` T3 ⇒ T4)
    
  -- ≤⊗ : ∀ {T1 T2 T3 T4}
  --   → T1 ≤ T3
  --   → T2 ≤ T4
  --   ---
  --   → (` T1 ⊗ T2) ≤ (` T3 ⊗ T4)
    
  -- ≤⊕ : ∀ {T1 T2 T3 T4}
  --   → T1 ≤ T3
  --   → T2 ≤ T4
  --   ---
  --   → (` T1 ⊕ T2) ≤ (` T3 ⊕ T4)

-- imprecise

data _⊑_ : Type → Type → Set where

  *⊑* : * ⊑ *
  
  P⊑* : ∀ P → (` P) ⊑ *
  
  ⊑B : (` B) ⊑ (` B)
  
  ⊑⇒ : ∀ {T1 T2 T3 T4}
    → T1 ⊑ T3
    → T2 ⊑ T4
    ---
    → (` T1 ⇒ T2) ⊑ (` T3 ⇒ T4)
    
  -- ⊑⊗ : ∀ {T1 T2 T3 T4}
  --   → T1 ⊑ T3
  --   → T2 ⊑ T4
  --   ---
  --   → (` T1 ⊗ T2) ⊑ (` T3 ⊗ T4)
    
  -- ⊑⊕ : ∀ {T1 T2 T3 T4}
  --   → T1 ⊑ T3
  --   → T2 ⊑ T4
  --   ---
  --   → (` T1 ⊕ T2) ⊑ (` T3 ⊕ T4)
