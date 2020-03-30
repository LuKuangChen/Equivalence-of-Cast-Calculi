module CastRepresentations.LazyUDThreesomes (Label : Set) where

open import Types
open import Cast Label using (_⟹[_]_) renaming (Cast to SrcCast)
open import Terms Label
open import S.CastADT Label

open import Data.Empty using (⊥-elim)
open import Data.Product using (∃-syntax; proj₁; proj₂; _×_)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

{-
Siek, Jeremy G., and Philip Wadler. "Threesomes, with and without blame."
ACM Sigplan Notices 45.1 (2010): 365-376.
-}

open import Data.Maybe

data OptionalLabel : Set where
  ⁇ : (l : Label) → OptionalLabel
  ε : OptionalLabel

data TypeTag : Set where
  B   : TypeTag
  *⇒* : TypeTag
  *⊗* : TypeTag

data IsTagof : TypeTag → PreType → Set where
  B   : IsTagof B B
  *⇒* : ∀ {S T} → IsTagof *⇒* (S ⇒ T)
  *⊗* : ∀ {S T} → IsTagof *⊗* (S ⊗ T)

same-tag-consis : ∀ {G H P Q}
  → (G ≡ H)
  → IsTagof G P
  → IsTagof H Q
  → ((` P) ⌣ (` Q))
same-tag-consis refl B B = ⌣B
same-tag-consis refl *⇒* *⇒* = ⌣⇒
same-tag-consis refl *⊗* *⊗* = ⌣⊗

diff-tag-inconsis : ∀ {G H P Q}
  → ¬ (G ≡ H)
  → IsTagof G P
  → IsTagof H Q
  → ¬ ((` P) ⌣ (` Q))
diff-tag-inconsis ¬p B B = ⊥-elim (¬p refl)
diff-tag-inconsis ¬p B *⇒* = λ ()
diff-tag-inconsis ¬p B *⊗* = λ ()
diff-tag-inconsis ¬p *⇒* B = λ ()
diff-tag-inconsis ¬p *⇒* *⇒* = ⊥-elim (¬p refl)
diff-tag-inconsis ¬p *⇒* *⊗* = λ ()
diff-tag-inconsis ¬p *⊗* B = λ ()
diff-tag-inconsis ¬p *⊗* *⇒* = λ ()
diff-tag-inconsis ¬p *⊗* *⊗* = ⊥-elim (¬p refl)

_≟t_ : (G H : TypeTag) → Dec (G ≡ H)
B ≟t B = yes refl
B ≟t *⇒* = no (λ ())
B ≟t *⊗* = no (λ ())
*⇒* ≟t B = no (λ ())
*⇒* ≟t *⇒* = yes refl
*⇒* ≟t *⊗* = no (λ ())
*⊗* ≟t B = no (λ ())
*⊗* ≟t *⇒* = no (λ ())
*⊗* ≟t *⊗* = yes refl

⌊_⌋ : ∀ {P} → Ground P → TypeTag
⌊ `B ⌋ = B
⌊ `⇒ ⌋ = *⇒*
⌊ `⊗ ⌋ = *⊗*

lem⌊_⌋≡⌊_⌋ : ∀ {P Q} → (gP : Ground P) → (gQ : Ground Q) → ⌊ gP ⌋ ≡ ⌊ gQ ⌋ → P ≡ Q
lem⌊ `B ⌋≡⌊ `B ⌋ p = refl
lem⌊ `⇒ ⌋≡⌊ `⇒ ⌋ p = refl
lem⌊ `⊗ ⌋≡⌊ `⊗ ⌋ p = refl 

mutual
  data LabeledType : Set where
    * : LabeledType
    ⊥ : (l : Label)
      → (G : TypeTag)
      → (p : OptionalLabel)
        ---------------
      → LabeledType
    ⟨_,_⟩ : (P̂ : LabeledPreType)(p : OptionalLabel) → LabeledType
  
  data LabeledPreType : Set where
    B   : LabeledPreType
    _⇒_ : (S : LabeledType)(T : LabeledType) → LabeledPreType
    _⊗_ : (S : LabeledType)(T : LabeledType) → LabeledPreType

data ⊢p_⦂_⟹_ : OptionalLabel → Type → PreType → Set where
  ⊢⁇ : ∀ {P}
    → (gP : Ground P)
    → (l  : Label)
    → ⊢p ⁇ l ⦂ * ⟹ P

  ⊢ε : ∀ {P}
    → ⊢p ε ⦂ (` P) ⟹ P

data _≺_ : PreType → Type → Set where
  ⊢‼ : ∀ {P}
    → (gP : Ground P)
    → P ≺ *

  ⊢ε : ∀ {P}
    → P ≺ (` P)

inv-label : ∀ {P T p Q}
  → ¬ ((` P) ⌣ (` Q))
  → P ≺ T
  → ⊢p p ⦂ T ⟹ Q
  → ∃[ l ](p ≡ ⁇ l)
inv-label ¬P⌣Q ⊢ε ⊢ε = ⊥-elim (¬P⌣Q (⌣refl _))
inv-label ¬P⌣Q (⊢‼ gP) (⊢⁇ gQ l) = ⟨ _ , refl ⟩

inv-equal : ∀ {P T p Q}
  → ((` P) ⌣ (` Q))
  → P ≺ T
  → ⊢p p ⦂ T ⟹ Q
  → P ≡ Q
inv-equal P⌣Q ⊢ε ⊢ε = refl
inv-equal P⌣Q (⊢‼ gP) (⊢⁇ gQ l) = ground-≡ gP gQ P⌣Q

mutual
  data ⊢P_⦂_⟹_ : LabeledPreType → PreType → PreType → Set where
    ⊢B : ⊢P B ⦂ B ⟹ B
      
    ⊢_⇒_ : ∀ {P̂ Q̂ S1 T1 S2 T2}
      → (⊢Ŝ : ⊢  P̂ ⦂ S2 ⟹ S1)
      → (⊢T̂ : ⊢  Q̂ ⦂ T1 ⟹ T2)
        ----------------------------
      → ⊢P (P̂ ⇒ Q̂) ⦂ (S1 ⇒ T1) ⟹ (S2 ⇒ T2)
      
    ⊢_⊗_ : ∀ {Ŝ T̂ S1 T1 S2 T2}
      → (⊢Ŝ : ⊢  Ŝ ⦂ S1 ⟹ S2)
      → (⊢T̂ : ⊢  T̂ ⦂ T1 ⟹ T2)
        ----------------------------
      → ⊢P (Ŝ ⊗ T̂) ⦂ (S1 ⊗ T1) ⟹ (S2 ⊗ T2)
  
  
  data ⊢_⦂_⟹_ : LabeledType → Type → Type → Set where
  
    ⊢* : ⊢ * ⦂ * ⟹ *
    
    ⊢⊥ : ∀ {S P Q T}
      → (l : Label)
      → {G : TypeTag}
      → (GtP : IsTagof G P)
      → {p : OptionalLabel}
      → (⊢p : ⊢p p ⦂ S ⟹ P)
      → (⊢! : Q ≺ T)
        ---------------
      → ⊢ ⊥ l G p ⦂ S ⟹ T
      
    ⊢` : ∀ {S p P P̂ Q T}
      → (⊢p : ⊢p p ⦂ S ⟹ P)
      → (⊢P̂ : ⊢P P̂ ⦂ P ⟹ Q)
      → (⊢! : Q ≺ T)
        ------------
      → ⊢ ⟨ P̂ , p ⟩ ⦂ S ⟹ T 

gnd : LabeledPreType → TypeTag
gnd B = B
gnd (S ⇒ T) = *⇒*
gnd (S ⊗ T) = *⊗*

lem-gnd-l : ∀ {P̂ P Q} → (⊢P P̂ ⦂ P ⟹ Q) → IsTagof (gnd P̂) P
lem-gnd-l (⊢B) = B
lem-gnd-l (⊢ ⊢Ŝ ⇒ ⊢T̂) = *⇒*
lem-gnd-l (⊢ ⊢Ŝ ⊗ ⊢T̂) = *⊗*

lem-gnd-r : ∀ {P̂ P Q} → (⊢P P̂ ⦂ P ⟹ Q) → IsTagof (gnd P̂) Q
lem-gnd-r (⊢B) = B
lem-gnd-r (⊢ ⊢Ŝ ⇒ ⊢T̂) = *⇒*
lem-gnd-r (⊢ ⊢Ŝ ⊗ ⊢T̂) = *⊗*

mutual
  _∘P_ : ∀ {T1 T2 T3}
    → (T̂ : LabeledPreType)
    → (Ŝ : LabeledPreType)
    → {⊢T̂ : ⊢P T̂ ⦂ T2 ⟹ T3}
    → {⊢Ŝ : ⊢P Ŝ ⦂ T1 ⟹ T2}
    → LabeledPreType
  ((B) ∘P (B)) {⊢B} {⊢B} = B
  ((S₂ ⇒ T₂) ∘P (S₁ ⇒ T₁)) {⊢ ⊢Ŝ₂ ⇒ ⊢T̂₂} {⊢ ⊢Ŝ₁ ⇒ ⊢T̂₁} = (S₁ ∘ S₂) {⊢Ŝ₁} {⊢Ŝ₂} ⇒ (T₂ ∘ T₁) {⊢T̂₂} {⊢T̂₁}
  ((S₂ ⊗ T₂) ∘P (S₁ ⊗ T₁)) {⊢ ⊢Ŝ₂ ⊗ ⊢T̂₂} {⊢ ⊢Ŝ₁ ⊗ ⊢T̂₁} = (S₂ ∘ S₁) {⊢Ŝ₂} {⊢Ŝ₁} ⊗ (T₂ ∘ T₁) {⊢T̂₂} {⊢T̂₁}

  _∘_ : ∀ {T1 T2 T3}
    → (T̂ : LabeledType)
    → (Ŝ : LabeledType)
    → {⊢T̂ : ⊢ T̂ ⦂ T2 ⟹ T3}
    → {⊢Ŝ : ⊢ Ŝ ⦂ T1 ⟹ T2}
    → LabeledType
  --- L2
  (T̂ ∘ *) = T̂
  --- L3
  (* ∘ Ŝ) = Ŝ
  --- L5
  (T̂ ∘ ⊥ l G p) = ⊥ l G p
  (⊥ m H q ∘ ⟨ P̂ , p ⟩) {⊢⊥ m HIsTagofQ ⊢q _} {⊢` ⊢p ⊢P̂ ⊢!}
    with lem-gnd-r ⊢P̂
  ... | GIsTagofP
    with gnd P̂
  ... | G
    with G ≟t H
  ... | yes G≡H = ⊥ m H p
  ... | no ¬G≡H
    with inv-label (diff-tag-inconsis ¬G≡H GIsTagofP HIsTagofQ) ⊢! ⊢q
  ... | ⟨ l , q=⁇l ⟩
    = ⊥ l G p
  (⟨ Q̂ , q ⟩ ∘ ⟨ P̂ , p ⟩) {⊢` ⊢q ⊢Q̂ ⊢!Q} {⊢` ⊢p ⊢P̂ ⊢!P}
    with lem-gnd-r ⊢P̂ | lem-gnd-l ⊢Q̂
  ... | GIsTagofP | HIsTagofQ
    with gnd P̂ | gnd Q̂
  ... | G | H
    with G ≟t H
  ... | yes G≡H
    rewrite inv-equal (same-tag-consis G≡H GIsTagofP HIsTagofQ) ⊢!P ⊢q
    = ⟨ (Q̂ ∘P P̂) {⊢Q̂} {⊢P̂} , p ⟩
  ... | no ¬G≡H
    with inv-label (diff-tag-inconsis ¬G≡H GIsTagofP HIsTagofQ) ⊢!P ⊢q
  ... | ⟨ m , q=⁇m ⟩
    = ⊥ m G p


mutual
  ⊢_∘P_ : ∀ {T1 T2 T3}
    → {T̂ : LabeledPreType}
    → {Ŝ : LabeledPreType}
    → (⊢T̂ : ⊢P T̂ ⦂ T2 ⟹ T3)
    → (⊢Ŝ : ⊢P Ŝ ⦂ T1 ⟹ T2)
    → ⊢P (T̂ ∘P Ŝ){⊢T̂}{⊢Ŝ} ⦂ T1 ⟹ T3
  (⊢ (⊢B) ∘P (⊢B)) = ⊢B
  (⊢ (⊢ S₂ ⇒ T₂) ∘P (⊢ S₁ ⇒ T₁)) = ⊢ (⊢_∘_ _ _ S₁ S₂) ⇒ (⊢_∘_ _ _ T₂ T₁)
  (⊢ (⊢ S₂ ⊗ T₂) ∘P (⊢ S₁ ⊗ T₁)) = ⊢ (⊢_∘_ _ _ S₂ S₁) ⊗ (⊢_∘_ _ _ T₂ T₁)

  ⊢_∘_ : ∀ {T1 T2 T3}
    → (T̂ : LabeledType)
    → (Ŝ : LabeledType)
    → (⊢T̂ : ⊢ T̂ ⦂ T2 ⟹ T3)
    → (⊢Ŝ : ⊢ Ŝ ⦂ T1 ⟹ T2)
    → ⊢ (T̂ ∘ Ŝ){⊢T̂}{⊢Ŝ} ⦂ T1 ⟹ T3
  (⊢ T ∘ *) ⊢T ⊢* = ⊢T
  (⊢ * ∘ ⊥ l G p) ⊢* ⊢T = ⊢T
  (⊢ * ∘ ⟨ P̂ , p ⟩) ⊢* ⊢T = ⊢T
  (⊢ ⊥ l₁ G₁ p₁ ∘ ⊥ l G p) (⊢⊥ .l₁ GtP₁ ⊢p₁ ⊢!₁) (⊢⊥ .l GtP ⊢p ⊢!) = ⊢⊥ l GtP ⊢p ⊢!₁
  (⊢ ⟨ P̂ , p₁ ⟩ ∘ ⊥ l G p) (⊢` ⊢p₁ ⊢P̂ ⊢!₁) (⊢⊥ .l GtP ⊢p ⊢!) = ⊢⊥ l GtP ⊢p ⊢!₁
  (⊢ ⊥ m H q ∘ ⟨ P̂ , p ⟩) (⊢⊥ m HIsTagofQ ⊢q ⊢!q) (⊢` ⊢p ⊢P̂ ⊢!)
    with lem-gnd-r ⊢P̂ | lem-gnd-l ⊢P̂
  ... | GIsTagofP | GIsTagofBlah
    with gnd P̂
  ... | G
    with G ≟t H
  ... | yes refl = ⊢⊥ m GIsTagofBlah ⊢p ⊢!q
  ... | no ¬G≡H
    with inv-label (diff-tag-inconsis ¬G≡H GIsTagofP HIsTagofQ) ⊢! ⊢q
  ... | ⟨ l , q=⁇l ⟩
    = ⊢⊥ l GIsTagofBlah ⊢p ⊢!q
  (⊢ ⟨ Q̂ , q ⟩ ∘ ⟨ P̂ , p ⟩) (⊢` ⊢q ⊢Q̂ ⊢!Q) (⊢` ⊢p ⊢P̂ ⊢!P)
    with lem-gnd-r ⊢P̂ | lem-gnd-l ⊢P̂ | lem-gnd-l ⊢Q̂
  ... | GIsTagofP | GIsTagofBlah | HIsTagofQ
    with gnd P̂ | gnd Q̂
  ... | G | H
    with G ≟t H
  (⊢ ⟨ Q̂ , q ⟩ ∘ ⟨ P̂ , p ⟩) (⊢` ⊢q ⊢Q̂ ⊢!Q) (⊢` ⊢p ⊢P̂ ⊢!P) | GIsTagofP | GIsTagofBlah | HIsTagofQ | G | H | yes G≡H
    with inv-equal (same-tag-consis G≡H GIsTagofP HIsTagofQ) ⊢!P ⊢q
  ... | refl = ⊢` ⊢p (⊢ ⊢Q̂ ∘P ⊢P̂) ⊢!Q
  (⊢ ⟨ Q̂ , q ⟩ ∘ ⟨ P̂ , p ⟩) (⊢` ⊢q ⊢Q̂ ⊢!Q) (⊢` ⊢p ⊢P̂ ⊢!P) | GIsTagofP | GIsTagofBlah | HIsTagofQ | G | H | no ¬G≡H
    with inv-label (diff-tag-inconsis ¬G≡H GIsTagofP HIsTagofQ) ⊢!P ⊢q
  ... | ⟨ m , q=⁇m ⟩
    = ⊢⊥ m GIsTagofBlah ⊢p ⊢!Q

