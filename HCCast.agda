module HCCast (Label : Set) where
open import Types
open import Relation.Nullary using (Dec; yes; no)

data Head (P : PreType) : Type → Set where
  ε : Head P (` P)
  ⁇ : (l : Label) → Head P ⋆

data Tail (P : PreType) : Type → Set where
  ε : Tail P (` P)
  ‼ : Tail P ⋆
  ⊥ : ∀ {B} → (l : Label) → Tail P B

mutual
  data Cast : Type → Type → Set where
    id⋆ : Cast ⋆ ⋆
    ↷ : ∀ {A B P Q} →
        (h : Head P A)(b : Body P Q)(t : Tail Q B) →
        Cast A B

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
