module Types where
open import Relation.Nullary using (Dec; yes; no)

infix 100 _⇒_
infix 100 _⊗_
infix 100 _⊕_

mutual
  data Type : Set where
    ⋆ : Type
    `_ : (P : PreType) → Type
    
  data PreType : Set where
    U : PreType -- the unit type, adding other base type should be straightforward
    _⇒_ : (T₁ T₂ : Type) → PreType
    _⊗_ : (T₁ T₂ : Type) → PreType
    _⊕_ : (T₁ T₂ : Type) → PreType

data _⌣_ : (T1 T2 : Type) → Set where
  ⋆⌣⋆ : ⋆ ⌣ ⋆
  ⋆⌣P : ∀ P → ⋆ ⌣ (` P)
  P⌣⋆ : ∀ P → (` P) ⌣ ⋆
  ⌣U : (` U) ⌣ (` U)
  ⌣⇒ : ∀ {T1 T2 T3 T4} → (` T1 ⇒ T2) ⌣ (` T3 ⇒ T4)
  ⌣⊗ : ∀ {T1 T2 T3 T4} → (` T1 ⊗ T2) ⌣ (` T3 ⊗ T4)
  ⌣⊕ : ∀ {T1 T2 T3 T4} → (` T1 ⊕ T2) ⌣ (` T3 ⊕ T4)

_⌣?_ : ∀ T1 T2 → Dec (T1 ⌣ T2)
⋆ ⌣? ⋆ = yes ⋆⌣⋆
⋆ ⌣? (` P) = yes (⋆⌣P P)
(` P) ⌣? ⋆ = yes (P⌣⋆ P)
(` U) ⌣? (` U) = yes ⌣U
(` U) ⌣? (` (T₁ ⇒ T₂)) = no (λ ())
(` U) ⌣? (` (T₁ ⊗ T₂)) = no (λ ())
(` U) ⌣? (` (T₁ ⊕ T₂)) = no (λ ())
(` (T₁ ⇒ T₂)) ⌣? (` U) = no (λ ())
(` (T₁ ⇒ T₂)) ⌣? (` (T₃ ⇒ T₄)) = yes ⌣⇒
(` (T₁ ⇒ T₂)) ⌣? (` (T₃ ⊗ T₄)) = no (λ ())
(` (T₁ ⇒ T₂)) ⌣? (` (T₃ ⊕ T₄)) = no (λ ())
(` (T₁ ⊗ T₂)) ⌣? (` U) = no (λ ())
(` (T₁ ⊗ T₂)) ⌣? (` (T₃ ⇒ T₄)) = no (λ ())
(` (T₁ ⊗ T₂)) ⌣? (` (T₃ ⊗ T₄)) = yes ⌣⊗
(` (T₁ ⊗ T₂)) ⌣? (` (T₃ ⊕ T₄)) = no (λ ())
(` (T₁ ⊕ T₂)) ⌣? (` U) = no (λ ())
(` (T₁ ⊕ T₂)) ⌣? (` (T₃ ⇒ T₄)) = no (λ ())
(` (T₁ ⊕ T₂)) ⌣? (` (T₃ ⊗ T₄)) = no (λ ())
(` (T₁ ⊕ T₂)) ⌣? (` (T₃ ⊕ T₄)) = yes ⌣⊕
  
