module Coercion (Label : Set) where

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
    
data Head (P : PreType) : Type → Set where
  ε : Head P (` P)
  ¿ : (l : Label) → Head P ⋆

data Tail (P : PreType) : Type → Set where
  ε : Tail P (` P)
  ¡ : Tail P ⋆
  ⊥ : ∀ {B} → (l : Label) → Tail P B

mutual
  data Coercion : Type → Type → Set where
    id⋆ : Coercion ⋆ ⋆
    ↷ : ∀ {A B P Q} →
        (h : Head P A)(b : Body P Q)(t : Tail Q B) →
        Coercion A B

  data Body : PreType → PreType → Set where
    U : Body U U
    _⇒_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Coercion S2 S1) →
      (c₂ : Coercion T1 T2) →
      Body (S1 ⇒ T1) (S2 ⇒ T2)
    _⊗_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Coercion S1 S2) →
      (c₂ : Coercion T1 T2) →
      Body (S1 ⊗ T1) (S2 ⊗ T2)
    _⊕_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Coercion S1 S2) →
      (c₂ : Coercion T1 T2) →
      Body (S1 ⊕ T1) (S2 ⊕ T2)

mutual
  seq : Label → ∀ {T1 T2 T3 T4} → Coercion T1 T2 → Coercion T3 T4 →
    Coercion T1 T4
  -- here ℓ is the label that associates with all casts in the middle
  seq ℓ id⋆ id⋆ =
    id⋆
  seq ℓ id⋆ (↷ ε b t) =
    ↷ (¿ ℓ) b t
  seq ℓ id⋆ (↷ (¿ l) b t) =
    ↷ (¿ l) b t
  seq ℓ (↷ h b (⊥ l)) c2 =
    ↷ h b (⊥ l)
  -- now t is either ε or ¿
  seq ℓ (↷ h b t) id⋆ =
    ↷ h b ¡
  seq ℓ (↷ h b t) (↷ ε b₁ t₁) =
    seq-body ℓ h b b₁ t₁
  seq ℓ (↷ h b t) (↷ (¿ l) b₁ t₁) =
    seq-body l h b b₁ t₁
  
  seq-body : ∀ {T1 T2 P1 P2 P3 P4} → Label →
    Head P1 T1 → Body P1 P2 → Body P3 P4 → Tail P4 T2 →
    Coercion T1 T2
  seq-body ℓ h U U t =
    ↷ h U t
  seq-body ℓ h (c₁ ⇒ c₂) (c₃ ⇒ c₄) t =
    ↷ h (seq ℓ c₃ c₁ ⇒ seq ℓ c₂ c₄) t
  seq-body ℓ h (c₁ ⊗ c₂) (c₃ ⊗ c₄) t =
    ↷ h (seq ℓ c₁ c₃ ⊗ seq ℓ c₂ c₄) t
  seq-body ℓ h (c₁ ⊕ c₂) (c₃ ⊕ c₄) t =
    ↷ h (seq ℓ c₁ c₃ ⊕ seq ℓ c₂ c₄) t
  seq-body ℓ h b b₁ t =
    ↷ h b (⊥ ℓ)

user-seq : ∀ {T1 T2 T3} → Coercion T1 T2 → Coercion T2 T3 → Coercion T1 T3
user-seq id⋆ id⋆ =
  id⋆
user-seq id⋆ (↷ h b t) =
  ↷ h b t
user-seq (↷ h b (⊥ l)) c2 =
  ↷ h b (⊥ l)
user-seq (↷ h U ε) (↷ ε U t) =
  ↷ h U t
user-seq (↷ h (c₁ ⇒ c₂) ε) (↷ ε (c₃ ⇒ c₄) t) =
  ↷ h (user-seq c₃ c₁ ⇒ user-seq c₂ c₄) t
user-seq (↷ h (c₁ ⊗ c₂) ε) (↷ ε (c₃ ⊗ c₄) t) =
  ↷ h (user-seq c₁ c₃ ⊗ user-seq c₂ c₄) t
user-seq (↷ h (c₁ ⊕ c₂) ε) (↷ ε (c₃ ⊕ c₄) t) =
  ↷ h (user-seq c₁ c₃ ⊕ user-seq c₂ c₄) t
user-seq (↷ h b ¡) id⋆ =
  ↷ h b ¡
user-seq (↷ h b ¡) (↷ (¿ l) b₁ t) =
  seq-body l h b b₁ t
