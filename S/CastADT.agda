open import Types

module S.CastADT
  (Label : Set)
  (Injectable : PreType → Set)
  where

open import Error using (_>=>_; Error; return)
open import Cast Label renaming (Cast to SrcCast)
import S.Values using (Value)

open import Relation.Binary.PropositionalEquality using (_≡_)

record CastADT : Set₁ where
  open S.Values Label Injectable
  field
    Cast : Type → Type → Set

    id : (T : Type) → Cast T T
    ⌈_⌉ : ∀ {S T} → SrcCast S T → Cast S T
    _⨟_ : ∀ {T1 T2 T3}
      → Cast T1 T2
      → Cast T2 T3
      -----
      → Cast T1 T3
    ⟦_⟧ : ∀ {T1 T2}
      → Cast T1 T2
      -----
      → Value Cast T1
      → Error Label (Value Cast T2)

record CastADTBasic (CADT : CastADT) : Set₁ where
  open CastADT CADT
  open S.Values Label Injectable Cast
  field
    lem-id : ∀ {T}
      → ∀ v
      → ⟦ id T ⟧ v ≡ return v
    lem-seq : ∀ {T1 T2 T3}
      → (c1 : Cast T1 T2)
      → (c2 : Cast T2 T3)
      → ∀ v
      --------------------
      → ⟦ c1 ⨟ c2 ⟧ v ≡ (⟦ c1 ⟧ >=> ⟦ c2 ⟧) v
