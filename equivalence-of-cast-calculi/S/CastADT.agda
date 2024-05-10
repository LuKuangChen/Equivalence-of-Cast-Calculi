open import equivalence-of-cast-calculi.Type

module equivalence-of-cast-calculi.S.CastADT
  (Label : Set)
  (Injectable : PreType → Set)
  where

open import equivalence-of-cast-calculi.LabelUtilities Label
open import equivalence-of-cast-calculi.Error using (_>=>_; Error; return)
open import equivalence-of-cast-calculi.Cast Label renaming (Cast to SrcCast)
open import equivalence-of-cast-calculi.S.Value Label Injectable

open import Relation.Binary.PropositionalEquality using (_≡_)

record CastADT : Set₁ where
  field
    Cast : Type → Type → Set

    -- compile a type to the representation of an identity cast
    id : (T : Type) → Cast T T

    -- compile a cast to its representation
    ⌈_⌉ : ∀ {S T} → SrcCast S T → Cast S T

    -- compose two cast representations
    _⨟_ : ∀ {T1 T2 T3}
      → Cast T1 T2
      → Cast T2 T3
      -----
      → Cast T1 T3

    -- apply a cast
    ⟦_⟧ : ∀ {T1 T2}
      → Cast T1 T2
      -----
      → Value Cast T1
      → Error Label×Polarity (Value Cast T2)

    -- that identity cast is indeed identity
    lem-id : ∀ T v
      → ⟦ id T ⟧ v ≡ return v

    -- that cast composition is indeed composition
    lem-seq : ∀ {T1 T2 T3}
      → (c1 : Cast T1 T2)
      → (c2 : Cast T2 T3)
      → ∀ v
      --------------------
      → ⟦ c1 ⨟ c2 ⟧ v ≡ (⟦ c1 ⟧ >=> ⟦ c2 ⟧) v
