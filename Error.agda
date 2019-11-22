module Error
  (Label : Set)
  where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Error (A : Set) : Set where
  just : (v : A) → Error A
  error : (l : Label) → Error A

Handler : (A B : Set) → Set
Handler A B = A → Error B

_>>=_ : ∀ {A B}
  → Error A
  → Handler A B
  → Error B
just x >>= h = h x
error l >>= h = error l

>>=assoc : ∀ {A B C}
  → (r : Error A)
  → (f : Handler A B)
  → (g : Handler B C)
  → (r >>= f) >>= g
    ≡
    r >>= λ v → (f v) >>= g
>>=assoc (just v) f g = refl
>>=assoc (error l) f g = refl

>>=just : ∀ {A}
  → (r : Error A)
  → r >>= just ≡ r
>>=just (just v) = refl
>>=just (error l) = refl
