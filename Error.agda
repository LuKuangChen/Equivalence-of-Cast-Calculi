module Error
  (Label : Set)
  where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Error (A : Set) : Set where
  succ : (v : A) → Error A
  fail : (l : Label) → Error A

Handler : (A B : Set) → Set
Handler A B = A → Error B

_>>=_ : ∀ {A B}
  → Error A
  → Handler A B
  → Error B
succ x >>= h = h x
fail l >>= h = fail l

>>=assoc : ∀ {A B C}
  → (r : Error A)
  → (f : Handler A B)
  → (g : Handler B C)
  → (r >>= f) >>= g
    ≡
    r >>= λ v → (f v) >>= g
>>=assoc (succ v) f g = refl
>>=assoc (fail l) f g = refl

>>=succ : ∀ {A}
  → (r : Error A)
  → r >>= succ ≡ r
>>=succ (succ v) = refl
>>=succ (fail l) = refl
