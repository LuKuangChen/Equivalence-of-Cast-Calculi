module Error where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Error (Label : Set) (A : Set) : Set where
  return : (v : A) → Error Label A
  raise : (l : Label) → Error Label A

Handler : ∀ (Label A B : Set) → Set
Handler Label A B = A → Error Label B

_>>=_ : ∀ {L A B}
  → Error L A
  → Handler L A B
  → Error L B
return x >>= h = h x
raise l >>= h = raise l

>>=-assoc : ∀ {L A B C}
  → (r : Error L A)
  → (f : Handler L A B)
  → (g : Handler L B C)
  → (r >>= f) >>= g
    ≡
    r >>= λ v → (f v) >>= g
>>=-assoc (return v) f g = refl
>>=-assoc (raise l) f g = refl

>>=-return : ∀ {L A}
  → (r : Error L A)
  → r >>= return ≡ r
>>=-return (return v) = refl
>>=-return (raise l) = refl

_>=>_ : ∀ {L A B C}
  → Handler L A B
  → Handler L B C
  → Handler L A C
(f >=> g) x = f x >>= g
