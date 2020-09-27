module Error where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infixl 30 _>>=_
infixl 30 _>=>_

data Error (Label : Set) (A : Set) : Set where
  raise  : (l : Label) → Error Label A
  return : (v : A) → Error Label A

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
    r >>= λ v → (f v >>= g)
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

>=>-assoc : ∀ {L A B C D}
  → (f : Handler L A B)
  → (g : Handler L B C)
  → (h : Handler L C D)
  → (∀ x → ((f >=> g) >=> h) x ≡ (f >=> (g >=> h)) x)
>=>-assoc f g h x = >>=-assoc (f x) g h

>=>->>= : ∀ {L A B C}
  → (r : Error L A)
  → (f : Handler L A B)
  → (g : Handler L B C)
  → r >>= (f >=> g) ≡ (r >>= f) >>= g
>=>->>= (raise l)  f g = refl
>=>->>= (return v) f g = refl

drop-after-raise : ∀ {L A B C}
  → (r : Error L A)
  → (l : L)
  → (f : Handler L B C)
  → (r >>= λ _ → raise l) >>= f
    ≡ 
    (r >>= λ _ → raise l)
drop-after-raise (raise l') l f = refl
drop-after-raise (return v) l f = refl

>>=-extensionality : ∀ {L A B}
  → (r : Error L A)
  → {f g : Handler L A B}
  → (f≡g : ∀ x → f x ≡ g x)
  → (r >>= f) ≡ (r >>= g)
>>=-extensionality (raise l)  f≡g = refl
>>=-extensionality (return v) f≡g = f≡g v
