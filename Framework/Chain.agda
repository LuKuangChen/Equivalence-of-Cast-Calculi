module Chain where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

data Chain {A : Set} (Link : A → A → Set) : A → A → Set where
  []  : ∀ {a} → Chain Link a a
  _∷_ : ∀ {a b c} → Link a b → Chain Link b c → Chain Link a c

_++_ : ∀ {A Link} → {a b c : A} → Chain Link a b → Chain Link b c → Chain Link a c
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀ {A Link} → {a b c d : A}
  → (xs : Chain Link a b)
  → (ys : Chain Link b c)
  → (zs : Chain Link c d)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-identityˡ : ∀ {A Link} → {a b : A}
  → (xs : Chain Link a b)
  → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A Link} → {a b : A}
  → (xs : Chain Link a b)
  → xs ++ [] ≡ xs
++-identityʳ []       = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)
