module Utilities where
open import Data.Nat using (ℕ; suc; zero)

repeat : {A : Set} → ℕ → (A → A) → A → A
repeat zero f x = x
repeat (suc n) f x = repeat n f (f x)

