module Variables where

open import Types

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

infix  4 _∋_
infix 99 _,_

data _∋_ : Context → Type → Set where

  zero : ∀ {Γ A}
      ----------
    → Γ , A ∋ A

  suc  : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A

extL :  Type → Context → Context
extL t ∅ = ∅ , t
extL t (C , x) = (extL t C) , x
