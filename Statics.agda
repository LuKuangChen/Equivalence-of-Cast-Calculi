module Statics where

open import Label
open import Type

<<<<<<< HEAD:Terms.agda
open import Variables
open import Cast Label
=======
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

infix  4 _∋_

data _∋_ : Context → Type → Set where

  zero : ∀ {Γ A}
      ----------
    → Γ , A ∋ A

  suc : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A
>>>>>>> 3a6456f2895084c56b39ebb3004d74c927a89071:Statics.agda

infix  4 _⊢_

data _⊢_ : Context → Type → Set where
                                
  var : ∀ {Γ T}
    → (x : Γ ∋ T)
    --------
    → Γ ⊢ T
     
  #t : ∀ {Γ}
    --------
    → Γ ⊢ ` B

  #f : ∀ {Γ}
    --------
    → Γ ⊢ ` B

  if : ∀ {Γ T}
    → Γ ⊢ ` B
    → Γ ⊢ T
    → Γ ⊢ T
    --------
    → Γ ⊢ T

  lam : ∀ {Γ T1 T2}
    → (e : Γ , T1 ⊢ T2)
    -------------
    → Γ ⊢ ` T1 ⇒ T2
  
  app : ∀ {Γ T1 T2}
    → (e1 : Γ ⊢ ` T1 ⇒ T2)
    → (e2 : Γ ⊢ T1)
    --------
    → Γ ⊢ T2

  cons : ∀ {Γ T1 T2}
    → (e1 : Γ ⊢ T1)
    → (e2 : Γ ⊢ T2)
    -----
    → Γ ⊢ (` T1 ⊗ T2)
  
  _⟨_⟩ : ∀ {Γ T S}
    → (e : Γ ⊢ S)
    → (c : Cast S T)
    --------
    → Γ ⊢ T

  blame : ∀ {Γ T}
    → (l : Label)
    ---
    → Γ ⊢ T

