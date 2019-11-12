open import Types

module S.CastADT
  (Label : Set)
  (Injectable : PreType → Set)
  where

open import Variables
open import Terms Label
open import S.Values Label Injectable


open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)

record CastADT : Set₁ where
  field
    Cast : Type → Type → Set

    mk-cast : Label → (T1 T2 : Type) → Cast T1 T2
    id : (T : Type) → Cast T T
    seq : ∀ {T1 T2 T3}
      → Cast T1 T2
      → Cast T2 T3
      -----
      → Cast T1 T3
    apply-cast : ∀ {T1 T2}
      → Val Cast T1
      → Cast T1 T2
      -----
      → CastResult Cast T2


-- only required for the bisim between D and S(C)
record CastIdIsId (CR : CastADT) : Set where
  open CastADT CR
  field
    lem-cast-id-is-id : ∀ l T →
      mk-cast l T T ≡ id T

record Monoid (CR : CastADT) : Set where
  open CastADT CR
  field
    lem-id-l : ∀ {T1 T2}
      → (c : Cast T1 T2)
      ---
      → seq (id T1) c ≡ c
    lem-id-r : ∀ {T1 T2}
      → (c : Cast T1 T2)
      ---
      → seq c (id T2) ≡ c
    lem-assoc : ∀ {T1 T2 T3 T4}
      → (c1 : Cast T1 T2)
      → (c2 : Cast T2 T3)
      → (c3 : Cast T3 T4)
      ---
      → seq (seq c1 c2) c3 ≡ seq c1 (seq c2 c3)
