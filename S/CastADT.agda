open import Types
-- open import X.BlameStrategies using (BlameStrategy)

module S.CastADT
  (Label : Set)
--  (BS : BlameStrategy Label)
  (Injectable : PreType → Set)
  where

-- open BlameStrategy BS using (Injectable)

open import Variables
open import Terms Label
open import Error Label
open import Cast Label using (it) renaming (Cast to SrcCast)
import S.Values

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)

record CastADT : Set₁ where
  open S.Values Label Injectable
  field
    Cast : Type → Type → Set

    mk-cast : ∀ {S T} → SrcCast S T → Cast S T
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

-- basic properties of CastADT
record CastADTBasic (CADT : CastADT) : Set₁ where
  open CastADT CADT
  open S.Values Label Injectable Cast
  field
    lem-apply-seq : ∀ {T1 T2 T3}
      → (v : Val T1)
      → (c1 : Cast T1 T2)
      → (c2 : Cast T2 T3)
      --------------------
      → apply-cast v (seq c1 c2) ≡ (apply-cast v c1) >>= (λ u → apply-cast u c2)

    lem-apply-id : ∀ {T}
      → (v : Val T)  
      -----------------------------
      → apply-cast v (id T) ≡ just v

-- only required for the bisim between D and S(C)
record CastIdIsId (CR : CastADT) : Set where
  open CastADT CR
  field
    lem-cast-id-is-id : ∀ l T →
      mk-cast (it l T T) ≡ id T

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
