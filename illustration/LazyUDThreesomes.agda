module illustration.LazyUDThreesomes (Label : Set) where

open import equivalence-of-cast-calculi.LazyUDCastADT Label
  renaming (negate-label×polarity to neg)

open import Data.Empty using () renaming (⊥ to Empty)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Product using (Σ-syntax; ∃-syntax; proj₁; proj₂; _×_; _,_)
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
  using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

{-
Siek, Jeremy G., and Philip Wadler. "Threesomes, with and without blame."
ACM Sigplan Notices 45.1 (2010): 365-376.
-}

{-
Ground Types are isomorphic to Type Constructors in the obvious way. To make
proof easier, we use type constructors in place of ground types.
-}

data OptionalLabel (op : TypeOp) : Type → (Vec Type (arity op)) → Set where
  ⁇ : (l : Label×Polarity) → OptionalLabel op * (replicate *)
  ε : ∀ {Ts} → OptionalLabel op (` op · Ts) Ts

data Tail (op : TypeOp) : (Vec Type (arity op)) → Type → Set where
  ‼ : Tail op (replicate *) *
  ε : ∀ {Ts} → Tail op Ts (` op · Ts)

data LabeledType : Type → Type → Set
data LabeledPreType : (op : TypeOp) → (Ss Ts : Vec Type (arity op)) → Set

data LabeledType where

  * : LabeledType * *

  ⊥ : ∀ {T S}
    → (l : Label×Polarity)
    → (G : TypeOp)
    → ∀ {Ss}
    → (p : OptionalLabel G S Ss)
    → LabeledType S T

  ^ : ∀ {S G Ss Ts T}
    → (P̂ : LabeledPreType G Ss Ts)
    → (p : OptionalLabel G S Ss)
    → {t : Tail G Ts T}
      ---------------
    → LabeledType S T

data LabeledPreType where

  B̂ : LabeledPreType `B [] []

  _⇒̂_ : ∀ {S1 S2 T1 T2}
    → (Ŝ : LabeledType S2 S1)
    → (T̂ : LabeledType T1 T2)
    → LabeledPreType `⇒ (S1 ∷ T1 ∷ []) (S2 ∷ T2 ∷ [])

  _⊗̂_ : ∀ {S1 S2 T1 T2}
    → (Ŝ : LabeledType S1 S2)
    → (T̂ : LabeledType T1 T2)
    → LabeledPreType `⊗ (S1 ∷ T1 ∷ []) (S2 ∷ T2 ∷ [])

-- In real implementation, one should use the gnd function
-- But here we use quick-gnd to simplify the proof.
-- Functions gnd and quick-gnd are equivalent, as shown in gnd-faithful

quick-gnd : ∀ {op Ss Ts} → (P̂ : LabeledPreType op Ss Ts) → TypeOp
quick-gnd {op} P̂ = op

gnd : ∀ {op Ss Ts} → (P̂ : LabeledPreType op Ss Ts) → TypeOp
gnd B̂ = `B
gnd (Ŝ ⇒̂ T̂) = `⇒
gnd (Ŝ ⊗̂ T̂) = `⊗

gnd-faithful : ∀ {op Ss Ts} → (P̂ : LabeledPreType op Ss Ts) → gnd P̂ ≡ quick-gnd P̂
gnd-faithful B̂ = refl
gnd-faithful (Ŝ ⇒̂ T̂) = refl
gnd-faithful (Ŝ ⊗̂ T̂) = refl

impossible-tail : ∀ {G H Ss Ts}
  → Tail G  Ss (` H · Ts)
  → ¬ G ≡ H
  → Empty
impossible-tail ε ¬G≡H = ¬G≡H refl

no-gap-at-all : ∀ {G Ss T Ts}
  → Tail G Ss T
  → OptionalLabel G T Ts
  → Ss ≡ Ts
no-gap-at-all ‼ (⁇ l) = refl
no-gap-at-all ε ε = refl

_∘_ : ∀ {T1 T2 T3} → LabeledType T2 T3 → LabeledType T1 T2 → LabeledType T1 T3
T̂ ∘ *         = T̂
T̂ ∘ ⊥ m G p   = ⊥ m G p
* ∘ Ŝ@(^ P̂ p) = Ŝ
⊥ m H q     ∘ ^ P̂ p with quick-gnd P̂ ≟op H
⊥ m H q     ∘ ^ P̂ p | yes refl = ⊥ m H p
⊥ m H (⁇ l) ∘ ^ P̂ p | no ¬G≡H  = ⊥ l (quick-gnd P̂) p
⊥ m H ε     ∘ ^ P̂ p {t} | no ¬G≡H  = ⊥-elim (impossible-tail t ¬G≡H)
^ Q̂ q     ∘ ^ P̂ p {t} with quick-gnd P̂ ≟op quick-gnd Q̂
^ Q̂ (⁇ m) ∘ ^ P̂ p {t} | no ¬G≡H = ⊥ m (quick-gnd P̂) p
^ Q̂ ε     ∘ ^ P̂ p {t} | no ¬G≡H = ⊥-elim (impossible-tail t ¬G≡H)
^ Q̂ q     ∘ ^ P̂ p {t} | yes refl with no-gap-at-all t q
^ B̂         q {s} ∘ ^ B̂         p {t} | yes refl | refl = ^ B̂ p {s}
^ (Ŝ₂ ⇒̂ T̂₂) q {s} ∘ ^ (Ŝ₁ ⇒̂ T̂₁) p {t} | yes refl | refl
  = ^ ((Ŝ₁ ∘ Ŝ₂) ⇒̂ (T̂₂ ∘ T̂₁)) p {s}
^ (Ŝ₂ ⊗̂ T̂₂) q {s} ∘ ^ (Ŝ₁ ⊗̂ T̂₁) p {t} | yes refl | refl
  = ^ ((Ŝ₂ ∘ Ŝ₁) ⊗̂ (T̂₂ ∘ T̂₁)) p {s}

fail-left : ∀ {T1 T2} l G {Ss}
  → (p : OptionalLabel G T2 Ss)
  → (T̂ : LabeledType T1 T2)
  → ∃[ l' ]
    (∃[ G' ]
    (∃[ Ss ]
    (Σ[ p' ∈ OptionalLabel G' T1 Ss ]
    (∀ {T3} → (⊥ {T3} l G p ∘ T̂) ≡ ⊥ {T3} l' G' p' ))))
fail-left l G p * = _ , _ , _ , _ , refl
fail-left l G p (⊥ l₁ G₁ p₁) = _ , _ , _ , _ , refl
fail-left l G p (^ P̂ p₁) with quick-gnd P̂ ≟op G
fail-left l G p (^ P̂ p₁) | yes refl = _ , _ , _ , _ , refl
fail-left l G (⁇ l₁) (^ P̂ p₁) | no ¬p = _ , _ , _ , _ , refl
fail-left l G ε (^ P̂ p₁ {t}) | no ¬p = ⊥-elim (impossible-tail t ¬p)

dyn-left : ∀ {T}
  → (T̂ : LabeledType T *)
  → * ∘ T̂ ≡ T̂
dyn-left * = refl
dyn-left (⊥ l G p) = refl
dyn-left (^ P̂ p) = refl

dec-yes : {A : Set}{a : A}(a≟a : Dec (a ≡ a)) → ∃[ p ](a≟a ≡ yes p)
dec-yes (yes p) = p , refl
dec-yes (no ¬p) = ⊥-elim (¬p refl)

∘-assoc : ∀ {T1 T2 T3 T4}
  → (T̂₃ : LabeledType T3 T4)
  → (T̂₂ : LabeledType T2 T3)
  → (T̂₁ : LabeledType T1 T2)
  → (T̂₃ ∘ (T̂₂ ∘ T̂₁)) ≡ ((T̂₃ ∘ T̂₂) ∘ T̂₁)
∘-assoc T̂₃ T̂₂ * = refl
∘-assoc T̂₃ T̂₂ (⊥ l₁ G₁ p₁) = refl
∘-assoc T̂₃ * (^ P̂₁ p₁) = refl
∘-assoc {T3 = T3}{T4 = T4} T̂₃ T̂₂@(⊥ l₂ G₂ p₂) T̂₁@(^ P̂₁ p₁)
  with fail-left l₂ G₂ p₂ T̂₁
... | _ , _ , _ , _ , eq
  rewrite eq {T3} | eq {T4} = refl
∘-assoc * T̂₂@(^ P̂₂ p₂) T̂₁@(^ P̂₁ p₁) rewrite dyn-left (T̂₂ ∘ T̂₁) = refl
∘-assoc (⊥ l₃ G₃ p₃) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  with quick-gnd P̂₁ ≟op quick-gnd P̂₂
∘-assoc (⊥ l₃ G₃ p₃) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁}) | yes G₁≡G₂
  with quick-gnd P̂₂ ≟op G₃
∘-assoc (⊥ l₃ G₃ p₃) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁}) | yes refl | yes refl
  with no-gap-at-all t₁ p₂
∘-assoc (⊥ l₃ .`B p₃) (^ B̂ p₂ {t₂}) (^ B̂ p₁ {t₁})
  | yes refl | yes refl | refl = refl
∘-assoc (⊥ l₃ .`⇒ p₃) (^ (Ŝ₁ ⇒̂ T̂₁) p₂ {t₂}) (^ (Ŝ ⇒̂ T̂) p₁ {t₁})
  | yes refl | yes refl | refl = refl
∘-assoc (⊥ l₃ .`⊗ p₃) (^ (Ŝ₁ ⊗̂ T̂₁) p₂ {t₂}) (^ (Ŝ ⊗̂ T̂) p₁ {t₁})
  | yes refl | yes refl | refl = refl
∘-assoc (⊥ l₃ G₃ (⁇ l)) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  | yes G₁≡G₂ | no ¬G₂≡G₃
  with quick-gnd P̂₁ ≟op quick-gnd P̂₂
∘-assoc (⊥ l₃ G₃ (⁇ l)) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  | yes refl | no ¬G₂≡G₃ | yes refl
  with no-gap-at-all t₁ p₂
∘-assoc (⊥ l₃ `B (⁇ l)) (^ B̂ p₂ {t₂}) (^ B̂ p₁ {t₁})
  | yes refl | no ¬G₂≡G₃ | yes refl | refl = ⊥-elim (¬G₂≡G₃ refl)
∘-assoc (⊥ l₃ `⊗ (⁇ l)) (^ B̂ p₂ {t₂}) (^ B̂ p₁ {t₁})
  | yes refl | no ¬G₂≡G₃ | yes refl | refl = refl
∘-assoc (⊥ l₃ `⇒ (⁇ l)) (^ B̂ p₂ {t₂}) (^ B̂ p₁ {t₁})
  | yes refl | no ¬G₂≡G₃ | yes refl | refl = refl
∘-assoc (⊥ l₃ `B (⁇ l)) (^ (Ŝ₂ ⇒̂ T̂₂) p₂ {t₂}) (^ (Ŝ₁ ⇒̂ T̂₁) p₁ {t₁})
  | yes refl | no ¬G₂≡G₃ | yes refl | refl = refl
∘-assoc (⊥ l₃ `⊗ (⁇ l)) (^ (Ŝ₂ ⇒̂ T̂₂) p₂ {t₂}) (^ (Ŝ₁ ⇒̂ T̂₁) p₁ {t₁})
  | yes refl | no ¬G₂≡G₃ | yes refl | refl = refl
∘-assoc (⊥ l₃ `⇒ (⁇ l)) (^ (Ŝ₂ ⇒̂ T̂₂) p₂ {t₂}) (^ (Ŝ₁ ⇒̂ T̂₁) p₁ {t₁})
  | yes refl | no ¬G₂≡G₃ | yes refl | refl = ⊥-elim (¬G₂≡G₃ refl)
∘-assoc (⊥ l₃ `B (⁇ l)) (^ (Ŝ₂ ⊗̂ T̂₂) p₂ {t₂}) (^ (Ŝ₁ ⊗̂ T̂₁) p₁ {t₁})
  | yes refl | no ¬G₂≡G₃ | yes refl | refl = refl
∘-assoc (⊥ l₃ `⊗ (⁇ l)) (^ (Ŝ₂ ⊗̂ T̂₂) p₂ {t₂}) (^ (Ŝ₁ ⊗̂ T̂₁) p₁ {t₁})
  | yes refl | no ¬G₂≡G₃ | yes refl | refl = ⊥-elim (¬G₂≡G₃ refl)
∘-assoc (⊥ l₃ `⇒ (⁇ l)) (^ (Ŝ₂ ⊗̂ T̂₂) p₂ {t₂}) (^ (Ŝ₁ ⊗̂ T̂₁) p₁ {t₁})
  | yes refl | no ¬G₂≡G₃ | yes refl | refl = refl
∘-assoc (⊥ l₃ G₃ (⁇ l)) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  | yes G₁≡G₂ | no ¬G₂≡G₃ | no ¬G₁≡G₂' = ⊥-elim (¬G₁≡G₂' G₁≡G₂)
∘-assoc (⊥ l₃ G₃ ε) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  | yes G₁≡G₂ | no ¬G₂≡G₃ = ⊥-elim (impossible-tail t₂ ¬G₂≡G₃)
∘-assoc (⊥ l₃ G₃ p₃) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂
  with quick-gnd P̂₂ ≟op G₃
∘-assoc (⊥ l₃ G₃ p₃) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂
  | yes refl
  with quick-gnd P̂₁ ≟op quick-gnd P̂₂
∘-assoc (⊥ l₃ G₃ p₃) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂ | yes refl
  | yes G₁≡G₂' = ⊥-elim (¬G₁≡G₂ G₁≡G₂')
∘-assoc (⊥ l₃ G₃ p₃) (^ P̂₂ (⁇ l) {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂ | yes refl | no ¬G₁≡G₂' = refl
∘-assoc (⊥ l₃ G₃ p₃) (^ P̂₂ ε {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂ | yes refl | no ¬G₁≡G₂' = ⊥-elim (impossible-tail t₁ ¬G₁≡G₂)
∘-assoc (⊥ l₃ G₃ (⁇ l)) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂ | no ¬G₂≡G₃
  with quick-gnd P̂₁ ≟op quick-gnd P̂₂
∘-assoc (⊥ l₃ G₃ (⁇ l)) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂ | no ¬G₂≡G₃ | yes G₁≡G₂' = ⊥-elim (¬G₁≡G₂ G₁≡G₂')
∘-assoc (⊥ l₃ G₃ (⁇ l)) (^ P̂₂ (⁇ l₁) {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂ | no ¬G₂≡G₃ | no ¬G₁≡G₂' = refl
∘-assoc (⊥ l₃ G₃ (⁇ l)) (^ P̂₂ ε {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂ | no ¬G₂≡G₃ | no ¬G₁≡G₂' = ⊥-elim (impossible-tail t₁ ¬G₁≡G₂)
∘-assoc (⊥ l₃ G₃ ε) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂ | no ¬G₂≡G₃ = ⊥-elim (impossible-tail t₂ ¬G₂≡G₃)
-- ∘-assoc (^ P̂₃ p₃) (^ P̂₂ p₂) (^ P̂₁ p₁) = {!!}
∘-assoc (^ P̂₃ p₃) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  with quick-gnd P̂₁ ≟op quick-gnd P̂₂
∘-assoc (^ P̂₃ p₃) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁}) | yes refl
  with no-gap-at-all t₁ p₂
∘-assoc (^ B̂ p₃) (^ B̂ p₂ {t₂}) (^ B̂ p₁ {t₁}) | yes refl | refl
  with no-gap-at-all t₂ p₃
... | refl
  with no-gap-at-all t₁ p₂
... | refl = refl
∘-assoc (^ (Ŝ ⇒̂ T̂) (⁇ l)) (^ B̂ p₂ {t₂}) (^ B̂ p₁ {t₁}) | yes refl | refl = refl
∘-assoc (^ (Ŝ ⊗̂ T̂) (⁇ l)) (^ B̂ p₂ {t₂}) (^ B̂ p₁ {t₁}) | yes refl | refl = refl
∘-assoc (^ B̂ (⁇ l)) (^ (Ŝ₂ ⇒̂ T̂₂) p₂ {t₂}) (^ (Ŝ₁ ⇒̂ T̂₁) p₁ {t₁})
  | yes refl | refl = refl
∘-assoc (^ (Ŝ₃ ⇒̂ T̂₃) p₃) (^ (Ŝ₂ ⇒̂ T̂₂) p₂ {t₂}) (^ (Ŝ₁ ⇒̂ T̂₁) p₁ {t₁})
  | yes refl | refl
  with no-gap-at-all t₂ p₃
... | refl
  with no-gap-at-all t₁ p₂
... | refl
  rewrite ∘-assoc Ŝ₁ Ŝ₂ Ŝ₃ | ∘-assoc T̂₃ T̂₂ T̂₁ = refl
∘-assoc (^ (Ŝ ⊗̂ T̂) (⁇ l)) (^ (Ŝ₂ ⇒̂ T̂₂) p₂ {t₂}) (^ (Ŝ₁ ⇒̂ T̂₁) p₁ {t₁})
  | yes refl | refl = refl
∘-assoc (^ B̂ (⁇ l)) (^ (Ŝ₂ ⊗̂ T̂₂) p₂ {t₂}) (^ (Ŝ₁ ⊗̂ T̂₁) p₁ {t₁})
  | yes refl | refl = refl
∘-assoc (^ (Ŝ ⇒̂ T̂) (⁇ l)) (^ (Ŝ₂ ⊗̂ T̂₂) p₂ {t₂}) (^ (Ŝ₁ ⊗̂ T̂₁) p₁ {t₁})
  | yes refl | refl = refl
∘-assoc (^ (Ŝ₃ ⊗̂ T̂₃) p₃) (^ (Ŝ₂ ⊗̂ T̂₂) p₂ {t₂}) (^ (Ŝ₁ ⊗̂ T̂₁) p₁ {t₁})
  | yes refl | refl
  with no-gap-at-all t₂ p₃
... | refl
  with no-gap-at-all t₁ p₂
... | refl
  rewrite ∘-assoc Ŝ₃ Ŝ₂ Ŝ₁ | ∘-assoc T̂₃ T̂₂ T̂₁ = refl
∘-assoc (^ P̂₃ p₃) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁}) | no ¬G₁≡G₂
  with quick-gnd P̂₂ ≟op quick-gnd P̂₃
∘-assoc (^ P̂₃ p₃) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁}) | no ¬G₁≡G₂ | yes refl
  with no-gap-at-all t₂ p₃
∘-assoc (^ B̂ p₃) (^ B̂ p₂ {t₂}) (^ B̂ p₁ {t₁}) | no ¬G₁≡G₂
  | yes refl | refl = ⊥-elim (¬G₁≡G₂ refl)
∘-assoc (^ B̂ p₃) (^ B̂ (⁇ l) {t₂}) (^ (Ŝ ⇒̂ T̂) p₁ {t₁})
  | no ¬G₁≡G₂ | yes refl | refl = refl
∘-assoc (^ B̂ p₃) (^ B̂ (⁇ l) {t₂}) (^ (Ŝ ⊗̂ T̂) p₁ {t₁})
  | no ¬G₁≡G₂ | yes refl | refl = refl
∘-assoc (^ (Ŝ₃ ⇒̂ T̂₃) p₃) (^ (Ŝ₂ ⇒̂ T̂₂) (⁇ l) {t₂}) (^ B̂ p₁ {t₁})
  | no ¬G₁≡G₂ | yes refl | refl = refl
∘-assoc (^ (Ŝ₃ ⇒̂ T̂₃) p₃) (^ (Ŝ₂ ⇒̂ T̂₂) p₂ {t₂}) (^ (Ŝ ⇒̂ T̂) p₁ {t₁})
  | no ¬G₁≡G₂ | yes refl | refl = ⊥-elim (¬G₁≡G₂ refl)
∘-assoc (^ (Ŝ₃ ⇒̂ T̂₃) p₃) (^ (Ŝ₂ ⇒̂ T̂₂) (⁇ l) {t₂}) (^ (Ŝ ⊗̂ T̂) p₁ {t₁})
  | no ¬G₁≡G₂ | yes refl | refl = refl
∘-assoc (^ (Ŝ₃ ⊗̂ T̂₃) p₃) (^ (Ŝ₂ ⊗̂ T̂₂) (⁇ l) {t₂}) (^ B̂ p₁ {t₁})
  | no ¬G₁≡G₂ | yes refl | refl = refl
∘-assoc (^ (Ŝ₃ ⊗̂ T̂₃) p₃) (^ (Ŝ₂ ⊗̂ T̂₂) (⁇ l) {t₂}) (^ (Ŝ ⇒̂ T̂) p₁ {t₁})
  | no ¬G₁≡G₂ | yes refl | refl = refl
∘-assoc (^ (Ŝ₃ ⊗̂ T̂₃) p₃) (^ (Ŝ₂ ⊗̂ T̂₂) p₂ {t₂}) (^ (Ŝ ⊗̂ T̂) p₁ {t₁})
  | no ¬G₁≡G₂ | yes refl | refl = ⊥-elim (¬G₁≡G₂ refl)
∘-assoc (^ P̂₃ (⁇ l)) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂ | no ¬G₂≡G₃
  with quick-gnd P̂₁ ≟op quick-gnd P̂₂
... | yes G₁≡G₂' = ⊥-elim (¬G₁≡G₂ G₁≡G₂')
∘-assoc (^ P̂₃ (⁇ l)) (^ P̂₂ (⁇ l₁) {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂ | no ¬G₂≡G₃ | no ¬G₁≡G₂' = refl
∘-assoc (^ P̂₃ (⁇ l)) (^ P̂₂ ε {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂ | no ¬G₂≡G₃ | no ¬G₁≡G₂' = ⊥-elim (impossible-tail t₁ ¬G₁≡G₂)
∘-assoc (^ P̂₃ ε) (^ P̂₂ p₂ {t₂}) (^ P̂₁ p₁ {t₁})
  | no ¬G₁≡G₂ | no ¬G₂≡G₃ = ⊥-elim (impossible-tail t₂ ¬G₂≡G₃)

data Cast : Type → Type → Set where
  _⟹_[_] : ∀ S T
    → (T̂ : LabeledType S T)
    → Cast S T

_⨟_ : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
(T1 ⟹ T2 [ Ŝ ]) ⨟ (.T2 ⟹ T3 [ T̂ ]) = T1 ⟹ T3 [ T̂ ∘ Ŝ ]

id^ : ∀ T → LabeledType T T
id^ * = *
id^ (` B) = ^ B̂ ε {ε}
id^ (` S ⇒ T) = ^ (id^ S ⇒̂ id^ T) ε {ε}
id^ (` S ⊗ T) = ^ (id^ S ⊗̂ id^ T) ε {ε}

id : ∀ T → Cast T T
id T = T ⟹ T [ id^ T ]

mutual
  ⇑ : Label×Polarity → ∀ T → LabeledType T *
  ⇑ l *     = *
  ⇑ l (` B)     = ^ (B̂)             ε {‼}
  ⇑ l (` S ⇒ T) = ^ (⇓ (neg l) S ⇒̂ ⇑ l T) ε {‼}
  ⇑ l (` S ⊗ T) = ^ (⇑ l S ⊗̂ ⇑ l T) ε {‼}

  ⇓ : Label×Polarity → ∀ T → LabeledType * T
  ⇓ l *     = *
  ⇓ l (` B)     = ^ (B̂)               (⁇ l) {ε}
  ⇓ l (` S ⇒ T) = ^ (⇑ (neg l) S ⇒̂ (⇓ l T)) (⁇ l) {ε}
  ⇓ l (` S ⊗ T) = ^ (⇓ l S ⊗̂ (⇓ l T)) (⁇ l) {ε}

⌈_⌉' : ∀ {T1 T2} → SrcCast T1 T2 → LabeledType T1 T2
⌈ *   ⟹[ l ] *   ⌉' = *
⌈ *   ⟹[ l ] ` Q ⌉' = ⇓ l (` Q)
⌈ ` P ⟹[ l ] *   ⌉' = ⇑ l (` P)
⌈ ` P ⟹[ l ] ` Q ⌉' with (` P) ⌣? (` Q)
⌈ ` P ⟹[ l ] ` Q ⌉'             | no P⌣̸Q = ⊥ l _ ε
⌈ ` B       ⟹[ l ] ` B       ⌉' | yes ⌣B = ^ (B̂) ε {ε}
⌈ ` S1 ⇒ T1 ⟹[ l ] ` S2 ⇒ T2 ⌉' | yes ⌣⇒
  = ^ (⌈ S2 ⟹[ neg l ] S1 ⌉' ⇒̂ ⌈ T1 ⟹[ l ] T2 ⌉') ε {ε}
⌈ ` L1 ⊗ R1 ⟹[ l ] ` L2 ⊗ R2 ⌉' | yes ⌣⊗
  = ^ (⌈ L1 ⟹[ l ] L2 ⌉' ⊗̂ ⌈ R1 ⟹[ l ] R2 ⌉') ε {ε}

⌈_⌉ : ∀ {T1 T2} → SrcCast T1 T2 → Cast T1 T2
⌈ S ⟹[ l ] T ⌉ = S ⟹ T [ ⌈ S ⟹[ l ] T ⌉' ]


CastResult : Type → Set
CastResult T = Error Label×Polarity (Value Cast T)

typeop→ground : (op : TypeOp) → Ground (op · replicate *)
typeop→ground `B = `B
typeop→ground `⊗ = `⊗
typeop→ground `⇒ = `⇒

project : ∀ G {S Ts}
  → OptionalLabel G S Ts
  → Value Cast S
  → CastResult (` G · Ts)
project H ε v = return v
project H (⁇ l) (dyn G v) with G ≟G (typeop→ground H)
project H (⁇ l) (dyn G v) | yes refl = return v
project H (⁇ l) (dyn G v) | no ¬G≡H  = raise l

proxy : ∀ {G} Ss Ts
  → LabeledPreType G Ss Ts
  → Value Cast (` G · Ss)
  ---
  → Value Cast (` G · Ts)
proxy [] [] B̂ v
  = v
proxy (S₂ ∷ T₂ ∷ []) (S₃ ∷ T₃ ∷ []) (Ŝ ⇒̂ T̂) (lam⟨ c ⇒ d ⟩ e E)
  = lam⟨ (S₃ ⟹ S₂ [ Ŝ ]) ⨟ c ⇒ d ⨟ (T₂ ⟹ T₃ [ T̂ ]) ⟩ e E
proxy (S₂ ∷ T₂ ∷ []) (S₃ ∷ T₃ ∷ []) (Ŝ ⊗̂ T̂) (cons⟨ c ⊗ d ⟩ u v)
  = cons⟨ c ⨟ (S₂ ⟹ S₃ [ Ŝ ]) ⊗ d ⨟ (T₂ ⟹ T₃ [ T̂ ]) ⟩ u v

quick-left-types : ∀ S G {Ss}
  → OptionalLabel G S Ss
  → Vec Type (arity G)
quick-left-types S G {Ss} p = Ss

quick-right-types : ∀ T G {Ts}
  → Tail G Ts T
  → Vec Type (arity G)
quick-right-types T G {Ts} p = Ts

left-types : ∀ S G {Ss}
  → OptionalLabel G S Ss
  → Vec Type (arity G)
left-types * G (⁇ l) = replicate *
left-types (` G · Ss) G ε = Ss

right-types : ∀ T G {Ts}
  → Tail G Ts T
  → Vec Type (arity G)
right-types * G ‼ = replicate *
right-types (` G · Ts) G ε = Ts

left-types-faithful : ∀ S G {Ss}
  → (p : OptionalLabel G S Ss)
  → left-types S G p ≡ quick-left-types S G p
left-types-faithful * G (⁇ l) = refl
left-types-faithful (` .(G · _)) G ε = refl

right-types-faithful : ∀ T G {Ts}
  → (t : Tail G Ts T)
  → right-types T G t ≡ quick-right-types T G t
right-types-faithful * G ‼ = refl
right-types-faithful (` G · _) G ε = refl

inject : ∀ G {Ss} T
  → {t : Tail G Ss T}
  → Value Cast (` G · Ss)
  → Value Cast T
inject G *     {‼} v = dyn (typeop→ground G) v
inject G (` P) {ε} v = v

⟦_⟧ : ∀ {T1 T2}
  → Cast T1 T2
  → Value Cast T1
  ---
  → CastResult T2
⟦ .* ⟹ .* [ * ] ⟧ v = return v
⟦ S ⟹ T [ ⊥ l G p ] ⟧ v = project G p v >>= λ _ → raise l
⟦ S ⟹ T [ ^ P̂ p {t} ] ⟧ v
  = project (quick-gnd P̂) p v >>= λ u
  → return (inject (quick-gnd P̂) T {t}
                   (proxy (quick-left-types S (quick-gnd P̂) p)
                          (quick-right-types T (quick-gnd P̂) t)
                          P̂ u))

⨟-assoc : ∀ {T1 T2 T3 T4}
  → (c₁ : Cast T1 T2)
  → (c₂ : Cast T2 T3)
  → (c₃ : Cast T3 T4)
  → ((c₁ ⨟ c₂) ⨟ c₃) ≡ (c₁ ⨟ (c₂ ⨟ c₃))
⨟-assoc (T₁ ⟹ T₂ [ T̂₁ ]) (T₂ ⟹ T₃ [ T̂₂ ]) (T₃ ⟹ T₄ [ T̂₃ ]) =
  begin
    ((T₁ ⟹ T₂ [ T̂₁ ]) ⨟ (T₂ ⟹ T₃ [ T̂₂ ])) ⨟ (T₃ ⟹ T₄ [ T̂₃ ])
  ≡⟨⟩
    (T₁ ⟹ T₄ [ T̂₃ ∘ (T̂₂ ∘ T̂₁) ])
  ≡⟨ cong (λ □ → T₁ ⟹ T₄ [ □ ]) (∘-assoc T̂₃ T̂₂ T̂₁) ⟩
    (T₁ ⟹ T₄ [ (T̂₃ ∘ T̂₂) ∘ T̂₁ ])
  ≡⟨⟩
    (T₁ ⟹ T₂ [ T̂₁ ]) ⨟ ((T₂ ⟹ T₃ [ T̂₂ ]) ⨟ (T₃ ⟹ T₄ [ T̂₃ ]))
  ∎

∘-identityˡ : ∀ {S} T → (T̂ : LabeledType S T) → id^ T ∘ T̂ ≡ T̂
∘-identityʳ : ∀ S {T} → (T̂ : LabeledType S T) → T̂ ∘ id^ S ≡ T̂

∘-identityˡ .* * = refl
∘-identityˡ T (⊥ l G p) = refl
∘-identityˡ * (^ P̂ p) = dyn-left (^ P̂ p)
∘-identityˡ (` B) (^ B̂ p {ε}) = refl
∘-identityˡ (` S ⇒ T) (^ (Ŝ ⇒̂ T̂) p {ε}) =
  begin
    id^ (` S ⇒ T) ∘ ^ (Ŝ ⇒̂ T̂) p {ε}
  ≡⟨⟩
    ^ ((Ŝ ∘ id^ S) ⇒̂ (id^ T ∘ T̂)) p {ε}
  ≡⟨ cong (λ □ → ^ (□ ⇒̂ (id^ T ∘ T̂)) p {ε}) (∘-identityʳ S Ŝ) ⟩
    ^ (Ŝ ⇒̂ (id^ T ∘ T̂)) p {ε}
  ≡⟨ cong (λ □ → ^ (Ŝ ⇒̂ □) p {ε}) (∘-identityˡ T T̂) ⟩
    ^ (Ŝ ⇒̂ T̂) p {ε}
  ∎
∘-identityˡ (` S ⊗ T) (^ (Ŝ ⊗̂ T̂) p {ε}) =
  begin
    id^ (` S ⊗ T) ∘ ^ (Ŝ ⊗̂ T̂) p {ε}
  ≡⟨⟩
    ^ ((id^ S ∘ Ŝ) ⊗̂ (id^ T ∘ T̂)) p {ε}
  ≡⟨ cong (λ □ → ^ (□ ⊗̂ (id^ T ∘ T̂)) p {ε}) (∘-identityˡ S Ŝ) ⟩
    ^ (Ŝ ⊗̂ (id^ T ∘ T̂)) p {ε}
  ≡⟨ cong (λ □ → ^ (Ŝ ⊗̂ □) p {ε}) (∘-identityˡ T T̂) ⟩
    ^ (Ŝ ⊗̂ T̂) p {ε}
  ∎

∘-identityʳ * T̂ = refl
∘-identityʳ (` B) (⊥ l `B ε) = refl
∘-identityʳ (` S ⊗ T) (⊥ l `⊗ ε) = refl
∘-identityʳ (` S ⇒ T) (⊥ l `⇒ ε) = refl
∘-identityʳ (` B) (^ B̂ ε) = refl
∘-identityʳ (` S ⇒ T) (^ (Ŝ ⇒̂ T̂) ε) =
  begin
    (^ (Ŝ ⇒̂ T̂) ε ∘ id^ (` S ⇒ T))
  ≡⟨⟩
    ^ ((id^ S ∘ Ŝ) ⇒̂ (T̂ ∘ id^ T)) ε
  ≡⟨ cong (λ □ → ^ (□ ⇒̂ (T̂ ∘ id^ T)) ε) (∘-identityˡ S Ŝ) ⟩
    ^ (Ŝ ⇒̂ (T̂ ∘ id^ T)) ε
  ≡⟨ cong (λ □ → ^ (Ŝ ⇒̂ □) ε) (∘-identityʳ T T̂) ⟩
    ^ (Ŝ ⇒̂ T̂) ε
  ∎
∘-identityʳ (` S ⊗ T) (^ (Ŝ ⊗̂ T̂) ε) =
  begin
    (^ (Ŝ ⊗̂ T̂) ε ∘ id^ (` S ⊗ T))
  ≡⟨⟩
    ^ ((Ŝ ∘ id^ S) ⊗̂ (T̂ ∘ id^ T)) ε
  ≡⟨ cong (λ □ → ^ (□ ⊗̂ (T̂ ∘ id^ T)) ε) (∘-identityʳ S Ŝ) ⟩
    ^ (Ŝ ⊗̂ (T̂ ∘ id^ T)) ε
  ≡⟨ cong (λ □ → ^ (Ŝ ⊗̂ □) ε) (∘-identityʳ T T̂) ⟩
    ^ (Ŝ ⊗̂ T̂) ε
  ∎

⨟-identityˡ : ∀ {S T} → (c : Cast S T) → id S ⨟ c ≡ c
⨟-identityˡ (S ⟹ T [ T̂ ]) = cong (λ □ → S ⟹ T [ □ ]) (∘-identityʳ S T̂)

⨟-identityʳ : ∀ {S T} → (c : Cast S T) → c ⨟ id T ≡ c
⨟-identityʳ (S ⟹ T [ T̂ ]) = cong (λ □ → S ⟹ T [ □ ]) (∘-identityˡ T T̂)

lem-id : ∀ T
  → (v : Value Cast T)
  -----------------------------
  → ⟦ id T ⟧ v ≡ return v
lem-id (*) v = refl
lem-id (` B) v = refl
lem-id (` S ⊗ T) (cons⟨ c1 ⊗ c2 ⟩ v1 v2) =
  begin
    ⟦ id (` S ⊗ T) ⟧ (cons⟨ c1 ⊗ c2 ⟩ v1 v2)
  ≡⟨⟩
    return (cons⟨ (c1 ⨟ id S) ⊗ (c2 ⨟ id T) ⟩ v1 v2)
  ≡⟨ cong (λ □ → return (cons⟨ □ ⊗ (c2 ⨟ id T) ⟩ v1 v2)) (⨟-identityʳ c1)  ⟩
    return (cons⟨ c1 ⊗ (c2 ⨟ id T) ⟩ v1 v2)
  ≡⟨ cong (λ □ → return (cons⟨ c1 ⊗ □ ⟩ v1 v2)) (⨟-identityʳ c2) ⟩
    return (cons⟨ c1 ⊗ c2 ⟩ v1 v2)
  ∎
lem-id (` S ⇒ T) (lam⟨ c1 ⇒ c2 ⟩ e E) =
  begin
    ⟦ id (` S ⇒ T) ⟧ (lam⟨ c1 ⇒ c2 ⟩ e E)
  ≡⟨⟩
    return (lam⟨ (id S ⨟ c1) ⇒ (c2 ⨟ id T) ⟩ e E)
  ≡⟨ cong (λ □ → return (lam⟨ □ ⇒ (c2 ⨟ id T) ⟩ e E)) (⨟-identityˡ c1)  ⟩
    return (lam⟨ c1 ⇒ (c2 ⨟ id T) ⟩ e E)
  ≡⟨ cong (λ □ → return (lam⟨ c1 ⇒ □ ⟩ e E)) (⨟-identityʳ c2) ⟩
    return (lam⟨ c1 ⇒ c2 ⟩ e E)
  ∎

project-inject-cancel : ∀ {G T Ss Ts}
  → (p : OptionalLabel G T Ts)
  → (t : Tail G Ss T)
  → (v : Value Cast (` G · Ss))
  → ∃[ u ](project G p (inject G T {t} v) ≡ return u)
project-inject-cancel ε ε v = _ , refl
project-inject-cancel {`B} (⁇ l) ‼ u = u , refl
project-inject-cancel {`⊗} (⁇ l) ‼ u = u , refl
project-inject-cancel {`⇒} (⁇ l) ‼ u = u , refl

project-inject-succeed : ∀ {G T Ts}
  → (p : OptionalLabel G T Ts)
  → (t : Tail G Ts T)
  → (v : Value Cast (` G · Ts))
  → project G p (inject G T {t} v) ≡ return v
project-inject-succeed ε ε v = refl
project-inject-succeed {`B} (⁇ l) ‼ u = refl
project-inject-succeed {`⊗} (⁇ l) ‼ u = refl
project-inject-succeed {`⇒} (⁇ l) ‼ u = refl

project-inject-fail : ∀ {G H Ss}
  → (¬G≡H : ¬ G ≡ H)
  → (l : Label×Polarity)
  → (t : Tail G Ss *)
  → (v : Value Cast (` G · Ss))
  → (project H (⁇ l) (inject G * {t} v) ≡ raise l)
project-inject-fail {G} {H} ¬G≡H l ‼ v
  with (typeop→ground G) ≟G (typeop→ground H)
... | yes refl = ⊥-elim (¬G≡H refl)
... | no ¬G≡H' = refl

lem-seq : ∀ {T1 T2 T3}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → (v  : Value Cast T1)
  --------------------
  → ⟦ c1 ⨟ c2 ⟧ v ≡ ⟦ c1 ⟧ v >>= ⟦ c2 ⟧
lem-seq (.* ⟹ .* [ * ]) (.* ⟹ T3 [ T̂2 ]) v = refl
lem-seq (T1 ⟹ T2 [ ⊥ l G p ]) (T2 ⟹ T3 [ T̂2 ]) v =
  begin
    ⟦ (T1 ⟹ T2 [ ⊥ l G p ]) ⨟ (T2 ⟹ T3 [ T̂2 ]) ⟧ v
  ≡⟨⟩
    ⟦ T1 ⟹ T3 [ ⊥ l G p ] ⟧ v
  ≡⟨⟩
    (project G p v >>= λ _ → raise l)
  ≡⟨ sym (drop-after-raise (project G p v) l ⟦ T2 ⟹ T3 [ T̂2 ] ⟧) ⟩
    (project G p v >>= λ _ → raise l) >>= ⟦ T2 ⟹ T3 [ T̂2 ] ⟧
  ≡⟨⟩
    ⟦ T1 ⟹ T2 [ ⊥ l G p ] ⟧ v >>= ⟦ T2 ⟹ T3 [ T̂2 ] ⟧
  ∎
lem-seq (T1 ⟹ .* [ ^ P̂ p ]) (.* ⟹ .* [ * ]) v
  = sym (>>=-return (⟦ T1 ⟹ * [ ^ P̂ p ] ⟧ v))
lem-seq (T1 ⟹ T2 [ ^ P̂₁ p₁ {t} ]) (T2 ⟹ T3 [ ⊥ l₂ G₂ p₂ ]) v
  with quick-gnd P̂₁ ≟op G₂
lem-seq (T1 ⟹ T2 [ ^ P̂₁ p₁ {t} ]) (T2 ⟹ T3 [ ⊥ l₂ G₂ p₂ ]) v | yes refl
  with project G₂ p₁ v
lem-seq (T1 ⟹ T2 [ ^ P̂₁ p₁ {t} ]) (T2 ⟹ T3 [ ⊥ l₂ G₂ p₂ ]) v
  | yes refl | raise l
  = refl
lem-seq (T1 ⟹ T2 [ ^ P̂₁ p₁ {t} ]) (T2 ⟹ T3 [ ⊥ l₂ G₂ p₂ ]) v
  | yes refl
  | return v₁
  with project-inject-cancel p₂ t (proxy _ _ P̂₁ v₁)
... | x , eq
  rewrite eq = refl
lem-seq (T1 ⟹ .* [ ^ P̂₁ p₁ {t} ])
        (.* ⟹ T3 [ ⊥ l₂ G₂ (⁇ l) ]) v
  | no ¬p
  with project _ p₁ v
... | raise  _ = refl
... | return u
  rewrite project-inject-fail ¬p l t (proxy _ _ P̂₁ u)
  = refl
lem-seq (T1 ⟹ .(` G₂ · _) [ ^ P̂₁ p₁ {t} ])
        (.(` G₂ · _) ⟹ T3 [ ⊥ l₂ G₂ ε ]) v
  | no ¬p = ⊥-elim (impossible-tail t ¬p)
lem-seq (T1 ⟹ T2 [ ^ P̂₁ p₁ {t} ]) (T2 ⟹ T3 [ ^ P̂₂ p₂ ]) v
  with quick-gnd P̂₁ ≟op quick-gnd P̂₂
lem-seq (T1 ⟹ .* [ ^ P̂₁ p₁ {t} ]) (.* ⟹ T3 [ ^ P̂₂ (⁇ l) ]) v | no ¬p
  with project _ p₁ v
... | raise l' = refl
... | return u
  rewrite project-inject-fail ¬p l t (proxy _ _ P̂₁ u)
  = refl
lem-seq (T1 ⟹ .(` _ · _) [ ^ P̂₁ p₁ {t} ]) (.(` _ · _) ⟹ T3 [ ^ P̂₂ ε ]) v | no ¬p = ⊥-elim (impossible-tail t ¬p)
lem-seq (T1 ⟹ T2 [ ^ P̂₁ p₁ {t} ]) (T2 ⟹ T3 [ ^ P̂₂ p₂ ]) v | yes refl
  with no-gap-at-all t p₂
lem-seq (T1 ⟹ T2 [ ^ B̂ p₁ {t} ]) (T2 ⟹ T3 [ ^ B̂ p₂ ]) v
  | yes refl | refl
  with project `B p₁ v
... | raise _  = refl
... | return u
  rewrite project-inject-succeed p₂ t u
  = refl
lem-seq (T1 ⟹ T2 [ ^ (Ŝ₁ ⇒̂ T̂₁) p₁ {t} ]) (T2 ⟹ T3 [ ^ (Ŝ₂ ⇒̂ T̂₂) p₂ ]) v
  | yes refl | refl
  with (project `⇒ p₁ v)
... | raise _  = refl
... | return (lam⟨ (_ ⟹ _ [ S ]) ⇒ (_ ⟹ _ [ T ]) ⟩ e E)
  rewrite project-inject-succeed p₂ t
          (lam⟨ (_ ⟹ _ [ S ∘ Ŝ₁ ]) ⇒ (_ ⟹ _ [ T̂₁ ∘ T ]) ⟩ e E)
  | ∘-assoc S Ŝ₁ Ŝ₂
  | ∘-assoc T̂₂ T̂₁ T
  = refl
lem-seq (T1 ⟹ T2 [ ^ (Ŝ₁ ⊗̂ T̂₁) p₁ {t} ]) (T2 ⟹ T3 [ ^ (Ŝ₂ ⊗̂ T̂₂) p₂ ]) v
  | yes refl | refl
  with (project `⊗ p₁ v)
... | raise _  = refl
... | return (cons⟨ (_ ⟹ _ [ S ]) ⊗ (_ ⟹ _ [ T ]) ⟩ v₁ v₂)
  rewrite project-inject-succeed p₂ t
          (cons⟨ (_ ⟹ _ [ Ŝ₁ ∘ S ]) ⊗ (_ ⟹ _ [ T̂₁ ∘ T ]) ⟩ v₁ v₂)
  | ∘-assoc Ŝ₂ Ŝ₁ S
  | ∘-assoc T̂₂ T̂₁ T
  = refl


C : CastADT
C = record
    { Cast = Cast
    ; id  = id
    ; ⌈_⌉ = ⌈_⌉
    ; _⨟_ = _⨟_
    ; ⟦_⟧ = ⟦_⟧
    ; lem-id = lem-id
    ; lem-seq = lem-seq
    }

eq-¬⌣ : ∀ {T1 T2}
  → (v : Value Cast T1)
  → (l : Label×Polarity)
  → ¬ (T1 ⌣ T2)
  ---
  → (⟦ ⌈ T1 ⟹[ l ] T2 ⌉ ⟧ v)
      ≡
    (raise l)
eq-¬⌣ {*} {*} v l ¬p = ⊥-elim (¬p *⌣*)
eq-¬⌣ {*} {` P} v l ¬p = ⊥-elim (¬p (*⌣P P))
eq-¬⌣ {` P} {*} v l ¬p = ⊥-elim (¬p (P⌣* P))
eq-¬⌣ {` P} {` Q} v l ¬p with (` P) ⌣? (` Q)
eq-¬⌣ {` P} {` Q} v l ¬p | yes p' = ⊥-elim (¬p p')
eq-¬⌣ {` P} {` Q} v l ¬p | no ¬p' = refl

lem-rewrite-inj : ∀ l T
  → (⇑ l T) ≡ ⌈ T ⟹[ l ] * ⌉'
lem-rewrite-inj l * = refl
lem-rewrite-inj l (` P) = refl

lem-rewrite-proj : ∀ l T
  → (⇓ l T) ≡ ⌈ * ⟹[ l ] T ⌉'
lem-rewrite-proj l * = refl
lem-rewrite-proj l (` P) = refl

lem-expand-inj : ∀ l P
  → (⇑ l (` P)) ≡ (⌈ ` ground P ⟹[ l ] * ⌉' ∘ ⌈ (` P) ⟹[ l ] ` ground P ⌉')
lem-expand-inj l B = refl
lem-expand-inj l (S ⇒ T)
  rewrite lem-rewrite-proj (neg l) S | lem-rewrite-inj l T
    | ∘-identityˡ * ⌈ T ⟹[ l ] * ⌉'
  = refl
lem-expand-inj l (S ⊗ T)
  rewrite lem-rewrite-inj l S | lem-rewrite-inj l T
    | ∘-identityʳ T ⌈ T ⟹[ l ] * ⌉'
    | ∘-identityʳ S ⌈ S ⟹[ l ] * ⌉'
    | dyn-left ⌈ S ⟹[ l ] * ⌉'
    | dyn-left ⌈ T ⟹[ l ] * ⌉'
  = refl

lem-expand-proj : ∀ l P
  → (⇓ l (` P)) ≡ (⌈ ` ground P ⟹[ l ] ` P ⌉' ∘ ⌈ * ⟹[ l ] ` ground P ⌉')
lem-expand-proj l B = refl
lem-expand-proj l (S ⇒ T)
  rewrite lem-rewrite-inj (neg l) S | lem-rewrite-proj l T
    | ∘-identityˡ * ⌈ S ⟹[ neg l ] * ⌉'
  = refl
lem-expand-proj l (S ⊗ T)
  rewrite lem-rewrite-proj l S | lem-rewrite-proj l T
  = refl

eq-P* : ∀ {P}
  → (v : Value Cast (` P))
  → (l : Label×Polarity)
  → ¬ Ground P
  → ⟦ ⌈ (` P) ⟹[ l ] * ⌉ ⟧ v
      ≡
    ⟦ ⌈ (` P) ⟹[ l ] (` ground P) ⌉ ⟧ v >>= ⟦ ⌈ (` ground P) ⟹[ l ] * ⌉ ⟧
eq-P* {P} v l ¬gP
  rewrite lem-expand-inj l P
  | lem-seq ⌈ (` P) ⟹[ l ] (` ground P) ⌉ ⌈ (` ground P) ⟹[ l ] * ⌉ v
  = refl

eq-I* : ∀ {P}
  → (v : Value Cast (` P))
  → (l : Label×Polarity)
  → (gP : Ground P)
  → ⟦ ⌈ ` P ⟹[ l ] * ⌉ ⟧ v
      ≡
    return (dyn gP v)
eq-I* {.B} v l `B = refl
eq-I* {.(* ⇒ *)} (lam⟨ c1 ⇒ c2 ⟩ e E) l `⇒
  rewrite ⨟-identityʳ c2 | ⨟-identityˡ c1
  = refl
eq-I* {.(* ⊗ *)} (cons⟨ c1 ⊗ c2 ⟩ v v₁) l `⊗
  rewrite ⨟-identityʳ c1 | ⨟-identityʳ c2
  = refl

eq-*P : ∀ {P}
  → (v : Value Cast *)
  → ∀ l
  → ¬ Ground P
  → ⟦ ⌈ * ⟹[ l ] (` P) ⌉ ⟧ v
      ≡
    ⟦ ⌈ * ⟹[ l ] (` ground P) ⌉ ⟧ v >>= ⟦ ⌈ (` ground P) ⟹[ l ] (` P) ⌉ ⟧
eq-*P {P} v l ¬gP
  rewrite lem-expand-proj l P
  | lem-seq ⌈ * ⟹[ l ] (` ground P) ⌉ ⌈ (` ground P) ⟹[ l ] (` P) ⌉ v
  = refl

eq-*I-succ : ∀ {P}
  → (v : Value Cast (` P))
  → ∀ l
  → (gP : Ground P)
  → ⟦ ⌈ * ⟹[ l ] (` P) ⌉ ⟧ (dyn gP v)
      ≡
    return v
eq-*I-succ v l `B = refl
eq-*I-succ (lam⟨ c1 ⇒ c2 ⟩ e E) l `⇒
  rewrite ⨟-identityˡ c1 | ⨟-identityʳ c2
  = refl
eq-*I-succ (cons⟨ c1 ⊗ c2 ⟩ v v₁) l `⊗
  rewrite ⨟-identityʳ c1 | ⨟-identityʳ c2
  = refl

eq-*I-fail : {P Q : PreType}
  → (v : Value Cast (` P))
  → ∀ l
  → (gP : Ground P)
  → (gQ : Ground Q)
  → ¬ (_≡_ {A = Type} (` P) (` Q))
  → ⟦ ⌈ * ⟹[ l ] (` Q) ⌉ ⟧ (dyn gP v)
      ≡
    raise l
eq-*I-fail {B} v l `B `B ¬p = ⊥-elim (¬p refl)
eq-*I-fail {B} v l `B `⇒ ¬p = refl
eq-*I-fail {B} v l `B `⊗ ¬p = refl
eq-*I-fail {.* ⇒ .*} v l `⇒ `B ¬p = refl
eq-*I-fail {.* ⇒ .*} v l `⇒ `⇒ ¬p = ⊥-elim (¬p refl)
eq-*I-fail {.* ⇒ .*} v l `⇒ `⊗ ¬p = refl
eq-*I-fail {.* ⊗ .*} v l `⊗ `B ¬p = refl
eq-*I-fail {.* ⊗ .*} v l `⊗ `⇒ ¬p = refl
eq-*I-fail {.* ⊗ .*} v l `⊗ `⊗ ¬p = ⊥-elim (¬p refl)

CIsLazyUD : IsLazyUD C
CIsLazyUD = record
             { eq-¬⌣ = eq-¬⌣
             ; eq-** = λ l v → refl
             ; eq-P* = eq-P*
             ; eq-I* = eq-I*
             ; eq-*P = eq-*P
             ; eq-*I-succ = eq-*I-succ
             ; eq-*I-fail = eq-*I-fail
             ; eq-B = λ l b → refl
             ; eq-⇒ = λ T21 T22 T11 T12 {S} {T} l {Γ} c₁ c₂ e E → refl
             ; eq-⊗ = λ T21 T22 T11 T12 {S} {T} l c₁ c₂ v1 v2 → refl
             }


correctness-1 : ∀ {T e}
  → {o : Observable T}
  → Evalₛ C e o
  ---
  → Evalᵣ e o
correctness-1
  = theorem-LazyUD-CastADT-correct-part-1 C CIsLazyUD

correctness-2 : ∀ {T e}
  → {o : Observable T}
  → Evalᵣ e o
  ---
  → Evalₛ C e o
correctness-2
  = theorem-LazyUD-CastADT-correct-part-2 C CIsLazyUD
