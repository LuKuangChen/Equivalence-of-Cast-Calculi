module CastRepresentations.LazyUDThreesomes2 (Label : Set) where

open import Types hiding (Tag)
open import Cast Label using (_⟹[_]_) renaming (Cast to SrcCast)
open import Terms Label
open import S.CastADT Label

open import Data.Empty using (⊥-elim) renaming (⊥ to Empty)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Product using (∃-syntax; proj₁; proj₂; _×_; _,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

{-
Siek, Jeremy G., and Philip Wadler. "Threesomes, with and without blame."
ACM Sigplan Notices 45.1 (2010): 365-376.
-}

open import Data.Maybe

data OptionalLabel : Type → PreType → Set where
  ⁇ : ∀ {P}
    → (l : Label)
    → .{G : Ground P}
    → OptionalLabel * P
  ε : ∀ {P}
    → OptionalLabel (` P) P

data Tail : PreType → Type → Set where
  ‼ : ∀ {P}
    → (gP : Ground P)
    → Tail P *

  ε : ∀ {P}
    → Tail P (` P)

mutual
  data LabeledType : Type → Type → Set where
    * : LabeledType * *
    ↷ : ∀ {S P Q T}
      → (p : OptionalLabel S P)
      → (P̂ : LabeledPreType P Q)
      → .(t : Tail Q T)
        ---------------
      → LabeledType S T
  
  data LabeledPreType : PreType → PreType → Set where
    ⊥ : ∀ {P G Q}
      → (l : Label)
      → (gG : Ground G)
      → .{P~G : (` P) ~ (` G)}
      → LabeledPreType P Q
    B̂ : LabeledPreType B B
    _⇒̂_ : ∀ {S1 S2 T1 T2}
      → (S* : LabeledType S2 S1)
      → (T* : LabeledType T1 T2)
      → LabeledPreType (S1 ⇒ T1) (S2 ⇒ T2)
    _⊗̂_ : ∀ {S1 S2 T1 T2}
      → (S* : LabeledType S1 S2)
      → (T* : LabeledType T1 T2)
      → LabeledPreType (S1 ⊗ T1) (S2 ⊗ T2)

data Gnd : ∀ {S T P} → Ground P → LabeledType S T → Set where
  `B : ∀ {S T}
    → {p : OptionalLabel S B}
    → .{t : Tail B T}
    → Gnd `B (↷ p B̂ t)
  `⇒ : ∀ {S S1 T1 S2 T2 T}
    → {p : OptionalLabel S (S1 ⇒ T1)}
    → {Ŝ : LabeledType S2 S1}
    → {T̂ : LabeledType T1 T2}
    → .{t : Tail (S2 ⇒ T2) T}
    → Gnd `⇒ (↷ p (Ŝ ⇒̂ T̂) t)
  `⊗ : ∀ {S S1 T1 S2 T2 T}
    → {p : OptionalLabel S (S1 ⊗ T1)}
    → {Ŝ : LabeledType S1 S2}
    → {T̂ : LabeledType T1 T2}
    → .{t : Tail (S2 ⊗ T2) T}
    → Gnd `⊗ (↷ p (Ŝ ⊗̂ T̂) t)

inv-gnd-left : ∀ {G S P Q T}
  → {gG : Ground G}
  → {p : OptionalLabel S P}
  → {P̂ : LabeledPreType P Q}
  → .{t : Tail Q T}
  → Gnd gG (↷ p P̂ t)
  → (` P) ~ (` G)
inv-gnd-left `B = ~B
inv-gnd-left `⇒ = ~⇒ T~* T~*
inv-gnd-left `⊗ = ~⊗ T~* T~*

inv-gnd-right : ∀ {G S P Q T}
  → {gG : Ground G}
  → {p : OptionalLabel S P}
  → {P̂ : LabeledPreType P Q}
  → .{t : Tail Q T}
  → Gnd gG (↷ p P̂ t)
  → (` Q) ~ (` G)
inv-gnd-right `B = ~B
inv-gnd-right `⇒ = ~⇒ T~* T~*
inv-gnd-right `⊗ = ~⊗ T~* T~*

impossible-case : ∀ {G H P1 P2 Q1 Q2}
  → (P̂ : LabeledPreType P1 Q1)
  → (Q̂ : LabeledPreType P2 Q2)
  → (gG : Ground G)
  → (gH : Ground H)
  → (Q1~G : (` Q1) ~ (` G))
  → (P2~H : (` P2) ~ (` H))
  → (¬G≡H : ¬ G ≡ H)
  → (t : Tail Q1 (` P2))
  → Empty
impossible-case P̂ Q̂ `B `B ~B P2~H ¬G≡H t = ¬G≡H refl
impossible-case P̂ Q̂ `B `⇒ ~B (~⇒ P2~H P2~H₁) ¬G≡H ()
impossible-case P̂ Q̂ `B `⊗ ~B (~⊗ P2~H P2~H₁) ¬G≡H ()
impossible-case P̂ Q̂ `⇒ `B (~⇒ Q1~G Q1~G₁) ~B ¬G≡H ()
impossible-case P̂ Q̂ `⇒ `⇒ Q1~G P2~H ¬G≡H t = ¬G≡H refl
impossible-case P̂ Q̂ `⇒ `⊗ (~⇒ Q1~G Q1~G₁) (~⊗ P2~H P2~H₁) ¬G≡H ()
impossible-case P̂ Q̂ `⊗ `B (~⊗ Q1~G Q1~G₁) ~B ¬G≡H ()
impossible-case P̂ Q̂ `⊗ `⇒ (~⊗ Q1~G Q1~G₁) (~⇒ P2~H P2~H₁) ¬G≡H ()
impossible-case P̂ Q̂ `⊗ `⊗ (~⊗ Q1~G Q1~G₁) (~⊗ P2~H P2~H₁) ¬G≡H t = ¬G≡H refl

must-be-equal : ∀ {preG preH T1 P1 P2 T2 Q1 Q2 T3}
  → {p : OptionalLabel T1 P1}
  → {P̂ : LabeledPreType P1 Q1}
  → {t : Tail Q1 T2}
  → {q : OptionalLabel  T2 P2}
  → {Q̂ : LabeledPreType P2 Q2}
  → {s : Tail Q2 T3}
  → {G : Ground preG}
  → {H : Ground preH}
  → Gnd G (↷ p P̂ t)
  → Gnd H (↷ q Q̂ s)
  → (G≡H : preG ≡ preH)
  → Q1 ≡ P2
must-be-equal = {!!}
  
data View : ∀ {S T} → LabeledType S T → Set where
  top : View *
  bot : ∀ {S P Q T l}
    → {p : OptionalLabel S P}
    → {G : PreType}
    → {gG : Ground G}
    → .{P~G : (` P) ~ (` G)}
    → .{t : Tail Q T}
    → View (↷ p (⊥ l gG {P~G}) t)
  gnd : ∀ {S P T}
    → {T̂ : LabeledType S T}
    → (gP : Ground P)
    → (gnd-prf : Gnd gP T̂)
    → View T̂

view : ∀ {S T} → (T̂ : LabeledType S T) → View T̂
view * = top
view (↷ p (⊥ l G {P~G}) t) = bot {P~G = P~G}
view (↷ p B̂ t) = gnd `B `B
view (↷ p (S* ⇒̂ T*) t) = gnd `⇒ `⇒
view (↷ p (S* ⊗̂ T*) t) = gnd `⊗ `⊗

data Cast : Type → Type → Set where
  _⟹_[_] : ∀ S T
    → (T̂ : LabeledType S T)
    → Cast S T

anytail : ∀ {T}
  → ∃[ Q ](Tail Q T)
anytail {*}   = B , ‼ `B
anytail {` P} = P , ε

_∘_ : ∀ {T1 T2 T3} → LabeledType T2 T3 → LabeledType T1 T2 → LabeledType T1 T3
T̂ ∘ Ŝ with view T̂ | view Ŝ
(T̂ ∘ *)                     | vT | top = T̂
(T̂ ∘ (↷ p (⊥ l G {P~G}) t)) | vT | bot = ↷ p (⊥ l G {P~G}) (proj₂ anytail)
(* ∘ Ŝ)                     | top | gnd G gnd[P^p]=P^[Gp] = Ŝ
(↷ q     (⊥ m H)       s ∘ Ŝ)       | bot | gnd G gnd[P^p]=P^[Gp] with G ≟G H
(↷ q     (⊥ m H)       s ∘ ↷ p P̂ t) | bot | gnd G gnd[P^p]=P^[Gp] | yes refl = ↷ p (⊥ m H {inv-gnd-left gnd[P^p]=P^[Gp]}) s
(↷ (⁇ l) (⊥ m H)       s ∘ ↷ p P̂ t) | bot | gnd G gnd[P^p]=P^[Gp] | no ¬G≡H  = ↷ p (⊥ l G {inv-gnd-left gnd[P^p]=P^[Gp]}) s 
(↷ ε   Q̂@(⊥ m H {P~H}) s ∘ ↷ p P̂ t) | bot | gnd G gnd[P^p]=P^[Gp] | no ¬G≡H  = ⊥-elim-irr (impossible-case P̂ Q̂ G H (inv-gnd-right gnd[P^p]=P^[Gp]) P~H ¬G≡H t)
(↷ q     Q̂ s ∘ ↷ p P̂ t) | gnd H gnd[Q^q]=Q^[Hq] | gnd G gnd[P^p]=P^[Gp] with G ≟G H
(↷ (⁇ m) Q̂ s ∘ ↷ p P̂ t) | gnd H gnd[Q^q]=Q^[Hq] | gnd G gnd[P^p]=P^[Gp] | no ¬G≡H = ↷ p (⊥ m G {inv-gnd-left gnd[P^p]=P^[Gp]}) s
(↷ ε     Q̂ s ∘ ↷ p P̂ t) | gnd H gnd[Q^q]=Q^[Hq] | gnd G gnd[P^p]=P^[Gp] | no ¬G≡H
  = ⊥-elim-irr (impossible-case P̂ Q̂ G H (inv-gnd-right gnd[P^p]=P^[Gp]) (inv-gnd-left gnd[Q^q]=Q^[Hq]) ¬G≡H t)
(↷ q Q̂ s ∘ ↷ p P̂ t) | gnd H gnd[Q^q]=Q^[Hq] | gnd G gnd[P^p]=P^[Gp] | yes G≡H with must-be-equal gnd[P^p]=P^[Gp] gnd[Q^q]=Q^[Hq] G≡H
... | rr = {!!}

_⨟_ : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
(T1 ⟹ T2 [ Ŝ ]) ⨟ (.T2 ⟹ T3 [ T̂ ]) = T1 ⟹ T3 [ T̂ ∘ Ŝ ]
