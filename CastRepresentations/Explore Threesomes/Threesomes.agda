module CastRepresentations.Threesomes (Label : Set) where

open import Types
open import Cast Label using (_⟹[_]_) renaming (Cast to SrcCast)
open import Terms Label
open import S.CastADT Label

open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (∃-syntax; proj₁; proj₂; _×_; _,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

{-
Siek, Jeremy G., and Philip Wadler. "Threesomes, with and without blame."
ACM Sigplan Notices 45.1 (2010): 365-376.

Extrincively typed style
-}

OptionalLabel : Set
OptionalLabel = Maybe Label

data LabeledType : Set
data LabeledPreType : Set

data LabeledType where
  * : LabeledType
  _,_ : (P : LabeledPreType)(p : OptionalLabel) → LabeledType

data LabeledPreType where
  ⊥ : (l : Label) → ∀ {P} → (G : Ground P) → LabeledPreType
  B̂ : LabeledPreType
  _⇒̂_ : LabeledType → LabeledType → LabeledPreType
  _⊗̂_ : LabeledType → LabeledType → LabeledPreType

data Gnd : LabeledType → ∀ {P} → (Ground P) → OptionalLabel → Set where
  `B : ∀ p
    → Gnd (B̂ , p) `B p
  `⇒ : ∀ p S T
    → Gnd (S ⇒̂ T , p) `⇒ p 
  `⊗ : ∀ p S T
    → Gnd (S ⊗̂ T , p) `⊗ p

data LabeledTypeView : LabeledType → Set where
  star : LabeledTypeView *
  fail : ∀ l {P} G p
    → LabeledTypeView (⊥ l {P} G , p)
  nonfail : ∀ {T P} G p
    → (gnd : Gnd T {P} G p)
    → LabeledTypeView T
    
view : ∀ T → LabeledTypeView T
view * = star
view (⊥ l G , p) = fail l G p
view (B̂ , p) = nonfail `B p (`B p)
view ((x ⇒̂ x₁) , p) = nonfail `⇒ p (`⇒ p x x₁)
view ((x ⊗̂ x₁) , p) = nonfail `⊗ p (`⊗ p x x₁)

data ⊢p_⦂_⟹_ : OptionalLabel → Type → PreType → Set where
  ⊢ε : ∀ {P} → ⊢p nothing ⦂ (` P) ⟹ P
  ⊢⁇ : ∀ {P}
    → (gP : Ground P)
    → (l  : Label)
    → ⊢p just l ⦂ * ⟹ P

data ⊢t_⟹_ : PreType → Type → Set where
  ⊢ε : ∀ {P} → ⊢t P ⟹ (` P)
  ⊢‼ : ∀ {P} → Ground P → ⊢t P ⟹ *

data ⊢T_⦂_⟹_ : LabeledType → Type → Type → Set
data ⊢P_⦂_⟹_ : LabeledPreType → PreType → PreType → Set

data ⊢T_⦂_⟹_ where
  ⊢*     : ⊢T * ⦂ * ⟹ *
  ⊢_,_,_ : ∀ {Q P S T P̂ p}
    → (⊢t : ⊢t Q ⟹ T)
    → (⊢P : ⊢P P̂ ⦂ P ⟹ Q)
    → (⊢p : ⊢p p ⦂ S ⟹ P)
    → ⊢T (P̂ , p) ⦂ S ⟹ T
    
data ⊢P_⦂_⟹_ where
  ⊢⊥ : ∀ l {P Q}
    → (gP : Ground P)
    → ⊢P (⊥ l gP) ⦂ P ⟹ Q
  ⊢B   : ⊢P B̂ ⦂ B ⟹ B
  ⊢_⇒_ : ∀ {Ŝ T̂ S1 S2 T1 T2}
    → (S : ⊢T Ŝ ⦂ S2 ⟹ S1)
    → (T : ⊢T T̂ ⦂ T1 ⟹ T2)
    → ⊢P (Ŝ ⇒̂ T̂) ⦂ (S1 ⇒ T1) ⟹ (S2 ⇒ T2)
  ⊢_⊗_ : ∀ {Ŝ T̂ S1 S2 T1 T2}
    → (S : ⊢T Ŝ ⦂ S1 ⟹ S2)
    → (T : ⊢T T̂ ⦂ T1 ⟹ T2)
    → ⊢P (Ŝ ⊗̂ T̂) ⦂ (S1 ⊗ T1) ⟹ (S2 ⊗ T2)
    
_∘_ : LabeledType → LabeledType → Maybe LabeledType
(T ∘ S)  with view T | view S
(T ∘ .*)           | VT | star = just T                      
(T ∘ .(⊥ l G , p)) | VT | fail l G p = just (⊥ l G , p)      
(.* ∘ S)           | star       | nonfail G p gnd = just S
(.(⊥ l H , q) ∘ S) | fail l H q | nonfail G p gnd with G ≟G H
(.(⊥ l H , q) ∘ S) | fail l H q | nonfail G p gnd | yes G≡H = just (⊥ l H , q)
(.(⊥ m H , (just l))  ∘ S) | fail m H (just l)  | nonfail G p gnd | no ¬p = just (⊥ l G , p)
(.(⊥ m H , (nothing)) ∘ S) | fail m H (nothing) | nonfail G p gnd | no ¬p = nothing
(T ∘ S) | nonfail H q gndQ | nonfail G p gndP with G ≟G H
(.(B̂ , q) ∘ .(B̂ , p)) | nonfail `B q (`B .q) | nonfail `B p (`B .p) | yes G≡H = just (B̂ , p)
(.((S2 ⇒̂ T2) , q) ∘ .((S1 ⇒̂ T1) , p)) | nonfail `⇒ q (`⇒ .q S2 T2) | nonfail `⇒ p (`⇒ .p S1 T1) | yes G≡H
  = S1 ∘ S2 >>= λ S →
    T2 ∘ T1 >>= λ T →
    just (S ⇒̂ T , p)
(.((S2 ⊗̂ T2) , q) ∘ .((S1 ⊗̂ T1) , p)) | nonfail `⊗ q (`⊗ .q S2 T2) | nonfail `⊗ p (`⊗ .p S1 T1) | yes G≡H
  = S2 ∘ S1 >>= λ S →
    T2 ∘ T1 >>= λ T →
    just (S ⊗̂ T , p)
(T ∘ S) | nonfail H (just l) gndQ | nonfail G p gndP | no ¬G≡H = just (⊥ l G , p)
(T ∘ S) | nonfail H nothing gndQ  | nonfail G p gndP | no ¬G≡H = nothing

untype : ∀ {T̂ S T}
  → ⊢T T̂ ⦂ S ⟹ T
  → LabeledType
untype {T̂} _ = T̂

⊢_∘_ : ∀ T̂ Ŝ {T1 T2 T3}
  → ⊢T T̂ ⦂ T2 ⟹ T3
  → ⊢T Ŝ ⦂ T1 ⟹ T2
  → ∃[ R̂ ](T̂ ∘ Ŝ ≡ just R̂)
(⊢ T ∘ S) ⊢T ⊢S with view T | view S
(⊢ T ∘ .*) ⊢T ⊢S | x | star = T , refl
(⊢ T ∘ .(⊥ l G , p)) ⊢T ⊢S | x | fail l G p = (⊥ l G , p) , refl
(⊢ .* ∘ S) ⊢T ⊢S | star | nonfail G p gnd = S , refl
(⊢ .(⊥ l H , q) ∘ S) ⊢T ⊢S | fail l H q | nonfail G p gnd with G ≟G H
(⊢ .(⊥ l H , q) ∘ S) ⊢T ⊢S | fail l H q | nonfail G p gnd | yes G≡H = _ , refl
(⊢ .(⊥ l H , just l') ∘ S) ⊢T ⊢S | fail l H (just l') | nonfail G p gnd | no ¬G≡H = _ , refl
(⊢ .(⊥ l `B , nothing) ∘ .(B̂ , p)) (⊢ ⊢t , ⊢Q , ⊢ε) (⊢ ⊢ε , ⊢B , ⊢p) | fail l `B nothing | nonfail .`B p (`B .p) | no ¬G≡H = ⊥-elim (¬G≡H refl)
(⊢ .(⊥ l `⇒ , nothing) ∘ .((S ⇒̂ T) , p)) (⊢ ⊢t , ⊢Q , ⊢ε) (⊢ ⊢ε , ⊢ S₁ ⇒ T₁ , ⊢p) | fail l `⇒ nothing | nonfail .`⇒ p (`⇒ .p S T) | no ¬G≡H = ⊥-elim (¬G≡H refl)
(⊢ .(⊥ l `⊗ , nothing) ∘ .((S ⊗̂ T) , p)) (⊢ ⊢t , ⊢Q , ⊢ε) (⊢ ⊢ε , ⊢ S₁ ⊗ T₁ , ⊢p) | fail l `⊗ nothing | nonfail .`⊗ p (`⊗ .p S T) | no ¬G≡H = ⊥-elim (¬G≡H refl)
(⊢ T ∘ S) ⊢T ⊢S | nonfail H q gnd' | nonfail G p gnd with G ≟G H
(⊢ .(B̂ , q) ∘ .(B̂ , p)) ⊢T ⊢S | nonfail .`B q (`B .q) | nonfail .`B p (`B .p) | yes G≡H = (B̂ , p) , refl
(⊢ .((S2 ⇒̂ T2) , q) ∘ .((S1 ⇒̂ T1) , p)) (⊢ _ , ⊢ ⊢S2 ⇒ ⊢T2 , _) (⊢ _ , ⊢ ⊢S1 ⇒ ⊢T1 , _) | nonfail .`⇒ q (`⇒ .q S2 T2) | nonfail .`⇒ p (`⇒ .p S1 T1) | yes G≡H = {!!}
(⊢ .((S2 ⊗̂ T2) , q) ∘ .((S1 ⊗̂ T1) , p)) ⊢T ⊢S | nonfail .`⊗ q (`⊗ .q S2 T2) | nonfail .`⊗ p (`⊗ .p S1 T1) | yes G≡H = {!!}
(⊢ T ∘ S) ⊢T ⊢S | nonfail H q gnd' | nonfail G p gnd | no ¬G≡H = {!!}

data Threesome : Type → Type → Set where
  _⟹_[_] : ∀ S T
    → (T̂ : LabeledType)
    → .(⊢T T̂ ⦂ S ⟹ T)
    → Threesome S T

Cast : Type → Type → Set
Cast = Threesome

_⨟_ : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
c ⨟ d = {!!}
