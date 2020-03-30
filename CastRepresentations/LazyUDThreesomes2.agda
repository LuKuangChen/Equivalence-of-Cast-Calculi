module CastRepresentations.LazyUDThreesomes2 (Label : Set) where

open import Types hiding (Tag)
open import Cast Label using (_⟹[_]_) renaming (Cast to SrcCast)
open import Terms Label
open import S.CastADT Label

open import Data.Empty using (⊥-elim)
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
    → .(G : Ground P)
    → OptionalLabel * P
  ε : ∀ {P}
    → OptionalLabel (` P) P

data Tail : PreType → Type → Set where
  ‼ : ∀ {P}
    → .(gP : Ground P)
    → Tail P *

  ε : ∀ {P}
    → Tail P (` P)

data Tag : Set where
  `B : Tag
  `⇒ : Tag
  `⊗ : Tag

_≟tag_ : (t1 t2 : Tag) → Dec (t1 ≡ t2)
`B ≟tag `B = yes refl
`B ≟tag `⇒ = no (λ ())
`B ≟tag `⊗ = no (λ ())
`⇒ ≟tag `B = no (λ ())
`⇒ ≟tag `⇒ = yes refl
`⇒ ≟tag `⊗ = no (λ ())
`⊗ ≟tag `B = no (λ ())
`⊗ ≟tag `⇒ = no (λ ())
`⊗ ≟tag `⊗ = yes refl

data IsTagof : Tag → PreType → Set where
  `B : IsTagof `B B
  `⇒ : ∀ {S T} → IsTagof `⇒ (S ⇒ T)
  `⊗ : ∀ {S T} → IsTagof `⊗ (S ⊗ T)

mutual
  data LabeledType : Type → Type → Set where
    * : LabeledType * *
    ⊥ : ∀ {S P T}
      → (l : Label)
      → (G : Tag)
      → .(Grel : IsTagof G P)
      → (p : OptionalLabel S P)
        ---------------
      → LabeledType S T
    ⟨_,_,_⟩ : ∀ {S P Q T}
      → (P* : LabeledPreType P Q)
      → (p : OptionalLabel S P)
      → .(t : Tail Q T)
        ---------------
      → LabeledType S T
  
  data LabeledPreType : PreType → PreType → Set where
    B : LabeledPreType B B
    _⇒_ : ∀ {S1 S2 T1 T2}
      → (S* : LabeledType S2 S1)
      → (T* : LabeledType T1 T2)
      → LabeledPreType (S1 ⇒ T1) (S2 ⇒ T2)
    _⊗_ : ∀ {S1 S2 T1 T2}
      → (S* : LabeledType S1 S2)
      → (T* : LabeledType T1 T2)
      → LabeledPreType (S1 ⊗ T1) (S2 ⊗ T2)

data InterestingTag (G : Tag) (P Q : PreType) : Set where
  _,_ : .(l : IsTagof G P) → .(r : IsTagof G Q) → InterestingTag G P Q

observeP : ∀ {P Q}
  → LabeledPreType P Q
  → ∃[ G ](InterestingTag G P Q)
observeP B         = `B , `B , `B
observeP (S* ⇒ T*) = `⇒ , `⇒ , `⇒
observeP (S* ⊗ T*) = `⊗ , `⊗ , `⊗

inv-G≢H : ∀ {P T Q}
  → {G H : Tag}
  → ¬ G ≡ H
  → .(GtagP : IsTagof G P)
  → .(HtagQ : IsTagof H Q)
  → .(t : Tail P T)
  → (p : OptionalLabel T Q)
  → T ≡ *
inv-G≢H {T = *} ¬G≡H GtagP HtagQ t p = refl
inv-G≢H {B} {` B} {B} {`B} {`B} ¬G≡H GtagP HtagQ t p = ⊥-elim (¬G≡H refl)
inv-G≢H {S ⇒ T} {` S₁ ⇒ T₁} {S₂ ⇒ T₂} {`⇒} {`⇒} ¬G≡H GtagP HtagQ t p = ⊥-elim (¬G≡H refl)
inv-G≢H {S ⊗ T} {` S₁ ⊗ T₁} {S₂ ⊗ T₂} {`⊗} {`⊗} ¬G≡H GtagP HtagQ t p = ⊥-elim (¬G≡H refl)

dec-tail : ∀ {P Q}
  → Dec (Tail P (` Q))
dec-tail {P} {Q} with (` P) ≟ (` Q)
dec-tail {P} {.P} | yes refl = yes ε
dec-tail {P} {Q}  | no ¬p = no λ { ε → ¬p refl }

dec-tail* : ∀ {P}
  → Dec (Tail P *)
dec-tail* {P} with ground? P
dec-tail* {P} | yes gP = yes (‼ gP)
dec-tail* {P} | no ¬gP = no (λ { (‼ gP) → ⊥-elim-irr (¬gP gP)})

laundering-tail : ∀ {P Q}
  → .(t : Tail P (` Q))
  → Tail P (` Q)
laundering-tail {P}{Q} t with dec-tail {P}{Q}
laundering-tail {P} {Q} t | yes p = p
laundering-tail {P} {Q} t | no ¬p = ⊥-elim-irr (¬p t)

laundering-tail* : ∀ {P}
  → .(t : Tail P *)
  → Tail P *
laundering-tail* {P} t with dec-tail* {P}
laundering-tail* {P} t | yes p = p
laundering-tail* {P} t | no ¬p = ⊥-elim-irr (¬p t)

lau-ground : ∀ {P}
  → .(Ground P)
  → Ground P
lau-ground {P} gP with ground? P
lau-ground {P} gP | yes gP' = gP'
lau-ground {P} gP | no ¬gP' = ⊥-elim-irr (¬gP' gP)

inv-tail : ∀ {P Q}
  → .(t : Tail P (` Q))
  → (` P) ≡ (` Q)
inv-tail t with laundering-tail t
inv-tail t | ε = refl

inv-tail* : ∀ {P}
  → .(t : Tail P *)
  → Ground P
inv-tail* t with laundering-tail* t
inv-tail* t | ‼ gP = lau-ground gP

inv-G≡H : ∀ {P Q G H T}
  → G ≡ H
  → .(GtagP : IsTagof G P)
  → .(HtagQ : IsTagof H Q)
  → .(t : Tail P T)
  → (p : OptionalLabel T Q)
  → P ≡ Q
inv-G≡H refl GtagP HtagQ t ε with inv-tail t
inv-G≡H refl GtagP HtagQ t ε | refl = refl
inv-G≡H {P} {Q} {G} {H} refl GtagP HtagQ t (⁇ l gQl) with inv-tail* t
inv-G≡H {B} {B} {`B} {`B} refl GtagP HtagQ t (⁇ l gQl) | gP = refl
inv-G≡H {* ⇒ *} {* ⇒ *} {`⇒} {`⇒} refl GtagP HtagQ t (⁇ l gQl) | gP = refl
inv-G≡H {* ⊗ *} {* ⊗ *} {`⊗} {`⊗} refl GtagP HtagQ t (⁇ l gQl) | gP = refl

_∘_ : ∀ {T3 T2 T1}
  → LabeledType T2 T3
  → LabeledType T1 T2
  → LabeledType T1 T3
T* ∘ * = T*
T* ∘ ⊥ l G Gp p     = ⊥ l G Gp p
*  ∘ ⟨ P* , p , t ⟩ = ⟨ P* , p , t ⟩
⊥ m H Hrel q   ∘ ⟨ P* , p , t ⟩
  with observeP P*
... | G , Grelₗ , Grelᵣ
  with G ≟tag H
... | yes G≡H = ⊥ m G Grelₗ p
... | no ¬G≡H
  with inv-G≢H ¬G≡H Grelᵣ Hrel t q
... | refl
  with q
... | ⁇ l gQl = ⊥ l G Grelₗ p
⟨ Q* , q , r ⟩ ∘ ⟨ P* , p , t ⟩
  with observeP P* | observeP Q*
... | G , Grelₗ , Grelᵣ | H , Hrelₗ , Hrelᵣ
  with G ≟tag H
... | no ¬G≡H
  with inv-G≢H ¬G≡H Grelᵣ Hrelₗ t q
... | refl
  with q
... | ⁇ m gQl = ⊥ m G Grelₗ p 
(⟨ Q* , q , r ⟩ ∘ ⟨ P* , p , t ⟩) | G , (Grelₗ , Grelᵣ) | H , (Hrelₗ , Hrelᵣ) | yes G≡H
  with inv-G≡H G≡H Grelᵣ Hrelₗ t q
(⟨ B , q , r ⟩ ∘ ⟨ B , p , t ⟩) | G , (Grelₗ , Grelᵣ) | H , (Hrelₗ , Hrelᵣ) | yes G≡H | refl = ⟨ B , p , r ⟩
(⟨ S*2 ⇒ T*2 , q , r ⟩ ∘ ⟨ S*1 ⇒ T*1 , p , t ⟩) | G , (Grelₗ , Grelᵣ) | H , (Hrelₗ , Hrelᵣ) | yes G≡H | refl = ⟨ (S*1 ∘ S*2) ⇒ (T*2 ∘ T*1) , p , r ⟩
(⟨ S*2 ⊗ T*2 , q , r ⟩ ∘ ⟨ S*1 ⊗ T*1 , p , t ⟩) | G , (Grelₗ , Grelᵣ) | H , (Hrelₗ , Hrelᵣ) | yes G≡H | refl = ⟨ (S*2 ∘ S*1) ⊗ (T*2 ∘ T*1) , p , r ⟩

Cast : Type → Type → Set
Cast = LabeledType

_⨟_ : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
c1 ⨟ c2 = c2 ∘ c1

mutual
  id : ∀ T → Cast T T
  id *     = *
  id (` P) = ⟨ id-P P , ε , ε ⟩

  id-P : ∀ P → LabeledPreType P P
  id-P B = B
  id-P (S ⇒ T) = (id S) ⇒ (id T)
  id-P (S ⊗ T) = (id S) ⊗ (id T) 
  
mutual
  ⇑* : Label → ∀ T → Cast T *
  ⇑* l *     = *
  ⇑* l (` P) = ⇑ l P
  
  ⇑ : Label → ∀ P → Cast (` P) *
  ⇑ l B       = ⟨ (B)               , ε , (‼ `B) ⟩
  ⇑ l (S ⇒ T) = ⟨ (⇓* l S ⇒ ⇑* l T) , ε , (‼ `⇒) ⟩
  ⇑ l (S ⊗ T) = ⟨ (⇑* l S ⊗ ⇑* l T) , ε , (‼ `⊗) ⟩

  ⇓* : Label → ∀ T → Cast * T
  ⇓* l *     = *
  ⇓* l (` P) = ⇓ l P
  
  ⇓ : Label → ∀ P → Cast * (` P)
  ⇓ l B       = ⟨ (B)                 , (⁇ l `B) , ε ⟩
  ⇓ l (S ⇒ T) = ⟨ (⇑* l S ⇒ (⇓* l T)) , (⁇ l `⇒) , ε ⟩
  ⇓ l (S ⊗ T) = ⟨ (⇓* l S ⊗ (⇓* l T)) , (⁇ l `⊗) , ε ⟩

tagof : PreType → Tag
tagof B       = `B
tagof (S ⇒ T) = `⇒
tagof (S ⊗ T) = `⊗

tagof-correct : ∀ P → IsTagof (tagof P) P
tagof-correct B = `B
tagof-correct (S ⇒ T) = `⇒
tagof-correct (S ⊗ T) = `⊗

⌈_⌉ : ∀ {T1 T2} → SrcCast T1 T2 → Cast T1 T2
⌈ *   ⟹[ l ] *   ⌉ = *
⌈ *   ⟹[ l ] ` Q ⌉ = ⇓ l Q
⌈ ` P ⟹[ l ] *   ⌉ = ⇑ l P
⌈ ` P ⟹[ l ] ` Q ⌉ with (` P) ⌣? (` Q)
⌈ ` P ⟹[ l ] ` Q ⌉             | no P⌣̸Q = ⊥ l (tagof P) (tagof-correct P) ε
⌈ ` B       ⟹[ l ] ` B       ⌉ | yes ⌣B = ⟨ B , ε , ε ⟩
⌈ ` S1 ⇒ T1 ⟹[ l ] ` S2 ⇒ T2 ⌉ | yes ⌣⇒ = ⟨ ⌈ S2 ⟹[ l ] S1 ⌉ ⇒ ⌈ T1 ⟹[ l ] T2 ⌉ , ε , ε ⟩
⌈ ` L1 ⊗ R1 ⟹[ l ] ` L2 ⊗ R2 ⌉ | yes ⌣⊗ = ⟨ ⌈ L1 ⟹[ l ] L2 ⌉ ⊗ ⌈ R1 ⟹[ l ] R2 ⌉ , ε , ε ⟩

