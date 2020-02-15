module CastRepresentations.LazyUDCanonicalCoercions (Label : Set) where

open import Types
open import Cast Label using (_⟹[_]_) renaming (Cast to SrcCast)
open import Terms Label
open import S.CastADT Label

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

mutual

  data CoeG : PreType → PreType → Set where
  
    B : CoeG B B
    
    _⇒_ : ∀ {S1 T1 S2 T2}
      → (s : CoeS S2 S1)
      → (t : CoeS T1 T2)
      → CoeG (S1 ⇒ T1) (S2 ⇒ T2)
      
    _⊗_ : ∀ {S1 T1 S2 T2}
      → (s : CoeS S1 S2)
      → (t : CoeS T1 T2)
      → CoeG (S1 ⊗ T1) (S2 ⊗ T2)

  data CoeI : PreType → Type → Set where
  
    _,_‼ : ∀ {P Q}
      → (g : CoeG P Q)
      → (G : Ground Q)
      → CoeI P *
  
    `_ : ∀ {P Q}
      → (g : CoeG P Q)
      → CoeI P (` Q)
  
    ⊥ : ∀ {A P Q T}
      → (A⌣P : (` A) ⌣ (` P))
      → (G : Ground P)
      → (l : Label)
      → (H : Ground Q)
      → (¬P≡Q : ¬ (_≡_ {A = Type} (` P) (` Q)))
      → CoeI A T
  
  data CoeS : Type → Type → Set where
  
    id*   : CoeS * *
    
    _⁇_,_ : ∀ {P T}
      → (G : Ground P)
      → (l : Label)
      → (i : CoeI P T)
      → CoeS * T
      
    `_    : ∀ {P T}
      → (i : CoeI P T)
      → CoeS (` P) T

Cast : Type → Type → Set
Cast = CoeS

lem-g⌣ : ∀ {P Q} → CoeG P Q → (` P) ⌣ (` Q)
lem-g⌣ B = ⌣B
lem-g⌣ (s ⇒ t) = ⌣⇒
lem-g⌣ (s ⊗ t) = ⌣⊗

mutual
  _g⨟g_ : ∀ {T1 T2 T3} → CoeG T1 T2 → CoeG T2 T3 → CoeG T1 T3
  B g⨟g B = B
  (s1 ⇒ t1) g⨟g (s2 ⇒ t2) = (s2 ⨟ s1) ⇒ (t1 ⨟ t2)
  (s1 ⊗ t1) g⨟g (s2 ⊗ t2) = (s1 ⨟ s2) ⊗ (t1 ⨟ t2)

  _g⨟i_ : ∀ {T1 T2 T3} → CoeG T1 T2 → CoeI T2 T3 → CoeI T1 T3
  g g⨟i (  h , G ‼) =   (g g⨟g h) , G ‼
  g g⨟i (` h      ) = ` (g g⨟g h)
  g g⨟i ⊥ A⌣P G l H ¬P≡Q = ⊥ (⌣trans (lem-g⌣ g) A⌣P) G l H ¬P≡Q

  _i⨟s_ : ∀ {T1 T2 T3} → CoeI T1 T2 → CoeS T2 T3 → CoeI T1 T3
  ⊥ A⌣G G l H ¬G≡H i⨟s s = ⊥ A⌣G G l H ¬G≡H
  (g , G ‼) i⨟s id* = (g , G ‼)
  (g , G ‼) i⨟s (H ⁇ l , i) with (` unground G) ≟ (` unground H)
  (g , G ‼) i⨟s (H ⁇ l , i) | yes refl = g g⨟i i
  (g , G ‼) i⨟s (H ⁇ l , i) | no ¬G≡H  = ⊥ (lem-g⌣ g) G l H ¬G≡H
  (` g) i⨟s (` i) = (g g⨟i i)

  _⨟_ : ∀ {T1 T2 T3} → CoeS T1 T2 → CoeS T2 T3 → CoeS T1 T3
  id* ⨟ t = t
  (G ⁇ l , i) ⨟ t = G ⁇ l , (i i⨟s t)
  (`       i) ⨟ t = `       (i i⨟s t)

mutual
  id : ∀ T → CoeS T T
  id *
    = id*
  id (` P)
    = ` (` id-g P)

  id-g : ∀ P → CoeG P P
  id-g B
    = B
  id-g (S ⇒ T)
    = id S ⇒ id T
  id-g (S ⊗ T)
    = (id S) ⊗ (id T)

⌈_⌉ : ∀ {T1 T2} → SrcCast T1 T2 → Cast T1 T2
⌈ *   ⟹[ l ] *   ⌉ = id*
⌈ *   ⟹[ l ] ` Q ⌉ with ground? Q
⌈ *   ⟹[ l ] ` Q ⌉ | yes gQ = gQ                ⁇ l , (` id-g Q)
⌈ *   ⟹[ l ] ` Q ⌉ | no ¬gQ = (ground-Ground Q) ⁇ l , {!!}
⌈ ` P ⟹[ l ] *   ⌉ = {!!}
⌈ ` P ⟹[ l ] ` Q ⌉ with (` P) ⌣? (` Q)
⌈ ` P ⟹[ l ] ` Q ⌉             | no ¬P⌣Q
  = ` ⊥ (ground-⌣ P) (ground-Ground P) l (ground-Ground Q)
        (ground-≢ (ground-Ground P) (ground-Ground Q) (¬⌣-¬ground⌣ ¬P⌣Q))
⌈ ` B       ⟹[ l ] ` B       ⌉ | yes ⌣B = ` (` B)
⌈ ` S1 ⇒ T1 ⟹[ l ] ` S2 ⇒ T2 ⌉ | yes ⌣⇒ = ` (` ⌈ S2 ⟹[ l ] S1 ⌉ ⇒ ⌈ T1 ⟹[ l ] T2 ⌉)
⌈ ` S1 ⊗ T1 ⟹[ l ] ` S2 ⊗ T2 ⌉ | yes ⌣⊗ = ` (` ⌈ S1 ⟹[ l ] S2 ⌉ ⊗ ⌈ T1 ⟹[ l ] T2 ⌉)
