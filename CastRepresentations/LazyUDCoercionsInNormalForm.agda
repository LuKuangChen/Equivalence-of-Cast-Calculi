module CastRepresentations.LazyUDCoercionsInNormalForm (Label : Set) where

open import Types renaming (B to tB; _⇒_ to _t⇒_; _⊗_ to _t⊗_)
open import Cast Label using (_⟹[_]_) renaming (Cast to SrcCast)
open import Terms Label
open import S.CastADT Label

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

infix  99 `_
infix 100 _⇒_
infix 100 _⊗_

mutual

  data CoeG : PreType → PreType → Set where
  
    B : CoeG tB tB
    
    _⇒_ : ∀ {S1 T1 S2 T2}
      → (s : CoeS S2 S1)
      → (t : CoeS T1 T2)
      → CoeG (S1 t⇒ T1) (S2 t⇒ T2)
      
    _⊗_ : ∀ {S1 T1 S2 T2}
      → (s : CoeS S1 S2)
      → (t : CoeS T1 T2)
      → CoeG (S1 t⊗ T1) (S2 t⊗ T2)

  data CoeI : PreType → Type → Set where
  
    ⊥ : ∀ {A P Q}
      → (A⌣G : (` A) ⌣ (` P))
      → (G : Ground P)
      → (l : Label)
      → (H : Ground Q)
      → (¬G≡H : ¬ (P ≡ Q))
      → ∀ {T}
      → CoeI A T
  
    _,_‼ : ∀ {P Q}
      → (g : CoeG P Q)
      → (G : Ground Q)
      → CoeI P *
  
    `_ : ∀ {P Q}
      → (g : CoeG P Q)
      → CoeI P (` Q)
  
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
  (g , G ‼) i⨟s (H ⁇ l , i) with G ≟G H
  (g , G ‼) i⨟s (H ⁇ l , i) | yes refl = g g⨟i i
  (g , G ‼) i⨟s (H ⁇ l , i) | no ¬G≡H  = ⊥ (lem-g⌣ g) G l H ¬G≡H
  (` g) i⨟s (` i) = (g g⨟i i)

  _⨟_ : ∀ {T1 T2 T3} → CoeS T1 T2 → CoeS T2 T3 → CoeS T1 T3
  id* ⨟ t = t
  (G ⁇ l , i) ⨟ t = G ⁇ l , (i i⨟s t)
  (`       i) ⨟ t = `       (i i⨟s t)
                                      
mutual
  ⇑* : Label → ∀ T → Cast T *
  ⇑* l *     = id*
  ⇑* l (` P) = ⇑ l P
  
  ⇑ : Label → ∀ P → Cast (` P) *
  ⇑ l tB       = ` (B , `B ‼)
  ⇑ l (S t⇒ T) = ` (⇓* l S ⇒ ⇑* l T , `⇒ ‼)
  ⇑ l (S t⊗ T) = ` (⇑* l S ⊗ ⇑* l T , `⊗ ‼)

  ⇓* : Label → ∀ T → Cast * T
  ⇓* l *     = id*
  ⇓* l (` P) = ⇓ l P
  
  ⇓ : Label → ∀ P → Cast * (` P)
  ⇓ l tB       = (`B ⁇ l , ` B)                
  ⇓ l (S t⇒ T) = (`⇒ ⁇ l , ` ⇑* l S ⇒ (⇓* l T))
  ⇓ l (S t⊗ T) = (`⊗ ⁇ l , ` ⇓* l S ⊗ (⇓* l T))

lem-¬⌣-ground : {P Q : PreType}
  → ¬ (` P) ⌣ (` Q)
  → ¬ (ground P ≡ ground Q)
lem-¬⌣-ground {tB} {tB} ¬p = λ _ → ¬p ⌣B
lem-¬⌣-ground {tB} {S t⇒ T} ¬p = λ ()
lem-¬⌣-ground {tB} {S t⊗ T} ¬p = λ ()
lem-¬⌣-ground {S t⇒ T} {tB} ¬p = λ ()
lem-¬⌣-ground {S t⇒ T} {S₁ t⇒ T₁} ¬p = λ _ → ¬p ⌣⇒
lem-¬⌣-ground {S t⇒ T} {S₁ t⊗ T₁} ¬p = λ ()
lem-¬⌣-ground {S t⊗ T} {tB} ¬p = λ ()
lem-¬⌣-ground {S t⊗ T} {S₁ t⇒ T₁} ¬p = λ ()
lem-¬⌣-ground {S t⊗ T} {S₁ t⊗ T₁} ¬p = λ _ → ¬p ⌣⊗

⌈_⌉ : ∀ {T1 T2} → SrcCast T1 T2 → Cast T1 T2
⌈ *   ⟹[ l ] *   ⌉ = id*
⌈ *   ⟹[ l ] ` Q ⌉ = ⇓ l Q
⌈ ` P ⟹[ l ] *   ⌉ = ⇑ l P
⌈ ` P ⟹[ l ] ` Q ⌉ with (` P) ⌣? (` Q)
⌈ ` P ⟹[ l ] ` Q ⌉             | no ¬P⌣Q
  = ` (⊥ (ground-⌣ P) (ground-Ground P) l (ground-Ground Q) (lem-¬⌣-ground ¬P⌣Q))
⌈ ` tB       ⟹[ l ] ` tB       ⌉ | yes ⌣B = ` (` B)
⌈ ` S1 t⇒ T1 ⟹[ l ] ` S2 t⇒ T2 ⌉ | yes ⌣⇒
  = ` (` ⌈ S2 ⟹[ l ] S1 ⌉ ⇒ ⌈ T1 ⟹[ l ] T2 ⌉)
⌈ ` L1 t⊗ R1 ⟹[ l ] ` L2 t⊗ R2 ⌉ | yes ⌣⊗
  = ` (` ⌈ L1 ⟹[ l ] L2 ⌉ ⊗ ⌈ R1 ⟹[ l ] R2 ⌉)


mutual
  id : ∀ T → CoeS T T
  id *
    = id*
  id (` P)
    = ` (` id-g P)

  id-g : ∀ P → CoeG P P
  id-g tB
    = B
  id-g (S t⇒ T)
    = id S ⇒ id T
  id-g (S t⊗ T)
    = (id S) ⊗ (id T)

open import R.BlameStrategies Label using (BlameStrategy; LazyUDBS)
open BlameStrategy LazyUDBS using (Injectable)

open import S.Values Label Injectable Cast

open import Error
  using (Error; return; raise; _>>=_; _>=>_
        ;>>=-return; >>=-assoc; >=>-assoc; >=>->>=)

CastResult : Type → Set
CastResult T = Error Label (Value T)

⟦_⟧g : ∀ {P Q}
  → CoeG P Q
  → Value (` P)
  → Value (` Q)
⟦ B ⟧g v = v
⟦ s2 ⇒ t2 ⟧g (lam⟨ s1 ⇒ t1 ⟩ e E) = lam⟨ s2 ⨟ s1 ⇒ t1 ⨟ t2 ⟩ e E
⟦ s2 ⊗ t2 ⟧g (cons⟨ s1 ⊗ t1 ⟩ v u) = cons⟨ s1 ⨟ s2 ⊗ t1 ⨟ t2 ⟩ v u

⟦_⟧i : ∀ {P T}
  → CoeI P T
  → Value (` P)
  → CastResult T
⟦ g , G ‼ ⟧i v = return ((dyn G) (⟦ g ⟧g v))
⟦ ` g     ⟧i v = return (⟦ g ⟧g v)
⟦ ⊥ A⌣G G l H ¬G≡H ⟧i v = raise l

project : ∀ {P}
  → Ground P
  → Label
  → Value *
  → CastResult (` P)
project H l (dyn G v) with G ≟G H
project H l (dyn G v) | yes refl = return v
project H l (dyn G v) | no ¬G≡H  = raise l

⟦_⟧ : ∀ {S T}
  → Cast S T
  → Value S
  → CastResult T
⟦ id*       ⟧ v = return v
⟦ G ⁇ l , i ⟧ v = project G l v >>= ⟦ i ⟧i
⟦ ` i       ⟧ v = ⟦ i ⟧i v

S : CastADT Injectable
S = record
    { Cast = Cast
    ; id  = id
    ; ⌈_⌉ = ⌈_⌉
    ; _⨟_ = _⨟_
    ; ⟦_⟧ = ⟦_⟧
    }

mutual
  g-identityˡ : ∀ {P1 P2} → (g : CoeG P1 P2) → id-g P1 g⨟g g ≡ g
  g-identityˡ B = refl
  g-identityˡ (s ⇒ t) rewrite identityʳ s | identityˡ t = refl
  g-identityˡ (s ⊗ t) rewrite identityˡ s | identityˡ t = refl
  
  g-identityʳ : ∀ {P1 P2} → (g : CoeG P1 P2) → g g⨟g id-g P2 ≡ g
  g-identityʳ B = refl
  g-identityʳ (s ⇒ t) rewrite identityˡ s | identityʳ t = refl
  g-identityʳ (s ⊗ t) rewrite identityʳ s | identityʳ t = refl

  i-identityʳ : ∀ {P1 P2} → (i : CoeI P1 P2) → i i⨟s id P2 ≡ i
  i-identityʳ (g , G ‼) = refl
  i-identityʳ (` g) rewrite g-identityʳ g = refl
  i-identityʳ (⊥ A⌣G G l H ¬G≡H) = refl

  identityˡ : ∀ {T1 T2} → (c : Cast T1 T2) → id T1 ⨟ c ≡ c
  identityˡ id* = refl
  identityˡ (G ⁇ l , i) = refl
  identityˡ (` (g , G ‼)) rewrite g-identityˡ g = refl
  identityˡ (` (` g))     rewrite g-identityˡ g = refl
  identityˡ (` ⊥ A⌣G G l H ¬G≡H) = cong (λ □ → (` ⊥ □ G l H ¬G≡H)) (⌣unique _ _)
  
  identityʳ : ∀ {T1 T2} → (c : Cast T1 T2) → c ⨟ id T2 ≡ c
  identityʳ id* = refl
  identityʳ (G ⁇ l , i) rewrite i-identityʳ i = refl
  identityʳ (` i) rewrite i-identityʳ i = refl

mutual
  assoc-ggg : ∀ {T1 T2 T3 T4}
    → (c1 : CoeG T1 T2)
    → (c2 : CoeG T2 T3)
    → (c3 : CoeG T3 T4)
    → (c1 g⨟g c2) g⨟g c3 ≡ c1 g⨟g (c2 g⨟g c3)
  assoc-ggg B B B = refl
  assoc-ggg (s1 ⇒ t1) (s2 ⇒ t2) (s3 ⇒ t3)
    rewrite assoc s3 s2 s1 | assoc t1 t2 t3
    = refl
  assoc-ggg (s1 ⊗ t1) (s2 ⊗ t2) (s3 ⊗ t3)
    rewrite assoc s1 s2 s3 | assoc t1 t2 t3
    = refl

  assoc-ggi : ∀ {T1 T2 T3 T4}
    → (c1 : CoeG T1 T2)
    → (c2 : CoeG T2 T3)
    → (c3 : CoeI T3 T4)
    → (c1 g⨟g c2) g⨟i c3 ≡ c1 g⨟i (c2 g⨟i c3)
  assoc-ggi g1 g2 (⊥ A⌣G G l H ¬G≡H) = cong (λ □ → ⊥ □ G l H ¬G≡H) (⌣unique _ _)
  assoc-ggi g1 g2 (g , G ‼)
    rewrite assoc-ggg g1 g2 g = refl
  assoc-ggi g1 g2 (` g)
    rewrite assoc-ggg g1 g2 g = refl
  
  assoc-gis : ∀ {T1 T2 T3 T4}
    → (c1 : CoeG T1 T2)
    → (c2 : CoeI T2 T3)
    → (c3 : CoeS T3 T4)
    → (c1 g⨟i c2) i⨟s c3 ≡ c1 g⨟i (c2 i⨟s c3)
  assoc-gis g1 (⊥ A⌣G G l H ¬G≡H) s = refl
  assoc-gis g1 (g2 , G ‼) id* = refl
  assoc-gis g1 (g2 , G ‼) (H ⁇ l , i3) with G ≟G H
  assoc-gis g1 (g2 , G ‼) (H ⁇ l , i3) | no ¬p
    = cong (λ □ → ⊥ □ G l H ¬p) (⌣unique _ _)
  assoc-gis g1 (g2 , G ‼) (H ⁇ l , i3) | yes refl
    rewrite assoc-ggi g1 g2 i3 = refl
  assoc-gis g1 (` g2) (` i3)
    rewrite assoc-ggi g1 g2 i3 = refl

  assoc-iss : ∀ {T1 T2 T3 T4}
    → (c1 : CoeI T1 T2)
    → (c2 : Cast T2 T3)
    → (c3 : Cast T3 T4)
    → (c1 i⨟s c2) i⨟s c3 ≡ c1 i⨟s (c2 ⨟ c3)
  assoc-iss (⊥ A⌣G G l H ¬G≡H) s1 s2 = refl
  assoc-iss (g , G ‼) id* s2 = refl
  assoc-iss (g , G ‼) (H ⁇ l , i) s2 with G ≟G H
  assoc-iss (g , G ‼) (H ⁇ l , i) s2 | no ¬G≡H  = refl
  assoc-iss (g , G ‼) (H ⁇ l , i) s2 | yes refl rewrite assoc-gis g i s2 = refl
  assoc-iss (` g) (` i) s2 rewrite assoc-gis g i s2 = refl

  assoc : ∀ {T1 T2 T3 T4}
    → (c1 : Cast T1 T2)
    → (c2 : Cast T2 T3)
    → (c3 : Cast T3 T4)
    → (c1 ⨟ c2) ⨟ c3 ≡ c1 ⨟ (c2 ⨟ c3)
  assoc id* c2 c3 = refl
  assoc (G ⁇ l , i) c2 c3 rewrite assoc-iss i c2 c3 = refl
  assoc (` i) c2 c3 rewrite assoc-iss i c2 c3 = refl

lem-id : ∀ {T}
  → (v : Value T)  
  -----------------------------
  → ⟦ id T ⟧ v ≡ return v
lem-id {*} v = refl
lem-id {` tB} v = refl
lem-id {` S t⇒ T} (lam⟨ s ⇒ t ⟩ e E)
  rewrite identityˡ s | identityʳ t
  = refl
lem-id {` S t⊗ T} (cons⟨ s ⊗ t ⟩ v u)
  rewrite identityʳ s | identityʳ t
  = refl

lem-g⨟g : ∀ {T1 T2 T3}
  → (c1 : CoeG T1 T2)
  → (c2 : CoeG T2 T3)
  → ∀ v
  --------------------
  → ⟦ c1 g⨟g c2 ⟧g v ≡ ⟦ c2 ⟧g (⟦ c1 ⟧g v) 
lem-g⨟g B B v = refl
lem-g⨟g (s2 ⇒ t2) (s3 ⇒ t3) (lam⟨ s1 ⇒ t1 ⟩ e E)
  rewrite assoc s3 s2 s1 | assoc t1 t2 t3
  = refl
lem-g⨟g (s2 ⊗ t2) (s3 ⊗ t3) (cons⟨ s1 ⊗ t1 ⟩ v u)
  rewrite assoc s1 s2 s3 | assoc t1 t2 t3
  = refl

lem-g⨟i : ∀ {T1 T2 T3}
  → (c1 : CoeG T1 T2)
  → (c2 : CoeI T2 T3)
  → ∀ v
  --------------------
  → ⟦ c1 g⨟i c2 ⟧i v ≡ (return (⟦ c1 ⟧g v)) >>= ⟦ c2 ⟧i
lem-g⨟i g1 (g2 , G ‼) v rewrite lem-g⨟g g1 g2 v = refl
lem-g⨟i g1 (` g2)     v rewrite lem-g⨟g g1 g2 v = refl
lem-g⨟i g1 (⊥ A⌣G G l H ¬G≡H) v = refl

lem-i⨟s : ∀ {T1 T2 T3}
  → (c1 : CoeI T1 T2)
  → (c2 : CoeS T2 T3)
  → ∀ v
  --------------------
  → ⟦ c1 i⨟s c2 ⟧i v ≡ ⟦ c1 ⟧i v >>= ⟦ c2 ⟧
lem-i⨟s (g , G ‼) id* v = refl
lem-i⨟s (g , G ‼) (H ⁇ l , i) v with G ≟G H
lem-i⨟s (g , G ‼) (H ⁇ l , i) v | yes refl = lem-g⨟i g i v
lem-i⨟s (g , G ‼) (H ⁇ l , i) v | no ¬G≡H  = refl
lem-i⨟s (` g) (` i) v = lem-g⨟i g i v
lem-i⨟s (⊥ A⌣G G l H ¬G≡H) s v = refl

lem-seq : ∀ {T1 T2 T3}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → ∀ v
  --------------------
  → ⟦ c1 ⨟ c2 ⟧ v ≡ ⟦ c1 ⟧ v >>= ⟦ c2 ⟧
lem-seq id* t v = refl
lem-seq (G1 ⁇ l1 , i1) t v with project G1 l1 v
lem-seq (G1 ⁇ l1 , i1) t v | raise  l' = refl
lem-seq (G1 ⁇ l1 , i1) t v | return v' = lem-i⨟s i1 t v'
lem-seq (` i1) t v = lem-i⨟s i1 t v

S-Basic : CastADTBasic Injectable S
S-Basic = record { lem-id = lem-id ; lem-seq = lem-seq }

open import S.LazyUDCastADT Label

eq-¬⌣ : ∀ {T1 T2}
  → (v : Value T1)
  → (l : Label)
  → ¬ (T1 ⌣ T2)
  ---
  → ⟦ ⌈ T1 ⟹[ l ] T2 ⌉ ⟧ v
      ≡
    raise l
eq-¬⌣ {*} {*} v l ¬p = ⊥-elim (¬p *⌣*)
eq-¬⌣ {*} {` P} v l ¬p = ⊥-elim (¬p (*⌣P P))
eq-¬⌣ {` P} {*} v l ¬p = ⊥-elim (¬p (P⌣* P))
eq-¬⌣ {` P} {` Q} v l ¬p with (` P) ⌣? (` Q)
eq-¬⌣ {` P} {` Q} v l ¬p | yes p' = ⊥-elim (¬p p')
eq-¬⌣ {` P} {` Q} v l ¬p | no ¬p' = refl

lem-⇑* : (l : Label)(T : Type)
  → (⇑* l T) ≡ ⌈ T ⟹[ l ] * ⌉
lem-⇑* l * = refl
lem-⇑* l (` P) = refl

lem-⇓* : (l : Label)(T : Type)
  → (⇓* l T) ≡ ⌈ * ⟹[ l ] T ⌉
lem-⇓* l * = refl
lem-⇓* l (` P) = refl

lem-⇑ : (l : Label)(P : PreType)
  → (⇑ l P) ≡ (⌈ (` P) ⟹[ l ] ` ground P ⌉ ⨟ ⌈ ` ground P ⟹[ l ] * ⌉)
lem-⇑ l tB = refl
lem-⇑ l (S t⇒ T)
  rewrite lem-⇓* l S | lem-⇑* l T
    | identityʳ ⌈ T ⟹[ l ] * ⌉
  = refl
lem-⇑ l (S t⊗ T)
  rewrite lem-⇑* l S | lem-⇑* l T
    | identityʳ ⌈ T ⟹[ l ] * ⌉
    | identityʳ ⌈ S ⟹[ l ] * ⌉
  = refl

lem-⇓ : (l : Label)(P : PreType)
  → (⇓ l P) ≡ (⌈ * ⟹[ l ] ` ground P ⌉ ⨟ ⌈ ` ground P ⟹[ l ] ` P ⌉)
lem-⇓ l tB = refl
lem-⇓ l (S t⇒ T)
  rewrite lem-⇑* l S | lem-⇓* l T
    | identityʳ ⌈ S ⟹[ l ] * ⌉
  = refl
lem-⇓ l (S t⊗ T)
  rewrite lem-⇓* l S | lem-⇓* l T
  = refl

eq-P* : ∀ {P}
  → (v : Value (` P))
  → (l : Label)
  → ¬ Ground P
  → ⟦ ⌈ (` P) ⟹[ l ] * ⌉ ⟧ v
      ≡
    ⟦ ⌈ (` P) ⟹[ l ] (` ground P) ⌉ ⟧ v >>= ⟦ ⌈ (` ground P) ⟹[ l ] * ⌉ ⟧
eq-P* {P} v l ¬gP
  rewrite lem-⇑ l P
  | lem-seq ⌈ (` P) ⟹[ l ] (` ground P) ⌉ ⌈ (` ground P) ⟹[ l ] * ⌉ v
  = refl

eq-I* : ∀ {P}
  → (v : Value (` P))
  → (l : Label)
  → (gP : Ground P)
  → ⟦ ⌈ ` P ⟹[ l ] * ⌉ ⟧ v
      ≡
    return (dyn gP v)
eq-I* {.tB} v l `B = refl
eq-I* {.(* t⇒ *)} (lam⟨ c1 ⇒ c2 ⟩ e E) l `⇒
  rewrite identityʳ c2
  = refl
eq-I* {.(* t⊗ *)} (cons⟨ c1 ⊗ c2 ⟩ v v₁) l `⊗
  rewrite identityʳ c1 | identityʳ c2
  = refl

eq-*P : ∀ {P}
  → (v : Value *)
  → (l : Label)
  → ¬ Ground P
  → ⟦ ⌈ * ⟹[ l ] (` P) ⌉ ⟧ v
      ≡
    ⟦ ⌈ * ⟹[ l ] (` ground P) ⌉ ⟧ v >>= ⟦ ⌈ (` ground P) ⟹[ l ] (` P) ⌉ ⟧
eq-*P {P} v l ¬gP
  rewrite lem-⇓ l P
  | lem-seq ⌈ * ⟹[ l ] (` ground P) ⌉ ⌈ (` ground P) ⟹[ l ] (` P) ⌉ v
  = refl

eq-*I-succ : ∀ {P}
  → (v : Value (` P))
  → (l : Label)
  → (gP : Ground P)
  → ⟦ ⌈ * ⟹[ l ] (` P) ⌉ ⟧ (dyn gP v)
      ≡
    return v
eq-*I-succ v l `B = refl
eq-*I-succ (lam⟨ c1 ⇒ c2 ⟩ e E) l `⇒
  rewrite identityʳ c2
  = refl
eq-*I-succ (cons⟨ c1 ⊗ c2 ⟩ v v₁) l `⊗
  rewrite identityʳ c1 | identityʳ c2
  = refl
    
eq-*I-fail : {P Q : PreType}
  → (v : Value (` P))  
  → (l : Label)
  → (gP : Ground P)
  → (gQ : Ground Q)
  → ¬ (_≡_ {A = Type} (` P) (` Q))
  → ⟦ ⌈ * ⟹[ l ] (` Q) ⌉ ⟧ (dyn gP v)
      ≡
    raise l
eq-*I-fail {tB} v l `B `B ¬p = ⊥-elim (¬p refl)
eq-*I-fail {tB} v l `B `⇒ ¬p = refl
eq-*I-fail {tB} v l `B `⊗ ¬p = refl
eq-*I-fail {.* t⇒ .*} v l `⇒ `B ¬p = refl
eq-*I-fail {.* t⇒ .*} v l `⇒ `⇒ ¬p = ⊥-elim (¬p refl)
eq-*I-fail {.* t⇒ .*} v l `⇒ `⊗ ¬p = refl
eq-*I-fail {.* t⊗ .*} v l `⊗ `B ¬p = refl
eq-*I-fail {.* t⊗ .*} v l `⊗ `⇒ ¬p = refl
eq-*I-fail {.* t⊗ .*} v l `⊗ `⊗ ¬p = ⊥-elim (¬p refl)

S-LazyUD : LazyUD S
S-LazyUD = record
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
