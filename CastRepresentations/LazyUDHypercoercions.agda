module CastRepresentations.LazyUDHypercoercions (Label : Set) where

open import Types
  renaming (B to TB; _⇒_ to _T⇒_; _⊗_ to _T⊗_)
open import Cast Label using (_⟹[_]_) renaming (Cast to SrcCast)
open import Terms Label
open import S.CastADT Label

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)

infix 100 _⇒_
infix 100 _⊗_

data Head : Type → PreType → Set where
  ε : ∀ {P}
      ---
    → Head (` P) P
  ⁇ : ∀ {P}
    → (gP : Ground P)
    → (l : Label)
      ---
    → Head * P

data Tail : PreType → Type → Set where
  ε : ∀ {P}
      ------------
    → Tail P (` P)
    
  ‼ : ∀ {P}
    → (gP : Ground P)
      ---------------
    → Tail P *

mutual
  data Cast : Type → Type → Set where
    id* :
      ---
      Cast * *
    ↷ : ∀ {A P Q B} →
      (h : Head A P) →
      (m : Body P Q) →
      (t : Tail Q B) →
      ---
      Cast A B
    
  data Body : PreType → PreType → Set where
    ⊥ : ∀ {P Q}
      → (l : Label)
        ---
      → Body P Q

    `_ : ∀ {P Q} →
      (m : PreBody P Q) →
      ---
      Body P Q

  data PreBody : PreType → PreType → Set where
    B :
      ---
      PreBody TB TB
    _⇒_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S2 S1) →
      (c₂ : Cast T1 T2) →
      ---
      PreBody (S1 T⇒ T1) (S2 T⇒ T2)
    _⊗_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S1 S2) →
      (c₂ : Cast T1 T2) →
      ---
      PreBody (S1 T⊗ T1) (S2 T⊗ T2)

data CompatibleTailHead {P : PreType} : ∀ {T} → Tail P T → Head T P → Set where
  none : CompatibleTailHead ε ε
  some : ∀ {l}
    → (G : Ground P)
    → CompatibleTailHead (‼ G) (⁇ G l)

data Gap : ∀ {P T Q} → Tail P T → Head T Q → Set where
  some : ∀ {P Q}
    → {gP : Ground P}
    → {gQ : Ground Q}
    → (¬p : ¬ (P ≡ Q))
    → (l  : Label)
    → Gap (‼ gP) (⁇ gQ l)

  none : ∀ {P T}
    → {t : Tail P T}
    → {h : Head T P}
    → (p : CompatibleTailHead t h)
    → Gap t h
    
check-gap : ∀ {P T Q}
  → (t : Tail P T)
  → (h : Head T Q)
  → Gap t h
check-gap ε ε = none none
check-gap (‼ gP) (⁇ gQ l) with gP ≟G gQ
check-gap (‼ gP) (⁇ gQ l) | yes refl rewrite ground-unique gP gQ = none (some gQ)
check-gap (‼ gP) (⁇ gQ l) | no ¬P≡Q  = some ¬P≡Q l
                                   
mutual
  _⨟_ : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
  id*        ⨟ d   = d
  ↷ h1 m1 t1 ⨟ id* = ↷ h1 m1 t1
  ↷ h1 m1 t1 ⨟ ↷ h2 m2 t2 = ↷ h1 (seq-m m1 t1 h2 m2) t2
                                                     
  seq-m : ∀ {P1 P2 T P3 P4}
    → Body P1 P2
    → Tail P2 T
    → Head T  P3
    → Body P3 P4
    → Body P1 P4
  seq-m (⊥ l1) t1 h2 m2 = ⊥ l1
  seq-m (` m1) t1 h2 m2 with check-gap t1 h2
  seq-m (` m1) .(‼ _) .(⁇ _ l) m2 | some ¬P≡Q l = ⊥ l
  seq-m (` m1) t1 h2 (⊥ l2) | none p = ⊥ l2
  seq-m (` m1) t1 h2 (` m2) | none p = ` (m1 ⨟' m2)
                                              
  _⨟'_ : ∀ {T1 T2 T3} → PreBody T1 T2 → PreBody T2 T3 → PreBody T1 T3
  B ⨟' B = B
  (c₁ ⇒ c₂) ⨟' (c₃ ⇒ c₄) = (c₃ ⨟ c₁) ⇒ (c₂ ⨟ c₄)
  (c₁ ⊗ c₂) ⨟' (c₃ ⊗ c₄) = (c₁ ⨟ c₃) ⊗ (c₂ ⨟ c₄)

mutual
  ⇑ : Label → ∀ T → Cast T *
  ⇑ l *     = id*
  ⇑ l (` TB)     = ↷ ε (` B)               (‼ `B)
  ⇑ l (` S T⇒ T) = ↷ ε (` (⇓ l S ⇒ ⇑ l T)) (‼ `⇒)
  ⇑ l (` S T⊗ T) = ↷ ε (` (⇑ l S ⊗ ⇑ l T)) (‼ `⊗)
  
  ⇓ : Label → ∀ T → Cast * T
  ⇓ l *     = id*
  ⇓ l (` TB)     = ↷ (⁇ `B l) (` B)                 ε
  ⇓ l (` S T⇒ T) = ↷ (⁇ `⇒ l) (` ⇑ l S ⇒ (⇓ l T)) ε
  ⇓ l (` S T⊗ T) = ↷ (⁇ `⊗ l) (` ⇓ l S ⊗ (⇓ l T)) ε

⌈_⌉ : ∀ {T1 T2} → SrcCast T1 T2 → Cast T1 T2
⌈ *   ⟹[ l ] *   ⌉ = id*
⌈ *   ⟹[ l ] ` Q ⌉ = ⇓ l (` Q)
⌈ ` P ⟹[ l ] *   ⌉ = ⇑ l (` P)
⌈ ` P ⟹[ l ] ` Q ⌉ with (` P) ⌣? (` Q)
⌈ ` P ⟹[ l ] ` Q ⌉             | no P⌣̸Q = ↷ ε (⊥ l) ε
⌈ ` TB       ⟹[ l ] ` TB       ⌉ | yes ⌣B = ↷ ε (` B) ε
⌈ ` S1 T⇒ T1 ⟹[ l ] ` S2 T⇒ T2 ⌉ | yes ⌣⇒
  = ↷ ε (` ⌈ S2 ⟹[ l ] S1 ⌉ ⇒ ⌈ T1 ⟹[ l ] T2 ⌉) ε
⌈ ` L1 T⊗ R1 ⟹[ l ] ` L2 T⊗ R2 ⌉ | yes ⌣⊗
  = ↷ ε (` ⌈ L1 ⟹[ l ] L2 ⌉ ⊗ ⌈ R1 ⟹[ l ] R2 ⌉) ε

mutual
  id : ∀ T → Cast T T
  id *
    = id*
  id (` P)
    = ↷ ε (` id-m P) ε

  id-m : ∀ P → PreBody P P
  id-m TB
    = B
  id-m (S T⇒ T)
    = id S ⇒ id T
  id-m (L T⊗ R)
    = (id L) ⊗ (id R)

open import X.BlameStrategies Label using (BlameStrategy; LazyUDBS)
open BlameStrategy LazyUDBS using (Injectable)

open import Error
  using (Error; return; raise; _>>=_; _>=>_
        ;>>=-return; >>=-assoc; >=>-assoc; >=>->>=)
open import S.Values Label Injectable Cast

CastResult : Type → Set
CastResult T = Error Label (Value T)

⟦_⟧t : ∀ {P T}
  → Tail P T
  → Value (` P)
  ---
  → CastResult T
⟦ ‼ gP ⟧t v = return (dyn gP v)
⟦ ε    ⟧t v = return v

proxy : ∀ {P1 P2}
  → Value (` P1)
  → PreBody P1 P2
  ---
  → Value (` P2)
proxy v B = v
proxy (lam⟨ c1 ⇒ c2 ⟩ e E) (c3 ⇒ c4)    = lam⟨ c3 ⨟ c1 ⇒ c2 ⨟ c4 ⟩ e E
proxy (cons⟨ c1 ⊗ c2 ⟩ v1 v2) (c3 ⊗ c4) = cons⟨ c1 ⨟ c3 ⊗ c2 ⨟ c4 ⟩ v1 v2

⟦_⟧m : ∀ {P1 P2}
  → Body P1 P2
  → Value (` P1)
  → CastResult (` P2)
⟦ ⊥ l ⟧m v = raise l
⟦ ` m ⟧m v = return (proxy v m)

⟦_⟧h : ∀ {T P}
  → Head T P
  → Value T
  → CastResult (` P)
⟦ ε      ⟧h v = return v
⟦ ⁇ gQ l ⟧h (dyn gP v) with gP ≟G gQ
⟦ ⁇ gQ l ⟧h (dyn gP v) | yes refl = return v
⟦ ⁇ gQ l ⟧h (dyn gP v) | no ¬P≡Q  = raise l

⟦_⟧ : ∀ {T1 T2}
  → Cast T1 T2
  → Value T1
  ---
  → CastResult T2
⟦ id*     ⟧ v = return v
⟦ ↷ h m t ⟧ v = ⟦ h ⟧h v >>= ⟦ m ⟧m >>= ⟦ t ⟧t

H : CastADT Injectable
H = record
    { Cast = Cast
    ; id  = id
    ; ⌈_⌉ = ⌈_⌉
    ; _⨟_ = _⨟_
    ; ⟦_⟧ = ⟦_⟧
    }

mutual
  identityˡ : ∀ {T1 T2} → (c : Cast T1 T2) → id T1 ⨟ c ≡ c
  identityˡ id* = refl
  identityˡ (↷ (⁇ P l) m t2) = refl
  identityˡ (↷ ε (⊥ l) t2) = refl
  identityˡ (↷ ε (` B) t2) = refl
  identityˡ (↷ ε (` (c₁ ⇒ c₂)) t2) rewrite identityʳ c₁ | identityˡ c₂ = refl
  identityˡ (↷ ε (` (c₁ ⊗ c₂)) t2) rewrite identityˡ c₁ | identityˡ c₂ = refl
  
  identityʳ : ∀ {T1 T2} → (c : Cast T1 T2) → c ⨟ id T2 ≡ c
  identityʳ id* = refl
  identityʳ (↷ t1 m (‼ P)) = refl
  identityʳ (↷ t1 (⊥ l) ε) = refl
  identityʳ (↷ t1 (` B) ε) = refl
  identityʳ (↷ t1 (` (c₁ ⇒ c₂)) ε) rewrite identityˡ c₁ | identityʳ c₂ = refl
  identityʳ (↷ t1 (` (c₁ ⊗ c₂)) ε) rewrite identityʳ c₁ | identityʳ c₂ = refl

mutual
  assoc : ∀ {T1 T2 T3 T4}
    → (c1 : Cast T1 T2)
    → (c2 : Cast T2 T3)
    → (c3 : Cast T3 T4)
    → (c1 ⨟ c2) ⨟ c3 ≡ c1 ⨟ (c2 ⨟ c3)
  assoc id* c2 c3 rewrite identityˡ c2 | identityˡ (c2 ⨟ c3) = refl
  assoc (↷ h₁ m₁ t₁) id* c3 rewrite identityˡ c3 = refl
  assoc (↷ h₁ m₁ t₁) (↷ h₂ m₂ t₂) id* = refl
  assoc (↷ h₁ m₁ t₁) (↷ h₂ m₂ t₂) (↷ h₃ m₃ t₃)
    = cong (λ □ → ↷ h₁ □ t₃) (assoc-seq-m m₁ t₁ h₂ m₂ t₂ h₃ m₃)

  assoc-seq-m : ∀ {P1 P2 T1 P3 P4 T2 P5 P6}
    → (m1 : Body P1 P2)
    → (t1 : Tail P2 T1)
    → (h2 : Head T1 P3)
    → (m2 : Body P3 P4)
    → (t2 : Tail P4 T2)
    → (h3 : Head T2 P5)
    → (m3 : Body P5 P6)
    → (seq-m (seq-m m1 t1 h2 m2) t2 h3 m3) ≡ (seq-m m1 t1 h2 (seq-m m2 t2 h3 m3))
  assoc-seq-m (⊥ l1) t1 h2 m2 t2 h3 m3 = refl
  assoc-seq-m (` m1) t1 h2 m2 t2 h3 m3 with check-gap t1 h2
  assoc-seq-m (` m1) t1 h2 m2 t2 h3 m3 | some ¬P≡Q l = refl
  assoc-seq-m (` m1) t1 h2 (⊥ l2) t2 h3 m3 | none p = refl
  assoc-seq-m (` m1) t1 h2 (` m2) t2 h3 m3 | none p with check-gap t2 h3
  assoc-seq-m (` m1) t1 h2 (` m2) t2 h3 m3 | none p | some ¬P≡Q l = refl
  assoc-seq-m (` m1) t1 h2 (` m2) t2 h3 (⊥ l3) | none p | none q = refl
  assoc-seq-m (` B) t1 h2 (` B) t2 h3 (` B) | none p | none q = refl
  assoc-seq-m (` (c₁ ⇒ c₂)) t1 h2 (` (c₃ ⇒ c₄)) t2 h3 (` (c₅ ⇒ c₆))
    | none p | none q
    = cong₂ (λ □ ■ → (` □ ⇒ ■)) (sym (assoc c₅ c₃ c₁)) (assoc c₂ c₄ c₆) 
  assoc-seq-m (` (c₁ ⊗ c₂)) t1 h2 (` (c₃ ⊗ c₄)) t2 h3 (` (c₅ ⊗ c₆))
    | none p | none q
    = cong₂ (λ □ ■ → (` □ ⊗ ■)) (assoc c₁ c₃ c₅) (assoc c₂ c₄ c₆) 

lem-id-m : ∀ {P}
  → (v : Value (` P))  
  -----------------------------
  → proxy v (id-m P) ≡ v
lem-id-m {TB} v = refl
lem-id-m {S T⇒ T} (lam⟨ c ⇒ d ⟩ e E)  rewrite identityˡ c | identityʳ d = refl
lem-id-m {S T⊗ T} (cons⟨ c ⊗ d ⟩ v u) rewrite identityʳ c | identityʳ d = refl

lem-id : ∀ {T}
  → (v : Value T)  
  -----------------------------
  → ⟦ id T ⟧ v ≡ return v
lem-id {*} v = refl
lem-id {` P} v rewrite lem-id-m v = refl

lem-proxy : ∀ {P1 P2 P3}
  → (v : Value (` P1))
  → (m1 : PreBody P1 P2)
  → (m2 : PreBody P2 P3)
  → proxy v (m1 ⨟' m2) ≡ proxy (proxy v m1) m2
lem-proxy v B B = refl
lem-proxy (lam⟨ c1 ⇒ d1 ⟩ e E) (c2 ⇒ d2) (c3 ⇒ d3)
  rewrite assoc c3 c2 c1 | assoc d1 d2 d3
  = refl
lem-proxy (cons⟨ c1 ⊗ d1 ⟩ v1 v2) (c2 ⊗ d2) (c3 ⊗ d3)
  rewrite assoc c1 c2 c3 | assoc d1 d2 d3
  = refl

lem-seq-m : ∀ {P1 P2 T P3 P4}
  → (m1 : Body P1 P2)
  → (t1 : Tail P2 T)
  → (h2 : Head T  P3)
  → (m2 : Body P3 P4)
  → (∀ v →
       ⟦ seq-m m1 t1 h2 m2 ⟧m v
         ≡
       (⟦ m1 ⟧m >=> ⟦ t1 ⟧t >=> ⟦ h2 ⟧h >=> ⟦ m2 ⟧m) v)
lem-seq-m (⊥ l1) t1 h2 m2 v = refl
lem-seq-m (` m1) ε ε (⊥ l2) v = refl
lem-seq-m (` m1) ε ε (` m2) v = cong return (lem-proxy v m1 m2)
lem-seq-m (` m1) (‼ gP) (⁇ gQ l) m2 v with gP ≟G gQ
lem-seq-m (` m1) (‼ gP) (⁇ gQ l) m2 v | no ¬p = refl
lem-seq-m (` m1) (‼ gP) (⁇ gQ l) (⊥ l2) v | yes refl
  rewrite ground-unique gP gQ = refl
lem-seq-m (` m1) (‼ gP) (⁇ gQ l) (` m2) v | yes refl
  rewrite ground-unique gP gQ = cong return (lem-proxy v m1 m2)

lem-seq : ∀ {T1 T2 T3}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → ∀ v
  --------------------
  → ⟦ c1 ⨟ c2 ⟧ v ≡ ⟦ c1 ⟧ v >>= ⟦ c2 ⟧
lem-seq id* c2 v = refl
lem-seq (↷ h1 m1 t1) id* v = sym (>>=-return _)
lem-seq (↷ h1 m1 t1) (↷ h2 m2 t2) v with ⟦ h1 ⟧h v
lem-seq (↷ h1 m1 t1) (↷ h2 m2 t2) v | raise l   = refl
lem-seq (↷ h1 m1 t1) (↷ h2 m2 t2) v | return v'
  rewrite lem-seq-m m1 t1 h2 m2 v'
  with ⟦ m1 ⟧m v' >>= ⟦ t1 ⟧t
... | raise l    = refl
... | return v'' = refl

H-Basic : CastADTBasic Injectable H
H-Basic = record { lem-id = lem-id ; lem-seq = lem-seq }

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

lem-rewrite-inj : (l : Label)(T : Type)
  → (⇑ l T) ≡ ⌈ T ⟹[ l ] * ⌉
lem-rewrite-inj l * = refl
lem-rewrite-inj l (` P) = refl

lem-rewrite-proj : (l : Label)(T : Type)
  → (⇓ l T) ≡ ⌈ * ⟹[ l ] T ⌉
lem-rewrite-proj l * = refl
lem-rewrite-proj l (` P) = refl

lem-expand-inj : (l : Label)(P : PreType)
  → (⇑ l (` P)) ≡ (⌈ (` P) ⟹[ l ] ` ground P ⌉ ⨟ ⌈ ` ground P ⟹[ l ] * ⌉)
lem-expand-inj l TB = refl
lem-expand-inj l (S T⇒ T)
  rewrite lem-rewrite-proj l S | lem-rewrite-inj l T
    | identityʳ ⌈ T ⟹[ l ] * ⌉
  = refl
lem-expand-inj l (S T⊗ T)
  rewrite lem-rewrite-inj l S | lem-rewrite-inj l T
    | identityʳ ⌈ T ⟹[ l ] * ⌉
    | identityʳ ⌈ S ⟹[ l ] * ⌉
  = refl

lem-expand-proj : (l : Label)(P : PreType)
  → (⇓ l (` P)) ≡ (⌈ * ⟹[ l ] ` ground P ⌉ ⨟ ⌈ ` ground P ⟹[ l ] ` P ⌉)
lem-expand-proj l TB = refl
lem-expand-proj l (S T⇒ T)
  rewrite lem-rewrite-inj l S | lem-rewrite-proj l T
    | identityʳ ⌈ S ⟹[ l ] * ⌉
  = refl
lem-expand-proj l (S T⊗ T)
  rewrite lem-rewrite-proj l S | lem-rewrite-proj l T
  = refl

eq-P* : ∀ {P}
  → (v : Value (` P))
  → (l : Label)
  → ¬ Ground P
  → ⟦ ⌈ (` P) ⟹[ l ] * ⌉ ⟧ v
      ≡
    ⟦ ⌈ (` P) ⟹[ l ] (` ground P) ⌉ ⟧ v >>= ⟦ ⌈ (` ground P) ⟹[ l ] * ⌉ ⟧
eq-P* {P} v l ¬gP
  rewrite lem-expand-inj l P
  | lem-seq ⌈ (` P) ⟹[ l ] (` ground P) ⌉ ⌈ (` ground P) ⟹[ l ] * ⌉ v
  = refl

eq-I* : ∀ {P}
  → (v : Value (` P))
  → (l : Label)
  → (gP : Ground P)
  → ⟦ ⌈ ` P ⟹[ l ] * ⌉ ⟧ v
      ≡
    return (dyn gP v)
eq-I* {.TB} v l `B = refl
eq-I* {.(* T⇒ *)} (lam⟨ c1 ⇒ c2 ⟩ e E) l `⇒
  rewrite identityʳ c2
  = refl
eq-I* {.(* T⊗ *)} (cons⟨ c1 ⊗ c2 ⟩ v v₁) l `⊗
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
  rewrite lem-expand-proj l P
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
eq-*I-fail {TB} v l `B `B ¬p = ⊥-elim (¬p refl)
eq-*I-fail {TB} v l `B `⇒ ¬p = refl
eq-*I-fail {TB} v l `B `⊗ ¬p = refl
eq-*I-fail {.* T⇒ .*} v l `⇒ `B ¬p = refl
eq-*I-fail {.* T⇒ .*} v l `⇒ `⇒ ¬p = ⊥-elim (¬p refl)
eq-*I-fail {.* T⇒ .*} v l `⇒ `⊗ ¬p = refl
eq-*I-fail {.* T⊗ .*} v l `⊗ `B ¬p = refl
eq-*I-fail {.* T⊗ .*} v l `⊗ `⇒ ¬p = refl
eq-*I-fail {.* T⊗ .*} v l `⊗ `⊗ ¬p = ⊥-elim (¬p refl)

H-LazyUD : LazyUD H
H-LazyUD = record
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
