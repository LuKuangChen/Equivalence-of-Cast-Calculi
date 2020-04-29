module CastRepresentations.LazyDHypercoercions (Label : Set) where

open import Types
open import Variables
open import Cast Label using (_⟹[_]_) renaming (Cast to SrcCast)
open import Terms Label
open import S.CastADT Label

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)


data Head : Type → PreType → Set where
  ⁇ : ∀ P →
    (l : Label) →
    ---
    Head * P
  ε : ∀ {P} →
    ---
    Head (` P) P

data Tail : PreType → Type → Set where
  ‼ : ∀ P
      ---
    → Tail P *
  ε : ∀ {P} →
    ---
    Tail P (` P)

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
    B̂ :
      ---
      PreBody B B
    _⇒̂_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S2 S1) →
      (c₂ : Cast T1 T2) →
      ---
      PreBody (S1 ⇒ T1) (S2 ⇒ T2)
    _⊗̂_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S1 S2) →
      (c₂ : Cast T1 T2) →
      ---
      PreBody (S1 ⊗ T1) (S2 ⊗ T2)

data GapT : Type → Type → Set where
  none : ∀ {T} → GapT T T
  some : (l : Label) → ∀ T1 T2 → GapT T1 T2

GapP : PreType → PreType → Set
GapP P Q = GapT (` P) (` Q)

data Check : ∀ {P Q} → GapP P Q → Set where
  bad : ∀ {P Q}
    → (¬P⌣Q : ¬ ((` P) ⌣ (` Q)))
    → (l    : Label)
    → Check (some l (` P) (` Q))

  good : ∀ {P Q}
    → (P⌣Q : (` P) ⌣ (` Q))
    → {g : GapP P Q}
    → Check g

check-gap : ∀ {P Q}
  → (g : GapP P Q)
  → Check g
check-gap none = good (⌣refl _)
check-gap (some l (` P) (` Q)) with (` P) ⌣? (` Q)
check-gap (some l P Q) | no ¬p = bad ¬p l
check-gap (some l P Q) | yes p = good p

g-dom : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⇒ T2) (T3 ⇒ T4)
  → GapT T3 T1
g-dom none = none
g-dom (some l (` T1 ⇒ T2) (` T3 ⇒ T4)) = some l T3 T1

g-cod : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⇒ T2) (T3 ⇒ T4)
  → GapT T2 T4
g-cod none = none
g-cod (some l (` T1 ⇒ T2) (` T3 ⇒ T4)) = some l T2 T4

g-car : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊗ T2) (T3 ⊗ T4)
  → GapT T1 T3
g-car none = none
g-car (some l (` T1 ⊗ T2) (` T3 ⊗ T4)) = some l T1 T3

g-cdr : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊗ T2) (T3 ⊗ T4)
  → GapT T2 T4
g-cdr none = none
g-cdr (some l (` T1 ⊗ T2) (` T3 ⊗ T4)) = some l T2 T4

mk-proj : ∀ {T P}
  → GapT * T
  → Head T P
  ---
  → Head * P
mk-proj g (⁇ P l) = (⁇ P l)
mk-proj (some l * (` P)) ε = ⁇ P l

mk-inj : ∀ {T P}
  → Tail P T
  → GapT T *
  ---
  → Tail P *
mk-inj (‼ P) g = ‼ P
mk-inj ε (some l (` P) *) = ‼ P

mk-inj-none : ∀ {P}
  → (t : Tail P *)
  ---
  → mk-inj t none ≡ t
mk-inj-none (‼ P) = refl

mk-gap : ∀ {P S T Q}
  → Tail P S
  → GapT S T
  → Head T Q
  -----------------
  → GapP P Q
mk-gap ε g ε = g
mk-gap ε (some l' (` P) *)    (⁇ Q l) = some l (` P) (` Q)
mk-gap (‼ P) g                (⁇ Q l) = some l (` P) (` Q)
mk-gap (‼ P) (some l * (` Q)) ε       = some l (` P) (` Q)

mutual
  seq : ∀ {T1 T2 T3 T4}
    → Cast T1 T2
    → GapT T2 T3
    → Cast T3 T4
  ----------------
    → Cast T1 T4
  seq id* g id* = id*
  seq id* g (↷ h2 m2 t2) = ↷ (mk-proj g h2) m2 t2
  seq (↷ h1 m1 t1) g id* = ↷ h1 m1 (mk-inj t1 g)
  seq (↷ h1 m1 t1) g (↷ h2 m2 t2) = ↷ h1 (seq-m m1 (mk-gap t1 g h2) m2) t2
  
  seq-m : ∀ {P1 P2 P3 P4}
    → Body P1 P2
    → GapP P2 P3
    → Body P3 P4
    ---
    → Body P1 P4
  seq-m (⊥ l1) g m2 = ⊥ l1
  seq-m (` m1) g m2 with check-gap g
  seq-m (` m1) .(some l _ _) m2 | bad ¬P⌣Q l = ⊥ l
  seq-m (` m1) g (⊥ l2) | good P⌣Q = ⊥ l2
  seq-m (` m1) g (` m2) | good P⌣Q = ` seq-mm P⌣Q m1 g m2
  
  seq-mm : ∀ {P1 P2 P3 P4}
    → (` P2) ⌣ (` P3)
    → PreBody P1 P2
    → GapP P2 P3
    → PreBody P3 P4
    ---
    → PreBody P1 P4
  seq-mm ⌣B B̂ g B̂ = B̂
  seq-mm ⌣⇒ (c₁ ⇒̂ c₂) g (c₃ ⇒̂ c₄) = (seq c₃ (g-dom g) c₁) ⇒̂ (seq c₂ (g-cod g) c₄)
  seq-mm ⌣⊗ (c₁ ⊗̂ c₂) g (c₃ ⊗̂ c₄) = (seq c₁ (g-car g) c₃) ⊗̂ (seq c₂ (g-cdr g) c₄)

mutual
  id : ∀ T → Cast T T
  id *
    = id*
  id (` P)
    = ↷ ε (` id-m P) ε

  id-m : ∀ P → PreBody P P
  id-m B
    = B̂
  id-m (T₁ ⇒ T₂)
    = id T₁ ⇒̂ id T₂
  id-m (T₁ ⊗ T₂)
    = id T₁ ⊗̂ id T₂

⌈_⌉ : ∀ {T1 T2} → SrcCast T1 T2 → Cast T1 T2
⌈ T1 ⟹[ l ] T2 ⌉ = seq (id T1) (some l T1 T2) (id T2)

_⨟_ : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
_⨟_ c1 c2 = seq c1 none c2

mutual
  identityˡ : ∀ {T1 T2} → (c : Cast T1 T2) → id T1 ⨟ c ≡ c
  identityˡ id* = refl
  identityˡ (↷ (⁇ P l) m t2) = refl
  identityˡ (↷ ε (⊥ l) t2) = refl
  identityˡ (↷ ε (` B̂) t2) = refl
  identityˡ (↷ ε (` (c₁ ⇒̂ c₂)) t2) rewrite identityʳ c₁ | identityˡ c₂ = refl
  identityˡ (↷ ε (` (c₁ ⊗̂ c₂)) t2) rewrite identityˡ c₁ | identityˡ c₂ = refl
  
  identityʳ : ∀ {T1 T2} → (c : Cast T1 T2) → c ⨟ id T2 ≡ c
  identityʳ id* = refl
  identityʳ (↷ t1 m (‼ P)) = refl
  identityʳ (↷ t1 (⊥ l) ε) = refl
  identityʳ (↷ t1 (` B̂) ε) = refl
  identityʳ (↷ t1 (` (c₁ ⇒̂ c₂)) ε) rewrite identityˡ c₁ | identityʳ c₂ = refl
  identityʳ (↷ t1 (` (c₁ ⊗̂ c₂)) ε) rewrite identityʳ c₁ | identityʳ c₂ = refl

lem-mk-gap : ∀ {P1 T1 T2 P2}
  → (t1 : Tail P1 T1)
  → (g1 : GapT T1 *)
  → (g2 : GapT *  T2)
  → (h2 : Head T2 P2)
  → mk-gap (mk-inj t1 g1) g2 h2
    ≡
    mk-gap t1 g1 (mk-proj g2 h2)
lem-mk-gap (‼ P1) g1 g2 (⁇ P2 l) = refl
lem-mk-gap ε (some l' .(` _) .*) g2 (⁇ P l) = refl
lem-mk-gap (‼ P) g1 (some l .* .(` _)) ε = refl
lem-mk-gap ε (some l' .(` _) .*) (some l .* .(` _)) ε = refl

mutual
  seq-m-assoc : ∀ {T1 T2 T3 T4 T5 T6}
    → (c1 : Body T1 T2)
    → (g1 : GapP T2 T3)
    → (c2 : Body T3 T4)
    → (g2 : GapP T4 T5)
    → (c3 : Body T5 T6)
    → seq-m (seq-m c1 g1 c2) g2 c3 ≡ seq-m c1 g1 (seq-m c2 g2 c3)
  seq-m-assoc (⊥ l1) g1 m2 g2 m3 = refl
  seq-m-assoc (` m1) g1 m2 g2 m3 with check-gap g1
  seq-m-assoc (` m1) .(some l _ _) m2 g2 m3 | bad ¬P⌣Q l = refl
  seq-m-assoc (` m1) g1 (⊥ l2) g2 m3 | good P⌣Q = refl
  seq-m-assoc (` m1) g1 (` m2) g2 m3 | good P⌣Q with check-gap g2
  seq-m-assoc (` m1) g1 (` m2) .(some l _ _) m3 | good P⌣Q | bad ¬P⌣Q l = refl
  seq-m-assoc (` m1) g1 (` m2) g2 (⊥ l3) | good P⌣Q | good P⌣Q' = refl
  seq-m-assoc (` B̂) g1 (` B̂) g2 (` B̂) | good ⌣B | good ⌣B = refl
  seq-m-assoc (` (c₁ ⇒̂ c₂)) g1 (` (c₃ ⇒̂ c₄)) g2 (` (c₅ ⇒̂ c₆)) | good ⌣⇒ | good ⌣⇒
    rewrite seq-assoc c₅ (g-dom g2) c₃ (g-dom g1) c₁
          | seq-assoc c₂ (g-cod g1) c₄ (g-cod g2) c₆
    = refl
  seq-m-assoc (` (c₁ ⊗̂ c₂)) g1 (` (c₃ ⊗̂ c₄)) g2 (` (c₅ ⊗̂ c₆)) | good ⌣⊗ | good ⌣⊗
    rewrite seq-assoc c₁ (g-car g1) c₃ (g-car g2) c₅
          | seq-assoc c₂ (g-cdr g1) c₄ (g-cdr g2) c₆
    = refl

  seq-assoc : ∀ {T1 T2 T3 T4 T5 T6}
    → (c1 : Cast T1 T2)
    → (g1 : GapT T2 T3)
    → (c2 : Cast T3 T4)
    → (g2 : GapT T4 T5)
      → (c3 : Cast T5 T6)
    → seq (seq c1 g1 c2) g2 c3 ≡ seq c1 g1 (seq c2 g2 c3)
  seq-assoc id* g1 id* g2 id* = refl
  seq-assoc id* g1 id* g2 (↷ h m t) with (mk-proj g2 h)
  seq-assoc id* g1 id* g2 (↷ h m t) | ⁇ P l = refl
  seq-assoc id* g1 (↷ h m t) g2 id* = refl
  seq-assoc id* g1 (↷ h m t) g2 (↷ h₁ m₁ t₁) = refl
  seq-assoc (↷ h m t) g1 id* g2 id* with (mk-inj t g1)
  seq-assoc (↷ h m t) g1 id* g2 id* | (‼ P) = refl
  seq-assoc (↷ h1 m1 t1) g1 id* g2 (↷ h3 m3 t3)
    rewrite lem-mk-gap t1 g1 g2 h3
    = refl
  seq-assoc (↷ h1 m1 t1) g1 (↷ h2 m2 t2) g2 id* = refl
  seq-assoc (↷ h1 m1 t1) g1 (↷ h2 m2 t2) g2 (↷ h3 m3 t3)
    rewrite seq-m-assoc m1 (mk-gap t1 g1 h2) m2 (mk-gap t2 g2 h3) m3
    = refl

⨟-assoc : ∀ {T1 T2 T3 T4}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → (c3 : Cast T3 T4)
  → (c1 ⨟ c2) ⨟ c3 ≡ c1 ⨟ (c2 ⨟ c3)
⨟-assoc c1 c2 c3 = seq-assoc c1 none c2 none c3

open import R.BlameStrategies Label using (BlameStrategy; LazyDBS)
open BlameStrategy LazyDBS using (Injectable)

open import S.Values Label Injectable Cast

open import Error
  using (Error; return; raise; _>>=_; _>=>_; >>=-return; >>=-assoc; >=>-assoc; >=>->>=)
open import Data.Unit using (tt)

CastResult : Type → Set
CastResult T = Error Label (Value T)

⟦_⟧t : ∀ {P T}
  → Tail P T
  → Value (` P)
  ---
  → CastResult T
⟦ ‼ P ⟧t v = return (dyn (same P) v)
⟦ ε   ⟧t v = return v

proxy : ∀ {P1 P2}
  → Value (` P1)
  → PreBody P1 P2
  ---
  → Value (` P2)
proxy v B̂ = v
proxy (lam⟨ c1 ⇒ c2 ⟩ e E) (c3 ⇒̂ c4)    = lam⟨ c3 ⨟ c1 ⇒ c2 ⨟ c4 ⟩ e E
proxy (cons⟨ c1 ⊗ c2 ⟩ v1 v2) (c3 ⊗̂ c4) = cons⟨ c1 ⨟ c3 ⊗ c2 ⨟ c4 ⟩ v1 v2

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
⟦ ⁇ P2 l ⟧h (dyn (same P1) v) = ⟦ seq-m (` id-m P1) (some l (` P1) (` P2)) (` id-m P2) ⟧m v 

⟦_⟧ : ∀ {T1 T2}
  → Cast T1 T2
  → Value T1
  ---
  → CastResult T2
⟦ id*     ⟧ v = return v
⟦ ↷ h m t ⟧ v = ⟦ h ⟧h v >>= ⟦ m ⟧m >>= ⟦ t ⟧t

mutual
  lem-id-m : ∀ {P}
    → (v : Value (` P))  
    -----------------------------
    → proxy v (id-m P) ≡ v
  lem-id-m {B} v = refl
  lem-id-m {S ⇒ T} (lam⟨ c ⇒ d ⟩ e E)  rewrite identityˡ c | identityʳ d = refl
  lem-id-m {S ⊗ T} (cons⟨ c ⊗ d ⟩ v u) rewrite identityʳ c | identityʳ d = refl
  
  lem-id : ∀ {T}
    → (v : Value T)  
    -----------------------------
    → ⟦ id T ⟧ v ≡ return v
  lem-id {*} v = refl
  lem-id {` P} v rewrite lem-id-m v = refl

lem1 : ∀ {T1 T2 T3 T4}
  → (l  : Label)
  → (c1 : Cast T1 T2)
  → (c2 : Cast T3 T4)
  → (c1 ⨟ ⌈ T2 ⟹[ l ] T3 ⌉) ⨟ c2 ≡ seq c1 (some l T2 T3) c2
lem1 {T2 = T2} {T3 = T3} l c1 c2
  rewrite sym (seq-assoc c1 none (id _) (some l _ _) (id T3))
    | identityʳ c1
    | seq-assoc c1 (some l _ _) (id T3) none c2
    | identityˡ c2
  = refl

mutual
  lem-seq-m : ∀ {P1 P2 T P3 P4}
    → (m1 : Body P1 P2)
    → (t1 : Tail P2 T)
    → (h2 : Head T  P3)
    → (m2 : Body P3 P4)
    → (∀ v →
         ⟦ seq-m m1 (mk-gap t1 none h2) m2 ⟧m v
           ≡
         (⟦ m1 ⟧m >=> ⟦ t1 ⟧t >=> ⟦ h2 ⟧h >=> ⟦ m2 ⟧m) v)
  lem-seq-m (⊥ l1) t1 h2 m2 v = refl
  lem-seq-m (` m1) (‼ P) (⁇ Q l) m2 v with (` P) ⌣? (` Q)
  lem-seq-m (` m1) (‼ P) (⁇ Q l) m2 v | no ¬p = refl
  lem-seq-m (` m1) (‼ P) (⁇ Q l) (⊥ l2) v | yes P⌣Q = refl
  lem-seq-m (` B̂) (‼ .B) (⁇ .B l) (` B̂) v | yes ⌣B = refl
  lem-seq-m (` (c2 ⇒̂ d2)) (‼ (S1 ⇒ T1)) (⁇ (S2 ⇒ T2) l) (` (c3 ⇒̂ d3))
            (lam⟨  c1 ⇒ d1 ⟩ e E) | yes ⌣⇒
    rewrite sym (seq-assoc c3 none ⌈ S2 ⟹[ l ] S1 ⌉ none (c2 ⨟ c1))
      | lem1 l c3 (c2 ⨟ c1) | lem1 l (d1 ⨟ d2) d3
    = cong₂ (λ c d → return (lam⟨ c ⇒ d ⟩ e E))
            (seq-assoc c3 _ c2 _ c1)
            (sym (seq-assoc d1 _ d2 _ d3)) 
  lem-seq-m (` (c2 ⊗̂ d2)) (‼ .(_ ⊗ _)) (⁇ .(_ ⊗ _) l) (` (c3 ⊗̂ d3))
            (cons⟨ c1 ⊗ d1 ⟩ v u) | yes ⌣⊗
    rewrite lem1 l (c1 ⨟ c2) c3 | lem1 l (d1 ⨟ d2) d3
    = cong₂ (λ c d → return (cons⟨ c ⊗ d ⟩ v u))
            (sym (seq-assoc c1 _ c2 _ c3))
            (sym (seq-assoc d1 _ d2 _ d3))
  lem-seq-m (` m1) ε ε (⊥ l2) v = refl
  lem-seq-m (` B̂) ε ε (` B̂) v = refl
  lem-seq-m (` (c2 ⇒̂ d2)) ε ε (` (c3 ⇒̂ d3)) (lam⟨ c1 ⇒ d1 ⟩ e E)
    = cong₂ (λ c d → return (lam⟨ c ⇒ d ⟩ e E))
            (seq-assoc c3 none c2 none c1)
            (sym (seq-assoc d1 none d2 none d3))
  lem-seq-m (` (c2 ⊗̂ d2)) ε ε (` (c3 ⊗̂ d3)) (cons⟨ c1 ⊗ d1 ⟩ v u)
    = cong₂ (λ c d → return (cons⟨ c ⊗ d ⟩ v u))
            (sym (seq-assoc c1 none c2 none c3))
            (sym (seq-assoc d1 none d2 none d3))
  
  lem-seq : ∀ {T1 T2 T3}
    → (c1 : Cast T1 T2)
    → (c2 : Cast T2 T3)
    → ∀ v
    --------------------
    → ⟦ c1 ⨟ c2 ⟧ v ≡ ⟦ c1 ⟧ v >>= ⟦ c2 ⟧
  lem-seq id* c2 v
    rewrite identityˡ c2
    = refl
  lem-seq (↷ h1 m1 t1) id* v
    rewrite identityʳ (↷ h1 m1 t1)
    | mk-inj-none t1
    | >>=-return (⟦ h1 ⟧h v >>= ⟦ m1 ⟧m >>= ⟦ t1 ⟧t)
    = refl
  lem-seq (↷ h1 m1 t1) (↷ h2 m2 t2) v with ⟦ h1 ⟧h v
  lem-seq (↷ h1 m1 t1) (↷ h2 m2 t2) v | raise l   = refl
  lem-seq (↷ h1 m1 t1) (↷ h2 m2 t2) v | return v'
    rewrite >=>->>= (⟦ m1 ⟧m v' >>= ⟦ t1 ⟧t) (⟦ h2 ⟧h >=> ⟦ m2 ⟧m) ⟦ t2 ⟧t
            | >=>->>= (⟦ m1 ⟧m v' >>= ⟦ t1 ⟧t) ⟦ h2 ⟧h ⟦ m2 ⟧m
    = cong (_>>= ⟦ t2 ⟧t) (lem-seq-m m1 t1 h2 m2 v')

H : CastADT Injectable
H = record
    { Cast = Cast
    ; id  = id
    ; ⌈_⌉ = ⌈_⌉
    ; _⨟_ = _⨟_
    ; ⟦_⟧ = ⟦_⟧
    ; lem-id = λ T v → lem-id v
    ; lem-seq = lem-seq
    }

eq-¬⌣ : ∀ {T1 T2}
  → (l : Label)
  → ¬ (T1 ⌣ T2)
  → (v : Value T1)
  ---
  → ⟦ ⌈ T1 ⟹[ l ] T2 ⌉ ⟧ v
      ≡
    raise l
eq-¬⌣ {*} {*} l ¬S⌣T v = ⊥-elim (¬S⌣T *⌣*)
eq-¬⌣ {*} {` P} l ¬S⌣T v = ⊥-elim (¬S⌣T (*⌣P P))
eq-¬⌣ {` P} {*} l ¬S⌣T v = ⊥-elim (¬S⌣T (P⌣* P))
eq-¬⌣ {` P} {` Q} l ¬S⌣T v with (` P) ⌣? (` Q)
eq-¬⌣ {` P} {` Q} l ¬S⌣T v | yes p = ⊥-elim (¬S⌣T p)
eq-¬⌣ {` P} {` Q} l ¬S⌣T v | no ¬p = refl

eq-** : ∀ l
  → (v : Value *)
  → ⟦ ⌈ * ⟹[ l ] * ⌉ ⟧ v
      ≡
    return v
eq-** l v = refl

eq-P* : ∀ {P}
  → (l : Label)
  → (v : Value (` P))  
  → ⟦ ⌈ (` P) ⟹[ l ] * ⌉ ⟧ v
      ≡
    return (dyn (same P) v)
eq-P* l v rewrite lem-id-m v = refl

eq-*P : ∀ Q P l v
  → ⟦ ⌈ *   ⟹[ l ] ` Q ⌉ ⟧ (dyn (same P) v)
      ≡
    ⟦ ⌈ ` P ⟹[ l ] ` Q ⌉ ⟧ v
eq-*P Q P l v with ⟦ seq-m (` id-m P) (some l (` P) (` Q)) (` id-m Q) ⟧m v
eq-*P Q P l v | raise  l' = refl
eq-*P Q P l v | return v' rewrite lem-id-m v' = refl

open import S.LazyDCastADT Label

H-LazyD : LazyD H
H-LazyD =
  record
    { eq-¬⌣ = eq-¬⌣
    ; eq-** = eq-**
    ; eq-P* = eq-P*
    ; eq-*P = eq-*P
    ; eq-B = λ l v → refl
    ; eq-⇒ = λ T21 T22 T11 T12 {S} {T} l {Γ} c₁ c₂ e E → refl
    ; eq-⊗ = λ T21 T22 T11 T12 {S} {T} l c₁ c₂ v1 v2 → refl
    }
