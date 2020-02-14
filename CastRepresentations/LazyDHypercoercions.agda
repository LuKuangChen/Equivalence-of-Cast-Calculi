module CastRepresentations.LazyDHypercoercions (Label : Set) where

open import Types
open import Variables
open import Cast Label using (_⟹[_]_) renaming (Cast to SrcCast)
open import Terms Label
open import S.CastADT Label

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)


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
    -- ⊥ : (P : PreType)
    --   → (l : Label)
    --   → (Q : PreType)
    --     ---
    --   → Body P Q
    ⊥ : ∀ {P Q}
      → (a : Tag P)
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
      PreBody B B
    _⇒_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S2 S1) →
      (c₂ : Cast T1 T2) →
      ---
      PreBody (S1 ⇒ T1) (S2 ⇒ T2)
    _⊗_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S1 S2) →
      (c₂ : Cast T1 T2) →
      ---
      PreBody (S1 ⊗ T1) (S2 ⊗ T2)
    -- _⊕_ : ∀ {S1 S2 T1 T2} →
    --   (c₁ : Cast S1 S2) →
    --   (c₂ : Cast T1 T2) →
    --   ---
    --   PreBody (S1 ⊕ T1) (S2 ⊕ T2)
    -- ref : ∀ {S T} →
    --   (c₁ : Cast T S) →
    --   (c₂ : Cast S T) →
    --   ---
    --   PreBody (ref S) (ref T)

tagof-mm-l : ∀ {P Q} → PreBody P Q → Tag P
tagof-mm-l B = `B
tagof-mm-l (c₁ ⇒ c₂) = `⇒
tagof-mm-l (c₁ ⊗ c₂) = `⊗
-- tagof-mm-l (c₁ ⊕ c₂) = `⊕
-- tagof-mm-l (ref c₁ c₂) = `ref

tagof-mm-r : ∀ {P Q} → PreBody P Q → Tag Q
tagof-mm-r B = `B
tagof-mm-r (c₁ ⇒ c₂) = `⇒
tagof-mm-r (c₁ ⊗ c₂) = `⊗
-- tagof-mm-r (c₁ ⊕ c₂) = `⊕
-- tagof-mm-r (ref c₁ c₂) = `ref

tagof-m-l : ∀ {P Q} → Body P Q → Tag P
tagof-m-l (⊥ `B l) = `B
tagof-m-l (⊥ `⇒ l) = `⇒
tagof-m-l (⊥ `⊗ l) = `⊗
-- tagof-m-l (⊥ `⊕ l) = `⊕
-- tagof-m-l (⊥ `ref l) = `ref
tagof-m-l (` m) = tagof-mm-l m

data GapP : PreType → PreType → Set where
  none : ∀ {P} → GapP P P
  some : (l : Label) → ∀ P1 P2 → GapP P1 P2

data GapT : Type → Type → Set where
  none : ∀ {T} → GapT T T
  some : (l : Label) → ∀ T1 T2 → GapT T1 T2

-- GapP : PreType → PreType → Set
-- GapP P1 P2 = P1 ≡ P2 ⊎ Label

-- GapT : Type → Type → Set
-- GapT T1 T2 = T1 ≡ T2 ⊎ Label

g-dom : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⇒ T2) (T3 ⇒ T4)
  → GapT T3 T1
g-dom none = none
g-dom (some l (T1 ⇒ T2) (T3 ⇒ T4)) = some l T3 T1

g-cod : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⇒ T2) (T3 ⇒ T4)
  → GapT T2 T4
g-cod none = none
g-cod (some l (T1 ⇒ T2) (T3 ⇒ T4)) = some l T2 T4

g-car : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊗ T2) (T3 ⊗ T4)
  → GapT T1 T3
g-car none = none
g-car (some l (T1 ⊗ T2) (T3 ⊗ T4)) = some l T1 T3

g-cdr : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊗ T2) (T3 ⊗ T4)
  → GapT T2 T4
g-cdr none = none
g-cdr (some l (T1 ⊗ T2) (T3 ⊗ T4)) = some l T2 T4

-- g-inl : ∀ {T1 T2 T3 T4}
--   → GapP (T1 ⊕ T2) (T3 ⊕ T4)
--   → GapT T1 T3
-- g-inl (inj₁ refl) = inj₁ refl
-- g-inl (inj₂ l) = inj₂ l

-- g-inr : ∀ {T1 T2 T3 T4}
--   → GapP (T1 ⊕ T2) (T3 ⊕ T4)
--   → GapT T2 T4
-- g-inr (inj₁ refl) = inj₁ refl
-- g-inr (inj₂ l) = inj₂ l

-- g-set : ∀ {S T} →
--   GapP (ref S) (ref T) →
--   ---
--   GapT T S
-- g-set (inj₁ refl) = inj₁ refl
-- g-set (inj₂ ll) = (inj₂ ll)

-- g-get : ∀ {S T} →
--   GapP (ref S) (ref T) →
--   ---
--   GapT S T
-- g-get (inj₁ refl) = inj₁ refl
-- g-get (inj₂ ll) = (inj₂ ll)

mk-head : ∀ {T P}
  → GapT * T
  → Head T P
  ---
  → Head * P
mk-head g (⁇ P l) = (⁇ P l)
mk-head (some l * (` P)) ε = ⁇ P l
-- mk-head (inj₁ ()) ε
-- mk-head (inj₂ l1) ε = ⁇ l1

mk-tail : ∀ {T P}
  → Tail P T
  → GapT T *
  ---
  → Tail P *
mk-tail (‼ P) g = ‼ P
mk-tail ε (some l (` P) *) = ‼ P
-- mk-tail (‼ P) g = ‼ P
-- mk-tail ε (inj₁ ())
-- mk-tail ε (inj₂ l) = ‼ _

mk-tail-none : ∀ {P}
  → (t : Tail P *)
  ---
  → mk-tail t none ≡ t
mk-tail-none (‼ P) = refl

link-src1 : ∀ {P S}
  → Tail P S
  → GapT S *
  → PreType
link-src1 (‼ P) g = P
link-src1 ε (some l (` P) *) = P

lem-link-src1 : ∀ {P S}
  → (t : Tail P S)
  → (g : GapT S *)
  → link-src1 t g ≡ P
lem-link-src1 (‼ P) g = refl
lem-link-src1 ε (some l .(` _) .*) = refl

link-src2 : ∀ {P1} S
  → Tail P1 S
  → PreType
link-src2 * (‼ P) = P
link-src2 (` P) ε = P

lem-link-src2 : ∀ {P} S
  → (t : Tail P S)
  → link-src2 S t ≡ P
lem-link-src2 * (‼ P) = refl
lem-link-src2 (` P) ε = refl

link : ∀ {P S T Q}
  → Tail P S
  → GapT S T
  → Head T Q
  -----------------
  → GapP P Q
link t g (⁇ P2 l) = some l _ P2
link t (some l T (` P2)) ε = some l _ P2
link ε none ε = none

blame-gap : {P1 P2 : PreType}
  → GapP P1 P2
  → ¬ ((` P1) ⌣ (` P2))
  ---
  → Label
blame-gap none ¬p = ⊥-elim (¬p (⌣refl _))
blame-gap (some l P1 P2) ¬p = l

⌣?-by-tags : ∀ {P Q} → Tag P → Tag Q → Dec ((` P) ⌣ (` Q))
⌣?-by-tags `B `B = yes ⌣B
⌣?-by-tags `B `⇒ = no (λ ())
⌣?-by-tags `B `⊗ = no (λ ())
⌣?-by-tags `⇒ `B = no (λ ())
⌣?-by-tags `⇒ `⇒ = yes ⌣⇒
⌣?-by-tags `⇒ `⊗ = no (λ ())
⌣?-by-tags `⊗ `B = no (λ ())
⌣?-by-tags `⊗ `⇒ = no (λ ())
⌣?-by-tags `⊗ `⊗ = yes ⌣⊗

mutual
  seq : ∀ {T1 T2 T3 T4}
    → Cast T1 T2
    → GapT T2 T3
    → Cast T3 T4
  ----------------
    → Cast T1 T4
  seq id* g id* = id*
  seq id* g (↷ t1 m t2) = ↷ (mk-head g t1) m t2
  seq (↷ t1 m1 t2) g id*          = ↷ t1 m1 (mk-tail t2 g)
  seq (↷ t1 m1 t2) g (↷ t3 m2 t4) = ↷ t1 (seq-m m1 (link t2 g t3) m2) t4
  
  seq-m : ∀ {P1 P2 P3 P4}
    → Body P1 P2
    → GapP P2 P3
    → Body P3 P4
    ---
    → Body P1 P4
  seq-m (⊥ a l) g m2 = ⊥ a l
  seq-m (` m1) g m2 with ⌣?-by-tags (tagof-mm-r m1) (tagof-m-l m2)
  seq-m (` m1) g m2      | no ¬p = ⊥ (tagof-mm-l m1) (blame-gap g ¬p)
  seq-m (` m1) g (⊥ a l) | yes p = ⊥ (tagof-mm-l m1) l
  seq-m (` m1) g (` m2)  | yes p = ` (seq-mm p m1 g m2)
  
  seq-mm : ∀ {P1 P2 P3 P4}
    → (` P2) ⌣ (` P3)
    → PreBody P1 P2
    → GapP P2 P3
    → PreBody P3 P4
    ---
    → PreBody P1 P4
  seq-mm ⌣B B g B = B
  seq-mm ⌣⇒ (c₁ ⇒ c₂) g (c₃ ⇒ c₄) = (seq c₃ (g-dom g) c₁) ⇒ (seq c₂ (g-cod g) c₄)
  seq-mm ⌣⊗ (c₁ ⊗ c₂) g (c₃ ⊗ c₄) = (seq c₁ (g-car g) c₃) ⊗ (seq c₂ (g-cdr g) c₄)
  -- seq-mm ⌣⊕ (c₁ ⊕ c₂) g (c₃ ⊕ c₄) = (seq c₁ (g-inl g) c₃) ⊕ (seq c₂ (g-inr g) c₄)
  -- seq-mm ⌣R (ref c₁ c₂) g (ref c₃ c₄) = ref (seq c₃ (g-set g) c₁) (seq c₂ (g-get g) c₄)

mutual
  id : ∀ T → Cast T T
  id *
    = id*
  id (` P)
    = ↷ ε (` id-m P) ε

  id-m : ∀ P → PreBody P P
  id-m B
    = B
  id-m (T₁ ⇒ T₂)
    = id T₁ ⇒ id T₂
  id-m (T₁ ⊗ T₂)
    = id T₁ ⊗ id T₂
  -- id-m (T₁ ⊕ T₂)
  --   = id T₁ ⊕ id T₂
  -- id-m (ref T)
  --   = ref (id T) (id T)

⌈_⌉ : ∀ {T1 T2} → SrcCast T1 T2 → Cast T1 T2
⌈ T1 ⟹[ l ] T2 ⌉ = seq (id T1) (some l T1 T2) (id T2)

_⨟_ : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
_⨟_ c1 c2 = seq c1 none c2

mutual
  identityˡ : ∀ {T1 T2} → (c : Cast T1 T2) → id T1 ⨟ c ≡ c
  identityˡ id* = refl
  identityˡ (↷ (⁇ P l) m t2) = refl
  identityˡ (↷ ε (⊥ `B l) t2) = refl
  identityˡ (↷ ε (⊥ `⇒ l) t2) = refl
  identityˡ (↷ ε (⊥ `⊗ l) t2) = refl
  -- identityˡ (↷ ε (⊥ `⊕ l) t2) = refl
  -- identityˡ (↷ ε (⊥ `ref l) t2) = refl
  identityˡ (↷ ε (` B) t2) = refl
  identityˡ (↷ ε (` (c₁ ⇒ c₂)) t2) rewrite identityʳ c₁ | identityˡ c₂ = refl
  identityˡ (↷ ε (` (c₁ ⊗ c₂)) t2) rewrite identityˡ c₁ | identityˡ c₂ = refl
  -- identityˡ (↷ ε (` (c₁ ⊕ c₂)) t2) rewrite identityˡ c₁ | identityˡ c₂ = refl
  -- identityˡ (↷ ε (` ref c₁ c₂) t2) rewrite identityʳ c₁ | identityˡ c₂ = refl
  
  identityʳ : ∀ {T1 T2} → (c : Cast T1 T2) → c ⨟ id T2 ≡ c
  identityʳ id* = refl
  identityʳ (↷ t1 m (‼ P)) = refl
  identityʳ (↷ t1 (⊥ a l) ε) = refl
  identityʳ (↷ t1 (` B) ε) = refl
  identityʳ (↷ t1 (` (c₁ ⇒ c₂)) ε) rewrite identityˡ c₁ | identityʳ c₂ = refl
  identityʳ (↷ t1 (` (c₁ ⊗ c₂)) ε) rewrite identityʳ c₁ | identityʳ c₂ = refl
  -- identityʳ (↷ t1 (` (c₁ ⊕ c₂)) ε) rewrite identityʳ c₁ | identityʳ c₂ = refl
  -- identityʳ (↷ t1 (` (ref c₁ c₂)) ε) rewrite identityˡ c₁ | identityʳ c₂ = refl

lem-link : ∀ {P1 T1 T2 P2}
  → (t1 : Tail P1 T1)
  → (g1 : GapT T1 *)
  → (g2 : GapT *  T2)
  → (h2 : Head T2 P2)
  → link (mk-tail t1 g1) g2 h2
    ≡
    link t1 g1 (mk-head g2 h2)
lem-link (‼ P1) g1 g2 (⁇ P2 l) = refl
lem-link ε (some l' .(` _) .*) g2 (⁇ P l) = refl
lem-link (‼ P) g1 (some l .* .(` _)) ε = refl
lem-link ε (some l' .(` _) .*) (some l .* .(` _)) ε = refl
-- lem-link t g1 g2 (⁇ P l) = refl
-- lem-link t g1 (some l * (` P)) ε = refl
-- lem-link t1 g1 g2 (⁇ l) = refl
-- lem-link t1 g1 (inj₁ ()) ε
-- lem-link t1 g1 (inj₂ l) ε = refl

mutual
  seq-m-assoc : ∀ {T1 T2 T3 T4 T5 T6}
    → (c1 : Body T1 T2)
    → (g1 : GapP T2 T3)
    → (c2 : Body T3 T4)
    → (g2 : GapP T4 T5)
    → (c3 : Body T5 T6)
    → seq-m (seq-m c1 g1 c2) g2 c3 ≡ seq-m c1 g1 (seq-m c2 g2 c3)
  seq-m-assoc (⊥ a l) g1 m2 g2 m3 = refl
  seq-m-assoc (` m) g1 m2 g2 m3
    rewrite tag-unique (tagof-m-l (seq-m m2 g2 m3)) (tagof-m-l m2)
    with ⌣?-by-tags (tagof-mm-r m) (tagof-m-l m2)
  seq-m-assoc (` m1) g1 m2 g2 m3 | no ¬p1 = refl
  seq-m-assoc (` m1) g1 (⊥ a l) g2 m3 | yes p1 = refl
  seq-m-assoc (` m1) g1 (` m2)  g2 m3 | yes p1
    rewrite tag-unique (tagof-mm-r (seq-mm p1 m1 g1 m2)) (tagof-mm-r m2)
    with ⌣?-by-tags (tagof-mm-r m2) (tagof-m-l m3)
  seq-m-assoc (` m1) g1 (` m2) g2 m3 | yes p1 | no ¬p2
    rewrite tag-unique (tagof-mm-l (seq-mm p1 m1 g1 m2)) (tagof-mm-l m1)
    = refl
  seq-m-assoc (` m1) g1 (` m2) g2 (⊥ a l) | yes p1 | yes p2
    rewrite tag-unique (tagof-mm-l (seq-mm p1 m1 g1 m2)) (tagof-mm-l m1)
    = refl
  seq-m-assoc (` B) g1 (` B) g2 (` B)  | yes ⌣B | yes ⌣B = refl
  seq-m-assoc (` c1 ⇒ c2) g1 (` c3 ⇒ c4) g2 (` c5 ⇒ c6)  | yes ⌣⇒ | yes ⌣⇒
    rewrite seq-assoc c5 (g-dom g2) c3 (g-dom g1) c1 | seq-assoc c2 (g-cod g1) c4 (g-cod g2) c6
    = refl
  seq-m-assoc (` c1 ⊗ c2) g1 (` c3 ⊗ c4) g2 (` c5 ⊗ c6)  | yes ⌣⊗ | yes ⌣⊗
    rewrite seq-assoc c1 (g-car g1) c3 (g-car g2) c5 | seq-assoc c2 (g-cdr g1) c4 (g-cdr g2) c6
    = refl
  -- seq-m-assoc (` c1 ⊕ c2) g1 (` c3 ⊕ c4) g2 (` c5 ⊕ c6)  | yes ⌣⊕ | yes ⌣⊕
  --   rewrite seq-assoc c1 (g-inl g1) c3 (g-inl g2) c5 | seq-assoc c2 (g-inr g1) c4 (g-inr g2) c6
  --   = refl
  -- seq-m-assoc (` ref c1 c2) g1 (` ref c3 c4) g2 (` ref c5 c6)  | yes ⌣R | yes ⌣R
  --   rewrite seq-assoc c5 (g-set g2) c3 (g-set g1) c1 | seq-assoc c2 (g-get g1) c4 (g-get g2) c6
  --   = refl

  seq-assoc : ∀ {T1 T2 T3 T4 T5 T6}
    → (c1 : Cast T1 T2)
    → (g1 : GapT T2 T3)
    → (c2 : Cast T3 T4)
    → (g2 : GapT T4 T5)
      → (c3 : Cast T5 T6)
    → seq (seq c1 g1 c2) g2 c3 ≡ seq c1 g1 (seq c2 g2 c3)
  seq-assoc id* g1 id* g2 id* = refl
  seq-assoc id* g1 id* g2 (↷ h m t) with (mk-head g2 h)
  seq-assoc id* g1 id* g2 (↷ h m t) | ⁇ P l = refl
  seq-assoc id* g1 (↷ h m t) g2 id* = refl
  seq-assoc id* g1 (↷ h m t) g2 (↷ h₁ m₁ t₁) = refl
  seq-assoc (↷ h m t) g1 id* g2 id* with (mk-tail t g1)
  seq-assoc (↷ h m t) g1 id* g2 id* | (‼ P) = refl
  seq-assoc (↷ h1 m1 t1) g1 id* g2 (↷ h3 m3 t3)
    rewrite lem-link t1 g1 g2 h3
    = refl
  seq-assoc (↷ h1 m1 t1) g1 (↷ h2 m2 t2) g2 id* = refl
  seq-assoc (↷ h1 m1 t1) g1 (↷ h2 m2 t2) g2 (↷ h3 m3 t3)
    rewrite seq-m-assoc m1 (link t1 g1 h2) m2 (link t2 g2 h3) m3
    = refl

⨟-assoc : ∀ {T1 T2 T3 T4}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → (c3 : Cast T3 T4)
  → (c1 ⨟ c2) ⨟ c3 ≡ c1 ⨟ (c2 ⨟ c3)
⨟-assoc c1 c2 c3 = seq-assoc c1 none c2 none c3

open import X.BlameStrategies Label using (BlameStrategy; LazyDBS)
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
proxy v B = v
proxy (lam⟨ c1 ⇒ c2 ⟩ e E) (c3 ⇒ c4)    = lam⟨ c3 ⨟ c1 ⇒ c2 ⨟ c4 ⟩ e E
proxy (cons⟨ c1 ⊗ c2 ⟩ v1 v2) (c3 ⊗ c4) = cons⟨ c1 ⨟ c3 ⊗ c2 ⨟ c4 ⟩ v1 v2

⟦_⟧m : ∀ {P1 P2}
  → Body P1 P2
  → Value (` P1)
  → CastResult (` P2)
⟦ ⊥ a l ⟧m v = raise l
⟦ ` m   ⟧m v = return (proxy v m)

⟦_⟧h : ∀ {T P}
  → Head T P
  → Value T
  → CastResult (` P)
⟦ ε      ⟧h v = return v
⟦ ⁇ P2 l ⟧h (dyn (same P1) v) = ⟦ seq-m (` id-m P1) (some l P1 P2) (` id-m P2) ⟧m v 

⟦_⟧ : ∀ {T1 T2}
  → Cast T1 T2
  → Value T1
  ---
  → CastResult T2
⟦ id*     ⟧ v = return v
⟦ ↷ h m t ⟧ v = ⟦ h ⟧h v >>= ⟦ m ⟧m >>= ⟦ t ⟧t

H : CastADT Injectable
H
  = record
    { Cast = Cast
    ; id  = id
    ; ⌈_⌉ = ⌈_⌉
    ; _⨟_ = _⨟_
    ; ⟦_⟧ = ⟦_⟧
    }

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

lem-seq-some : ∀ {T0 T1 T2 T3}
  → (c1 : Cast T0 T1)
  → (l  : Label)
  → (c2 : Cast T2 T3)
  → (c1 ⨟ ⌈ T1 ⟹[ l ] T2 ⌉) ⨟ c2 ≡ seq c1 (some l T1 T2) c2
lem-seq-some {T1 = T1} {T2 = T2} c1 l c2
  rewrite sym (seq-assoc c1 none (id T1) (some l T1 T2) (id T2))
  | identityʳ c1
  | seq-assoc c1 (some l T1 T2) (id T2) none c2
  | identityˡ c2
  = refl

lem⁻ : ∀ {T0 T1 T2 T3 T4}
  → (c1 : Cast   T0 T1)
  → (l  : Label)
  → (c2 : Cast   T2 T3)
  → (c3 : Cast T3 T4)
  → c1 ⨟ (⌈ T1 ⟹[ l ] T2 ⌉ ⨟ (c2 ⨟ c3))
      ≡
    (seq c1 (some l T1 T2) c2) ⨟ c3
lem⁻ {T1 = T1} c1 l c2 c3
  rewrite sym (seq-assoc ⌈ T1 ⟹[ l ] _ ⌉ none c2 none c3)
        | sym (seq-assoc c1 none (seq ⌈ _ ⟹[ l ] _ ⌉ none c2) none c3)
        | sym (seq-assoc c1 none ⌈ _ ⟹[ l ] _ ⌉ none c2)
        | lem-seq-some c1 l c2
  = refl

lem⁺ : ∀ {T1 T2 T3 T4 T5}
  → (c1 : Cast T1 T2)
  → (c2 : Cast   T2 T3)
  → (l  : Label)
  → (c3 : Cast   T4 T5)
  → ((c1 ⨟ c2) ⨟ ⌈ T3 ⟹[ l ] T4 ⌉ ) ⨟ c3
      ≡
    (c1 ⨟ (seq c2 (some l T3 T4) c3))
lem⁺ {T4 = T4} c1 c2 l c3
  rewrite seq-assoc c1 none c2 none ⌈ _ ⟹[ l ] T4 ⌉ 
        | seq-assoc c1 none (seq c2 none ⌈ _ ⟹[ l ] _ ⌉) none c3
        | lem-seq-some c2 l c3
  = refl

lem-seq-m : ∀ {P1 P2 T P3 P4}
  → (m1 : Body P1 P2)
  → (t1 : Tail P2 T)
  → (h2 : Head T  P3)
  → (m2 : Body P3 P4)
  → (∀ v →
       ⟦ seq-m m1 (link t1 none h2) m2 ⟧m v
         ≡
       (⟦ m1 ⟧m >=> ⟦ t1 ⟧t >=> ⟦ h2 ⟧h >=> ⟦ m2 ⟧m) v)
lem-seq-m (⊥ a l) t1 h2 m2 v = refl
lem-seq-m (` m1) (‼ P1) (⁇ P2 l) m2 v
  with tagof-mm-r m1 | tagof-m-l m2 | (tagof-mm-r (id-m P1)) | (tagof-mm-l (id-m P2))
... | t1 | t2 | t3 | t4
  rewrite tag-unique t1 t3 | tag-unique t2 t4
  with ⌣?-by-tags t3 t4
lem-seq-m (` m1) (‼ P1) (⁇ P2 l) m2       v | t1 | t2 | t3 | t4 | no ¬p = refl
lem-seq-m (` m1) (‼ P1) (⁇ P2 l) (⊥ a l') v | t1 | t2 | t3 | t4 | yes p = refl
lem-seq-m (` B) (‼ .B) (⁇ .B l) (` B) v | t1 | t2 | t3 | t4 | yes ⌣B = refl
lem-seq-m (` (c₁ ⇒ c₂)) (‼ .(_ ⇒ _)) (⁇ .(_ ⇒ _) l) (` (c₃ ⇒ c₄)) (lam⟨ c1 ⇒ c2 ⟩ e E) | t1 | t2 | t3 | t4 | yes ⌣⇒
  rewrite lem⁻ c₃ l c₁ c1 | lem⁺ c2 c₂ l c₄
  = refl
lem-seq-m (` (c₁ ⊗ c₂)) (‼ .(_ ⊗ _)) (⁇ .(_ ⊗ _) l) (` (c₃ ⊗ c₄)) (cons⟨ c1 ⊗ c2 ⟩ v1 v2) | t1 | t2 | t3 | t4 | yes ⌣⊗
  rewrite lem⁺ c1 c₁ l c₃ | lem⁺ c2 c₂ l c₄
  = refl
lem-seq-m (` m1) ε ε m2 v with ⌣?-by-tags (tagof-mm-r m1) (tagof-m-l m2) 
lem-seq-m (` m1) ε ε m2 v | no ¬p = ⊥-elim (¬p (⌣refl _))
lem-seq-m (` m1) ε ε (⊥ a l) v | yes p = refl
lem-seq-m (` B) ε ε (` B) v | yes ⌣B = refl
lem-seq-m (` (c₁ ⇒ c₂)) ε ε (` (c₃ ⇒ c₄)) (lam⟨ c1 ⇒ c2 ⟩ e E) | yes ⌣⇒
  rewrite ⨟-assoc (c₃) (c₁) c1 | ⨟-assoc c2 (c₂) (c₄) = refl
lem-seq-m (` (c₁ ⊗ c₂)) ε ε (` (c₃ ⊗ c₄)) (cons⟨ c1 ⊗ c2 ⟩ v1 v2) | yes ⌣⊗
  rewrite ⨟-assoc c1 (c₁) (c₃) | ⨟-assoc c2 (c₂) (c₄)
  = refl

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
  | mk-tail-none t1
  | >>=-return (⟦ h1 ⟧h v >>= ⟦ m1 ⟧m >>= ⟦ t1 ⟧t)
  = refl
lem-seq (↷ h1 m1 t1) (↷ h2 m2 t2) v with ⟦ h1 ⟧h v
lem-seq (↷ h1 m1 t1) (↷ h2 m2 t2) v | raise l   = refl
lem-seq (↷ h1 m1 t1) (↷ h2 m2 t2) v | return v'
  rewrite >=>->>= (⟦ m1 ⟧m v' >>= ⟦ t1 ⟧t) (⟦ h2 ⟧h >=> ⟦ m2 ⟧m) ⟦ t2 ⟧t
        | >=>->>= (⟦ m1 ⟧m v' >>= ⟦ t1 ⟧t) ⟦ h2 ⟧h ⟦ m2 ⟧m
  = cong (_>>= ⟦ t2 ⟧t) (lem-seq-m m1 t1 h2 m2 v')

H-Basic : CastADTBasic Injectable H
H-Basic = record { lem-id = lem-id ; lem-seq = lem-seq }

eq-¬⌣ : ∀ {T1 T2}
  → (l : Label)
  → ¬ (T1 ⌣ T2)
  → (v : Value T1)
  ---
  → ⟦ ⌈ T1 ⟹[ l ] T2 ⌉ ⟧ v
      ≡
    raise l
eq-¬⌣ {*} {*}   l ¬T1⌣T2 v = ⊥-elim (¬T1⌣T2 *⌣*)
eq-¬⌣ {*} {` P} l ¬T1⌣T2 v = ⊥-elim (¬T1⌣T2 (*⌣P P))
eq-¬⌣ {` P} {*} l ¬T1⌣T2 v = ⊥-elim (¬T1⌣T2 (P⌣* P))
eq-¬⌣ {` P1} {` P2} l ¬T1⌣T2 v
  with ⌣?-by-tags (tagof-mm-r (id-m P1)) (tagof-mm-l (id-m P2))
eq-¬⌣ {` P1} {` P2} l ¬T1⌣T2 v | yes p = ⊥-elim (¬T1⌣T2 p)
eq-¬⌣ {` P1} {` P2} l ¬T1⌣T2 v | no ¬p = refl

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
eq-*P Q P l v with ⟦ seq-m (` id-m P) (some l P Q) (` id-m Q) ⟧m v
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


-- data Cast : Type → Type → Set where
--   id : ∀ {T} → Cast T T
--   hc : ∀ {T1 T2} → Cast T1 T2 → Cast T1 T2

-- ⌈_⌉ : ∀ {T1 T2} → SrcCast T1 T2 → Cast T1 T2
-- ⌈ S ⟹[ l ] T ⌉ = hc (mk-cast l S T)

-- _⨟_ : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
-- id   ⨟ d    = d
-- hc c ⨟ id   = hc c
-- hc c ⨟ hc d = hc (_⨟_ c d)

-- ⨟-assoc : ∀ {T1 T2 T3 T4}
--   → (c1 : Cast T1 T2)
--   → (c2 : Cast T2 T3)
--   → (c3 : Cast T3 T4)
--   → (c1 ⨟ c2) ⨟ c3 ≡ c1 ⨟ (c2 ⨟ c3)
-- ⨟-assoc id      c2      c3      = refl
-- ⨟-assoc (hc c1) id      c3      = refl
-- ⨟-assoc (hc c1) (hc c2) id      = refl
-- ⨟-assoc (hc c1) (hc c2) (hc c3) = cong hc (seq-assoc c1 _ c2 _ c3)

-- --- New Apply Cast

-- maybe-dyn : ∀ {P T}
--   → Tail P T
--   → Value (` P)
--   ---
--   → Value T
-- maybe-dyn (‼ P) v = dyn P tt v
-- maybe-dyn ε     v = v


-- lem-id : ∀ {T}
--   → (v : Value T)  
--   -----------------------------
--   → ⟦ id ⟧ v ≡ return v
-- lem-id v = refl

-- lem-seq-some : ∀ {T0 T1 T2 T3}
--   → (c1 : Cast T0 T1)
--   → (l  : Label)
--   → (c2 : Cast T2 T3)
--   → _⨟_ (_⨟_ c1 (mk-cast l T1 T2)) c2 ≡ seq c1 (some l T1 T2) c2
-- lem-seq-some {T1 = T1} {T2 = T2} c1 l c2
--   rewrite sym (seq-assoc c1 none (id T1) (some l T1 T2) (id T2))
--   | identityʳ c1
--   | seq-assoc c1 (some l T1 T2) (id T2) none c2
--   | identityˡ c2
--   = refl

-- lem⁻ : ∀ {T0 T1 T2 T3 T4}
--   → (c1 : Cast   T0 T1)
--   → (l  : Label)
--   → (c2 : Cast   T2 T3)
--   → (c3 : Cast T3 T4)
--   → hc c1 ⨟ (hc (mk-cast l T1 T2) ⨟ (hc c2 ⨟ c3))
--       ≡
--     hc (seq c1 (some l T1 T2) c2) ⨟ c3
-- lem⁻ c1 l c2 id
--   rewrite sym (seq-assoc c1 none (mk-cast l _ _) none c2)
--   | lem-seq-some c1 l c2
--   = refl
-- lem⁻ {T1 = T1} c1 l c2 (hc c3)
--   rewrite sym (seq-assoc (mk-cast l T1 _) none c2 none c3)
--         | sym (seq-assoc c1 none (seq (mk-cast l _ _) none c2) none c3)
--         | sym (seq-assoc c1 none (mk-cast l _ _) none c2)
--         | lem-seq-some c1 l c2
--   = refl

-- lem⁺ : ∀ {T1 T2 T3 T4 T5}
--   → (c1 : Cast T1 T2)
--   → (c2 : Cast   T2 T3)
--   → (l  : Label)
--   → (c3 : Cast   T4 T5)
--   → ((c1 ⨟ hc c2) ⨟ hc (mk-cast l T3 T4)) ⨟ hc c3
--       ≡
--     (c1 ⨟ hc (seq c2 (some l T3 T4) c3))
-- lem⁺ id c2 l c3 rewrite lem-seq-some c2 l c3 = refl
-- lem⁺ {T4 = T4} (hc c1) c2 l c3
--   rewrite seq-assoc c1 none c2 none (mk-cast l _ T4)
--         | seq-assoc c1 none (seq c2 none (mk-cast l _ _)) none c3
--         | lem-seq-some c2 l c3
--   = refl

-- lem-seq-m : ∀ {P1 P2 T P3 P4}
--   → (m1 : Body P1 P2)
--   → (t1 : Tail P2 T)
--   → (h2 : Head T  P3)
--   → (m2 : Body P3 P4)
--   → (∀ v →
--        ⟦ seq-m m1 (link t1 none h2) m2 ⟧m v
--          ≡
--        (⟦ m1 ⟧m >=> ⟦ t1 ⟧t >=> ⟦ h2 ⟧h >=> ⟦ m2 ⟧m) v)
-- lem-seq-m (⊥ a l) t1 h2 m2 v = refl
-- lem-seq-m (` m1) (‼ P1) (⁇ P2 l) m2 v
--   with tagof-mm-r m1 | tagof-m-l m2 | (tagof-mm-r (id-m P1)) | (tagof-mm-l (id-m P2))
-- ... | t1 | t2 | t3 | t4
--   rewrite tag-unique t1 t3 | tag-unique t2 t4
--   with ⌣?-by-tags t3 t4
-- lem-seq-m (` m1) (‼ P1) (⁇ P2 l) m2       v | t1 | t2 | t3 | t4 | no ¬p = refl
-- lem-seq-m (` m1) (‼ P1) (⁇ P2 l) (⊥ a l') v | t1 | t2 | t3 | t4 | yes p = refl
-- lem-seq-m (` B) (‼ .B) (⁇ .B l) (` B) v | t1 | t2 | t3 | t4 | yes ⌣B = refl
-- lem-seq-m (` (c₁ ⇒ c₂)) (‼ .(_ ⇒ _)) (⁇ .(_ ⇒ _) l) (` (c₃ ⇒ c₄)) (lam⟨ c1 ⇒ c2 ⟩ e E) | t1 | t2 | t3 | t4 | yes ⌣⇒
--   rewrite lem⁻ c₃ l c₁ c1 | lem⁺ c2 c₂ l c₄
--   = refl
-- lem-seq-m (` (c₁ ⊗ c₂)) (‼ .(_ ⊗ _)) (⁇ .(_ ⊗ _) l) (` (c₃ ⊗ c₄)) (cons⟨ c1 ⊗ c2 ⟩ v1 v2) | t1 | t2 | t3 | t4 | yes ⌣⊗
--   rewrite lem⁺ c1 c₁ l c₃ | lem⁺ c2 c₂ l c₄
--   = refl
-- lem-seq-m (` m1) ε ε m2 v with ⌣?-by-tags (tagof-mm-r m1) (tagof-m-l m2) 
-- lem-seq-m (` m1) ε ε m2 v | no ¬p = ⊥-elim (¬p (⌣refl _))
-- lem-seq-m (` m1) ε ε (⊥ a l) v | yes p = refl
-- lem-seq-m (` B) ε ε (` B) v | yes ⌣B = refl
-- lem-seq-m (` (c₁ ⇒ c₂)) ε ε (` (c₃ ⇒ c₄)) (lam⟨ c1 ⇒ c2 ⟩ e E) | yes ⌣⇒
--   rewrite ⨟-assoc (hc c₃) (hc c₁) c1 | ⨟-assoc c2 (hc c₂) (hc c₄) = refl
-- lem-seq-m (` (c₁ ⊗ c₂)) ε ε (` (c₃ ⊗ c₄)) (cons⟨ c1 ⊗ c2 ⟩ v1 v2) | yes ⌣⊗
--   rewrite ⨟-assoc c1 (hc c₁) (hc c₃) | ⨟-assoc c2 (hc c₂) (hc c₄)
--   = refl

-- lem-seq-c : ∀ {T1 T2 T3}
--   → (c1 : Cast T1 T2)
--   → (c2 : Cast T2 T3)
--   → ∀ v
--   --------------------
--   → ⟦ _⨟_ c1 c2 ⟧c v ≡ (⟦ c1 ⟧c >=> ⟦ c2 ⟧c) v
-- lem-seq-c id* c2 v
--   rewrite identityˡ c2
--   = refl
-- lem-seq-c (↷ h1 m1 t1) id* v
--   rewrite identityʳ (↷ h1 m1 t1)
--   | mk-tail-none t1
--   | >>=-return (⟦ h1 ⟧h v >>= ⟦ m1 ⟧m >>= ⟦ t1 ⟧t)
--   = refl
-- lem-seq-c (↷ h1 m1 t1) (↷ h2 m2 t2) v with ⟦ h1 ⟧h v
-- lem-seq-c (↷ h1 m1 t1) (↷ h2 m2 t2) v | raise l   = refl
-- lem-seq-c (↷ h1 m1 t1) (↷ h2 m2 t2) v | return v'
--   rewrite >=>->>= (⟦ m1 ⟧m v' >>= ⟦ t1 ⟧t) (⟦ h2 ⟧h >=> ⟦ m2 ⟧m) ⟦ t2 ⟧t
--         | >=>->>= (⟦ m1 ⟧m v' >>= ⟦ t1 ⟧t) ⟦ h2 ⟧h ⟦ m2 ⟧m
--   = cong (_>>= ⟦ t2 ⟧t) (lem-seq-m m1 t1 h2 m2 v')

-- lem-seq : ∀ {T1 T2 T3}
--   → (c1 : Cast T1 T2)
--   → (c2 : Cast T2 T3)
--   → ∀ v
--   --------------------
--   → ⟦ c1 ⨟ c2 ⟧ v ≡ (⟦ c1 ⟧ >=> ⟦ c2 ⟧) v
-- lem-seq id     c2     v = refl
-- lem-seq (hc c) id     v = sym (>>=-return (⟦ hc c ⟧ v))
-- lem-seq (hc c) (hc d) v = lem-seq-c c d v

-- H-basic : CastADTBasic Injectable H
-- H-basic =
--   record
--     { lem-id = lem-id
--     ; lem-seq = lem-seq }
