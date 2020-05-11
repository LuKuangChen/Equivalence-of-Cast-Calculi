module CastRepresentations.LazyUDHypercoercions2 (Label : Set) where

open import Types
open import Cast Label using (_⟹[_]_) renaming (Cast to SrcCast)
open import Terms Label
open import S.CastADT Label

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Data.Vec using (Vec; replicate; []; _∷_; map)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Unit renaming (⊤ to Unit)
open import Data.Product 
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

data Head (op : TypeOp) : Type → Vec Type (arity op) → Set where
  ε : ∀ {Ts}
    → Head op (` (op · Ts)) Ts
  ⁇ : Label
    → Head op * (replicate *)

data Tail (op : TypeOp) : Vec Type (arity op) → Type → Set where
  ε : ∀ {Ts}
    → Tail op Ts (` (op · Ts))
  ‼ : Tail op (replicate *) *

mutual
  data Cast : Type → Type → Set where
    * : Cast * *
    ⊥ : ∀ op {A S* B}
      → (h : Head op A S*)
      → (l : Label)
        ------------------
      → Cast A B
    ↷ : ∀ op {A S* T* B}
      → (h : Head op A S*)
      → (m : Cast* (polarity op) S* T*)
      → (t : Tail op T* B)
        ------------------
      → Cast A B

  Middle : (o : TypeOp) → Vec Type (arity o) → Vec Type (arity o) → Set
  Middle o S* T* = Cast* (polarity o) S* T*

  data Cast* : {n : ℕ}(bs : Vec Polarity n) → Vec Type n → Vec Type n → Set where
    []  : Cast* [] [] []
    _∷_ : ∀ {n b S T}
      → {b* : Vec Polarity n}
      → {S* : Vec Type n}
      → {T* : Vec Type n}
      → Cast (choose b T S) (choose b S T)
      → Cast* b* S* T*
      → Cast* (b ∷ b*) (S ∷ S*) (T ∷ T*)

data Gap : ∀ {o1 o2 S* T T*} → Tail o1 S* T → Head o2 T T* → Set where
  some : ∀ {o1 o2}
    → (¬p : ¬ (o1 ≡ o2))
    → (l  : Label)
    → Gap {o1 = o1} {o2 = o2}  ‼ (⁇ l)

  none : ∀ {o S* T}
    → {t : Tail o S* T}
    → {h : Head o T S*}
    → Gap t h

check-gap : ∀ o1 o2 {S* T T*}
  → (t : Tail o1 S* T)
  → (h : Head o2 T T*)
  → Gap t h
check-gap o1 o2 ε ε = none
check-gap o1 o2 ‼ (⁇ l) with o1 ≟op o2
check-gap o2 o2 ‼ (⁇ l) | yes refl  = none
check-gap o1 o2 ‼ (⁇ l) | no ¬o1≡o2 = some ¬o1≡o2 l

mutual
  _⨟_ : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
  *        ⨟ d = d
  ⊥ op h l ⨟ d = ⊥ op h l
  ↷ op h m t ⨟ * = ↷ op h m t
  ↷ op h m t ⨟ ⊥ op' h' l with check-gap op op' t h'
  ↷ op h m t ⨟ ⊥ op' h' l | some ¬p l' = ⊥ op h l'
  ↷ op h m t ⨟ ⊥ op  h' l | none       = ⊥ op h l
  ↷ op h m t ⨟ ↷ op' h' m' t' with check-gap op op' t h'
  ↷ op h m t ⨟ ↷ op' h' m' t' | some ¬p l = ⊥ op h l
  ↷ op h m t ⨟ ↷ op  h' m' t' | none      = ↷ op h ([ polarity op ] m ⨟* m') t'

  [_]_⨟*_ : ∀ {n T*1 T*2 T*3}
    → (b* : Vec Polarity n)
    → Cast* b* T*1 T*2
    → Cast* b* T*2 T*3
    → Cast* b* T*1 T*3
  [ []     ] []       ⨟* []       = []
  [ - ∷ b* ] (c ∷ c*) ⨟* (d ∷ d*) = (d ⨟ c) ∷ ([ b* ] c* ⨟* d*)
  [ + ∷ b* ] (c ∷ c*) ⨟* (d ∷ d*) = (c ⨟ d) ∷ ([ b* ] c* ⨟* d*)

mutual
  ⇑* : Label → ∀ T → Cast T *
  ⇑* l *     = *
  ⇑* l (` P) = ⇑ l P
  
  ⇑ : Label → ∀ P → Cast (` P) *
  ⇑ l (op · T*) = ↷ op ε (f (polarity op) T*) ‼
    where
    f : ∀ {n}
      → (p* : Vec Polarity n)
      → (T* : Vec Type n)
      → Cast* p* T* (replicate *) 
    f [] [] = []
    f (- ∷ p*) (T ∷ T*) = (⇓* l T) ∷ (f p* T*)
    f (+ ∷ p*) (T ∷ T*) = (⇑* l T) ∷ (f p* T*)

  ⇓* : Label → ∀ T → Cast * T
  ⇓* l *     = *
  ⇓* l (` P) = ⇓ l P
  
  ⇓ : Label → ∀ P → Cast * (` P)
  ⇓ l (op · T*) = ↷ op (⁇ l) (f (polarity op) T*) ε
    where
    f : ∀ {n}
      → (p* : Vec Polarity n)
      → (T* : Vec Type n)
      → Cast* p* (replicate *) T*
    f [] [] = []
    f (- ∷ p*) (T ∷ T*) = (⇑* l T) ∷ (f p* T*)
    f (+ ∷ p*) (T ∷ T*) = (⇓* l T) ∷ (f p* T*)

⌈_⌉ : ∀ {T1 T2} → SrcCast T1 T2 → Cast T1 T2
⌈ S ⟹[ l ] T ⌉ = ⇑* l S ⨟ ⇓* l T

mutual
  id : ∀ T → Cast T T
  id * = *
  id (` (op · T*)) = ↷ op ε (id* (polarity op) T*) ε
  
  id* : ∀ {n}
    → (p* : Vec Polarity n)
    → (T* : Vec Type n)
    → Cast* p* T* T*
  id* [] [] = []
  id* (- ∷ p*) (T ∷ T*) = (id T) ∷ (id* p* T*)
  id* (+ ∷ p*) (T ∷ T*) = (id T) ∷ (id* p* T*)

open import R.BlameStrategies Label using (BlameStrategy; LazyUDBS)
open BlameStrategy LazyUDBS using (Injectable)

open import S.Values Label Injectable Cast

open import Error
  using (Error; return; raise; _>>=_; _>=>_
        ;>>=-return; >>=-assoc; >=>-assoc; >=>->>=)

CastResult : Type → Set
CastResult T = Error Label (Value T)

⟦_,_⟧t : ∀ op {T* T}
  → Tail op T* T
  → Value (` (op · T*))
  ---
  → CastResult T
⟦ op , ‼ ⟧t v = return (dyn (op→ground-Ground op) v)
⟦ op , ε ⟧t v = return v

⟦_,_⟧m : ∀ o {S* T*}
  → Middle o S* T*
  → Value (` (o · S*))
  ---
  → CastResult (` (o · T*))
⟦_,_⟧m `B [] v = return v
⟦_,_⟧m `⊗ (c₂ ∷ d₂ ∷ []) (cons⟨ c₁ ⊗ d₁ ⟩ v u) = return (cons⟨ c₁ ⨟ c₂ ⊗ d₁ ⨟ d₂ ⟩ v u)
⟦_,_⟧m `⇒ (c₂ ∷ d₂ ∷ [])  (lam⟨ c₁ ⇒ d₁ ⟩ e E) = return ( lam⟨ c₂ ⨟ c₁ ⇒ d₁ ⨟ d₂ ⟩ e E)

⟦_,_⟧h : ∀ op {S T*}
  → Head op S T*
  → Value S
  → CastResult (` op · T*)
⟦ o , ε   ⟧h v = return v
⟦ o , ⁇ l ⟧h (dyn gP v) with inv-ground gP
⟦ o , ⁇ l ⟧h (dyn gP v) | o' , refl with o' ≟op o
⟦ o , ⁇ l ⟧h (dyn gP v) | o' , refl | yes refl = return v
⟦ o , ⁇ l ⟧h (dyn gP v) | o' , refl | no ¬p    = raise  l

⟦_⟧ : ∀ {T1 T2}
  → Cast T1 T2
  → Value T1
  ---
  → CastResult T2
⟦ * ⟧ v = return v
⟦ ⊥ op h l   ⟧ v = raise l
⟦ ↷ op h m t ⟧ v = ⟦ op , h ⟧h v >>= ⟦ op , m ⟧m >>= ⟦ op , t ⟧t

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
  identityˡ * = refl
  identityˡ (⊥ op ε l)     = refl
  identityˡ (⊥ op (⁇ _) l) = refl
  identityˡ (↷ op (⁇ l) m t) = refl
  identityˡ (↷ op ε m t) = cong (λ □ → ↷ op ε □ t) (f (polarity op) m)
    where
    f : ∀ {n S* T*}
      → (p* : Vec Polarity n)
      → (c* : Cast* p* S* T*)
      → [ p* ] id* p* S* ⨟* c* ≡ c*
    f [] [] = refl
    f (- ∷ p*) (c ∷ c*) = cong₂ _∷_ (identityʳ c) (f p* c*)
    f (+ ∷ p*) (c ∷ c*) = cong₂ _∷_ (identityˡ c) (f p* c*)
  
  identityʳ : ∀ {T1 T2} → (c : Cast T1 T2) → c ⨟ id T2 ≡ c
  identityʳ * = refl
  identityʳ (⊥ op h l)     = refl
  identityʳ (↷ op h m ‼) = refl
  identityʳ (↷ op h m ε) = cong (λ □ → ↷ op h □ ε) (f (polarity op) m)
    where
    f : ∀ {n S* T*}
      → (p* : Vec Polarity n)
      → (c* : Cast* p* S* T*)
      → [ p* ] c* ⨟* id* p* T* ≡ c*
    f [] [] = refl
    f (- ∷ p*) (c ∷ c*) = cong₂ _∷_ (identityˡ c) (f p* c*)
    f (+ ∷ p*) (c ∷ c*) = cong₂ _∷_ (identityʳ c) (f p* c*)

mutual
  assoc : ∀ {T1 T2 T3 T4}
    → (c1 : Cast T1 T2)
    → (c2 : Cast T2 T3)
    → (c3 : Cast T3 T4)
    → (c1 ⨟ c2) ⨟ c3 ≡ c1 ⨟ (c2 ⨟ c3)
  assoc * c2 c3 = refl
  assoc (⊥ op h l) c2 c3 = refl
  assoc (↷ op h m t) * c3 = refl
  assoc (↷ op h m t) (⊥ op₁ h₁ l₁) c3 with check-gap op op₁ t h₁
  assoc (↷ op h m t) (⊥ op₁ h₁ l₁) c3 | some ¬p l = refl
  assoc (↷ op h m t) (⊥ .op h₁ l₁) c3 | none = refl
  assoc (↷ op h m t) (↷ op₁ h₁ m₁ t₁) * with check-gap op op₁ t h₁
  assoc (↷ op h m t) (↷ op₁ h₁ m₁ t₁) * | some ¬p l = refl
  assoc (↷ op h m t) (↷ .op h₁ m₁ t₁) * | none = refl
  assoc (↷ op h m t) (↷ op₁ h₁ m₁ t₁) (⊥ op₂ h₂ l) with check-gap op op₁ t h₁
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l₁) m₁ t₁) (⊥ op₂ h₂ l) | some ¬p l₁ with check-gap op₁ op₂ t₁ h₂
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l₁) m₁ .‼) (⊥ op₂ .(⁇ l₂) l) | some ¬p l₁ | some ¬p₁ l₂ with  op ≟op op₁
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l₁) m₁ .‼) (⊥ op₂ .(⁇ l₂) l) | some ¬p l₁ | some ¬p₁ l₂ | yes refl = ⊥-elim (¬p refl)
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l₁) m₁ .‼) (⊥ op₂ .(⁇ l₂) l) | some ¬p l₁ | some ¬p₁ l₂ | no ¬p₂ = refl
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l₁) m₁ t₁) (⊥ .op₁ h₂ l) | some ¬p l₁ | none with op ≟op op₁
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l₁) m₁ t₁) (⊥ .op₁ h₂ l) | some ¬p l₁ | none | yes refl = ⊥-elim (¬p refl)
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l₁) m₁ t₁) (⊥ .op₁ h₂ l) | some ¬p l₁ | none | no ¬p₁ = refl
  assoc (↷ op h m t) (↷ .op h₁ m₁ t₁) (⊥ op₂ h₂ l) | none with check-gap op op₂ t₁ h₂
  assoc (↷ op h m t) (↷ .op h₁ m₁ .‼) (⊥ op₂ .(⁇ l₁) l) | none | some ¬p l₁ with check-gap op op t h₁
  assoc (↷ op h m .‼) (↷ .op .(⁇ l₂) m₁ .‼) (⊥ op₂ .(⁇ l₁) l) | none | some ¬p l₁ | some ¬p₁ l₂ = ⊥-elim (¬p₁ refl)
  assoc (↷ op h m t) (↷ .op h₁ m₁ .‼) (⊥ op₂ .(⁇ l₁) l) | none | some ¬p l₁ | none = refl
  assoc (↷ op h m t) (↷ .op h₁ m₁ t₁) (⊥ .op h₂ l) | none | none with check-gap op op t h₁
  assoc (↷ op h m .‼) (↷ .op .(⁇ l₁) m₁ t₁) (⊥ .op h₂ l) | none | none | some ¬p l₁ = ⊥-elim (¬p refl)
  assoc (↷ op h m t) (↷ .op h₁ m₁ t₁) (⊥ .op h₂ l) | none | none | none = refl
  assoc (↷ op h m t) (↷ op₁ h₁ m₁ t₁) (↷ op₂ h₂ m₂ t₂) with check-gap op op₁ t h₁
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l) m₁ t₁) (↷ op₂ h₂ m₂ t₂) | some ¬p l with check-gap op₁ op₂ t₁ h₂
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l) m₁ .‼) (↷ op₂ .(⁇ l₁) m₂ t₂) | some ¬p l | some ¬p₁ l₁ with op ≟op op₁
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l) m₁ .‼) (↷ op₂ .(⁇ l₁) m₂ t₂) | some ¬p l | some ¬p₁ l₁ | yes refl = ⊥-elim (¬p refl)
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l) m₁ .‼) (↷ op₂ .(⁇ l₁) m₂ t₂) | some ¬p l | some ¬p₁ l₁ | no ¬p₂ = refl
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l) m₁ t₁) (↷ .op₁ h₂ m₂ t₂) | some ¬p l | none with op ≟op op₁
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l) m₁ t₁) (↷ .op₁ h₂ m₂ t₂) | some ¬p l | none | yes refl = ⊥-elim (¬p refl)
  assoc (↷ op h m .‼) (↷ op₁ .(⁇ l) m₁ t₁) (↷ .op₁ h₂ m₂ t₂) | some ¬p l | none | no ¬p₁ = refl
  assoc (↷ op h m t) (↷ .op h₁ m₁ t₁) (↷ op₂ h₂ m₂ t₂) | none with check-gap op op₂ t₁ h₂
  assoc (↷ op h m t) (↷ .op h₁ m₁ .‼) (↷ op₂ .(⁇ l) m₂ t₂) | none | some ¬p l with check-gap op op t h₁
  assoc (↷ op h m .‼) (↷ .op .(⁇ l₁) m₁ .‼) (↷ op₂ .(⁇ l) m₂ t₂) | none | some ¬p l | some ¬p₁ l₁ = ⊥-elim (¬p₁ refl)
  assoc (↷ op h m t) (↷ .op h₁ m₁ .‼) (↷ op₂ .(⁇ l) m₂ t₂) | none | some ¬p l | none = refl
  assoc (↷ op h m t) (↷ .op h₁ m₁ t₁) (↷ .op h₂ m₂ t₂) | none | none with check-gap op op t h₁
  assoc (↷ op h m .‼) (↷ .op .(⁇ l) m₁ t₁) (↷ .op h₂ m₂ t₂) | none | none | some ¬p l = ⊥-elim (¬p refl)
  assoc (↷ op h m t) (↷ .op h₁ m₁ t₁) (↷ .op h₂ m₂ t₂) | none | none | none = cong (λ □ → ↷ op h □ t₂) (assoc* (polarity op) m m₁ m₂)

  assoc* : ∀ {n T*1 T*2 T*3 T*4}
    → (b* : Vec Polarity n)
    → (xs : Cast* b* T*1 T*2)
    → (ys : Cast* b* T*2 T*3)
    → (zs : Cast* b* T*3 T*4)
    → [ b* ] ([ b* ] xs ⨟* ys) ⨟* zs
      ≡
      [ b* ] xs ⨟* [ b* ] ys ⨟* zs
  assoc* [] [] [] [] = refl
  assoc* (- ∷ b*) (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ _∷_ (sym (assoc z y x)) (assoc* b* xs ys zs)
  assoc* (+ ∷ b*) (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ _∷_      (assoc x y z)  (assoc* b* xs ys zs)

lem-seq : ∀ {T1 T2 T3}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → ∀ v
  --------------------
  → ⟦ c1 ⨟ c2 ⟧ v ≡ ⟦ c1 ⟧ v >>= ⟦ c2 ⟧
lem-seq * d v = refl
lem-seq (⊥ op h l) d v = refl
lem-seq (↷ op h m t) * v = sym (>>=-return _)
lem-seq (↷ op h m t) (⊥ op₁ h₁ l) v = {!!}
lem-seq (↷ op h m t) (↷ op₁ h₁ m₁ t₁) v = {!!}
