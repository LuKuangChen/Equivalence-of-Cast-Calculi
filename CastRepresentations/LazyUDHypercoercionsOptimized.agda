module CastRepresentations.LazyUDHypercoercionsOptimized
  (Label : Set)
  where
{-
2020-05-11 Kuang-Chen

This variant of hypercoercions has a unique representation for all
identity casts between pretypes, written as (↷ ε (` ε) ε).

This property has a benefit that applying identity casts, which
I guess happens a lot in realistic programs, always take constant time.
-}


open import Types
open import LabelUtilities Label
open import Cast Label using (_⟹[_]_) renaming (Cast to SrcCast)
open import Terms Label
open import S.CastADT Label
open import Variables using () renaming (_,_ to _,'_)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Vec using (Vec; replicate; []; _∷_; map)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)


data Head : (G : TypeOp) → Type → (Vec Type (arity G)) → Set where

  ⁇ : ∀ G
    → (l : Label×Polarity) → Head G * (replicate *) 

  ε : ∀ {G Ts}
    → Head G (` G · Ts) Ts


data Tail : (G : TypeOp) → (Vec Type (arity G)) → Type → Set where

  ‼ : ∀ G
    → Tail G (replicate *) *

  ε : ∀ {G Ts}
    → Tail G Ts (` G · Ts)




data Cast : Type → Type → Set
data Body : (G : TypeOp) → Vec Type (arity G)
          → (H : TypeOp) → Vec Type (arity H)
          → Set
data PreBody : (G : TypeOp) → Vec Type (arity G) → Vec Type (arity G) → Set
data Identity : {S T : Type} → Cast S T → Set


data Cast where
  * : Cast * *
  ↷ : ∀ {A G H Ss Ts B}
    → (h : Head G A Ss)
    → (m : Body G Ss H Ts)
    → (t : Tail H Ts B)
      --------------
    → Cast A B


data Body where

  ⊥ : ∀ {G Ss H Ts}
    → (l : Label×Polarity)
    → Body G Ss H Ts

  `_ : ∀ {G Ss Ts}
    → (m : PreBody G Ss Ts)
    → Body G Ss G Ts


data PreBody where

  ε : ∀ {G Ts}
    → PreBody G Ts Ts
    
  _⇒̂_ : ∀ {S₁ S₂ T₁ T₂}
    → (c : Cast S₂ S₁)
    → (d : Cast T₁ T₂)
    → .(¬p : ¬ (Identity c × Identity d))
      --------------------------------------
    → PreBody `⇒ (S₁ ∷ T₁ ∷ []) (S₂ ∷ T₂ ∷ [])
    
  _⊗̂_ : ∀ {S₁ S₂ T₁ T₂}
    → (c : Cast S₁ S₂)
    → (d : Cast T₁ T₂)
    → .(¬p : ¬ (Identity c × Identity d))
      ----------------------
    → PreBody `⊗ (S₁ ∷ T₁ ∷ []) (S₂ ∷ T₂ ∷ [])


data Identity where
  id-* : Identity *
  id-P : ∀ {G Ts}
    → Identity {` G · Ts} (↷ ε (` ε) ε)


identity? : ∀ {S T} → (c : Cast S T) → Dec (Identity c)
identity? * = yes id-*
identity? (↷ (⁇ G l) m t) = no λ ()
identity? (↷ ε (⊥ l) t) = no λ ()
identity? (↷ ε (` ε) (‼ G)) = no λ ()
identity? (↷ ε (` ε) ε) = yes id-P
identity? (↷ ε (` (c ⇒̂ d) ¬p) t) = no λ ()
identity? (↷ ε (` (c ⊗̂ d) ¬p) t) = no λ ()


identity-implies-type-equality : ∀ {S T} → {c : Cast S T} → (Identity c)
  → S ≡ T
identity-implies-type-equality id-* = refl
identity-implies-type-equality id-P = refl


mk⇒ : ∀ {S₁ T₁ S₂ T₂} → Cast S₂ S₁ → Cast T₁ T₂
  → PreBody `⇒ (S₁ ∷ T₁ ∷ []) (S₂ ∷ T₂ ∷ [])
mk⇒ c d with identity? c
mk⇒ c d | yes id-c with identity? d
mk⇒ c d | yes id-c | yes id-d
  with identity-implies-type-equality id-c
... | refl
  with identity-implies-type-equality id-d
... | refl
  = ε
mk⇒ c d | yes id-c | no ¬id-d = (c ⇒̂ d) λ id → ¬id-d (proj₂ id)
mk⇒ c d | no ¬id-c            = (c ⇒̂ d) λ id → ¬id-c (proj₁ id)


mk⇒-noop : ∀ {S₁ T₁ S₂ T₂}
  → (c : Cast S₂ S₁)
  → (d : Cast T₁ T₂)
  → .(¬p : ¬ (Identity c × Identity d))
  → mk⇒ c d ≡ (c ⇒̂ d) ¬p
mk⇒-noop c d ¬p with identity? c
mk⇒-noop c d ¬p | yes id-c with identity? d
mk⇒-noop c d ¬p | yes id-c | yes id-d = ⊥-elim (¬p (id-c , id-d))
mk⇒-noop c d ¬p | yes id-c | no ¬id-d = refl
mk⇒-noop c d ¬p | no ¬id-c = refl


mk⊗ : ∀ {S₁ T₁ S₂ T₂} → Cast S₁ S₂ → Cast T₁ T₂
  → PreBody `⊗ (S₁ ∷ T₁ ∷ []) (S₂ ∷ T₂ ∷ [])
mk⊗ c d with identity? c
mk⊗ c d | yes id-c with identity? d
mk⊗ c d | yes id-c | yes id-d
  with identity-implies-type-equality id-c
... | refl
  with identity-implies-type-equality id-d
... | refl
  = ε
mk⊗ c d | yes id-c | no ¬id-d = (c ⊗̂ d) λ id → ¬id-d (proj₂ id)
mk⊗ c d | no ¬id-c = (c ⊗̂ d) λ id → ¬id-c (proj₁ id)


mk⊗-noop : ∀ {S₁ T₁ S₂ T₂}
  → (c : Cast S₂ S₁)
  → (d : Cast T₁ T₂)
  → .(¬p : ¬ (Identity c × Identity d))
  → mk⊗ c d ≡ (c ⊗̂ d) ¬p
mk⊗-noop c d ¬p with identity? c
mk⊗-noop c d ¬p | yes id-c with identity? d
mk⊗-noop c d ¬p | yes id-c | yes id-d = ⊥-elim (¬p (id-c , id-d))
mk⊗-noop c d ¬p | yes id-c | no ¬id-d = refl
mk⊗-noop c d ¬p | no ¬id-c = refl


data Incompatible : ∀ {G Ss T H Ts} → Tail G Ss T → Head H T Ts → Set where

  it : ∀ {G H l}
    → (¬G≡H : ¬ (G ≡ H))
    → Incompatible {G} {replicate *} {*} {H} {replicate *} (‼ G) (⁇ H l)


incompatible? : ∀ {G Ss T H Ts} → (t : Tail G Ss T) → (h : Head H T Ts)
  → Incompatible t h ⊎ (G · Ss ≡ H · Ts)
incompatible? (‼ G) (⁇ H l) with G ≟op H
incompatible? (‼ G) (⁇ H l) | yes refl = inj₂ refl
incompatible? (‼ G) (⁇ H l) | no ¬G≡H  = inj₁ (it ¬G≡H)
incompatible? ε ε = inj₂ refl




-- Sequencing

_⨟_ : ∀ {T₁ T₂ T₃} → Cast T₁ T₂ → Cast T₂ T₃ → Cast T₁ T₃
_⨟[_,_]⨟_ : ∀ {G₁ G₂ G₃ G₄ Ts₁ Ts₂ Ts₃ Ts₄ T}
    → Body G₁ Ts₁ G₂ Ts₂
    → Tail G₂ Ts₂ T
    → Head G₃ T Ts₃
    → Body G₃ Ts₃ G₄ Ts₄
    → Body G₁ Ts₁ G₄ Ts₄
_⨟m_ : ∀ {G Ts₁ Ts₂ Ts₃} → PreBody G Ts₁ Ts₂ → PreBody G Ts₂ Ts₃
  → PreBody G Ts₁ Ts₃


*          ⨟ c₂         = c₂
↷ h₁ m₁ t₁ ⨟ *          = ↷ h₁ m₁ t₁
↷ h₁ m₁ t₁ ⨟ ↷ h₂ m₂ t₂ = ↷ h₁ (m₁ ⨟[ t₁ , h₂ ]⨟ m₂) t₂


(⊥  l) ⨟[ t₁ , h₂ ]⨟ m₂ = ⊥ l
(` m₁) ⨟[ t₁ , h₂ ]⨟ m₂ with incompatible? t₁ h₂
(` m₁) ⨟[ t₁ , h₂ ]⨟ (⊥ l) | inj₂ refl = ⊥ l
(` m₁) ⨟[ t₁ , h₂ ]⨟ (` m₂)  | inj₂ refl = ` (m₁ ⨟m m₂)
(` m₁) ⨟[ ‼ G , ⁇ H l ]⨟ m₂ | inj₁ (it ¬G≡H) = ⊥ l


ε             ⨟m m₂ = m₂
(c₁ ⇒̂ d₁) ¬p₁ ⨟m ε = (c₁ ⇒̂ d₁) ¬p₁
(c₁ ⊗̂ d₁) ¬p₁ ⨟m ε = (c₁ ⊗̂ d₁) ¬p₁
(c₁ ⇒̂ d₁) ¬p₁ ⨟m (c₂ ⇒̂ d₂) ¬p₂ = mk⇒ (c₂ ⨟ c₁) (d₁ ⨟ d₂)
(c₁ ⊗̂ d₁) ¬p₁ ⨟m (c₂ ⊗̂ d₂) ¬p₂ = mk⊗ (c₁ ⨟ c₂) (d₁ ⨟ d₂)




-- Compilation

⇑ : Label×Polarity → ∀ T → Cast T *
⇓ : Label×Polarity → ∀ T → Cast * T


⇑ l *     = *
⇑ l (` B)     = ↷ ε (` ε) (‼ `B)
⇑ l (` S ⇒ T) = ↷ ε (` (mk⇒ (⇓ (negate-label l) S) (⇑ l T))) (‼ `⇒)
⇑ l (` S ⊗ T) = ↷ ε (` (mk⊗ (⇑ l S) (⇑ l T))) (‼ `⊗)


⇓ l *     = *
⇓ l (` B)     = ↷ (⁇ `B l) (` ε)               ε
⇓ l (` S ⇒ T) = ↷ (⁇ `⇒ l) (` (mk⇒ (⇑ (negate-label l) S) (⇓ l T))) ε
⇓ l (` S ⊗ T) = ↷ (⁇ `⊗ l) (` (mk⊗ (⇓ l S) (⇓ l T))) ε


⌈_⌉ : ∀ {T₁ T₂} → SrcCast T₁ T₂ → Cast T₁ T₂
⌈ *   ⟹[ l ] *   ⌉ = *
⌈ *   ⟹[ l ] ` Q ⌉ = ⇓ l (` Q)
⌈ ` P ⟹[ l ] *   ⌉ = ⇑ l (` P)
⌈ ` P ⟹[ l ] ` Q ⌉ with (` P) ⌣? (` Q)
⌈ ` P ⟹[ l ] ` Q ⌉             | no P⌣̸Q = ↷ ε (⊥ l) ε
⌈ ` B       ⟹[ l ] ` B       ⌉ | yes ⌣B = ↷ ε (` ε) ε
⌈ ` S₁ ⇒ T₁ ⟹[ l ] ` S₂ ⇒ T₂ ⌉ | yes ⌣⇒
  = ↷ ε (` (mk⇒ ⌈ S₂ ⟹[ negate-label l ] S₁ ⌉ ⌈ T₁ ⟹[ l ] T₂ ⌉)) ε
⌈ ` S₁ ⊗ T₁ ⟹[ l ] ` S₂ ⊗ T₂ ⌉ | yes ⌣⊗
  = ↷ ε (` (mk⊗ ⌈ S₁ ⟹[ l ] S₂ ⌉ ⌈ T₁ ⟹[ l ] T₂ ⌉)) ε




-- Identity

id : ∀ T → Cast T T
id * = *
id (` P) = ↷ ε (` ε) ε


id-identity : ∀ T → Identity (id T)
id-identity *     = id-*
id-identity (` P) = id-P


identity-id : ∀ {T} → {c : Cast T T} → Identity c → c ≡ id T
identity-id id-* = refl
identity-id id-P = refl





open import R.BlameStrategies Label using (BlameStrategy; LazyUDBS)
open BlameStrategy LazyUDBS using (Injectable)

open import Error
  using (Error; return; raise; _>>=_; _>=>_
        ;>>=-return; >>=-assoc; >=>-assoc; >=>->>=
        ;>>=-extensionality)
open import S.Values Label Injectable Cast

CastResult : Type → Set
CastResult T = Error Label×Polarity (Value T)

typeop→ground : (op : TypeOp) → Ground (op · replicate *)
typeop→ground `B = `B
typeop→ground `⊗ = `⊗
typeop→ground `⇒ = `⇒

ground→typeop : ∀ {P} → Ground P → ∃[ o ](P ≡ o · replicate *)
ground→typeop `B = `B , refl
ground→typeop `⊗ = `⊗ , refl
ground→typeop `⇒ = `⇒ , refl


⟦_⟧t : ∀ {G Ts T}
  → Tail G Ts T
  → Value (` G · Ts)
  ---
  → CastResult T
⟦ ‼ G ⟧t v = return (dyn (typeop→ground G) v)
⟦ ε   ⟧t v = return v

proxy : ∀ {G Ts₁ Ts₂}
  → Value (` G · Ts₁)
  → PreBody G Ts₁ Ts₂
  ---
  → Value (` G · Ts₂)
proxy v ε = v
proxy (lam⟨ c₁ ⇒ d₁ ⟩ e E)    ((c₂ ⇒̂ d₂) ¬p) = lam⟨ c₂ ⨟ c₁ ⇒ d₁ ⨟ d₂ ⟩ e E
proxy (cons⟨ c₁ ⊗ d₁ ⟩ v₁ v₂) ((c₂ ⊗̂ d₂) ¬p) = cons⟨ c₁ ⨟ c₂ ⊗ d₁ ⨟ d₂ ⟩ v₁ v₂

⟦_⟧m : ∀ {G Ss H Ts}
  → Body G Ss H Ts
  → Value (` G · Ss)
  → CastResult (` H · Ts)
⟦ ⊥ l ⟧m v = raise l
⟦ ` m ⟧m v = return (proxy v m)

⟦_⟧h : ∀ {T G Ts}
  → Head G T Ts
  → Value T
  → CastResult (` G · Ts)
⟦ ε     ⟧h v = return v
⟦ ⁇ H l ⟧h (dyn gP v)
  with ground→typeop gP
... | G , refl
  with G ≟op H
... | yes refl = return v
... | no ¬P≡Q  = raise l

⟦_⟧ : ∀ {T₁ T₂}
  → Cast T₁ T₂
  → Value T₁
  ---
  → CastResult T₂
⟦ *       ⟧ v = return v
⟦ ↷ h m t ⟧ v = ⟦ h ⟧h v >>= ⟦ m ⟧m >>= ⟦ t ⟧t

-- Properties

-- Properties.Identity

identityˡ : ∀ {T₁ T₂} → (c : Cast T₁ T₂) → id T₁ ⨟ c ≡ c
identityʳ : ∀ {T₁ T₂} → (c : Cast T₁ T₂) → c ⨟ id T₂ ≡ c

identityˡ * = refl
identityˡ (↷ (⁇ P l) m t₂) = refl
identityˡ (↷ ε (⊥ l) t₂) = refl
identityˡ (↷ ε (` ε) t₂) = refl
identityˡ (↷ ε (` (c₁ ⇒̂ c₂) ¬p) t₂) rewrite identityʳ c₁ | identityˡ c₂ = refl
identityˡ (↷ ε (` (c₁ ⊗̂ c₂) ¬p) t₂) rewrite identityˡ c₁ | identityˡ c₂ = refl
                                                                       
identityʳ * = refl
identityʳ (↷ t₁ m (‼ P)) = refl
identityʳ (↷ t₁ (⊥ l) ε) = refl
identityʳ (↷ t₁ (` ε) ε) = refl
identityʳ (↷ t₁ (` (c₁ ⇒̂ c₂) ¬p) ε) rewrite identityˡ c₁ | identityʳ c₂ = refl
identityʳ (↷ t₁ (` (c₁ ⊗̂ c₂) ¬p) ε) rewrite identityʳ c₁ | identityʳ c₂ = refl

identity-mʳ : ∀ {G Ss Ts} → (m : PreBody G Ss Ts)
  → m ⨟m ε ≡ m
identity-mʳ ε = refl
identity-mʳ ((c ⇒̂ d) ¬p) = refl
identity-mʳ ((c ⊗̂ d) ¬p) = refl

-- Properties.Associativity

mk⇒-distr-r : ∀ {S₁ S₂ S₃ T₁ T₂ T₃}
  → (c₁ : Cast S₂ S₁)
  → (d₁ : Cast T₁ T₂)
  → (c₂ : Cast S₃ S₂)
  → (d₂ : Cast T₂ T₃)
  → .(¬p : ¬ (Identity c₂ × Identity d₂))
  → (mk⇒ c₁ d₁) ⨟m ((c₂ ⇒̂ d₂) ¬p)
    ≡
    (mk⇒ (c₂ ⨟ c₁) (d₁ ⨟ d₂))
mk⇒-distr-r c₁ d₁ c₂ d₂ ¬p with identity? c₁
mk⇒-distr-r c₁ d₁ c₂ d₂ ¬p | yes id-c₁ with identity? d₁
mk⇒-distr-r c₁ d₁ c₂ d₂ ¬p | yes id-c₁ | yes id-d₁
  with identity-implies-type-equality id-c₁
... | refl
  with identity-implies-type-equality id-d₁
... | refl
  with identity-id id-c₁
... | refl
  with identity-id id-d₁
... | refl
  rewrite
    identityʳ c₂
  | identityˡ d₂
  = sym (mk⇒-noop c₂ d₂ ¬p)
mk⇒-distr-r c₁ d₁ c₂ d₂ ¬p | yes id-c₁ | no ¬id-d₁ = refl
mk⇒-distr-r c₁ d₁ c₂ d₂ ¬p | no ¬id-c₂ = refl

mk⊗-distr-r : ∀ {S₁ S₂ S₃ T₁ T₂ T₃}
  → (c₁ : Cast S₁ S₂)
  → (d₁ : Cast T₁ T₂)
  → (c₂ : Cast S₂ S₃)
  → (d₂ : Cast T₂ T₃)
  → .(¬p : ¬ (Identity c₂ × Identity d₂))
  → (mk⊗ c₁ d₁) ⨟m ((c₂ ⊗̂ d₂) ¬p)
    ≡
    (mk⊗ (c₁ ⨟ c₂) (d₁ ⨟ d₂))
mk⊗-distr-r c₁ d₁ c₂ d₂ ¬p with identity? c₁
mk⊗-distr-r c₁ d₁ c₂ d₂ ¬p | yes id-c₁ with identity? d₁
mk⊗-distr-r c₁ d₁ c₂ d₂ ¬p | yes id-c₁ | yes id-d₁
  with identity-implies-type-equality id-c₁
... | refl
  with identity-implies-type-equality id-d₁
... | refl
  with identity-id id-c₁
... | refl
  with identity-id id-d₁
... | refl
  rewrite
    identityˡ c₂
  | identityˡ d₂
  = sym (mk⊗-noop c₂ d₂ ¬p)
mk⊗-distr-r c₁ d₁ c₂ d₂ ¬p | yes id-c₁ | no ¬id-d₁ = refl
mk⊗-distr-r c₁ d₁ c₂ d₂ ¬p | no ¬id-c₂ = refl

mk⇒-distr-l : ∀ {S₁ S₂ S₃ T₁ T₂ T₃}
  → (c₁ : Cast S₂ S₁)
  → (d₁ : Cast T₁ T₂)
  → .(¬p : ¬ (Identity c₁ × Identity d₁))
  → (c₂ : Cast S₃ S₂)
  → (d₂ : Cast T₂ T₃)
  → ((c₁ ⇒̂ d₁) ¬p) ⨟m (mk⇒ c₂ d₂)
    ≡
    (mk⇒ (c₂ ⨟ c₁) (d₁ ⨟ d₂))
mk⇒-distr-l c₁ d₁ ¬p c₂ d₂ with identity? c₂
mk⇒-distr-l c₁ d₁ ¬p c₂ d₂ | yes id-c₂ with identity? d₂
mk⇒-distr-l c₁ d₁ ¬p c₂ d₂ | yes id-c₂ | yes id-d₂
  with identity-implies-type-equality id-c₂
... | refl
  with identity-implies-type-equality id-d₂
... | refl
  with identity-id id-c₂
... | refl
  with identity-id id-d₂
... | refl
  rewrite
    identityˡ c₁
  | identityʳ d₁
  = sym (mk⇒-noop c₁ d₁ ¬p)
mk⇒-distr-l c₁ d₁ ¬p c₂ d₂ | yes id-c₂ | no ¬id-d₂ = refl
mk⇒-distr-l c₁ d₁ ¬p c₂ d₂ | no ¬id-c₂ = refl

mk⊗-distr-l : ∀ {S₁ S₂ S₃ T₁ T₂ T₃}
  → (c₁ : Cast S₁ S₂)
  → (d₁ : Cast T₁ T₂)
  → .(¬p : ¬ (Identity c₁ × Identity d₁))
  → (c₂ : Cast S₂ S₃)
  → (d₂ : Cast T₂ T₃)
  → ((c₁ ⊗̂ d₁) ¬p) ⨟m (mk⊗ c₂ d₂)
    ≡
    (mk⊗ (c₁ ⨟ c₂) (d₁ ⨟ d₂))
mk⊗-distr-l c₁ d₁ ¬p c₂ d₂ with identity? c₂
mk⊗-distr-l c₁ d₁ ¬p c₂ d₂ | yes id-c₂ with identity? d₂
mk⊗-distr-l c₁ d₁ ¬p c₂ d₂ | yes id-c₂ | yes id-d₂
  with identity-implies-type-equality id-c₂
... | refl
  with identity-implies-type-equality id-d₂
... | refl
  with identity-id id-c₂
... | refl
  with identity-id id-d₂
... | refl
  rewrite
    identityʳ c₁
  | identityʳ d₁
  = sym (mk⊗-noop c₁ d₁ ¬p)
mk⊗-distr-l c₁ d₁ ¬p c₂ d₂ | yes id-c₂ | no ¬id-d₂ = refl
mk⊗-distr-l c₁ d₁ ¬p c₂ d₂ | no ¬id-c₂ = refl

assoc : ∀ {T₁ T₂ T₃ T₄} → (c₁ : Cast T₁ T₂) → (c₂ : Cast T₂ T₃) → (c₃ : Cast T₃ T₄)
  → (c₁ ⨟ c₂) ⨟ c₃ ≡ c₁ ⨟ (c₂ ⨟ c₃)
assoc-m : ∀ {G Ts₁ Ts₂ Ts₃ Ts₄}
  → (m₁ : PreBody G Ts₁ Ts₂)
  → (m₂ : PreBody G Ts₂ Ts₃)
  → (m₃ : PreBody G Ts₃ Ts₄)
  → (m₁ ⨟m m₂) ⨟m m₃ ≡ m₁ ⨟m (m₂ ⨟m m₃)
assoc-seq-m : ∀ {G₁ Ts₁ G₂ Ts₂ T₁ G₃ Ts₃ G₄ Ts₄ T₂ G₅ Ts₅ G₆ Ts₆}
  → (m₁ : Body G₁ Ts₁ G₂ Ts₂)
  → (t₁ : Tail G₂ Ts₂ T₁)
  → (h₂ : Head G₃ T₁ Ts₃)
  → (m₂ : Body G₃ Ts₃ G₄ Ts₄)
  → (t₂ : Tail G₄ Ts₄ T₂)
  → (h₃ : Head G₅ T₂ Ts₅)
  → (m₃ : Body G₅ Ts₅ G₆ Ts₆)
  → ((m₁ ⨟[ t₁ , h₂ ]⨟ m₂) ⨟[ t₂ , h₃ ]⨟ m₃)
    ≡
    (m₁ ⨟[ t₁ , h₂ ]⨟ (m₂ ⨟[ t₂ , h₃ ]⨟ m₃))

assoc * c₂ c₃ rewrite identityˡ c₂ | identityˡ (c₂ ⨟ c₃) = refl
assoc (↷ h₁ m₁ t₁) * c₃ rewrite identityˡ c₃ = refl
assoc (↷ h₁ m₁ t₁) (↷ h₂ m₂ t₂) * = refl
assoc (↷ h₁ m₁ t₁) (↷ h₂ m₂ t₂) (↷ h₃ m₃ t₃)
  = cong (λ □ → ↷ h₁ □ t₃) (assoc-seq-m m₁ t₁ h₂ m₂ t₂ h₃ m₃)

assoc-m ε m₂ m₃ = refl
assoc-m ((c₁ ⇒̂ d₁) ¬p₁) ε m₃ = refl
assoc-m ((c₁ ⇒̂ d₁) ¬p₁) ((c₂ ⇒̂ d₂) ¬p₂) ε = identity-mʳ _
assoc-m ((c₁ ⇒̂ d₁) ¬p₁) ((c₂ ⇒̂ d₂) ¬p₂) ((c₃ ⇒̂ d₃) ¬p₃)
  rewrite
    mk⇒-distr-r (c₂ ⨟ c₁) (d₁ ⨟ d₂) c₃ d₃ ¬p₃
  | mk⇒-distr-l c₁ d₁ ¬p₁ (c₃ ⨟ c₂) (d₂ ⨟ d₃)
  | assoc c₃ c₂ c₁
  | assoc d₁ d₂ d₃
  = refl
assoc-m ((c₁ ⊗̂ d₁) ¬p₁) ε m₃ = refl
assoc-m ((c₁ ⊗̂ d₁) ¬p₁) ((c₂ ⊗̂ d₂) ¬p₂) ε = identity-mʳ _
assoc-m ((c₁ ⊗̂ d₁) ¬p₁) ((c₂ ⊗̂ d₂) ¬p₂) ((c₃ ⊗̂ d₃) ¬p₃)
  rewrite
    mk⊗-distr-r (c₁ ⨟ c₂) (d₁ ⨟ d₂) c₃ d₃ ¬p₃
  | mk⊗-distr-l c₁ d₁ ¬p₁ (c₂ ⨟ c₃) (d₂ ⨟ d₃)
  | assoc c₁ c₂ c₃
  | assoc d₁ d₂ d₃
  = refl

assoc-seq-m (⊥ l₁) t₁ h₂ m₂ t₂ h₃ m₃ = refl
assoc-seq-m (` m₁) t₁ h₂ m₂ t₂ h₃ m₃ with incompatible? t₁ h₂
assoc-seq-m (` m₁) t₁ h₂ (⊥ l₂) t₂ h₃ m₃ | inj₂ refl = refl
assoc-seq-m (` m₁) t₁ h₂ (` m₂) t₂ h₃ m₃ | inj₂ refl with incompatible? t₂ h₃
assoc-seq-m (` m₁) t₁ h₂ (` m₂) t₂ h₃ (⊥ l₃) | inj₂ refl | inj₂ refl = refl
assoc-seq-m (` m₁) t₁ h₂ (` m₂) t₂ h₃ (` m₃) | inj₂ refl | inj₂ refl
  = cong `_ (assoc-m m₁ m₂ m₃)
assoc-seq-m (` m₁) t₁ h₂ (` m₂) (‼ G) (⁇ H l) m₃ | inj₂ refl | inj₁ (it ¬G≡H) = refl
assoc-seq-m (` m₁) (‼ G) (⁇ H l) m₂ t₂ h₃ m₃ | inj₁ (it ¬G≡H) = refl

lem-id : ∀ T
  → (v : Value T)  
  -----------------------------
  → ⟦ id T ⟧ v ≡ return v
lem-id *     v = refl
lem-id (` P) v = refl

lem-proxy-mk⇒ : ∀ {S₁ S₂ S₃ T₁ T₂ T₃ Γ}
  → (e  : (Γ ,' S₁) ⊢ T₁)
  → (E  : Env Γ)
  → (c₁ : Cast S₂ S₁)
  → (d₁ : Cast T₁ T₂)
  → (c₂ : Cast S₃ S₂)
  → (d₂ : Cast T₂ T₃)
  → proxy (lam⟨ c₁ ⇒ d₁ ⟩ e E) (mk⇒ c₂ d₂)
    ≡
    lam⟨ (c₂ ⨟ c₁) ⇒ (d₁ ⨟ d₂) ⟩ e E
lem-proxy-mk⇒ e E c₁ d₁ c₂ d₂ with identity? c₂
lem-proxy-mk⇒ e E c₁ d₁ c₂ d₂ | yes id-c₂ with identity? d₂
lem-proxy-mk⇒ e E c₁ d₁ c₂ d₂ | yes id-c₂ | yes id-d₂
  with identity-implies-type-equality id-c₂
... | refl
  with identity-implies-type-equality id-d₂
... | refl
  with identity-id id-c₂
... | refl
  with identity-id id-d₂
... | refl
  rewrite
    identityˡ c₁
  | identityʳ d₁
  = refl
lem-proxy-mk⇒ e E c₁ d₁ c₂ d₂ | yes id-c₂ | no ¬id-d₂ = refl
lem-proxy-mk⇒ e E c₁ d₁ c₂ d₂ | no ¬id-c₂ = refl

lem-proxy-mk⊗ : ∀ {S₁ S₂ S₃ T₁ T₂ T₃}
  → (v : Value S₁)
  → (u : Value T₁)
  → (c₁ : Cast S₁ S₂)
  → (d₁ : Cast T₁ T₂)
  → (c₂ : Cast S₂ S₃)
  → (d₂ : Cast T₂ T₃)
  → proxy (cons⟨ c₁ ⊗ d₁ ⟩ v u) (mk⊗ c₂ d₂)
    ≡
    cons⟨ (c₁ ⨟ c₂) ⊗ (d₁ ⨟ d₂) ⟩ v u
lem-proxy-mk⊗ e E c₁ d₁ c₂ d₂ with identity? c₂
lem-proxy-mk⊗ e E c₁ d₁ c₂ d₂ | yes id-c₂ with identity? d₂
lem-proxy-mk⊗ e E c₁ d₁ c₂ d₂ | yes id-c₂ | yes id-d₂
  with identity-implies-type-equality id-c₂
... | refl
  with identity-implies-type-equality id-d₂
... | refl
  with identity-id id-c₂
... | refl
  with identity-id id-d₂
... | refl
  rewrite
    identityʳ c₁
  | identityʳ d₁
  = refl
lem-proxy-mk⊗ e E c₁ d₁ c₂ d₂ | yes id-c₂ | no ¬id-d₂ = refl
lem-proxy-mk⊗ e E c₁ d₁ c₂ d₂ | no ¬id-c₂ = refl

lem-proxy : ∀ {G Ts₁ Ts₂ Ts₃}
  → (v : Value (` G · Ts₁))
  → (m₁ : PreBody G Ts₁ Ts₂)
  → (m₂ : PreBody G Ts₂ Ts₃)
  → proxy v (m₁ ⨟m m₂) ≡ proxy (proxy v m₁) m₂
lem-proxy v ε m₂ = refl
lem-proxy (lam⟨ c₁ ⇒ d₁ ⟩ e E) ((c₂ ⇒̂ d₂) _) ε = refl
lem-proxy (lam⟨ c₁ ⇒ d₁ ⟩ e E) ((c₂ ⇒̂ d₂) _) ((c₃ ⇒̂ d₃) _)
  rewrite
    lem-proxy-mk⇒ e E c₁ d₁ (c₃ ⨟ c₂) (d₂ ⨟ d₃)
  | assoc c₃ c₂ c₁
  | assoc d₁ d₂ d₃
  = refl
lem-proxy (cons⟨ c₁ ⊗ d₁ ⟩ v u) ((c₂ ⊗̂ d₂) _) ε = refl
lem-proxy (cons⟨ c₁ ⊗ d₁ ⟩ v u) ((c₂ ⊗̂ d₂) _) ((c₃ ⊗̂ d₃) _)
  rewrite
    lem-proxy-mk⊗ v u c₁ d₁ (c₂ ⨟ c₃) (d₂ ⨟ d₃)
  | assoc c₁ c₂ c₃
  | assoc d₁ d₂ d₃
  = refl
lem-seq-m : ∀ {G₁ Ts₁ G₂ Ts₂ T G₃ Ts₃ G₄ Ts₄}
  → (m₁ : Body G₁ Ts₁ G₂ Ts₂)
  → (t₁ : Tail G₂ Ts₂ T)
  → (h₂ : Head G₃ T Ts₃)
  → (m₂ : Body G₃ Ts₃ G₄ Ts₄)
  → (∀ v →
       ⟦ m₁ ⨟[ t₁ , h₂ ]⨟ m₂ ⟧m v
         ≡
       (⟦ m₁ ⟧m >=> ⟦ t₁ ⟧t >=> ⟦ h₂ ⟧h >=> ⟦ m₂ ⟧m) v)
lem-seq-m (⊥ l₁) t₁ h₂ m₂ v = refl
lem-seq-m (` m₁) (‼ G) (⁇ H l) m₂ v
  with ground→typeop (typeop→ground G)
... | G , refl
  with G ≟op H
lem-seq-m (` m₁) (‼ G) (⁇ .G l) (⊥ l₂) v | G , refl | yes refl = refl
lem-seq-m (` m₁) (‼ G) (⁇ .G l) (` m₂) v | G , refl | yes refl
  = cong return (lem-proxy v m₁ m₂)
... | no ¬G≡H  = refl
lem-seq-m (` m₁) ε ε (⊥ l₂) v = refl
lem-seq-m (` m₁) ε ε (` m₂) v = cong return (lem-proxy v m₁ m₂)

lem-seq : ∀ {T₁ T₂ T₃}
  → (c₁ : Cast T₁ T₂)
  → (c₂ : Cast T₂ T₃)
  → ∀ v
  --------------------
  → ⟦ c₁ ⨟ c₂ ⟧ v ≡ ⟦ c₁ ⟧ v >>= ⟦ c₂ ⟧
lem-seq * c₂ v = refl
lem-seq (↷ h₁ m₁ t₁) * v = sym (>>=-return _)
lem-seq (↷ h₁ m₁ t₁) (↷ h₂ m₂ t₂) v with ⟦ h₁ ⟧h v
lem-seq (↷ h₁ m₁ t₁) (↷ h₂ m₂ t₂) v | raise l   = refl
lem-seq (↷ h₁ m₁ t₁) (↷ h₂ m₂ t₂) v | return v'
  rewrite
    lem-seq-m m₁ t₁ h₂ m₂ v'
  with ⟦ m₁ ⟧m v' >>= ⟦ t₁ ⟧t
... | raise l    = refl
... | return v'' = refl

H : CastADT Injectable
H = record
    { Cast = Cast
    ; id  = id
    ; ⌈_⌉ = ⌈_⌉
    ; _⨟_ = _⨟_
    ; ⟦_⟧ = ⟦_⟧
    ; lem-id = lem-id
    ; lem-seq = lem-seq
    }




open import Bisimulation.LazyUDCastADT Label


eq-¬⌣ : ∀ {T₁ T₂}
  → (v : Value T₁)
  → (l : Label×Polarity)
  → ¬ (T₁ ⌣ T₂)
  ---
  → ⟦ ⌈ T₁ ⟹[ l ] T₂ ⌉ ⟧ v
      ≡
    raise l
eq-¬⌣ {*} {*} v l ¬p = ⊥-elim (¬p *⌣*)
eq-¬⌣ {*} {` P} v l ¬p = ⊥-elim (¬p (*⌣P P))
eq-¬⌣ {` P} {*} v l ¬p = ⊥-elim (¬p (P⌣* P))
eq-¬⌣ {` P} {` Q} v l ¬p with (` P) ⌣? (` Q)
eq-¬⌣ {` P} {` Q} v l ¬p | yes p' = ⊥-elim (¬p p')
eq-¬⌣ {` P} {` Q} v l ¬p | no ¬p' = refl


lem-rewrite-inj : (l : Label×Polarity)(T : Type)
  → (⇑ l T) ≡ ⌈ T ⟹[ l ] * ⌉
lem-rewrite-inj l * = refl
lem-rewrite-inj l (` P) = refl


lem-rewrite-proj : (l : Label×Polarity)(T : Type)
  → (⇓ l T) ≡ ⌈ * ⟹[ l ] T ⌉
lem-rewrite-proj l * = refl
lem-rewrite-proj l (` P) = refl


lem-expand-inj : (l : Label×Polarity)(P : PreType)
  → (⇑ l (` P)) ≡ (⌈ (` P) ⟹[ l ] ` ground P ⌉ ⨟ ⌈ ` ground P ⟹[ l ] * ⌉)
lem-expand-inj l B = refl
lem-expand-inj l (S ⇒ T)
  rewrite
    lem-rewrite-proj (negate-label l) S
  | lem-rewrite-inj l T
  | identity-mʳ (mk⇒ ⌈ * ⟹[ negate-label l ] S ⌉ ⌈ T ⟹[ l ] * ⌉)
  = refl
lem-expand-inj l (S ⊗ T)
  rewrite
    lem-rewrite-inj l S
  | lem-rewrite-inj l T
  | identity-mʳ (mk⊗ ⌈ S ⟹[ l ] * ⌉ ⌈ T ⟹[ l ] * ⌉)
  = refl


lem-expand-proj : (l : Label×Polarity)(P : PreType)
  → (⇓ l (` P)) ≡ (⌈ * ⟹[ l ] ` ground P ⌉ ⨟ ⌈ ` ground P ⟹[ l ] ` P ⌉)
lem-expand-proj l B = refl
lem-expand-proj l (S ⇒ T)
  rewrite lem-rewrite-inj (negate-label l) S | lem-rewrite-proj l T
    | identityʳ ⌈ S ⟹[ negate-label l ] * ⌉
  = refl
lem-expand-proj l (S ⊗ T)
  rewrite lem-rewrite-proj l S | lem-rewrite-proj l T
  = refl


eq-P* : ∀ {P}
  → (v : Value (` P))
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
  → (v : Value (` P))
  → (l : Label×Polarity)
  → (gP : Ground P)
  → ⟦ ⌈ ` P ⟹[ l ] * ⌉ ⟧ v
      ≡
    return (dyn gP v)
eq-I* {.B} v l `B = refl
eq-I* {.(* ⇒ *)} (lam⟨ c₁ ⇒ c₂ ⟩ e E) l `⇒
  rewrite identityʳ c₂
  = refl
eq-I* {.(* ⊗ *)} (cons⟨ c₁ ⊗ c₂ ⟩ v v₁) l `⊗
  rewrite identityʳ c₁ | identityʳ c₂
  = refl


eq-*P : ∀ {P}
  → (v : Value *)
  → (l : Label×Polarity)
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
  → (l : Label×Polarity)
  → (gP : Ground P)
  → ⟦ ⌈ * ⟹[ l ] (` P) ⌉ ⟧ (dyn gP v)
      ≡
    return v
eq-*I-succ v l `B = refl
eq-*I-succ (lam⟨ c₁ ⇒ c₂ ⟩ e E) l `⇒
  rewrite identityʳ c₂
  = refl
eq-*I-succ (cons⟨ c₁ ⊗ c₂ ⟩ v v₁) l `⊗
  rewrite identityʳ c₁ | identityʳ c₂
  = refl
    

eq-*I-fail : {P Q : PreType}
  → (v : Value (` P))  
  → (l : Label×Polarity)
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

H-LazyUD : IsLazyUD H
H-LazyUD = record
             { eq-¬⌣ = eq-¬⌣
             ; eq-** = λ l v → refl
             ; eq-P* = eq-P*
             ; eq-I* = eq-I*
             ; eq-*P = eq-*P
             ; eq-*I-succ = eq-*I-succ
             ; eq-*I-fail = eq-*I-fail
             ; eq-B = λ l b → refl
             ; eq-⇒ = λ T₂₁ T₂₂ T₁₁ T₁₂ l c d e E
                    → cong return
                           (lem-proxy-mk⇒ e E c d
                             ⌈ T₂₁ ⟹[ negate-label l ] T₁₁ ⌉ ⌈ T₁₂ ⟹[ l ] T₂₂ ⌉)
             ; eq-⊗ = λ T₂₁ T₂₂ T₁₁ T₁₂ l c d v u
                    → cong return
                           (lem-proxy-mk⊗ v u c d
                             ⌈ T₁₁ ⟹[ l ] T₂₁ ⌉ ⌈ T₁₂ ⟹[ l ] T₂₂ ⌉)
             }
