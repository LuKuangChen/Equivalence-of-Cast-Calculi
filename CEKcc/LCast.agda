module CEKcc.LCast
  (Label : Set)
  where

open import Types
open import CEKcc.CastRep Label

open import Relation.Nullary using (Dec; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)


data Step : Type → Type → Set where
  step : (l : Label) → (T1 T2 : Type) → Step T1 T2

data Cast : Type → Type → Set where
  [] : ∀ {T}
    ---
    → Cast T T
  _∷_ : ∀ {T1 T2 T3}
    → (x  : Step T1 T2)
    → (xs : Cast T2 T3)
    ---
    → Cast T1 T3

mk-id : ∀ T → Cast T T
mk-id T = []

mk-cast : Label → ∀ T1 T2 → Cast T1 T2
mk-cast l T1 T2 = step l T1 T2 ∷ []

mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
mk-seq [] ys = ys
mk-seq (x ∷ xs) ys = x ∷ (mk-seq xs ys)

open import Terms Label
open import CEKcc.Values Label Cast
open import Variables

do-cast : Label → (T1 T2 : Type) → Val T1 → CastResult T2
do-cast l T1 T2 v with T1 ⌣? T2
do-cast l .⋆ .⋆ v | yes ⋆⌣⋆ = succ v
do-cast l .⋆ .(` P) (inj P₁ v) | yes (⋆⌣P P) = do-cast l (` P₁) (` P) v
do-cast l .(` P) .⋆ v | yes (P⌣⋆ P) = succ (inj P v)
do-cast l .(` U) .(` U) v | yes ⌣U = succ v
do-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22)) (fun env c₁ b c₂) | yes ⌣⇒ =
  succ (fun env (mk-seq (mk-cast l T21 T11) c₁) b (mk-seq c₂ (mk-cast l T12 T22)))
do-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22)) (cons v₁ c₁ v₂ c₂) | yes ⌣⊗ =
  succ (cons v₁ (mk-seq c₁ (mk-cast l T11 T21)) v₂ ((mk-seq c₂ (mk-cast l T12 T22))))
do-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22)) (inl v c) | yes ⌣⊕ =
  succ (inl v (mk-seq c (mk-cast l T11 T21)))
do-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22)) (inr v c) | yes ⌣⊕ =
  succ (inr v (mk-seq c (mk-cast l T12 T22)))
do-cast l T1 T2 v | no ¬p = fail l

apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val T1 → CastResult T2
apply-cast [] v = succ v
apply-cast (step l T1 T2 ∷ xs) v
  = do-cast l T1 T2 v >>= λ u →
    apply-cast xs u


open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

lem-id : ∀ T
  → (v : Val T)  
  -----------------------------
  → apply-cast (mk-id T) v ≡ succ v
lem-id T v = refl

lem-seq : ∀ {T1 T2 T3}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → (v : Val T1)
  --------------------
  → apply-cast (mk-seq c1 c2) v ≡ apply-cast c1 v >>= λ u → apply-cast c2 u
lem-seq [] ys v = refl
lem-seq (step l T1 T2 ∷ xs) ys v with do-cast l T1 T2 v
lem-seq (step l T1 T2 ∷ xs) ys v | succ v₁ = lem-seq xs ys v₁
lem-seq (step l T1 T2 ∷ xs) ys v | fail l₁ = refl

lem-cast-¬⌣ : ∀ {T1 T2}
  → (l : Label)
  → ¬ (T1 ⌣ T2)
  → (v : Val T1)
  → apply-cast (mk-cast l T1 T2) v ≡ fail l
lem-cast-¬⌣ {T1} {T2} l p v with T1 ⌣? T2
lem-cast-¬⌣ {T1} {T2} l p v | yes p₁ = ⊥-elim (p p₁)
lem-cast-¬⌣ {T1} {T2} l p v | no ¬p = refl

lem-cast-id⋆ : ∀ l
  → (v : Val ⋆)
  → apply-cast (mk-cast l ⋆ ⋆) v ≡ succ v
lem-cast-id⋆ l v = refl

lem-cast-inj : ∀ {P}
  → (l : Label)
  → (v : Val (` P))  
  → apply-cast (mk-cast l (` P) ⋆) v ≡ succ (inj P v)
lem-cast-inj {P} l v = refl

lem-cast-proj : ∀ l P P₁ v
  → apply-cast (mk-cast l ⋆ (` P)) (inj P₁ v) ≡ apply-cast (mk-cast l (` P₁) (` P)) v
lem-cast-proj l P P₁ v = refl

lem-cast-U : ∀ l
  → apply-cast (mk-cast l (` U) (` U)) sole ≡ succ sole
lem-cast-U l = refl

lem-cast-⇒ : ∀ T11 T12 T21 T22
  → ∀ {S T}
  → (l : Label)
  → {Γ : Context}
  → (E : Env Γ)
  → (c₁ : Cast T11 S)
  → (b : (Γ , S) ⊢ T)
  → (c₂ : Cast T T12)
  → apply-cast (mk-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22))) (fun E c₁ b c₂) ≡
    succ (fun E (mk-seq (mk-cast l T21 T11) c₁) b (mk-seq c₂ (mk-cast l T12 T22)))
lem-cast-⇒ T11 T12 T21 T22 l E c₁ b c₂ = refl

lem-cast-⊗ : ∀ T01 T02 T11 T12 T21 T22
  → (l : Label)
  → (v₁ : Val T01)
  → (v₂ : Val T02)
  → (c₁ : Cast T01 T11)
  → (c₂ : Cast T02 T12)
  → apply-cast (mk-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22))) (cons v₁ c₁ v₂ c₂) ≡
    succ (cons v₁ (mk-seq c₁ (mk-cast l T11 T21)) v₂ (mk-seq c₂ (mk-cast l T12 T22)))
lem-cast-⊗ T01 T02 T11 T12 T21 T22 l v₁ v₂ c₁ c₂ = refl
    
lem-cast-⊕-l : ∀ T T11 T12 T21 T22
  → (l : Label)
  → (v : Val T)
  → (c : Cast T T11)
  → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inl v c) ≡
    succ (inl v (mk-seq c (mk-cast l T11 T21)))
lem-cast-⊕-l T T11 T12 T21 T22 l v c = refl

lem-cast-⊕-r : ∀ T T11 T12 T21 T22
  → (l : Label)
  → (v : Val T)
  → (c : Cast T T12)
  → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inr v c) ≡
    succ (inr v (mk-seq c (mk-cast l T12 T22)))
lem-cast-⊕-r T T11 T12 T21 T22 l v c = refl

cast-rep : CastRep
cast-rep
  = record
    { Cast = Cast
    ; mk-cast = mk-cast
    ; mk-seq = mk-seq
    ; mk-id = mk-id
    ; apply-cast = apply-cast
    }
cast-rep-surely-lazyD : SurelyLazyD cast-rep
cast-rep-surely-lazyD
  = record
    { lem-id = lem-id
    ; lem-seq = lem-seq
    ; lem-cast-¬⌣ = lem-cast-¬⌣
    ; lem-cast-id⋆ = lem-cast-id⋆
    ; lem-cast-inj = lem-cast-inj
    ; lem-cast-proj = lem-cast-proj
    ; lem-cast-U = lem-cast-U
    ; lem-cast-⇒ = lem-cast-⇒
    ; lem-cast-⊗ = lem-cast-⊗
    ; lem-cast-⊕-l = lem-cast-⊕-l
    ; lem-cast-⊕-r = lem-cast-⊕-r
    }


-- additional lemmas for bisimulation between CEKcc and CEKc

mk-seq-assoc : ∀ {T1 T2 T3 T4}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → (c3 : Cast T3 T4)
  ---
  → mk-seq (mk-seq c1 c2) c3 ≡ mk-seq c1 (mk-seq c2 c3)
mk-seq-assoc [] c2 c3 = refl
mk-seq-assoc (x ∷ c1) c2 c3 rewrite mk-seq-assoc c1 c2 c3 = refl
 
mk-seq-mk-id-l : ∀ {T1 T2}
  → (c : Cast T1 T2)
  ---
  → mk-seq (mk-id T1) c ≡ c
mk-seq-mk-id-l c = refl

mk-seq-mk-id-r : ∀ {T1 T2}
  → (c : Cast T1 T2)
  ---
  → mk-seq c (mk-id T2) ≡ c
mk-seq-mk-id-r [] = refl
mk-seq-mk-id-r (x ∷ c) rewrite mk-seq-mk-id-r c = refl

cast-rep-monoid : Monoid cast-rep
cast-rep-monoid
  = record
    { lem-id-l = mk-seq-mk-id-l
    ; lem-id-r = mk-seq-mk-id-r
    ; lem-assoc = mk-seq-assoc
    }
