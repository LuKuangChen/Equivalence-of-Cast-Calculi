module S.CastADT
  (Label : Set)
  where

open import Types
open import Variables
open import Terms Label
open import S.Values Label

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)

record CastADT : Set₁ where
  field
    Cast : Type → Type → Set

    mk-cast : Label → (T1 T2 : Type) → Cast T1 T2
    mk-id : (T : Type) → Cast T T
    mk-seq : ∀ {T1 T2 T3}
      → Cast T1 T2
      → Cast T2 T3
      -----
      → Cast T1 T3
    apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val Cast T1 → CastResult Cast T2

-- only required for the bisim between D and S(C)
record CastIdIsId (CR : CastADT) : Set where
  open CastADT CR
  field
    lem-cast-id-is-id : ∀ l T →
      mk-cast l T T ≡ mk-id T

record Monoid (CR : CastADT) : Set where
  open CastADT CR
  field
    lem-id-l : ∀ {T1 T2}
      → (c : Cast T1 T2)
      ---
      → mk-seq (mk-id T1) c ≡ c
    lem-id-r : ∀ {T1 T2}
      → (c : Cast T1 T2)
      ---
      → mk-seq c (mk-id T2) ≡ c
    lem-assoc : ∀ {T1 T2 T3 T4}
      → (c1 : Cast T1 T2)
      → (c2 : Cast T2 T3)
      → (c3 : Cast T3 T4)
      ---
      → mk-seq (mk-seq c1 c2) c3 ≡ mk-seq c1 (mk-seq c2 c3)

record LazyD (CR : CastADT) : Set where
  open CastADT CR
  field
    lem-id : ∀ T
      → (v : Val Cast T)  
      -----------------------------
      → apply-cast (mk-id T) v ≡ succ v

    lem-seq : ∀ {T1 T2 T3}
      → (c1 : Cast T1 T2)
      → (c2 : Cast T2 T3)
      → (v : Val Cast T1)
      --------------------
      → apply-cast (mk-seq c1 c2) v ≡ (_>>=_ Cast (apply-cast c1 v) (λ u → apply-cast c2 u))
      
    lem-cast-¬⌣ : ∀ {T1 T2}
      → (l : Label)
      → ¬ (T1 ⌣ T2)
      → (v : Val Cast T1)
      ---
      → apply-cast (mk-cast l T1 T2) v ≡ fail l

    lem-cast-id* : ∀ l
      → (v : Val Cast *)
      → apply-cast (mk-cast l * *) v ≡ succ v

    lem-cast-inj : ∀ {P}
      → (l : Label)
      → (v : Val Cast (` P))  
      → apply-cast (mk-cast l (` P) *) v ≡ succ (dyn P v)
      
    lem-cast-proj : ∀ l P P₁ v
      → apply-cast (mk-cast l * (` P)) (dyn P₁ v) ≡ apply-cast (mk-cast l (` P₁) (` P)) v

    lem-cast-U : ∀ l
      → apply-cast (mk-cast l (` U) (` U)) unit ≡ succ unit

    lem-cast-⇒ : ∀ T11 T12 T21 T22
      → ∀ {S T}
      → (l : Label)
      → {Γ : Context}
      → (c₁ : Cast T11 S)
      → (c₂ : Cast T T12)
      → (e : (Γ , S) ⊢ T)
      → (E : Env Cast Γ)
      → apply-cast (mk-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22))) (lam c₁ c₂ e E) ≡
        succ (lam (mk-seq (mk-cast l T21 T11) c₁) (mk-seq c₂ (mk-cast l T12 T22)) e E)


record LazyUD (CR : CastADT) : Set where
  open CastADT CR
  
  compose : ∀ {T1 T2 T3} →
    (Val Cast T1 → CastResult Cast T2) →
    (Val Cast T2 → CastResult Cast T3) →
    ---
    (Val Cast T1 → CastResult Cast T3)
  compose f g v = _>>=_ Cast (f v) g

  field
    lem-id : ∀ T 
      -----------------------------
      → apply-cast (mk-id T) ≡ succ

    lem-seq : ∀ {T1 T2 T3}
      → (c1 : Cast T1 T2)
      → (c2 : Cast T2 T3)
      --------------------
      → apply-cast (mk-seq c1 c2) ≡ compose (apply-cast c1) (apply-cast c2)
      
    lem-cast-id* : ∀ l
      → apply-cast (mk-cast l * *) ≡ succ
      
    lem-cast-P* : ∀ {P}
      → ¬ Ground P
      → (l : Label)
      → apply-cast (mk-cast l (` P) *)
        ≡
        compose (apply-cast (mk-cast l (` P) (` ground P)))
                (apply-cast (mk-cast l (` ground P) *))

    lem-cast-I* : ∀ {I}
      → Ground I
      → (l : Label)
      → apply-cast (mk-cast l (` I) *) ≡ λ v → succ (dyn I v)

    lem-cast-*P : ∀ {P}
      → ¬ Ground P
      → (l : Label)
      → apply-cast (mk-cast l * (` P))
        ≡
        compose (apply-cast (mk-cast l * (` ground P)))
                (apply-cast (mk-cast l (` ground P) (` P)))

    lem-cast-*I-succ : ∀ {I}
      → Ground I
      → (l : Label)
      → (v : Val Cast (` I))  
      → apply-cast (mk-cast l * (` I)) (dyn I v) ≡ succ v
    
    lem-cast-*I-fail : ∀ {I J}
      → Ground I
      → ¬ I ≡ J
      → (l : Label)
      → (v : Val Cast (` J))  
      → apply-cast (mk-cast l * (` I)) (dyn J v) ≡ fail l

    lem-cast-U : ∀ l
      → apply-cast (mk-cast l (` U) (` U)) unit ≡ succ unit

    lem-cast-⇒ : ∀ T11 T12 T21 T22
      → ∀ {S T}
      → (l : Label)
      → {Γ : Context}
      → (c₁ : Cast T11 S)
      → (c₂ : Cast T T12)
      → (e : (Γ , S) ⊢ T)
      → (E : Env Cast Γ)
      → apply-cast (mk-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22))) (lam c₁ c₂ e E) ≡
        succ (lam (mk-seq (mk-cast l T21 T11) c₁) (mk-seq c₂ (mk-cast l T12 T22)) e E)
