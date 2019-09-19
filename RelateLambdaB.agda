module RelateLambdaB
  (Label : Set)
  where

open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (Σ; _×_ ; Σ-syntax)

open import Variables
open import Types
open import Terms Label
import AbstractMachine
import Values

-- an abstract machine specialized for LCast

import LCast
module T = LCast Label

module TV = Values Label T.Cast
module TAM = AbstractMachine
  Label
  T.Cast
  T.mk-id T.mk-seq T.mk-cast
module TM = TAM.Machine T.apply-cast

-- LambdaB Machine
import LambdaB
module B = LambdaB Label

mutual

  data EnvRelate : ∀ {Γ} → TV.Env Γ → B.Env Γ → Set where
    []  : EnvRelate TV.[] B.[]
    _∷_ : ∀ {Γ T}
      → {v : TV.Val T}{u : B.Val T}
      → ValRelate v u
      → {E : TV.Env Γ}{F : B.Env Γ}
      → EnvRelate E F
      → EnvRelate (TV._∷_ v E) (B._∷_ u F)

  data ValRelate : ∀ {T} → TV.Val T → B.Val T → Set where
    inj : ∀ P
      → {v : TV.Val (` P)}
      → {u : B.Val (` P)}
      → ValRelate v u
      ----------------
      → ValRelate (TV.inj _ v) (B.inj _ u)
      
    fun : ∀ {Γ T1 T2}
      → {E : TV.Env Γ}{F : B.Env Γ}
      → EnvRelate E F
      → (b : Γ , T1 ⊢ T2)
      -------------
      → ValRelate (TV.fun E (T.mk-id T1) b (T.mk-id T2)) (B.clos F b)

    cfun : ∀ {Γ T1 T2 T3 T4 S T l}
      → {E : TV.Env Γ}
      → {c1 : T.Cast T1 S}
      → (b  : Γ , S ⊢ T)
      → {c2 : T.Cast T T2}
      → {f : TV.Val (` T1 ⇒ T2)}
      → {g : B.Val (` T1 ⇒ T2)}
      → ValRelate (TV.fun E c1 b c2) g
      → ValRelate (TV.fun E (T.mk-seq (T.mk-cast l T3 T1) c1) b (T.mk-seq c2 (T.mk-cast l T2 T4)))
                  (B.cast l ⌣⇒ g)

    sole :
      --------
        ValRelate TV.sole B.sole

    csole : ∀ {l}
      → {v : B.Val (` U)}
      -------
      → ValRelate TV.sole (B.cast l ⌣U v)

    cons : ∀ {T1 T2}
      → {v1 : TV.Val T1}
      → {u1 : B.Val T1}
      → ValRelate v1 u1
      → {v2 : TV.Val T2}
      → {u2 : B.Val T2}
      → ValRelate v2 u2
      ------------------
      → ValRelate (TV.cons v1 (T.mk-id T1) v2 (T.mk-id T2)) (B.cons u1 u2)

    ccons : ∀ {T1 T2 T3 T4 T5 T6 l}
      → {v1 : TV.Val T1}
      → {c1 : T.Cast T1 T3}
      → {v2 : TV.Val T2}
      → {c2 : T.Cast T2 T4}
      → {u : B.Val (` T3 ⊗ T4)}
      → ValRelate (TV.cons v1 c1 v2 c2) u
      ------------------
      → ValRelate (TV.cons v1 (T.mk-seq c1 (T.mk-cast l T3 T5)) v2 (T.mk-seq c2 (T.mk-cast l T4 T6)))
                  (B.cast l ⌣⊗ u)
      
    inl : ∀ {T1 T2}
      → {v : TV.Val T1}
      → {u : B.Val T1}
      → ValRelate v u
      -----------------
      → ValRelate (TV.inl {T2 = T2} v (T.mk-id T1)) (B.inl u)

    cinl : ∀ {T1 T3 T4 T5 T6 l}
      → {v : TV.Val T1}
      → {c : T.Cast T1 T3}
      → {u : B.Val (` T3 ⊕ T4)}
      → ValRelate (TV.inl v c) u
      ---------
      → ValRelate (TV.inl v (T.mk-seq c (T.mk-cast l T3 T5)))
                  (B.cast {T3 ⊕ T4} {T5 ⊕ T6} l ⌣⊕ u)
      
    inr : ∀ {T1 T2}
      → {v : TV.Val T2}
      → {u : B.Val T2}
      → ValRelate v u
      -----------------
      → ValRelate (TV.inr {T1 = T1} v (T.mk-id T2)) (B.inr u)

    cinr : ∀ {T2 T3 T4 T5 T6 l}
      → {v : TV.Val T2}
      → {c : T.Cast T2 T4}
      → {u : B.Val (` T3 ⊕ T4)}
      → ValRelate (TV.inr v c) u
      ---------
      → ValRelate (TV.inr v (T.mk-seq c (T.mk-cast l T4 T6)))
                  (B.cast {T3 ⊕ T4} {T5 ⊕ T6} l ⌣⊕ u)

_[_] : ∀ {Γ T}
  → {lE : TV.Env Γ}
  → {rE : B.Env Γ}
  → (E : EnvRelate lE rE)
  → (x : Γ ∋ T)
  → ValRelate (lE TV.[ x ]) (rE B.[ x ])
(c ∷ E) [ Z ] = c
(c ∷ E) [ S x ] = E [ x ]

data CastResultRelate {T : Type} : TV.CastResult T → B.CastResult T → Set where
  succ :
      {v : TV.Val T}{u : B.Val T}
    → ValRelate v u
    → CastResultRelate (TV.succ v) (B.succ u)
  fail : (l : Label)
    → CastResultRelate (TV.fail l) (B.fail l)

mutual
  data ContRelate : {T1 T3 : Type} (lκ : TAM.Cont T1 T3) (rκ : B.Cont T1 T3) → Set where
    id : ∀ {T1 T2}
      → {lκ : TAM.PreCont T1 T2}
      → {rκ : B.Cont T1 T2}
      → (κ : PreContRelate lκ rκ)
      ---
      → ContRelate record { fst = T.[]; snd = lκ } rκ

    ext : ∀ {l T1 T2 T3}
      → {lκ : TAM.Cont T2 T3}
      → {rκ : B.Cont T2 T3}
      → (κ : ContRelate lκ rκ)
      ---
      → ContRelate record { fst = LCast.step l T1 T2 T.∷ TAM.Cont.fst lκ ;
                            snd = TAM.Cont.snd lκ }
                   (B.cast l T1 T2 rκ)  
  
  data PreContRelate : {T1 T3 : Type} (lκ : TAM.PreCont T1 T3) (rκ : B.Cont T1 T3) → Set where
    mt : ∀ {Z}
      ----------
      → PreContRelate ( (TAM.mt {Z})) (B.mt {Z})
  
    cons₁ : ∀ {Γ T1 T2 Z}
      → {lE : TV.Env Γ}
      → {rE : B.Env Γ}
      → (E : EnvRelate lE rE)
      → (e1 : Γ ⊢ T2)
      → {lκ : TAM.Cont (` T1 ⊗ T2) Z}
      → {rκ : B.Cont (` T1 ⊗ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (TAM.cons₁ lE e1 lκ)) (B.cons₁ rE e1 rκ)
      
    cons₂ : ∀ {T1 T2 Z}
      → {lv1 : TV.Val T1}
      → {rv1 : B.Val T1}
      → (v1 : ValRelate lv1 rv1)
      → {lκ : TAM.Cont (` T1 ⊗ T2) Z}
      → {rκ : B.Cont (` T1 ⊗ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (TAM.cons₂ lv1 lκ)) (B.cons₂ rv1 rκ)
                                                         
    inl :  ∀ {T1 T2 Z}
      → {lκ : TAM.Cont (` T1 ⊕ T2) Z}
      → {rκ : B.Cont (` T1 ⊕ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (TAM.inl lκ)) (B.inl rκ)
                                             
    inr :  ∀ {T1 T2 Z}
      → {lκ : TAM.Cont (` T1 ⊕ T2) Z}
      → {rκ : B.Cont (` T1 ⊕ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (TAM.inr lκ)) (B.inr rκ)
        
    app₁ : ∀ {Γ T1 T2 Z}
      → {lE : TV.Env Γ}
      → {rE : B.Env Γ}
      → (E : EnvRelate lE rE)
      → (e2 : Γ ⊢ T1)
      → {lκ : TAM.Cont T2 Z}
      → {rκ : B.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (TAM.app₁ lE e2 lκ)) (B.app₁ rE e2 rκ)
                                                           
    app₂ : ∀ {T1 T2 Z}
      → {lv1 : TV.Val (` T1 ⇒ T2)}
      → {rv1 : B.Val (` T1 ⇒ T2)}
      → (v1 : ValRelate lv1 rv1)
      → {lκ : TAM.Cont T2 Z}
      → {rκ : B.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (TAM.app₂ lv1 lκ)) (B.app₂ rv1 rκ)
                                                       
    car : ∀ {T1 T2 Z}
      → {lκ : TAM.Cont T1 Z}
      → {rκ : B.Cont T1 Z}
      → (κ : ContRelate lκ rκ)
      -----------
      → PreContRelate ( (TAM.car {T2 = T2} lκ)) (B.car {T2 = T2} rκ)
      
    cdr : ∀ {T1 T2 Z}
      → {lκ : TAM.Cont T2 Z}
      → {rκ : B.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      -----------
      → PreContRelate ( (TAM.cdr {T1 = T1} lκ)) (B.cdr {T1 = T1} rκ)
      
    case₁ :  ∀ {Γ T1 T2 T3 Z}
      → {lE : TV.Env Γ}
      → {rE : B.Env Γ}
      → (E : EnvRelate lE rE)
      → (e2 : Γ ⊢ ` T1 ⇒ T3)
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → {lκ : TAM.Cont T3 Z}
      → {rκ : B.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (TAM.case₁ lE e2 e3 lκ)) (B.case₁ rE e2 e3 rκ)
      
    case₂ :  ∀ {Γ T1 T2 T3 Z}
      → {lE : TV.Env Γ}
      → {rE : B.Env Γ}
      → (E : EnvRelate lE rE)
      → {lv1 : TV.Val (` T1 ⊕ T2)}
      → {rv1 : B.Val (` T1 ⊕ T2)}
      → (v1 : ValRelate lv1 rv1)
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → {lκ : TAM.Cont T3 Z}
      → {rκ : B.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (TAM.case₂ lE lv1 e3 lκ)) (B.case₂ rE rv1 e3 rκ)
      
    case₃ : ∀ {T1 T2 T3 Z}
      → {lv1 : TV.Val (` T1 ⊕ T2)}
      → {rv1 : B.Val (` T1 ⊕ T2)}
      → (v1 : ValRelate lv1 rv1)
      → {lv2 : TV.Val (` T1 ⇒ T3)}
      → {rv2 : B.Val (` T1 ⇒ T3)}
      → (v2 : ValRelate lv2 rv2)
      → {lκ : TAM.Cont T3 Z}
      → {rκ : B.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      ----------------
      → PreContRelate ( (TAM.case₃ lv1 lv2 lκ)) (B.case₃ rv1 rv2 rκ)
  
data StateRelate : {T : Type} → TAM.State T → B.State T → Set where
  inspect : ∀ {Γ T1 T3}
    → (e : Γ ⊢ T1)
    → {lE : TV.Env Γ}
    → {rE : B.Env Γ}
    → (E : EnvRelate lE rE)
    → {lκ : TAM.Cont T1 T3}
    → {rκ : B.Cont T1 T3}
    → (κ : ContRelate lκ rκ)
    ------------
    → StateRelate (TAM.inspect e lE lκ) (B.inspect e rE rκ)
    
  return : ∀ {T1 T2}
    → {lv1 : TV.Val T1}
    → {rv1 : B.Val T1}
    → (v1 : ValRelate lv1 rv1)
    → {lκ : TAM.Cont T1 T2}
    → {rκ : B.Cont T1 T2}
    → (κ : ContRelate lκ rκ)
    ------------
    → StateRelate (TAM.return₁ lv1 lκ) (B.return rv1 rκ)

  blame : ∀ {T}
    → (l : Label)
    -------
    → StateRelate (TAM.blame {T} l) (B.blame {T} l)

  done : ∀ {T}
    → {lv : TV.Val T}
    → {rv : B.Val T}
    → (v : ValRelate lv rv)
    -------
    → StateRelate (TAM.done lv) (B.done rv)

repeat : {A : Set} → ℕ → (A → A) → A → A
repeat zero f x = x
repeat (suc n) f x = repeat n f (f x)

-- progress* : ∀ {T}
--   → {lS : TAM.State T}
--   → {rS : B.State T}
--   → StateRelate lS rS
--   → Σ[ n ∈ ℕ ]
--     Σ[ m ∈ ℕ ]
--     StateRelate (repeat (suc n) TM.progress lS)
--                 (repeat (suc m) B.progress rS)
-- progress* (inspect (var x) E κ)
--   = zero Data.Product., (zero Data.Product., (return (E [ x ]) κ))
-- progress* (inspect sole E κ)
--   = zero Data.Product., (zero Data.Product., (return sole κ))
-- progress* (inspect (lam T1 T2 e) E κ)
--   = {!!}
-- progress* (inspect (cons e e₁) E κ) = {!!}
-- progress* (inspect (inl e) E κ) = {!!}
-- progress* (inspect (inr e) E κ) = {!!}
-- progress* (inspect (app e e₁) E κ) = {!!}
-- progress* (inspect (car e) E κ) = {!!}
-- progress* (inspect (cdr e) E κ) = {!!}
-- progress* (inspect (case e e₁ e₂) E κ) = {!!}
-- progress* (inspect (cast l T1 T2 e) E κ)
--   = zero Data.Product., (zero Data.Product., (inspect e E (cast κ)))
-- progress* (return v1 {record { mid = _ ; fst = .T.id ; snd = .TAM.mt }} mt) = {!!}
-- progress* (return v1 {record { mid = _ ; fst = .T.id ; snd = .(TAM.cons₁ _ e1 _) }} (cons₁ E e1 κ)) = {!!}
-- progress* (return v1 {record { mid = _ ; fst = .T.id ; snd = .(TAM.cons₂ _ _) }} (cons₂ v2 κ)) = {!!}
-- progress* (return v1 {record { mid = _ ; fst = .T.id ; snd = .(TAM.inl _) }} (inl κ)) = {!!}
-- progress* (return v1 {record { mid = _ ; fst = .T.id ; snd = .(TAM.inr _) }} (inr κ)) = {!!}
-- progress* (return v1 {record { mid = .(` (_ ⇒ _)) ; fst = .T.id ; snd = .(TAM.app₁ _ e2 _) }} (app₁ E e2 κ)) = {!!}
-- progress* (return v1 {record { mid = _ ; fst = .T.id ; snd = .(TAM.app₂ _ _) }} (app₂ v2 κ)) = {!!}
-- progress* (return v1 {record { mid = .(` (_ ⊗ _)) ; fst = .T.id ; snd = .(TAM.car _) }} (car κ)) = {!!}
-- progress* (return v1 {record { mid = .(` (_ ⊗ _)) ; fst = .T.id ; snd = .(TAM.cdr _) }} (cdr κ)) = {!!}
-- progress* (return v1 {record { mid = .(` (_ ⊕ _)) ; fst = .T.id ; snd = .(TAM.case₁ _ e2 e3 _) }} (case₁ E e2 e3 κ)) = {!!}
-- progress* (return v1 {record { mid = .(` (_ ⇒ _)) ; fst = .T.id ; snd = .(TAM.case₂ _ _ e3 _) }} (case₂ E v2 e3 κ)) = {!!}
-- progress* (return v1 {record { mid = .(` (_ ⇒ _)) ; fst = .T.id ; snd = .(TAM.case₃ _ _ _) }} (case₃ v2 v3 κ)) = {!!}
-- progress* (return v1 {record { mid = mid ; fst = .(T.seq (T.cast _ _) fst) ; snd = snd }} (cast {lκ = record { mid = .mid ; fst = fst ; snd = .snd }} κ)) = {!!}
-- progress* (blame l)
--   = zero Data.Product., (zero Data.Product., (blame l))
-- progress* (done v)
--   = zero Data.Product., (zero Data.Product., (done v))

