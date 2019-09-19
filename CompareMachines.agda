module CompareMachines
  (Label : Set)
  where
open import Relation.Nullary using (Dec; yes; no)

open import Variables
open import Types
open import Terms Label
import AbstractMachine
import Vals

-- an abstract machine specialized for Type-based Cast

import TCast
module T = TCast Label

module TV = Vals Label T.Cast
module TAM = AbstractMachine
  Label
  T.Cast
  T.mk-id T.mk-seq T.mk-cast
module TM = TAM.Machine T.apply-cast

-- an abstract machine specialized for Hyper-coercion-based Cast

import HCast
module H = HCast Label

module HV = Vals Label H.Cast
module HAM = AbstractMachine
  Label
  H.Cast
  H.mk-id H.mk-seq H.mk-cast
module HM = HAM.Machine H.apply-cast


data CastRelate : ∀ {T1 T2} → T.Cast T1 T2 → H.Cast T1 T2 → Set where
  id : ∀ {T}
     --------------------------------------------------
     → CastRelate (T.mk-id T) (H.mk-id T)
  cast : ∀ l T1 T2
    ---------------------------------------------------------
    → CastRelate (T.mk-cast l T1 T2) (H.mk-cast l T1 T2)
  seq : ∀ {T1 T2 T3}
    → {c₁ : T.Cast T1 T2}
    → {ç₁ : H.Cast T1 T2}
    → CastRelate c₁ ç₁
    → {c₂ : T.Cast T2 T3}
    → {ç₂ : H.Cast T2 T3}
    → CastRelate c₂ ç₂
    ---------------------------------------------------------
    → CastRelate (T.mk-seq c₁ c₂) (H.mk-seq ç₁ ç₂)
    
mutual

  data EnvRelate : ∀ {Γ} → TV.Env Γ → HV.Env Γ → Set where
    []  : EnvRelate TV.[] HV.[]
    _∷_ : ∀ {Γ T}
      → {v : TV.Val T}{u : HV.Val T}
      → ValRelate v u
      → {E : TV.Env Γ}{F : HV.Env Γ}
      → EnvRelate E F
      → EnvRelate (TV._∷_ v E) (HV._∷_ u F)

  data ValRelate : ∀ {T} → TV.Val T → HV.Val T → Set where
    inj : ∀ P
      → {v : TV.Val (` P)}
      → {u : HV.Val (` P)}
      → ValRelate v u
      ----------------
      → ValRelate (TV.inj _ v) (HV.inj _ u)
      
    fun : ∀ {Γ T1 T2 T3 T4}
      → {E : TV.Env Γ}{F : HV.Env Γ}
      → EnvRelate E F
      → {c1 : T.Cast T3 T1}{ç1 : H.Cast T3 T1}
      → CastRelate c1 ç1
      → (b : Γ , T1 ⊢ T2)
      → {c2 : T.Cast T2 T4}{ç2 : H.Cast T2 T4}
      → CastRelate c2 ç2
      -------------
      → ValRelate (TV.fun E c1 b c2) (HV.fun F ç1 b ç2)

    sole :
      --------
        ValRelate TV.sole HV.sole

    cons : ∀ {T1 T2 T3 T4}
      → {v1 : TV.Val T1}
      → {u1 : HV.Val T1}
      → ValRelate v1 u1
      → {c1 : T.Cast T1 T3}
      → {ç1 : H.Cast T1 T3}
      → CastRelate c1 ç1
      → {v2 : TV.Val T2}
      → {u2 : HV.Val T2}
      → ValRelate v2 u2
      → {c2 : T.Cast T2 T4}
      → {ç2 : H.Cast T2 T4}
      → CastRelate c2 ç2
      ------------------
      → ValRelate (TV.cons v1 c1 v2 c2) (HV.cons u1 ç1 u2 ç2)

    inl : ∀ {T1 T2 T3}
      → {v : TV.Val T1}
      → {u : HV.Val T1}
      → ValRelate v u
      → {c : T.Cast T1 T3}
      → {ç : H.Cast T1 T3}
      → CastRelate c ç
      -----------------
      → ValRelate (TV.inl {T2 = T2} v c) (HV.inl u ç)
      
    inr : ∀ {T1 T2 T4}
      → {v : TV.Val T2}
      → {u : HV.Val T2}
      → ValRelate v u
      → {c : T.Cast T2 T4}
      → {ç : H.Cast T2 T4}
      → CastRelate c ç
      -----------------
      → ValRelate (TV.inr {T1 = T1} v c) (HV.inr u ç)

_[_] : ∀ {Γ T}
  → {lE : TV.Env Γ}
  → {rE : HV.Env Γ}
  → (E : EnvRelate lE rE)
  → (x : Γ ∋ T)
  → ValRelate (lE TV.[ x ]) (rE HV.[ x ])
(c ∷ E) [ Z ] = c
(c ∷ E) [ S x ] = E [ x ]


data CastResultRelate {T : Type} : TV.CastResult T → HV.CastResult T → Set where
  succ :
      {v : TV.Val T}{u : HV.Val T}
    → ValRelate v u
    → CastResultRelate (TV.succ v) (HV.succ u)
  fail : (l : Label)
    → CastResultRelate (TV.fail l) (HV.fail l)

mutual
  -- cast from T1 to T2
  data ContRelate : {T1 T3 : Type} (lκ : TAM.Cont T1 T3) (rκ : HAM.Cont T1 T3) → Set where
    cont : ∀ {T1 T3 mid}
      → {lfst : T.Cast T1 mid}
      → {rfst : H.Cast T1 mid}
      → (fst : CastRelate lfst rfst)
      → {lsnd : TAM.PreCont mid T3}
      → {rsnd : HAM.PreCont mid T3}
      → (snd : PreContRelate lsnd rsnd)
      → ContRelate record{ fst = lfst ; snd = lsnd} record{ fst = rfst ; snd = rsnd}

  data PreContRelate : {T1 T3 : Type} → TAM.PreCont T1 T3 → HAM.PreCont T1 T3 → Set where
  
    -- Every expression of arity n has n pre-continuations, except cast

    mt : ∀ {Z}
      ----------
      → PreContRelate (TAM.mt {Z}) (HAM.mt {Z})

    cons₁ : ∀ {Γ T1 T2 Z}
      → {lE : TV.Env Γ}
      → {rE : HV.Env Γ}
      → (E : EnvRelate lE rE)
      → (e1 : Γ ⊢ T2)
      → {lκ : TAM.Cont (` T1 ⊗ T2) Z}
      → {rκ : HAM.Cont (` T1 ⊗ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (TAM.cons₁ lE e1 lκ) (HAM.cons₁ rE e1 rκ)
      
    cons₂ : ∀ {T1 T2 Z}
      → {lv1 : TV.Val T1}
      → {rv1 : HV.Val T1}
      → (v1 : ValRelate lv1 rv1)
      → {lκ : TAM.Cont (` T1 ⊗ T2) Z}
      → {rκ : HAM.Cont (` T1 ⊗ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (TAM.cons₂ lv1 lκ) (HAM.cons₂ rv1 rκ)

    inl :  ∀ {T1 T2 Z}
      → {lκ : TAM.Cont (` T1 ⊕ T2) Z}
      → {rκ : HAM.Cont (` T1 ⊕ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (TAM.inl lκ) (HAM.inl rκ)

    inr :  ∀ {T1 T2 Z}
      → {lκ : TAM.Cont (` T1 ⊕ T2) Z}
      → {rκ : HAM.Cont (` T1 ⊕ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (TAM.inr lκ) (HAM.inr rκ)
           
    app₁ : ∀ {Γ T1 T2 Z}
      → {lE : TV.Env Γ}
      → {rE : HV.Env Γ}
      → (E : EnvRelate lE rE)
      → (e2 : Γ ⊢ T1)
      → {lκ : TAM.Cont T2 Z}
      → {rκ : HAM.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (TAM.app₁ lE e2 lκ) (HAM.app₁ rE e2 rκ)

    app₂ : ∀ {T1 T2 Z}
      → {lv1 : TV.Val (` T1 ⇒ T2)}
      → {rv1 : HV.Val (` T1 ⇒ T2)}
      → (v1 : ValRelate lv1 rv1)
      → {lκ : TAM.Cont T2 Z}
      → {rκ : HAM.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (TAM.app₂ lv1 lκ) (HAM.app₂ rv1 rκ)

    car : ∀ {T1 T2 Z}
      → {lκ : TAM.Cont T1 Z}
      → {rκ : HAM.Cont T1 Z}
      → (κ : ContRelate lκ rκ)
      -----------
      → PreContRelate (TAM.car {T2 = T2} lκ) (HAM.car {T2 = T2} rκ)
      
    cdr : ∀ {T1 T2 Z}
      → {lκ : TAM.Cont T2 Z}
      → {rκ : HAM.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      -----------
      → PreContRelate (TAM.cdr {T1 = T1} lκ) (HAM.cdr {T1 = T1} rκ)
      
    case₁ :  ∀ {Γ T1 T2 T3 Z}
      → {lE : TV.Env Γ}
      → {rE : HV.Env Γ}
      → (E : EnvRelate lE rE)
      → (e2 : Γ ⊢ ` T1 ⇒ T3)
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → {lκ : TAM.Cont T3 Z}
      → {rκ : HAM.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (TAM.case₁ lE e2 e3 lκ) (HAM.case₁ rE e2 e3 rκ)
      
    case₂ :  ∀ {Γ T1 T2 T3 Z}
      → {lE : TV.Env Γ}
      → {rE : HV.Env Γ}
      → (E : EnvRelate lE rE)
      → {lv1 : TV.Val (` T1 ⊕ T2)}
      → {rv1 : HV.Val (` T1 ⊕ T2)}
      → (v1 : ValRelate lv1 rv1)
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → {lκ : TAM.Cont T3 Z}
      → {rκ : HAM.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (TAM.case₂ lE lv1 e3 lκ) (HAM.case₂ rE rv1 e3 rκ)
      
    case₃ : ∀ {T1 T2 T3 Z}
      → {lv1 : TV.Val (` T1 ⊕ T2)}
      → {rv1 : HV.Val (` T1 ⊕ T2)}
      → (v1 : ValRelate lv1 rv1)
      → {lv2 : TV.Val (` T1 ⇒ T3)}
      → {rv2 : HV.Val (` T1 ⇒ T3)}
      → (v2 : ValRelate lv2 rv2)
      → {lκ : TAM.Cont T3 Z}
      → {rκ : HAM.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      ----------------
      → PreContRelate (TAM.case₃ lv1 lv2 lκ) (HAM.case₃ rv1 rv2 rκ)

    -- This additional pre-continuation is for function calls

    call : ∀ {Γ T1 T2 Z}
      → {lE : TV.Env Γ}
      → {rE : HV.Env Γ}
      → (E : EnvRelate lE rE)
      → (e : (Γ , T1) ⊢ T2)
      → {lκ : TAM.Cont T2 Z}
      → {rκ : HAM.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      -------------
      → PreContRelate (TAM.call lE e lκ) (HAM.call rE e rκ)

mk-cont : ∀ {T1 T2}
  → {lκ : TAM.PreCont T1 T2}
  → {rκ : HAM.PreCont T1 T2}
  → (κ : PreContRelate lκ rκ)
  → ContRelate (TAM.mk-cont lκ) (HAM.mk-cont rκ)
mk-cont κ = cont id κ

ext-cont : ∀ {T1 T2 T3}
  → {lc : T.Cast T1 T2}
  → {rc : H.Cast T1 T2}
  → (c : CastRelate lc rc)
  → {lκ : TAM.Cont T2 T3}
  → {rκ : HAM.Cont T2 T3}
  → (κ : ContRelate lκ rκ)
  → ContRelate (TAM.ext-cont lc lκ) (HAM.ext-cont rc rκ)
ext-cont c (cont fst snd) = cont (seq c fst) snd

data StateRelate : {T : Type} → TAM.State T → HAM.State T → Set where
  inspect : ∀ {Γ T1 T3}
    → (e : Γ ⊢ T1)
    → {lE : TV.Env Γ}
    → {rE : HV.Env Γ}
    → (E : EnvRelate lE rE)
    → {lκ : TAM.Cont T1 T3}
    → {rκ : HAM.Cont T1 T3}
    → (κ : ContRelate lκ rκ)
    ------------
    → StateRelate (TAM.inspect e lE lκ) (HAM.inspect e rE rκ)
    
  return₁ : ∀ {T1 T2}
    → {lv1 : TV.Val T1}
    → {rv1 : HV.Val T1}
    → (v1 : ValRelate lv1 rv1)
    → {lκ : TAM.Cont T1 T2}
    → {rκ : HAM.Cont T1 T2}
    → (κ : ContRelate lκ rκ)
    ------------
    → StateRelate (TAM.return₁ lv1 lκ) (HAM.return₁ rv1 rκ)
    
  return₂ : ∀ {T1 T2}
    → {lv : TV.Val T1}
    → {rv : HV.Val T1}
    → (v : ValRelate lv rv)
    → {lκ : TAM.PreCont T1 T2}
    → {rκ : HAM.PreCont T1 T2}
    → (κ : PreContRelate lκ rκ)
    ------------
    → StateRelate (TAM.return₂ lv lκ) (HAM.return₂ rv rκ)

  blame : ∀ {T}
    → (l : Label)
    -------
    → StateRelate (TAM.blame {T} l) (HAM.blame {T} l)

  done : ∀ {T}
    → {lv : TV.Val T}
    → {rv : HV.Val T}
    → (v : ValRelate lv rv)
    -------
    → StateRelate (TAM.done lv) (HAM.done rv)

rval : ∀ {T}
  → {v : TV.Val T}
  → {u : HV.Val T}
  → ValRelate v u
  → HV.Val T
rval {u = u} vr = u

renv : ∀ {Γ}
  → {E : TV.Env Γ}
  → {F : HV.Env Γ}
  → EnvRelate E F
  → HV.Env Γ
renv {F = F} vr = F

rcast : ∀ {T1 T2}
  → {c : T.Cast T1 T2}
  → {d : H.Cast T1 T2}
  → CastRelate c d
  → H.Cast T1 T2
rcast {d = d} cd = d

_>>=_ : ∀ {T1 T2}
  → {R : TV.CastResult T1}
  → {S : HV.CastResult T1}
  → CastResultRelate R S
  → {f : TV.Val T1 → (TV.CastResult T2)}
  → {g : HV.Val T1 → (HV.CastResult T2)}
  → ({v : TV.Val T1} → {u : HV.Val T1} → ValRelate v u → CastResultRelate (f v) (g u))
  → CastResultRelate (R TV.>>= f) (S HV.>>= g)
succ v >>= f = f v
fail l >>= f = fail l

do-cast :
    (l : Label)
  → (T1 T2 : Type)
  → {v : TV.Val T1}
  → {u : HV.Val T1}
  → ValRelate v u
  → CastResultRelate (T.apply-cast (T.mk-cast l T1 T2) v)
                     (H.apply-cast (H.mk-cast l T1 T2) u)
do-cast l T1 T2 v with T1 ⌣? T2
do-cast l .⋆ .⋆ v | yes ⋆⌣⋆
  rewrite H.lem-cast-id⋆ l (rval v)
  = succ v
do-cast l .⋆ .(` P) (inj P₁ v) | yes (⋆⌣P P)
  rewrite H.lem-cast-proj l P P₁ (rval v)
  = do-cast l (` P₁) (` P) v
do-cast l .(` P) .⋆ v | yes (P⌣⋆ P)
  rewrite H.lem-cast-inj l (rval v)
  = succ (inj P v)
do-cast l .(` U) .(` U) sole | yes ⌣U
  rewrite H.lem-cast-U l
  = succ sole
do-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22)) (fun E c₁ b c₂) | yes ⌣⇒
  rewrite H.lem-cast-⇒ T11 T12 T21 T22 l (renv E) (rcast c₁) b (rcast c₂)
  = succ (fun E (seq (cast l T21 T11) c₁) b (seq c₂ (cast l T12 T22)))
do-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22)) (cons v c v₁ c₁) | yes ⌣⊗
  rewrite H.lem-cast-⊗ _ _ T11 T12 T21 T22 l (rval v) (rval v₁) (rcast c) (rcast c₁)
  = succ (cons v (seq c (cast l T11 T21)) v₁ (seq c₁ (cast l T12 T22)))
do-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22)) (inl v c) | yes ⌣⊕
  rewrite H.lem-cast-⊕-l _ T11 T12 T21 T22 l (rval v) (rcast c)
  = succ (inl v (seq c (cast l T11 T21)))
do-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22)) (inr v c) | yes ⌣⊕
  rewrite H.lem-cast-⊕-r _ T11 T12 T21 T22 l (rval v) (rcast c)
  = succ (inr v (seq c (cast l T12 T22)))
do-cast l T1 T2 v | no ¬p
  rewrite H.lem-cast-¬⌣ l ¬p (rval v)
  = fail l

apply-cast : ∀ {T1 T2}
  → {c : T.Cast T1 T2}{ç : H.Cast T1 T2}
  → CastRelate c ç
  → {v : TV.Val T1}{u : HV.Val T1}
  → ValRelate v u
  ----------------------
  → CastResultRelate (T.apply-cast c v) (H.apply-cast ç u)
apply-cast (id {T}) {u = u} vr
  rewrite H.lem-id T u =
  succ vr
apply-cast (cast l T1 T2) vr = do-cast l T1 T2 vr
apply-cast (seq {c₁ = c₁}{ç₁ = ç₁} cç1 {c₂ = c₂}{ç₂ = ç₂} cç2) {v = v}{u = u} vr
  rewrite H.lem-seq ç₁ ç₂ u
  = apply-cast cç1 vr >>= λ ur →
    apply-cast cç2 ur

progress : ∀ {T}
  → {lS : TAM.State T}
  → {rS : HAM.State T}
  → StateRelate lS rS
  → StateRelate (TM.progress lS) (HM.progress rS)
progress (inspect sole E κ) = return₁ sole κ
progress (inspect (var X) E κ) = return₁ (E [ X ]) κ
progress (inspect (lam T1 T2 e) E κ) = return₁ (fun E id e id) κ
progress (inspect (cons e1 e2) E κ) = inspect e1 E (mk-cont (cons₁ E e2 κ))
progress (inspect (inl e) E κ) = inspect e E (mk-cont (inl κ))
progress (inspect (inr e) E κ) = inspect e E (mk-cont (inr κ))
progress (inspect (app e1 e2) E κ) = inspect e1 E (mk-cont (app₁ E e2 κ))
progress (inspect (car e) E κ) = inspect e E (mk-cont (car κ))
progress (inspect (cdr e) E κ) = inspect e E (mk-cont (cdr κ))
progress (inspect (case e1 e2 e3) E κ) = inspect e1 E (mk-cont (case₁ E e2 e3 κ))
progress (inspect (cast l T1 T2 e) E κ) = inspect e E (ext-cont (cast l T1 T2) κ)
progress (return₁ {lv1 = lv1} {rv1 = rv1} v {record { fst = fst ; snd = snd }} {record { fst = fst₁ ; snd = snd₁ }} (cont fst₂ snd₂))
  with (T.apply-cast fst lv1) | (H.apply-cast fst₁ rv1) | apply-cast fst₂ v
... | Vals.succ _ | (HV.succ _) | succ u = return₂ u snd₂
... | Vals.fail _ | (HV.fail _) | fail l = blame l
progress (return₂ v mt) = done v
progress (return₂ v (cons₁ E e1 κ)) = inspect e1 E (mk-cont (cons₂ v κ))
progress (return₂ v (cons₂ {T1} {T2} v1 κ)) = return₁ (cons v1 id v id) κ
progress (return₂ v (inl κ)) = return₁ (inl v id) κ
progress (return₂ v (inr κ)) = return₁ (inr v id) κ
progress (return₂ v (app₁ E e2 κ)) = inspect e2 E (mk-cont (app₂ v κ))
progress (return₂ v (app₂ (fun E c₁ b c₂) κ)) =
  return₁ v (ext-cont c₁ (mk-cont (call E b (ext-cont c₂ κ))))
progress (return₂ (cons v₁ c₁ v₂ c₂) (car κ)) = return₁ v₁ (ext-cont c₁ κ)
progress (return₂ (cons v₁ c₁ v₂ c₂) (cdr κ)) = return₁ v₂ (ext-cont c₂ κ)
progress (return₂ v (case₁ E e2 e3 κ)) = inspect e2 E (mk-cont (case₂ E v e3 κ))
progress (return₂ v (case₂ E v1 e3 κ)) = inspect e3 E (mk-cont (case₃ v1 v κ))
progress (return₂ v3 (case₃ (inl v1 c) v2 κ)) = return₁ v1 (ext-cont c (mk-cont (app₂ v2 κ)))
progress (return₂ v3 (case₃ (inr v1 c) v2 κ)) = return₁ v1 (ext-cont c (mk-cont (app₂ v3 κ)))
progress (return₂ v (call E e κ)) = inspect e (v ∷ E) κ
progress (blame l) = blame l
progress (done v) = done v
         
