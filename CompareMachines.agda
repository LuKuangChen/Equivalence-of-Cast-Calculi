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
module TFAM = AbstractMachine
  Label
  T.Cast
  T.mk-id T.mk-seq T.mk-cast
module TM = TFAM.Machine T.apply-cast

-- an abstract machine specialized for Hyper-coercion-based Cast

import HCast
module H = HCast Label

module HV = Vals Label H.Cast
module HFAM = AbstractMachine
  Label
  H.Cast
  H.mk-id H.mk-seq H.mk-cast
module HM = HFAM.Machine H.apply-cast


mutual
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
  
  data CastResultRelate {T : Type} : TV.CastResult T → HV.CastResult T → Set where
    succ :
        {v : TV.Val T}{u : HV.Val T}
      → ValRelate v u
      → CastResultRelate (TV.succ v) (HV.succ u)
    fail : (l : Label)
      → CastResultRelate (TV.fail l) (HV.fail l)

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

