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
import TCastInterface
module TC = TCast Label
module TCI = TCastInterface Label

module TV = Vals Label TC.Cast
module TFAM = AbstractMachine
  Label
  TC.Cast
  TCI.mk-id TCI.mk-seq TCI.mk-cast
module TM = TFAM.Machine TCI.apply-cast

-- an abstract machine specialized for Hyper-coercion-based Cast

import HCCast
import HCCastInterface
module HC = HCCast Label
module HCI = HCCastInterface Label

module HV = Vals Label HC.Cast
module HFAM = AbstractMachine
  Label
  HC.Cast
  HCI.mk-id HCI.mk-seq HCI.mk-cast
module HM = HFAM.Machine HCI.apply-cast


mutual
  data CastRelate : ∀ {T1 T2} → TC.Cast T1 T2 → HC.Cast T1 T2 → Set where
    id : ∀ {T}
      --------------------------------------------------
      → CastRelate (TCI.mk-id T) (HCI.mk-id T)
    cast : ∀ l T1 T2
      ---------------------------------------------------------
      → CastRelate (TCI.mk-cast l T1 T2) (HCI.mk-cast l T1 T2)
    seq : ∀ {T1 T2 T3}
      → {c₁ : TC.Cast T1 T2}{ç₁ : HC.Cast T1 T2}
      → CastRelate c₁ ç₁
      → {c₂ : TC.Cast T2 T3}{ç₂ : HC.Cast T2 T3}
      → CastRelate c₂ ç₂
      ---------------------------------------------------------
      → CastRelate (TCI.mk-seq c₁ c₂) (HCI.mk-seq ç₁ ç₂)

  data EnvRelate : ∀ {Γ} → TV.Env Γ → HV.Env Γ → Set where
    []  : EnvRelate TV.[] HV.[]
    _∷_ : ∀ {Γ T}
      → {v : TV.Val T}{u : HV.Val T}
      → ValRelate v u
      → {E : TV.Env Γ}{Ε : HV.Env Γ}
      → EnvRelate E Ε
      → EnvRelate (TV._∷_ v E) (HV._∷_ u Ε)

  data ValRelate : ∀ {T} → TV.Val T → HV.Val T → Set where
    inj : ∀ P
      → {u : TV.Val (` P)}{v : HV.Val (` P)}
      → ValRelate u v
      ----------------
      → ValRelate (TV.inj _ u) (HV.inj _ v)
      
    fun : ∀ {Γ T1 T2 T3 T4}
      → {E : TV.Env Γ}{Ε : HV.Env Γ}
      → EnvRelate E Ε
      → {c1 : TC.Cast T3 T1}{ç1 : HC.Cast T3 T1}
      → CastRelate c1 ç1
      → (b : Γ , T1 ⊢ T2)
      → {c2 : TC.Cast T2 T4}{ç2 : HC.Cast T2 T4}
      → CastRelate c2 ç2
      -------------
      → ValRelate (TV.fun E c1 b c2) (HV.fun Ε ç1 b ç2)

    sole :
      --------
        ValRelate TV.sole HV.sole

    cons : ∀ {T1 T2}
      → {v1 : TV.Val T1}{u1 : HV.Val T1}
      → ValRelate v1 u1
      → {v2 : TV.Val T2}{u2 : HV.Val T2}
      → ValRelate v2 u2
      ------------------
      → ValRelate (TV.cons v1 v2) (HV.cons u1 u2)

    inl : ∀ {T1 T2}
      → {v : TV.Val T1}{u : HV.Val T1}
      → ValRelate v u
      -----------------
      → ValRelate (TV.inl {T2 = T2} v) (HV.inl u)
      
    inr : ∀ {T1 T2}
      → {v : TV.Val T2}{u : HV.Val T2}
      → ValRelate v u
      -----------------
      → ValRelate (TV.inr {T1 = T1} v) (HV.inr u)
  
  data CastResultRelate  (T : Type) : TV.CastResult T → HV.CastResult T → Set where
    succ :
        {v : TV.Val T}{u : HV.Val T}
      → ValRelate v u
      → CastResultRelate T (TV.succ v) (HV.succ u)
    fail : (l : Label)
      → CastResultRelate T (TV.fail l) (HV.fail l)

  data StateRelate : ∀ {T} → TFAM.State T → HFAM.State T → Set where
    -- TODO

apply-cast≈ : ∀ {T1 T2}
  → {c : TC.Cast T1 T2}{ç : HC.Cast T1 T2}
  → CastRelate c ç
  → {v : TV.Val T1}{u : HV.Val T1}
  → ValRelate v u
  ----------------------
  → CastResultRelate T2 (TCI.apply-cast c v) (HCI.apply-cast ç u)
apply-cast≈ (id {T}) {u = u} vr
  rewrite HCI.lem-id T u =
  succ vr
apply-cast≈ (cast l T1 T2) vr = {!!}
apply-cast≈ (seq {c₁ = c₁}{ç₁ = ç₁} cr1 {c₂ = c₂}{ç₂ = ç₂} cr2) {v = v}{u = u} vr
  rewrite HCI.lem-seq ç₁ ç₂ u
  with apply-cast≈ cr1 vr
... | r = {!!}

AM≈ : ∀ {T}
  → (S1 : TFAM.State T)
  → (S2 : HFAM.State T)
  → StateRelate S1 S2
  --------------------
  → StateRelate (TM.progress S1) (HM.progress S2)
AM≈ S1 S2 = {!!}
