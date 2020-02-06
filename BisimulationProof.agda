open import Types
open import X.BlameStrategies
open import S.CastADT
open import ApplyCastBisimulate

module BisimulationProof
  (Label : Set)
  (BS : BlameStrategy Label)
  (CADT : CastADT Label (BlameStrategy.Injectable BS))
  (CADTB : CastADTBasic Label (BlameStrategy.Injectable BS) CADT)
  (lem-apply-cast : the-apply-cast-lemma Label BS CADT)
  where

open BlameStrategy BS using (Injectable; ⟦_⟧)
open import Variables using (∅)
open import Terms Label
open import Cast Label
open import Observables Label
open import Error using (Error; return; raise; _>=>_; _>>=_; >>=-return)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Bisimulation using (_∷_; [])
open import BisimulationRelation Label BS CADT renaming (module R to R')
module R where
  open R' public
open CastADTBasic CADTB public

open L using (error; halt; cont; expr; it)
open R using (error; halt; cont; expr; it; [□⟨_⟩]_)

load : ∀ {T} → (e : ∅ ⊢ T) → StateRelate (L.load e) (R.load e)
load e = return (expr e [] ([□⟨ id ⟩] □))

open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _∎; _≡⟨_⟩_; _≡⟨⟩_)

observe : ∀ {T}
  → {lv : L.Value T}
  → {rv : R.Value T}
  → ValueRelate lv rv
  → L.observe lv ≡ R.observe rv
observe (dyn P Pi v) = refl
observe #t = refl
observe #f = refl
observe (lam⟨ [] , c ⇒ d ⟩ e E) = refl
observe (lam⟨ lcs ⟪ lc , c ⇒ d ⟩ e E) = refl
observe (cons⟨ [] , c ⊗ d ⟩ v1 v2) = refl
observe (cons⟨ lcs ⟪ lc , c ⊗ d ⟩ v1 v2) = refl

ext-cont : ∀ {T1 T2 T3}
  → (c : Cast T1 T2)
  → {lk : L.Cont T2 T3}
  → {rk : R.Cont T2 T3}
  → ContRelate lk rk
  → ContRelate (L.[ L.□⟨ c ⟩ ] lk) (R.ext-cont R.⌈ c ⌉ rk)
ext-cont c ([□⟨ d ⟩] k) = [□⟨ just c ⨟ d ⟩] k

done : ∀ {T}
  → {lS : L.State T}
  → {rS : R.State T}
  → StateRelate lS rS
  → ∃[ lS' ]
    ∃[ rS' ]
      (lS L.−→* lS' ×
       rS R.−→* rS' ×
       StateRelate lS' rS')
done S = _ , _ , [] , [] , S

step : ∀ {T}
  → {lS lS' : L.State T}
  → {rS rS' : R.State T}
  → (lS L.−→* lS')
  → (rS R.−→* rS')
  → ∃[ lS'' ]
    ∃[ rS'' ]
      (lS' L.−→* lS'' ×
       rS' R.−→* rS'' ×
       StateRelate lS'' rS'')
  → ∃[ lS'' ]
    ∃[ rS'' ]
      (lS L.−→* lS'' ×
       rS R.−→* rS'' ×
       StateRelate lS'' rS'')
step lxs rxs (_ , _ , lys , rys , S) = _ , _ , (lxs L.++ lys) , (rxs R.++ rys) , S

-- inteprete cast lists
⟦_⟧* : ∀ {T1 T2}
  → CastList T1 T2
  → (L.Value T1 → Error Label (L.Value T2))
⟦ [] ⟧* = return
⟦ x ∷ xs ⟧* = L.⟦ x ⟧ >=> ⟦ xs ⟧*

lem-⟦++⟧* : ∀ {T1 T2 T3}
  → (xs : CastList T1 T2)
  → (ys : CastList T2 T3)
  → (∀ v → ⟦ xs ++ ys ⟧* v ≡ (⟦ xs ⟧* >=> ⟦ ys ⟧*) v)
lem-⟦++⟧* [] ys v = refl
lem-⟦++⟧* (x ∷ xs) ys v with L.⟦ x ⟧ v
... | return v' = lem-⟦++⟧* xs ys v'
... | raise l = refl

lem-cast-result : ∀ {T1 T2 lv rv lc rc}
  → ValueRelate {T1} lv rv
  → CastListRelate {T1} {T2} lc rc
  → CastResultRelate (⟦ lc ⟧* lv) (R.⟦ rc ⟧ rv)
lem-cast-result v id
  rewrite lem-id (rvalue v)
    = return v
lem-cast-result v (just c)
  rewrite >>=-return (L.⟦ c ⟧ (lvalue v))
    = lem-apply-cast v c
lem-cast-result v (c1 ⨟ c2)
  rewrite lem-⟦++⟧* (lcast c1) (lcast c2) (lvalue v)
    | lem-seq (rcast c1) (rcast c2) (rvalue v)
  with ⟦ lcast c1 ⟧* (lvalue v) | R.⟦ rcast c1 ⟧ (rvalue v) | lem-cast-result v c1
... | .(return _) | .(return _) | return v' = lem-cast-result v' c2
... | .(raise _) | .(raise _) | (raise l) = raise l

lem-cast-left : ∀ {T1 T2 T3}
  → (v : L.Value T1)
  → (cs : CastList T1 T2)
  → (k : L.Cont T2 T3)
  → (L.apply-cont v (view-cont cs k)) L.−→* (⟦ cs ⟧* v >>= λ v' → (L.apply-cont v' k))
lem-cast-left v [] k = []
lem-cast-left v (c ∷ cs) k with L.⟦ c ⟧ v
... | return v' = it (cont v' (view-cont cs k)) ∷ lem-cast-left v' cs k 
... | raise l = []

apply-cont : ∀ {T1 T2 lv rv lk rk}
  → ValueRelate {T1} lv rv
  → PreContRelate {T2} lk rk
  → ∃[ lS' ]
    ∃[ rS' ]
      (L.apply-cont lv lk L.−→* lS' ×
       R.apply-cont rv rk R.−→* rS' ×
       StateRelate lS' rS')
apply-cont v □ = done (return (halt v))
apply-cont v ([ app₁ e E ] k) = done (return (expr e E ([□⟨ id ⟩] [ app₂ v ] k)))
apply-cont v ([ app₂ v1 ] k)  = {!!}
apply-cont v ([ if₁ e2 e3 E ] k) = {!!}
apply-cont v ([ cons₁ e2 E ] k) = done (return (expr e2 E ([□⟨ id ⟩] [ cons₂ v ] k)))
apply-cont v ([ cons₂ v1 ] k)   = done (return (cont (cons⟨ [] , id ⊗ id ⟩ v1 v) k))
apply-cont v ([ car₁ ] k) = {!!}
apply-cont v ([ cdr₁ ] k) = {!!}

progress : ∀ {T}
  → {lS : L.State T}(lSp : L.Progressing lS)
  → {rS : R.State T}(rSp : R.Progressing rS)
  → StateRelate lS rS
  → ∃[ lS' ]
    ∃[ rS' ]
      (L.progress lSp L.−→* lS' ×
       R.progress rSp R.−→* rS' ×
       StateRelate lS' rS')
progress (expr (var x) lE lκ)
         (expr (var x) rE rκ)
         (return (expr (var x) E κ))
         = done (return (cont (lookup E x) κ))
progress (expr #t lE lκ)
         (expr #t rE rκ)
         (return (expr #t E κ))
         = done (return (cont #t κ))
progress (expr #f lE lκ)
         (expr #f rE rκ)
         (return (expr #f E κ))
         = done (return (cont #f κ))
progress (expr (if e e₁ e₂) lE lκ)
         (expr (if e e₁ e₂) rE rκ)
         (return (expr (if e e₁ e₂) E κ))
         = done (return (expr e E ([□⟨ id ⟩] [ if₁ e₁ e₂ E ] κ)))
progress (expr (lam e) lE lκ)
         (expr (lam e) rE rκ)
         (return (expr (lam e) E κ))
         = done (return (cont (lam⟨ [] , id ⇒ id ⟩ e E) κ))
progress (expr (app e e₁) lE lκ)
         (expr (app e e₁) rE rκ)
         (return (expr .(app e e₁) E κ))
         = done (return (expr e E ([□⟨ id ⟩] [ app₁ e₁ E ] κ)))
progress (expr (cons e e₁) lE lκ)
         (expr (cons e e₁) rE rκ)
         (return (expr .(cons e e₁) E κ))
         = done (return (expr e E (([□⟨ id ⟩] [ cons₁ e₁ E ] κ))))
progress (expr (e ⟨ c ⟩) lE lκ)
         (expr (e ⟨ c ⟩) rE rκ)
         (return (expr (e ⟨ c ⟩) E κ))
         = done (return (expr e E (ext-cont c κ)))
progress (expr (blame l) lE lκ)
         (expr (blame l) rE rκ)
         (return (expr (blame l) E κ))
         = done (raise l)
progress (cont lv lk)
         (cont rv rk)
         (return (cont v k))
  with lk | rk | k
... | .(view-cont (lcast c) (lprecont k')) | .([□⟨ rcast c ⟩] rprecont k') | [□⟨ c ⟩] k'
  with lem-cast-left lv (lcast c) (lprecont k')
... | lS⟼lS'
  with ⟦ (lcast c) ⟧* (lvalue v) | R.⟦ (rcast c) ⟧ (rvalue v) | lem-cast-result v c
... | .(raise _)  | .(raise _)  | raise l   = step lS⟼lS' [] (done (raise l))
... | .(return _) | .(return _) | return v' = step lS⟼lS' [] (apply-cont v' k')

final-or-progressing : ∀ {T}
  → {ls : L.State T}
  → {rs : R.State T}
  → StateRelate ls rs
  → (L.Final ls × R.Final rs)
    ⊎
    (L.Progressing ls × R.Progressing rs)
final-or-progressing (return (expr e E κ))
  = inj₂ (expr e (lenv E) (lcont κ) , expr e (renv E) (rcont κ))
final-or-progressing (return (cont v κ))
  = inj₂ (cont (lvalue v) (lcont κ) , cont (rvalue v) (rcont κ))
final-or-progressing (return (halt v))
  = inj₁ (halt (lvalue v) , halt (rvalue v))
final-or-progressing (raise l)
  = inj₁ (error l , error l)

safety : ∀ {T}
  → {ls : L.State T}
  → {rs : R.State T}
  → StateRelate ls rs
  → (L.Final ls × R.Final rs)
    ⊎
    (∃[ ls' ]
     ∃[ rs' ]
       (ls L.−→+ ls' ×
        rs R.−→+ rs' ×
        StateRelate ls' rs'))
safety S with final-or-progressing S
safety S | inj₁ (lSf , rSf) = inj₁ (lSf , rSf)
safety S | inj₂ (lSp , rSp) with progress lSp rSp S
safety S | inj₂ (lSp , rSp) | lS'' , rS'' , lS'⟼lS'' , rS'⟼rS'' , S''
  = inj₂ (lS'' , rS'' , (it lSp ∷ lS'⟼lS'') , (it rSp ∷ rS'⟼rS'') , S'')
