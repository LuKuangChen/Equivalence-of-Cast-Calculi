module equivalence-of-cast-calculi.Bisimulation.FromAFewStepsToTheEnd
  where

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_ ; inj₁; inj₂)
open import Data.Product using (Σ; _×_ ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import equivalence-of-cast-calculi.TransitionSystem public

-- This is a parameterized bisimulation proof between any two systems (System.agda)

-- The parameterized bisimulation proof claims that
-- given a bisimulation relation _≈_
-- If s₁ ≈ s₂ implies that either
--   - s₁ final and s₂ final, or
--   - there exist s₃ and s₄ such that s₁ —→+ s₃ and s₂ —→+ s₄ and s₃ ≈ s₄
-- then for all s₁ ≈ s₂
--   - s₁ —→* s₃ and s₃ final implies
--     s₂ —→* s₄ and s₄ final and s₃ ≈ s₄ for some s₄
--   - s₂ —→* s₄ and s₄ final implies
--     s₁ —→* s₃ and s₃ final and s₃ ≈ s₄ for some s₃

module OneWay
  {lState rState : Set}
  (lSystem : System lState)
  (rSystem : System rState)
  (_~_ : lState → rState → Set)
  (safety : {ls : lState}{rs : rState}
    → ls ~ rs
    → (System.Final lSystem ls × System.Final rSystem rs)
      ⊎
      ∃[ ls' ]
      ∃[ rs' ](
        System._—→+_ lSystem ls ls' ×
        System._—→+_ rSystem rs rs' ×        
        (ls' ~ rs')))
  where

  open System using (zero; suc)

  module L where
    open System lSystem public
    
  module R where
    open System rSystem public

  prefix : ∀ {ls}
    → ∀ {ls'}
    → (xs : ls L.—→* ls')
    → L.Final ls'
    → ∀ {ls*}
    → (ys : ls L.—→* ls*)
    → L.Prefix ys xs
  prefix xs halt [] = zero
  prefix [] halt (y ∷ ys) = ⊥-elim (L.final-progressing-absurd halt y)
  prefix (x ∷ xs) halt (y ∷ ys) with L.deterministic x y
  ... | refl = suc (prefix xs halt ys)

  lem-final-helper : ∀ {ls1 ls2 rs}     -- the job of this helper is cutting prefix
    → (ss : ls2 ~ rs)
    → ∀ {ls'}
    → (xs : ls1 L.—→* ls2)
    → (ys : ls1 L.—→* ls')
    → L.Prefix xs ys
    → L.Final ls'
    → ∃[ rs' ](rs R.—→* rs' × R.Final rs' × ls' ~ rs')
  lem-final : ∀ {ls rs}
    → (ss : ls ~ rs)
    → ∀ {ls'}
    → ls L.—→* ls'
    → L.Final ls'
    → ∃[ rs' ](rs R.—→* rs' × R.Final rs' × ls' ~ rs')

  lem-final-helper ss [] ys zero ht = lem-final ss ys ht
  lem-final-helper ss (x ∷ xs) (y ∷ ys) (suc n) ht = lem-final-helper ss xs ys n ht
                                                                                 
  lem-final ss [] ls-halt with safety ss
  lem-final ss [] ls-halt | inj₁ (ls-halt' , rs-halt)
    = _ , [] , rs-halt , ss
  lem-final ss [] ls-halt | inj₂ (ls' , rs' , (lx ∷ lxs) , (rx ∷ rxs) , ss')
    = ⊥-elim (L.final-progressing-absurd ls-halt lx)
  lem-final ss (lx ∷ lxs) ls'-halt with safety ss
  lem-final ss (lx ∷ lxs) ls'-halt | inj₁ (ls-halt , rs-halt)
    = ⊥-elim (L.final-progressing-absurd ls-halt lx)
  lem-final ss (lx ∷ lxs) ls'-halt
    | inj₂ (ls' , rs' , (lx' ∷ lxs') , (rx' ∷ rxs') , ss')
    with L.deterministic lx lx'
  ... | refl
    with lem-final-helper ss' lxs' lxs (prefix lxs ls'-halt lxs') ls'-halt
  ... | rs'' , rxs , rhalt , bis = rs'' , (rx' ∷ (rxs' ++ rxs)) , rhalt , bis

module BothWays
  {lState rState : Set}
  (lSystem : System lState)
  (rSystem : System rState)
  (_~_ : lState → rState → Set)
  (safety : {ls : lState}{rs : rState}
    → ls ~ rs
    → (System.Final lSystem ls × System.Final rSystem rs)
      ⊎
      ∃[ ls' ]
      ∃[ rs' ](
        System._—→+_ lSystem ls ls' ×
        System._—→+_ rSystem rs rs' ×
        (ls' ~ rs')))
  where
  
  module L where
    open System lSystem public
    
  module R where
    open System rSystem public

  thm-final-LR : ∀ {ls rs}
    → (ss : ls ~ rs)
    → ∀ {ls'}
    → ls L.—→* ls'
    → L.Final ls'
    → ∃[ rs' ]((rs R.—→* rs') × (R.Final rs') × (ls' ~ rs'))
  thm-final-LR = OneWay.lem-final lSystem rSystem _~_ safety

  safety' : {rs : rState}{ls : lState}
    → ls ~ rs
    → (System.Final rSystem rs × System.Final lSystem ls)
      ⊎
      ∃[ rs' ]
      ∃[ ls' ](
        System._—→+_ rSystem rs rs' ×
        System._—→+_ lSystem ls ls' ×        
        (ls' ~ rs'))
  safety' ss with safety ss
  safety' ss | inj₁ (lh , rh) = inj₁ (rh , lh)
  safety' ss | inj₂ (ls' , rs' , lxs , rxs , ss')
    = inj₂ (rs' , ls' , rxs , lxs , ss')

  thm-final-RL : ∀ {ls rs}
    → (ss : ls ~ rs)
    → ∀ {rs'}
    → rs R.—→* rs'
    → R.Final rs'
    → ∃[ ls' ]((ls L.—→* ls') × (L.Final ls') × (ls' ~ rs'))
  thm-final-RL
    = OneWay.lem-final rSystem lSystem (λ r l → l ~ r) safety'

open BothWays public
