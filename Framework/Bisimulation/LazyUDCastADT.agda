module Bisimulation.LazyUDCastADT
  (Label : Set)  
  where

open import Types
open import LabelUtilities Label
open import Variables using (Context)
open import Terms Label
open import Error
open import Cast Label using (_⟹[_]_)

open import R.BlameStrategies Label using (BlameStrategy; LazyUDBS)
open BlameStrategy LazyUDBS using (Injectable)

open import S.CastADT Label Injectable
import S.Values using (Env; Value; dyn; #t; #f; lam⟨_⇒_⟩; cons⟨_⊗_⟩)

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_; yes; no)

record IsLazyUD (ADT : CastADT) : Set where
  open CastADT ADT
  open S.Values Label Injectable Cast
  field      
    eq-¬⌣ : ∀ {T1 T2}
      → (v : Value T1)
      → (l : Label×Polarity)
      → ¬ (T1 ⌣ T2)
      ---
      → ⟦ ⌈ T1 ⟹[ l ] T2 ⌉ ⟧ v
          ≡
        raise l

    eq-** : ∀ l
      → (v : Value *)
      → ⟦ ⌈ * ⟹[ l ] * ⌉ ⟧ v
          ≡
        return v

    eq-P* : ∀ {P}
      → (v : Value (` P))
      → (l : Label×Polarity)
      → ¬ Ground P
      → ⟦ ⌈ (` P) ⟹[ l ] * ⌉ ⟧ v
          ≡
        ⟦ ⌈ (` P) ⟹[ l ] (` ground P) ⌉ ⟧ v >>= ⟦ ⌈ (` ground P) ⟹[ l ] * ⌉ ⟧

    eq-I* : ∀ {P}
      → (v : Value (` P))
      → (l : Label×Polarity)
      → (gP : Ground P)
      → ⟦ ⌈ ` P ⟹[ l ] * ⌉ ⟧ v
          ≡
        return (dyn gP v)

    eq-*P : ∀ {P}
      → (v : Value *)
      → (l : Label×Polarity)
      → ¬ Ground P
      → ⟦ ⌈ * ⟹[ l ] (` P) ⌉ ⟧ v
          ≡
        ⟦ ⌈ * ⟹[ l ] (` ground P) ⌉ ⟧ v >>= ⟦ ⌈ (` ground P) ⟹[ l ] (` P) ⌉ ⟧
      
    eq-*I-succ : ∀ {P}
      → (v : Value (` P))
      → (l : Label×Polarity)
      → (gP : Ground P)
      → ⟦ ⌈ * ⟹[ l ] (` P) ⌉ ⟧ (dyn gP v)
          ≡
        return v
    
    eq-*I-fail : ∀ {P Q}
      → (v : Value (` P))  
      → (l : Label×Polarity)
      → (gP : Ground P)
      → (gQ : Ground Q)
      → ¬ (` P) ≡ (` Q)
      → ⟦ ⌈ * ⟹[ l ] (` Q) ⌉ ⟧ (dyn gP v)
          ≡
        raise l

    eq-B : ∀ l b
      → ⟦ ⌈ (` B) ⟹[ l ] (` B) ⌉ ⟧ b
          ≡
        return b

    eq-⇒ : ∀ T21 T22 T11 T12
      → ∀ {S T}
      → (l : Label×Polarity)
      → {Γ : Context}
      → (c₁ : Cast T11 S)
      → (c₂ : Cast T T12)
      → ∀ e
      → (E : Env Γ)
      → ⟦ ⌈ (` T11 ⇒ T12) ⟹[ l ] (` T21 ⇒ T22) ⌉ ⟧ (lam⟨ c₁ ⇒ c₂ ⟩ e E)
          ≡
        return (lam⟨ ⌈ T21 ⟹[ negate-label l ] T11 ⌉ ⨟ c₁ ⇒ c₂ ⨟ ⌈ T12 ⟹[ l ] T22 ⌉ ⟩ e E)

    eq-⊗ : ∀ T21 T22 T11 T12
      → ∀ {S T}
      → (l : Label×Polarity)
      → (c₁ : Cast S T11)
      → (c₂ : Cast T T12)
      → (v1 : Value S)
      → (v2 : Value T)
      → ⟦ ⌈ (` T11 ⊗ T12) ⟹[ l ] (` T21 ⊗ T22) ⌉ ⟧ (cons⟨ c₁ ⊗ c₂ ⟩ v1 v2)
          ≡
        return (cons⟨ c₁ ⨟ ⌈ T11 ⟹[ l ] T21 ⌉ ⊗ c₂ ⨟ ⌈ T12 ⟹[ l ] T22 ⌉ ⟩ v1 v2)

{-
The following module proves that the ⟦_⟧ operator of every Lazy UD Cast ADT
 preserves the bisimulation relation (lem-⟦_⟧).
-}
module Theorems
  (CADT : CastADT)
  (CADTLazyUD : IsLazyUD CADT)
  where
  
  open import Cast Label using (Cast)
  open import R.BlameStrategies using (BlameStrategy)
  open import Bisimulation.BisimulationRelation Label LazyUDBS CADT
  open IsLazyUD CADTLazyUD

  open import Relation.Nullary using (yes; no)
  open import Data.Unit using (⊤; tt)
  open import Data.Product using (Σ; _×_ ; ∃-syntax; _,_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Data.Empty using (⊥; ⊥-elim)

  open R.BlameStrategies.LazyUD Label using (project)
  
  lem-project : ∀ {Q lv rv}
    → (l : Label×Polarity)
    → (gQ : Ground Q)
    → ValueRelate lv rv
    → CastResultRelate (project lv l gQ)
                       (R.⟦ R.⌈ * ⟹[ l ] ` Q ⌉ ⟧ rv)
  lem-project {Q = Q} l gQ (dyn gP v) with (` unground gP) ≟ (` unground gQ)
  ... | yes refl
    rewrite eq-*I-succ (rvalue v) l gP
    = return v
  ... | no ¬P≡Q
    rewrite eq-*I-fail (rvalue v) l gP gQ ¬P≡Q
    = raise l
  
  lem-proxy : ∀ {P Q}
            → {lv : L.Value (` P)}
            → {rv : R.Value (` P)}
            → ValueRelate lv rv
            → (c : Cast (` P) (` Q))
            → (p : (` P) ⌣ (` Q))
            → ∃[ ru ](
            (R.⟦ R.⌈ c ⌉ ⟧ rv ≡ return ru) ×
            ValueRelate (L.proxy lv c p) ru
            )
  lem-proxy v (` B ⟹[ l ] ` B) ⌣B rewrite eq-B l (rvalue v) = _ , refl , v
  lem-proxy (lam⟨ lcs , c1 ⇒ c2 ⟩ e E) (` S1 ⇒ T1 ⟹[ l ] ` S2 ⇒ T2) ⌣⇒
    rewrite eq-⇒ S2 T2 S1 T1 l (rcast c1) (rcast c2) e (renv E)
    = _ , refl
      , lam⟨ lcs ⟪ _ , just (S2 ⟹[ negate-label l ] S1) ⨟ c1 ⇒ c2 ⨟ just (T1 ⟹[ l ] T2) ⟩ e E
  lem-proxy (cons⟨ lcs , c1 ⊗ c2 ⟩ v1 v2) (` L1 ⊗ R1 ⟹[ l ] ` L2 ⊗ R2) ⌣⊗
    rewrite eq-⊗ L2 R2 L1 R1 l (rcast c1) (rcast c2) (rvalue v1) (rvalue v2)
    = _ , refl
    , cons⟨ lcs ⟪ _ , c1 ⨟ just (L1 ⟹[ l ] L2) ⊗ c2 ⨟ just (R1 ⟹[ l ] R2) ⟩ v1 v2
  
  lem-*P : ∀ {P lv rv}
    → (c : Cast * (` P))
    → ValueRelate lv rv
    → CastResultRelate (L.apply-cast c lv)
                       (R.⟦ R.⌈ c ⌉ ⟧ rv)
  lem-*P (* ⟹[ l ] ` Q) v
    with ground? Q
  ... | yes gQ = lem-project l gQ v
  ... | no ¬gQ
    rewrite eq-*P (rvalue v) l ¬gQ
    with project (lvalue v) l (ground-Ground Q)
      | R.⟦ R.⌈ * ⟹[ l ] (` ground Q) ⌉ ⟧ (rvalue v)
      | lem-project l (ground-Ground Q) v
  ... | .(raise  _) | .(raise  _) | raise l'  = raise l'
  ... | .(return _) | .(return _) | return v'
    with lem-proxy v' ((` ground Q) ⟹[ l ] (` Q)) (⌣sym (ground-⌣ Q))
  ... | _ , eq , v'' rewrite eq = return v''
  
  lem-P* : ∀ {P lv rv}
    → (c : Cast (` P) *)
    → ValueRelate lv rv
    → CastResultRelate (L.apply-cast c lv)
                       (R.⟦ R.⌈ c ⌉ ⟧ rv)
  lem-P* (` P ⟹[ l ] *) v with ground? P
  ... | yes gP rewrite eq-I* (rvalue v) l gP = return (dyn gP v)
  ... | no ¬gP rewrite eq-P* (rvalue v) l ¬gP
    with lem-proxy v (` P ⟹[ l ] ` ground P) (ground-⌣ P)
  ... | _ , eq , v'
    rewrite eq | eq-I* (rvalue v') l (ground-Ground P)
    = return (dyn (ground-Ground P) v')
  
  lem-⟦_⟧ : ∀ {S T lv rv}
          → (c : Cast S T)
          → ValueRelate lv rv
          → CastResultRelate (L.apply-cast c lv)
                             (R.⟦ R.⌈ c ⌉ ⟧ rv)
  lem-⟦ *   ⟹[ l ] *   ⟧ v rewrite eq-** l (rvalue v) = return v
  lem-⟦ *   ⟹[ l ] ` Q ⟧ v = lem-*P (* ⟹[ l ] ` Q) v
  lem-⟦ ` P ⟹[ l ] *   ⟧ v = lem-P* (` P ⟹[ l ] *) v
  lem-⟦ ` P ⟹[ l ] ` Q ⟧ v with (` P) ⌣? (` Q)
  ... | no ¬P⌣Q rewrite eq-¬⌣ (rvalue v) l ¬P⌣Q = raise l
  ... | yes P⌣Q with lem-proxy v ((` P) ⟹[ l ] (` Q)) P⌣Q
  ... | _ , eq , v' rewrite eq = return v'            
