module equivalence-of-cast-calculi.Bisimulation.LazyDCastADT
  (Label : Set)  
  where

open import equivalence-of-cast-calculi.Type
open import equivalence-of-cast-calculi.LabelUtilities Label
  renaming (negate-label×polarity to neg)
open import equivalence-of-cast-calculi.CC Label using (_⊢_; _⟹[_]_)
open import equivalence-of-cast-calculi.Error

open import equivalence-of-cast-calculi.R.BlameStrategies Label
  using (BlameStrategy; LazyDBS)
open BlameStrategy LazyDBS
  using (Injectable)

open import equivalence-of-cast-calculi.S.CastADT Label Injectable
import equivalence-of-cast-calculi.S.Value

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_; yes; no)

record IsLazyD (ADT : CastADT) : Set where
  open CastADT ADT
  open equivalence-of-cast-calculi.S.Value Label Injectable Cast
    using (Env; Value; dyn; #t; #f; lam⟨_⇒_⟩; cons⟨_⊗_⟩)
  field
    eq-¬⌣ : ∀ {T1 T2}
      → (l : Label×Polarity)
      → ¬ (T1 ⌣ T2)
      → (v : Value T1)
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
      → (l : Label×Polarity)
      → (v : Value (` P))  
      → ⟦ ⌈ (` P) ⟹[ l ] * ⌉ ⟧ v
          ≡
        return (dyn (same P) v)
      
    eq-*P : ∀ Q P l v
      → ⟦ ⌈ * ⟹[ l ] (` Q) ⌉ ⟧ (dyn (same P) v)
          ≡
        ⟦ ⌈ (` P) ⟹[ l ] (` Q) ⌉ ⟧ v

    eq-B : ∀ l v
      → ⟦ ⌈ (` B) ⟹[ l ] (` B) ⌉ ⟧ v
          ≡
        return v

    eq-⇒ : ∀ T21 T22 T11 T12
      → ∀ {S T} l {Γ}
      → (c₁ : Cast T11 S)
      → (c₂ : Cast T T12)
      → ∀ e
      → (E : Env Γ)
      → ⟦ ⌈ (` T11 ⇒ T12) ⟹[ l ] (` T21 ⇒ T22) ⌉ ⟧ (lam⟨ c₁ ⇒ c₂ ⟩ e E)
          ≡
        return (lam⟨ ⌈ T21 ⟹[ neg l ] T11 ⌉ ⨟ c₁ ⇒
                     c₂ ⨟ ⌈ T12 ⟹[ l ] T22 ⌉ ⟩
                 e E)

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
The following module proves that the ⟦_⟧ operator of every Lazy D Cast ADT
preserves the bisimulation (lem-⟦_⟧).
-}
module Theorems
  (CADT : CastADT)
  (CADTLazyD : IsLazyD CADT)
  where
  
  open import equivalence-of-cast-calculi.R.BlameStrategies using (BlameStrategy)
  open import equivalence-of-cast-calculi.Bisimulation.BisimulationRelation Label LazyDBS CADT
  open IsLazyD CADTLazyD

  lem-⟦_⟧' : ∀ {P Q lv rv}
           → (c : L.Cast (` P) (` Q))
           → ValueRelate lv rv
           → CastResultRelate (L.apply-cast c lv)
                              (R.⟦ R.⌈ c ⌉ ⟧ rv)
  lem-⟦_⟧' (` P ⟹[ l ] ` Q) v with (` P) ⌣? (` Q)
  lem-⟦_⟧' (` B ⟹[ l ] ` B) v | yes ⌣B rewrite eq-B l (rvalue v) = return v
  lem-⟦_⟧' (` T11 ⇒ T12 ⟹[ l ] ` T21 ⇒ T22) (lam⟨ lcs , c1 ⇒ c2 ⟩ e E) | yes ⌣⇒
    rewrite eq-⇒ T21 T22 T11 T12 l (rcast c1) (rcast c2) e (renv E)
    = return (lam⟨ lcs ⟪ _
                       , just (T21 ⟹[ neg l ] T11) ⨟ c1 ⇒ c2 ⨟ just (T12 ⟹[ l ] T22) ⟩
                   e E)
  lem-⟦_⟧' (` T11 ⊗ T12 ⟹[ l ] ` T21 ⊗ T22) (cons⟨ lcs , c1 ⊗ c2 ⟩ v1 v2) | yes ⌣⊗
    rewrite eq-⊗ T21 T22 T11 T12 l (rcast c1) (rcast c2) (rvalue v1) (rvalue v2)
    = return (cons⟨ lcs ⟪ _
                        , c1 ⨟ just (T11 ⟹[ l ] T21) ⊗ c2 ⨟ just (T12 ⟹[ l ] T22) ⟩
                    v1 v2)
  lem-⟦_⟧' (.(` _) ⟹[ l ] .(` _)) v | no ¬p
    rewrite eq-¬⌣ l ¬p (rvalue v)
    = raise l
  
  lem-⟦_⟧ : ∀ {S T lv rv}
          → (c : L.Cast S T)
          → ValueRelate lv rv
          → CastResultRelate (L.apply-cast c lv)
                             (R.⟦ R.⌈ c ⌉ ⟧ rv)
  lem-⟦_⟧ (*   ⟹[ l ] *)   v rewrite eq-** l (rvalue v) = return v
  lem-⟦_⟧ (` P ⟹[ l ] *)   v rewrite eq-P* l (rvalue v) = return (dyn (same P) v)
  lem-⟦_⟧ (` P ⟹[ l ] ` Q) v = lem-⟦_⟧' (` P ⟹[ l ] ` Q) v
  lem-⟦_⟧ (*   ⟹[ l ] ` Q) (dyn (same P) v)
    rewrite eq-*P Q P l (rvalue v)
    = lem-⟦_⟧' (` P ⟹[ l ] ` Q) v
                  
