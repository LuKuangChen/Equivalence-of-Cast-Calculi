open import X.BlameStrategies using (BlameStrategy; LazyDBS)
open import S.CastADT
open import S.LazyDCastADT using (LazyD)

module Bisimulation.LazyDApplyCast
  (Label : Set)
  (CADT : CastADT Label (BlameStrategy.Injectable (LazyDBS Label)))
  (CADTLazyD : LazyD Label CADT)
  where

open import Types
open import Bisimulation.BisimulationRelation Label (LazyDBS Label) CADT
open import Cast Label using (Cast; _⟹[_]_)
open LazyD CADTLazyD

open import Relation.Nullary using (yes; no)
open import Data.Unit using (⊤; tt)

lem-⟦_⟧' : ∀ {P Q lv rv}
    → (c : Cast (` P) (` Q))
    → ValueRelate lv rv
    → CastResultRelate (L.⟦ c ⟧ lv)
                       (R.⟦ R.⌈ c ⌉ ⟧ rv)
lem-⟦_⟧' (` P ⟹[ l ] ` Q) v with (` P) ⌣? (` Q)
lem-⟦_⟧' (` B ⟹[ l ] ` B) v | yes ⌣B rewrite eq-B l (rvalue v) = return v
lem-⟦_⟧' (` T11 ⇒ T12 ⟹[ l ] ` T21 ⇒ T22) (lam⟨ lcs , c1 ⇒ c2 ⟩ e E) | yes ⌣⇒
  rewrite eq-⇒ T21 T22 T11 T12 l (rcast c1) (rcast c2) e (renv E)
  = return (lam⟨ lcs ⟪ _ , just (T21 ⟹[ l ] T11) ⨟ c1 ⇒ c2 ⨟ just (T12 ⟹[ l ] T22) ⟩ e E)
lem-⟦_⟧' (` T11 ⊗ T12 ⟹[ l ] ` T21 ⊗ T22) (cons⟨ lcs , c1 ⊗ c2 ⟩ v1 v2) | yes ⌣⊗
  rewrite eq-⊗ T21 T22 T11 T12 l (rcast c1) (rcast c2) (rvalue v1) (rvalue v2)
  = return (cons⟨ lcs ⟪ _ , c1 ⨟ just (T11 ⟹[ l ] T21) ⊗ c2 ⨟ just (T12 ⟹[ l ] T22) ⟩ v1 v2)
lem-⟦_⟧' (.(` _) ⟹[ l ] .(` _)) v | no ¬p
  rewrite eq-¬⌣ l ¬p (rvalue v)
  = raise l

lem-⟦_⟧ : ∀ {S T lv rv}
    → (c : Cast S T)
    → ValueRelate lv rv
    → CastResultRelate (L.⟦ c ⟧ lv)
                       (R.⟦ R.⌈ c ⌉ ⟧ rv)
lem-⟦_⟧ (*   ⟹[ l ] *)   v rewrite eq-** l (rvalue v) = return v
lem-⟦_⟧ (` P ⟹[ l ] *)   v rewrite eq-P* l (rvalue v) = return (dyn P _ v)
lem-⟦_⟧ (` P ⟹[ l ] ` Q) v = lem-⟦_⟧' (` P ⟹[ l ] ` Q) v
lem-⟦_⟧ (*   ⟹[ l ] ` Q) (dyn P tt v)
  rewrite eq-*P Q P l (rvalue v)
  = lem-⟦_⟧' (` P ⟹[ l ] ` Q) v
