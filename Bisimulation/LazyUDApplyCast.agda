open import X.BlameStrategies using (BlameStrategy; LazyUDBS)
open import S.CastADT
open import S.LazyUDCastADT using (LazyUD)

module Bisimulation.LazyUDApplyCast
  (Label : Set)
  (CADT : CastADT Label (BlameStrategy.Injectable (LazyUDBS Label)))
  (CADTLazyUD : LazyUD Label CADT)
  where

open import Types
open import Bisimulation.BisimulationRelation Label (LazyUDBS Label) CADT
open import Error
open import Cast Label using (Cast; _⟹[_]_)
open LazyUD CADTLazyUD

open import Relation.Nullary using (yes; no)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_ ; ∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)

open X.BlameStrategies.LazyUD Label using (project)

lem-project : ∀ {Q lv rv}
  → (l : Label)
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
         ValueRelate (L.add-proxy lv c p) ru
      )
lem-proxy v (` B ⟹[ l ] ` B) ⌣B rewrite eq-B l (rvalue v) = _ , refl , v
lem-proxy (lam⟨ lcs , c1 ⇒ c2 ⟩ e E) (` S1 ⇒ T1 ⟹[ l ] ` S2 ⇒ T2) ⌣⇒
  rewrite eq-⇒ S2 T2 S1 T1 l (rcast c1) (rcast c2) e (renv E)
  = _ , refl
  , lam⟨ lcs ⟪ _ , just (S2 ⟹[ l ] S1) ⨟ c1 ⇒ c2 ⨟ just (T1 ⟹[ l ] T2) ⟩ e E
lem-proxy (cons⟨ lcs , c1 ⊗ c2 ⟩ v1 v2) (` L1 ⊗ R1 ⟹[ l ] ` L2 ⊗ R2) ⌣⊗
  rewrite eq-⊗ L2 R2 L1 R1 l (rcast c1) (rcast c2) (rvalue v1) (rvalue v2)
  = _ , refl
  , cons⟨ lcs ⟪ _ , c1 ⨟ just (L1 ⟹[ l ] L2) ⊗ c2 ⨟ just (R1 ⟹[ l ] R2) ⟩ v1 v2

lem-*P : ∀ {P lv rv}
  → (c : Cast * (` P))
  → ValueRelate lv rv
  → CastResultRelate (L.⟦ c ⟧ lv)
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
  → CastResultRelate (L.⟦ c ⟧ lv)
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
    → CastResultRelate (L.⟦ c ⟧ lv)
                       (R.⟦ R.⌈ c ⌉ ⟧ rv)
lem-⟦ *   ⟹[ l ] *   ⟧ v rewrite eq-** l (rvalue v) = return v
lem-⟦ *   ⟹[ l ] ` Q ⟧ v = lem-*P (* ⟹[ l ] ` Q) v
lem-⟦ ` P ⟹[ l ] *   ⟧ v = lem-P* (` P ⟹[ l ] *) v
lem-⟦ ` P ⟹[ l ] ` Q ⟧ v with (` P) ⌣? (` Q)
... | no ¬P⌣Q rewrite eq-¬⌣ (rvalue v) l ¬P⌣Q = raise l
... | yes P⌣Q with lem-proxy v ((` P) ⟹[ l ] (` Q)) P⌣Q
... | _ , eq , v' rewrite eq = return v'
