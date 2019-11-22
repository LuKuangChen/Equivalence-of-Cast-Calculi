module X.BlameStrategies
  (Label : Set)
  where

open import Types

open import X.Values Label
open import Cast Label
open import Error Label

record BlameStrategy : Set₁ where
  field
    Injectable : PreType → Set
    apply-cast : ∀ {S T}
      → Val Injectable S
      → Cast S T
      → CastResult Injectable T

module LazyD where
  open import Types
  open import Data.Unit using (⊤; tt)
  open import Relation.Nullary using (yes; no)

  I? : PreType → Set
  I? P = ⊤
  
  apply-cast' : ∀ {P Q} → Val I? (` P) → Cast (` P) (` Q) → CastResult I? (` Q)
  apply-cast' v (it l (` P) (` Q)) with (` P) ⌣? (` Q)
  ... | yes p = just (proxy v (it l (` P) (` Q)) p)
  ... | no ¬p = error l

  apply-cast : ∀ {S T} → Val I? S → Cast S T → CastResult I? T
  apply-cast v (it l * *) = just v
  apply-cast v (it l (` P) *) = just (dyn P tt v)
  apply-cast v (it l (` P) (` Q)) = apply-cast' v (it l (` P) (` Q))
  apply-cast (dyn P I v) (it l * (` Q)) = apply-cast' v (it l (` P) (` Q))

LazyDBS : BlameStrategy
LazyDBS = record { Injectable = LazyD.I? ; apply-cast = LazyD.apply-cast }

module LazyUD where
  open import Types

  I? : PreType → Set
  I? = Ground

  open import Relation.Nullary using (yes; no)
  open import Relation.Binary.PropositionalEquality using (refl)

  project : Val I? * → Label → (Q : PreType) → Ground Q → CastResult I? (` Q)
  project (dyn P Pg v) l Q Qg with (` P) ≡? (` Q)
  ... | yes refl = just v
  ... | no ¬p = error l
  
  apply-cast : ∀ {S T} → Val I? S → Cast S T → CastResult I? T
  apply-cast v (it l * *) = just v
  apply-cast v (it l (` P) *) with ground? P
  ... | yes Pg = just (dyn P Pg v)
  ... | no ¬Pg = just (dyn _ (ground-Ground P)
                      (proxy v (it l (` P) (` ground P)) (ground-⌣ P)))
  apply-cast v (it l (` P) (` Q)) with (` P) ⌣? (` Q)
  ... | yes p = just (proxy v (it l (` P) (` Q)) p)
  ... | no ¬p = error l
  apply-cast v (it l * (` Q)) with ground? Q
  apply-cast v (it l .* (` Q)) | yes Qg = project v l Q Qg
  apply-cast v (it l .* (` Q)) | no ¬Qg
    = project v l (ground Q) (ground-Ground Q) >>= λ u →
      just (proxy u (it l (` ground Q) (` Q)) (⌣sym (ground-⌣ Q)))

LazyUDBS : BlameStrategy
LazyUDBS = record { Injectable = LazyUD.I? ; apply-cast = LazyUD.apply-cast }
