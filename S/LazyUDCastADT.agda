module S.LazyUDCastADT
  (Label : Set)  
  where

open import Types

open import Variables
open import Terms Label using (_⊢_)
open import Error
open import Cast Label using (_⟹[_]_)

open import X.BlameStrategies Label using (BlameStrategy; LazyUDBS)
open BlameStrategy LazyUDBS using (Injectable)

open import S.CastADT Label Injectable
import S.Values using (Env; Value; dyn; #t; #f; lam⟨_⇒_⟩; cons⟨_⊗_⟩)

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_; yes; no)

record LazyUD (ADT : CastADT) : Set where
  open CastADT ADT
  open S.Values Label Injectable Cast
  field      
    eq-¬⌣ : ∀ {T1 T2}
      → (v : Value T1)
      → (l : Label)
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
      → (l : Label)
      → ¬ Ground P
      → ⟦ ⌈ (` P) ⟹[ l ] * ⌉ ⟧ v
          ≡
        ⟦ ⌈ (` P) ⟹[ l ] (` ground P) ⌉ ⟧ v >>= ⟦ ⌈ (` ground P) ⟹[ l ] * ⌉ ⟧

    eq-I* : ∀ {P}
      → (v : Value (` P))
      → (l : Label)
      → (gP : Ground P)
      → ⟦ ⌈ ` P ⟹[ l ] * ⌉ ⟧ v
          ≡
        return (dyn P gP v)

    eq-*P : ∀ {P}
      → (v : Value *)
      → (l : Label)
      → ¬ Ground P
      → ⟦ ⌈ * ⟹[ l ] (` P) ⌉ ⟧ v
          ≡
        ⟦ ⌈ * ⟹[ l ] (` ground P) ⌉ ⟧ v >>= ⟦ ⌈ (` ground P) ⟹[ l ] (` P) ⌉ ⟧
      
    eq-*I-succ : ∀ {P}
      → (v : Value (` P))
      → (l : Label)
      → (gP : Ground P)
      → ⟦ ⌈ * ⟹[ l ] (` P) ⌉ ⟧ (dyn P gP v)
          ≡
        return v
    
    eq-*I-fail : ∀ {P Q}
      → (v : Value (` P))  
      → (l : Label)
      → (gP : Ground P)
      → (gQ : Ground Q)
      → ¬ (` P) ≡ (` Q)
      → ⟦ ⌈ * ⟹[ l ] (` Q) ⌉ ⟧ (dyn P gP v)
          ≡
        raise l

    eq-B : ∀ l b
      → ⟦ ⌈ (` B) ⟹[ l ] (` B) ⌉ ⟧ b
          ≡
        return b

    eq-⇒ : ∀ T21 T22 T11 T12
      → ∀ {S T}
      → (l : Label)
      → {Γ : Context}
      → (c₁ : Cast T11 S)
      → (c₂ : Cast T T12)
      → (e : (Γ , S) ⊢ T)
      → (E : Env Γ)
      → ⟦ ⌈ (` T11 ⇒ T12) ⟹[ l ] (` T21 ⇒ T22) ⌉ ⟧ (lam⟨ c₁ ⇒ c₂ ⟩ e E)
          ≡
        return (lam⟨ ⌈ T21 ⟹[ l ] T11 ⌉ ⨟ c₁ ⇒ c₂ ⨟ ⌈ T12 ⟹[ l ] T22 ⌉ ⟩ e E)

    eq-⊗ : ∀ T21 T22 T11 T12
      → ∀ {S T}
      → (l : Label)
      → (c₁ : Cast S T11)
      → (c₂ : Cast T T12)
      → (v1 : Value S)
      → (v2 : Value T)
      → ⟦ ⌈ (` T11 ⊗ T12) ⟹[ l ] (` T21 ⊗ T22) ⌉ ⟧ (cons⟨ c₁ ⊗ c₂ ⟩ v1 v2)
          ≡
        return (cons⟨ c₁ ⨟ ⌈ T11 ⟹[ l ] T21 ⌉ ⊗ c₂ ⨟ ⌈ T12 ⟹[ l ] T22 ⌉ ⟩ v1 v2)
