open import Types
open import R.BlameStrategies
open import S.CastADT
open import Bisimulation.ApplyCastBisimulate

module Bisimulation.BisimulationProof
  (Label : Set)
  (BS : BlameStrategy Label)
  (CADT : CastADT Label (BlameStrategy.Injectable BS))
  (CADTB : CastADTBasic Label (BlameStrategy.Injectable BS) CADT)
  (lem-⌈_⌉ : the-apply-cast-lemma Label BS CADT)
  where

open BlameStrategy BS using (Injectable)
open import Variables using (∅)
open import Terms Label
open import Cast Label
open import Observables Label
open import Error using (Error; return; raise; _>=>_; _>>=_; >>=-return)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Bisimulation.Bisimulation using (_∷_; [])
open import Bisimulation.BisimulationRelation Label BS CADT
  renaming (module L to L'; module R to R')

module L where
  open L' hiding (_++_; ⟦_⟧) public
  
  -- inteprete cast lists
  ⟦_⟧ : ∀ {T1 T2}
    → CastList T1 T2
    → (Value T1 → Error Label (Value T2))
  ⟦ [] ⟧ = return
  ⟦ x ∷ xs ⟧ = L'.⟦ x ⟧ >=> ⟦ xs ⟧

  lem-id : ∀ {T}
    → (v : Value T)
    → ⟦ [] ⟧ v ≡ return v
  lem-id v = refl

  lem-seq : ∀ {T1 T2 T3}
    → (xs : CastList T1 T2)
    → (ys : CastList T2 T3)
    → (∀ v → ⟦ xs ++ ys ⟧ v ≡ (⟦ xs ⟧ >=> ⟦ ys ⟧) v)
  lem-seq [] ys v = refl
  lem-seq (x ∷ xs) ys v with L'.⟦ x ⟧ v
  ... | return v' = lem-seq xs ys v'
  ... | raise l = refl

module R where
  open R' public
  open CastADTBasic CADTB public

lem-⟦_⟧ : ∀ {T1 T2 lv rv lc rc}
  → CastListRelate {T1} {T2} lc rc
  → ValueRelate {T1} lv rv
  → CastResultRelate (L.⟦ lc ⟧ lv) (R.⟦ rc ⟧ rv)
lem-⟦ id ⟧ v
  rewrite R.lem-id (rvalue v)
    = return v
lem-⟦ just c ⟧ v
  rewrite >>=-return (L'.⟦ c ⟧ (lvalue v))
    = lem-⌈ c ⌉ v
lem-⟦ c1 ⨟ c2 ⟧ v
  rewrite L.lem-seq (lcast c1) (lcast c2) (lvalue v)
        | R.lem-seq (rcast c1) (rcast c2) (rvalue v)
  with L.⟦ lcast c1 ⟧ (lvalue v) | R.⟦ rcast c1 ⟧ (rvalue v) | lem-⟦ c1 ⟧ v
... | .(return _) | .(return _) | return v' = lem-⟦ c2 ⟧ v'
... | .(raise _)  | .(raise _)  | raise l   = raise l

open L using (error; halt; cont; expr; it)
open R using (error; halt; cont; expr; it; [□⟨_⟩]_)

load : ∀ {T} → (e : ∅ ⊢ T) → StateRelate (L.load e) (R.load e)
load e = return (expr e [] ([□⟨ id ⟩] □))

observe : ∀ {T}
  → {lv : L.Value T}
  → {rv : R.Value T}
  → ValueRelate lv rv
  → L.observe lv ≡ R.observe rv
observe (dyn Pi v) = refl
observe #t = refl
observe #f = refl
observe (lam⟨ [] , c ⇒ d ⟩ e E) = refl
observe (lam⟨ lcs ⟪ lc , c ⇒ d ⟩ e E) = refl
observe (cons⟨ [] , c ⊗ d ⟩ v1 v2) = refl
observe (cons⟨ lcs ⟪ lc , c ⊗ d ⟩ v1 v2) = refl

view-cont-++ : ∀ {T1 T2 T3 Z}
  → (cs : CastList T1 T2)
  → (ds : CastList T2 T3)
  → (k  : L.Cont T3 Z)
  → view-cont cs (view-cont ds k) ≡ view-cont (cs ++ ds) k
view-cont-++ []       ds k = refl
view-cont-++ (c ∷ cs) ds k rewrite view-cont-++ cs ds k = refl

-- the next two lemmas are not useful yet in formal proof
lemma-mk-cont : ∀ {T1 T2}
  → {lk : L.Cont T1 T2}
  → {rk : R.PreCont T1 T2}
  → PreContRelate lk rk
  → ContRelate lk (R.mk-cont rk)
lemma-mk-cont k = [□⟨ id ⟩] k

lemma-ext-cont : ∀ {T1 T2 T3}
  → {lc : CastList T1 T2}
  → {rc : R.Cast T1 T2}
  → CastListRelate lc rc
  → {lk : L.Cont T2 T3}
  → {rk : R.Cont T2 T3}
  → ContRelate lk rk
  → ContRelate (view-cont lc lk) (R.ext-cont rc rk)
lemma-ext-cont c ([□⟨ d ⟩] k)
  rewrite view-cont-++ (lcast c) (lcast d) (lprecont k)
  = [□⟨ c ⨟ d ⟩] k

lem->>= : ∀ {T1 T2 lr rr}
  → CastResultRelate {T1} lr rr
  → {lf : L.Value T1 → L.State T2}
  → {rf : R.Value T1 → R.State T2}
  → (f : ∀ {lv rv} → ValueRelate {T1} lv rv → StateRelate (lf lv) (rf rv))
  → StateRelate (lr >>= lf) (rr >>= rf)
lem->>= (return v) f = f v
lem->>= (raise l)  f = raise l

done : ∀ {T}
  → {lS : L.State T}
  → {rS : R.State T}
  → StateRelate lS rS
  → ∃[ lS' ]
    ∃[ rS' ]
      (lS L.—→* lS' ×
       rS R.—→* rS' ×
       StateRelate lS' rS')
done S = _ , _ , [] , [] , S

step : ∀ {T}
  → {lS lS' : L.State T}
  → {rS rS' : R.State T}
  → (lS L.—→* lS')
  → (rS R.—→* rS')
  → ∃[ lS'' ]
    ∃[ rS'' ]
      (lS' L.—→* lS'' ×
       rS' R.—→* rS'' ×
       StateRelate lS'' rS'')
  → ∃[ lS'' ]
    ∃[ rS'' ]
      (lS L.—→* lS'' ×
       rS R.—→* rS'' ×
       StateRelate lS'' rS'')
step lxs rxs (_ , _ , lys , rys , S) = _ , _ , (lxs L'.++ lys) , (rxs R.++ rys) , S

cnd : ∀ {A lv rv} → ValueRelate {` B} lv rv → (x y : A)
  → L.cnd lv x y ≡ R.cnd rv x y
cnd #t x y = refl
cnd #f x y = refl

lem-L-apply-cont : ∀ {T1 T2 T3}
  → (v : L.Value T1)
  → (cs : CastList T1 T2)
  → (k : L.Cont T2 T3)
  → (L.apply-cont v (view-cont cs k))
    L.—→*
    (L.⟦ cs ⟧ v >>= λ v' → (L.apply-cont v' k))
lem-L-apply-cont v [] k = []
lem-L-apply-cont v (c ∷ cs) k with L'.⟦ c ⟧ v
... | return v' = it (cont v' (view-cont cs k)) ∷ lem-L-apply-cont v' cs k 
... | raise l = []

++-assoc : ∀ {T1 T2 T3 T4}
  → (xs : CastList T1 T2)
  → (ys : CastList T2 T3)
  → (zs : CastList T3 T4)
  → (xs ++ (ys ++ zs)) ≡ ((xs ++ ys) ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

lemma-L-do-app : ∀ {S1 T1 S2 T2 T}
  → (f  : L.Value (` S1 ⇒ T1))
  → (cs : FCastList S1 T1 S2 T2)
  → (a  : L.Value S2)
  → (k  : L.Cont T2 T)
  → (L.do-app (view-lambda f cs) a k)
      L.—→*
    (L.⟦ dom cs ⟧ a >>= λ v → (L.do-app f v (view-cont (cod cs) k)))
lemma-L-do-app f []       a k = L.[]
lemma-L-do-app f (cs ⟪ (` S1 ⇒ T1 ⟹[ l ] ` S2 ⇒ T2)) a k
  = it (cont _ _) ∷ next
  where
  next : (L'.⟦ S2 ⟹[ l ] S1 ⟧ a
          >>= λ v →
          (return (L.cont v (L.[ L.app₂ (view-lambda f cs) ]
                             L.[ L.□⟨ T1 ⟹[ l ] T2 ⟩ ] k))))
           L.—→*
         (L'.⟦ S2 ⟹[ l ] S1 ⟧ a
          >>= L.⟦ dom cs ⟧
          >>= λ v →
          L.do-app f v (view-cont (cod cs ++ ((T1 ⟹[ l ] T2) ∷ [])) k))
  next with L'.⟦ S2 ⟹[ l ] S1 ⟧ a
  next | raise l  = L.[]
  next | return v
    rewrite sym (view-cont-++ (cod cs) ((T1 ⟹[ l ] T2) ∷ []) k)
    = it (cont _ _) ∷ lemma-L-do-app f cs v (L.[ L.□⟨ T1 ⟹[ l ] T2 ⟩ ] k)

do-app : ∀ {T1 T2 Z lv1 rv1 lv2 rv2 lk rk}
  → ValueRelate {` T1 ⇒ T2} lv1 rv1
  → ValueRelate {T1} lv2 rv2
  → ContRelate lk rk
  → ∃[ lS' ]
    ∃[ rS' ]
      (L.do-app lv1 lv2 lk L.—→* lS' ×
       R.do-app rv1 rv2 rk R.—→* rS' ×
       StateRelate {Z} lS' rS')
do-app (lam⟨ lcs , c1 ⇒ c2 ⟩ e E) a k
  = step (lemma-L-do-app (L.lam e (lenv E)) lcs (lvalue a) (lcont k))
         []
         (done (lem->>= (lem-⟦ c1 ⟧ a)
                        λ v → return (expr e (v ∷ E) (lemma-ext-cont c2 k))))

lem-L-do-car : ∀ {T1 T2 T3 T4 Z}
  → (v1 : L.Value T1)
  → (v2 : L.Value T2)
  → (cs : PCastList T1 T2 T3 T4)
  → (k : L.Cont T3 Z)
  → (L.do-car (view-cons (L.cons v1 v2) cs) k)
      L.—→*
    (L.⟦ lft cs ⟧ v1 >>= λ v' → (return (cont v' k)))
lem-L-do-car v1 v2 []       k = []
lem-L-do-car v1 v2 (cs ⟪ ((` T1 ⊗ T2) ⟹[ l ] (` T3 ⊗ T4))) k
  with lem-L-do-car v1 v2 cs (view-cont ((T1 ⟹[ l ] T3) ∷ []) k)
... | IH
  rewrite L.lem-seq (lft cs) ((T1 ⟹[ l ] T3) ∷ []) v1
  = it (cont _ _) ∷ (IH L'.++ next)
  where
    next : (L.⟦ lft cs ⟧ v1 >>=
       (λ v' → return (cont v' (L.[ L.□⟨ T1 L.⟹[ l ] T3 ⟩ ] k))))
      L.—→*
      ((L.⟦ lft cs ⟧ v1 >>= (λ x → L'.⟦ T1 L.⟹[ l ] T3 ⟧ x >>= return))
       >>= (λ v' → return (cont v' k)))
    next
      with L.⟦ lft cs ⟧ v1
    ... | raise l' = []
    ... | return v1'
      rewrite >>=-return (L'.⟦ T1 ⟹[ l ] T3 ⟧ v1')
      = it (cont _ _) ∷ []

do-car : ∀ {T1 T2 Z lv rv lk rk}
  → ValueRelate {` T1 ⊗ T2} lv rv
  → ContRelate lk rk
  → ∃[ lS' ]
    ∃[ rS' ]
      (L.do-car lv lk L.—→* lS' ×
       R.do-car rv rk R.—→* rS' ×
       StateRelate {Z} lS' rS')
do-car (cons⟨ lcs , c1 ⊗ c2 ⟩ v1 v2) k
  = step (lem-L-do-car (lvalue v1) (lvalue v2) lcs (lcont k)) []
         (done (lem->>= (lem-⟦ c1 ⟧ v1) λ v1' → return (cont v1' k)))

lem-L-do-cdr : ∀ {T1 T2 T3 T4 Z}
  → (v1 : L.Value T1)
  → (v2 : L.Value T2)
  → (cs : PCastList T1 T2 T3 T4)
  → (k : L.Cont T4 Z)
  → (L.do-cdr (view-cons (L.cons v1 v2) cs) k)
      L.—→*
    (L.⟦ rht cs ⟧ v2 >>= λ v' → (return (cont v' k)))
lem-L-do-cdr v1 v2 []       k = []
lem-L-do-cdr v1 v2 (cs ⟪ ((` T1 ⊗ T2) ⟹[ l ] (` T3 ⊗ T4))) k
  with lem-L-do-cdr v1 v2 cs (view-cont ((T2 ⟹[ l ] T4) ∷ []) k)
... | IH
  rewrite L.lem-seq (rht cs) ((T2 ⟹[ l ] T4) ∷ []) v2
  = it (cont _ _) ∷ (IH L'.++ next)
  where
    next : (L.⟦ rht cs ⟧ v2 >>=
       (λ v' → return (cont v' (L.[ L.□⟨ T2 ⟹[ l ] T4 ⟩ ] k))))
      L.—→*
      ((L.⟦ rht cs ⟧ v2 >>= (λ x → L'.⟦ T2 ⟹[ l ] T4 ⟧ x >>= return))
       >>= (λ v' → return (cont v' k)))
    next
      with L.⟦ rht cs ⟧ v2
    ... | raise l' = []
    ... | return v'
      rewrite >>=-return (L'.⟦ T2 ⟹[ l ] T4 ⟧ v')
      = it (cont _ _) ∷ []

do-cdr : ∀ {T1 T2 Z lv rv lk rk}
  → ValueRelate {` T1 ⊗ T2} lv rv
  → ContRelate lk rk
  → ∃[ lS' ]
    ∃[ rS' ]
      (L.do-cdr lv lk L.—→* lS' ×
       R.do-cdr rv rk R.—→* rS' ×
       StateRelate {Z} lS' rS')
do-cdr (cons⟨ lcs , c1 ⊗ c2 ⟩ v1 v2) k
  = step (lem-L-do-cdr (lvalue v1) (lvalue v2) lcs (lcont k)) []
         (done (lem->>= (lem-⟦ c2 ⟧ v2) λ v' → return (cont v' k)))

apply-cont : ∀ {T1 T2 lv rv lk rk}
  → ValueRelate {T1} lv rv
  → PreContRelate {T2} lk rk
  → ∃[ lS' ]
    ∃[ rS' ]
      (L.apply-cont lv lk L.—→* lS' ×
       R.apply-cont rv rk R.—→* rS' ×
       StateRelate lS' rS')
apply-cont v □ = done (return (halt v))
apply-cont v ([ app₁ e E ] k) = done (return (expr e E ([□⟨ id ⟩] [ app₂ v ] k)))
apply-cont v ([ app₂ v1 ] k)  = do-app v1 v k
apply-cont v ([ if₁ e2 e3 E ] k)
  with L.cnd (lvalue v) e2 e3 | R.cnd (rvalue v) e2 e3 | cnd v e2 e3
... | e | e | refl = done (return (expr e E k))
apply-cont v ([ cons₁ e2 E ] k)
  = done (return (expr e2 E ([□⟨ id ⟩] [ cons₂ v ] k)))
apply-cont v ([ cons₂ v1 ] k)
  = done (return (cont (cons⟨ [] , id ⊗ id ⟩ v1 v) k))
apply-cont v ([ car₁ ] k) = do-car v k
apply-cont v ([ cdr₁ ] k) = do-cdr v k

progress : ∀ {T}
  → {lS : L.State T}(lSp : L.Progressing lS)
  → {rS : R.State T}(rSp : R.Progressing rS)
  → StateRelate lS rS
  → ∃[ lS' ]
    ∃[ rS' ]
      (L.progress lSp L.—→* lS' ×
       R.progress rSp R.—→* rS' ×
       StateRelate lS' rS')
progress (expr (var x) lE lK)
         (expr (var x) rE rK)
         (return (expr (var x) E K))
         = done (return (cont (lookup E x) K))
progress (expr #t lE lK)
         (expr #t rE rK)
         (return (expr #t E K))
         = done (return (cont #t K))
progress (expr #f lE lK)
         (expr #f rE rK)
         (return (expr #f E K))
         = done (return (cont #f K))
progress (expr (if e e₁ e₂) lE lK)
         (expr (if e e₁ e₂) rE rK)
         (return (expr (if e e₁ e₂) E K))
         = done (return (expr e E (lemma-mk-cont ([ if₁ e₁ e₂ E ] K))))
progress (expr (lam e) lE lK)
         (expr (lam e) rE rK)
         (return (expr (lam e) E K))
         = done (return (cont (lam⟨ [] , id ⇒ id ⟩ e E) K))
progress (expr (app e e₁) lE lK)
         (expr (app e e₁) rE rK)
         (return (expr .(app e e₁) E K))
         = done (return (expr e E (lemma-mk-cont ([ app₁ e₁ E ] K))))
progress (expr (cons e e₁) lE lK)
         (expr (cons e e₁) rE rK)
         (return (expr .(cons e e₁) E K))
         = done (return (expr e E ((lemma-mk-cont ([ cons₁ e₁ E ] K)))))
progress (expr (e ⟨ c ⟩) lE lK)
         (expr (e ⟨ c ⟩) rE rK)
         (return (expr (e ⟨ c ⟩) E K))
         = done (return (expr e E (lemma-ext-cont (just c) K)))
progress (expr (car e) lE lK)
         (expr (car e) rE rK)
         (return (expr (car e) E K))
         = done (return (expr e E (lemma-mk-cont ([ car₁ ] K))))
progress (expr (cdr e) lE lK)
         (expr (cdr e) rE rK)
         (return (expr (cdr e) E K))
         = done (return (expr e E (lemma-mk-cont ([ cdr₁ ] K))))
-- progress (expr (blame l) lE lK)
--          (expr (blame l) rE rK)
--          (return (expr (blame l) E K))
--          = done (raise l)
progress (cont lv lk)
         (cont rv rk)
         (return (cont v k))
  with lk | rk | k
... | .(view-cont (lcast c) (lprecont k'))
    | .([□⟨ rcast c ⟩] rprecont k')
    | [□⟨ c ⟩] k'
  with lem-L-apply-cont lv (lcast c) (lprecont k')
... | lS⟼lS'
  with L.⟦ (lcast c) ⟧ (lvalue v) | R.⟦ (rcast c) ⟧ (rvalue v)
    | lem-⟦ c ⟧ v
... | .(raise _)  | .(raise _)  | raise l   = step lS⟼lS' [] (done (raise l))
... | .(return _) | .(return _) | return v' = step lS⟼lS' [] (apply-cont v' k')

final-or-progressing : ∀ {T}
  → {ls : L.State T}
  → {rs : R.State T}
  → StateRelate ls rs
  → (L.Final ls × R.Final rs)
    ⊎
    (L.Progressing ls × R.Progressing rs)
final-or-progressing (return (expr e E K))
  = inj₂ (expr e (lenv E) (lcont K) , expr e (renv E) (rcont K))
final-or-progressing (return (cont v K))
  = inj₂ (cont (lvalue v) (lcont K) , cont (rvalue v) (rcont K))
final-or-progressing (return (halt v))
  = inj₁ (halt (lvalue v) , halt (rvalue v))
final-or-progressing (raise l)
  = inj₁ (error l , error l)

-- the main lemma
safety : ∀ {T}
  → {ls : L.State T}
  → {rs : R.State T}
  → StateRelate ls rs
  → (L.Final ls × R.Final rs)
    ⊎
    (∃[ ls' ]
     ∃[ rs' ]
       (ls L.—→+ ls' ×
        rs R.—→+ rs' ×
        StateRelate ls' rs'))
safety S with final-or-progressing S
safety S | inj₁ (lSf , rSf) = inj₁ (lSf , rSf)
safety S | inj₂ (lSp , rSp) with progress lSp rSp S
safety S | inj₂ (lSp , rSp) | lS'' , rS'' , lS'⟼lS'' , rS'⟼rS'' , S''
  = inj₂ (lS'' , rS'' , (it lSp ∷ lS'⟼lS'') , (it rSp ∷ rS'⟼rS'') , S'')

module Foo {T : Type} where
  import Bisimulation.Bisimulation
  module CorrectnessTheorems =
    Bisimulation.Bisimulation.Theorems (L.system {T = T}) R.system StateRelate safety
  open CorrectnessTheorems using (thm-final-LR; thm-final-RL) public

correctness-l : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → L.Evalo e o
  ---
  → R.Evalo e o
correctness-l {e = e} (L.val xs) with Foo.thm-final-LR (load e) xs (halt _)
correctness-l {e = e} (L.val xs) | _ , ys , (R.halt rv) , return (halt v)
  rewrite observe v
  = R.val ys
correctness-l {e = e} (L.err xs) with Foo.thm-final-LR (load e) xs (error _)
correctness-l {e = e} (L.err xs) | _ , ys , (R.error l) , raise l
  = R.err ys

correctness-r : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → R.Evalo e o
  ---
  → L.Evalo e o
correctness-r {e = e} (R.val xs) with Foo.thm-final-RL (load e) xs (halt _)
correctness-r {e = e} (R.val xs) | _ , ys , (L.halt rv) , return (halt v)
  rewrite sym (observe v)
  = L.val ys
correctness-r {e = e} (R.err xs) with Foo.thm-final-RL (load e) xs (error _)
correctness-r {e = e} (R.err xs) | _ , ys , (L.error l) , raise l
  = L.err ys
