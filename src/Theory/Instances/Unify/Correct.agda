{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Soundness: the substitution a derivation carries unifies its stack.  Lemmas use
   `Maybe`-valued predicates so failing cases are definitional; converse: see end of file. -}
open import Cubical.Foundations.Prelude
module Theory.Instances.Unify.Correct where

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.Properties using (discreteFin)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Unify.Term public

private variable k n m : ℕ

Unif : (Tm n → Tm m) → Stack n → Type ℓ-zero
Unif f [] = Unit
Unif f (p ∷ ps) = (f (p .fst) ≡ f (p .snd)) × Unif f ps

UnifM : (Tm n → Tm m) → Maybe (FStack n) → Type ℓ-zero
UnifM f nothing = Empty.⊥
UnifM f (just qs) = Unif f (unflexAll qs)


-- the only structural fact `flatSound` needs of a chain
applyFork : (τ : Steps k n m) (a b : Tm n)
  → applySteps τ (fork a b) ≡ fork (applySteps τ a) (applySteps τ b)
applyFork {k = zero} Eq.refl a b = refl
applyFork {k = suc k} {n = suc n} (x , w , τ) a b =
  applyFork τ (subst1 x w a) (subst1 x w b)


module _ {n m : ℕ} (f : Tm n → Tm m)
  (hfork : (a b : Tm n) → f (fork a b) ≡ fork (f a) (f b)) where

  pushSound : (e : Flex n) (acc : Maybe (FStack n)) → UnifM f (pushF e acc)
    → (f (var (e .fst)) ≡ f (e .snd)) × UnifM f acc
  pushSound e nothing ()
  pushSound e (just as) h = h

  flatSound : (t u : Tm n) (acc : Maybe (FStack n))
    → UnifM f (flatA t u acc) → (f t ≡ f u) × UnifM f acc
  flatSound (var x) (var y) acc h = onSame (discreteFin x y) h
    where
    onSame : (d : Dec (x ≡ y)) → UnifM f (sameF x y d acc)
      → (f (var x) ≡ f (var y)) × UnifM f acc
    onSame (yes e) h = cong (λ z → f (var z)) e , h
    onSame (no _) h = pushSound (x , var y) acc h
  flatSound (var x) leaf acc h = pushSound (x , leaf) acc h
  flatSound (var x) (fork a b) acc h = pushSound (x , fork a b) acc h
  flatSound leaf (var y) acc h = sym (r .fst) , r .snd
    where r = pushSound (y , leaf) acc h
  flatSound (fork a b) (var y) acc h = sym (r .fst) , r .snd
    where r = pushSound (y , fork a b) acc h
  flatSound leaf leaf acc h = refl , h
  flatSound leaf (fork _ _) acc ()
  flatSound (fork _ _) leaf acc ()
  flatSound (fork s₁ t₁) (fork s₂ t₂) acc h =
      hfork s₁ t₁ ∙∙ cong₂ fork (l .fst) (r .fst) ∙∙ sym (hfork s₂ t₂)
    , r .snd
    where
    l = flatSound s₁ s₂ (flatA t₁ t₂ acc) h
    r = flatSound t₁ t₂ acc (l .snd)


unifStack : (g : Tm n → Tm m) (x : Fin (suc n)) (w : Tm n) (rs : Stack (suc n))
  → Unif g (applyStack x w rs) → Unif (λ t → g (subst1 x w t)) rs
unifStack g x w [] h = h
unifStack g x w (p ∷ rs) h = h .fst , unifStack g x w rs (h .snd)

unifSplit : (f : Tm n → Tm m) (as bs : Stack n)
  → Unif f (as ++ bs) → Unif f as × Unif f bs
unifSplit f [] bs h = tt , h
unifSplit f (p ∷ as) bs h = (h .fst , r .fst) , r .snd
  where r = unifSplit f as bs (h .snd)


-- McBride's two occurs-check facts: `thick` loses exactly its own variable,
-- and `check` returns what substituting for that variable produces.
thickxx : (x : Fin (suc n)) → thick x x ≡ nothing
thickxx zero = refl
thickxx {zero} (suc ())
thickxx {suc n} (suc x) = cong sucM (thickxx x)

substVar : (x : Fin (suc n)) (w : Tm n) → subst1 x w (var x) ≡ w
substVar x w = cong (forM w) (thickxx x)

Eqm : Tm n → Maybe (Tm n) → Type ℓ-zero
Eqm t nothing = Unit
Eqm t (just v) = t ≡ v

checkSubst : (x : Fin (suc n)) (w : Tm n) (u : Tm (suc n))
  → Eqm (subst1 x w u) (check x u)
checkSubst {n} x w (var y) = onThick (thick x y)
  where
  onThick : (c : Maybe (Fin n)) → Eqm (forM w c) (varM c)
  onThick nothing = tt
  onThick (just y') = refl
checkSubst x w leaf = refl
checkSubst {n} x w (fork s t) =
  onBoth (subst1 x w s) (subst1 x w t) (check x s) (check x t)
    (checkSubst x w s) (checkSubst x w t)
  where
  onBoth : (a b : Tm n) (ca cb : Maybe (Tm n))
    → Eqm a ca → Eqm b cb → Eqm (fork a b) (forkM ca cb)
  onBoth a b nothing cb _ _ = tt
  onBoth a b (just _) nothing _ _ = tt
  onBoth a b (just a') (just b') p q = cong₂ fork p q

substCheck : (x : Fin (suc n)) (u : Tm (suc n)) (w : Tm n)
  → checked n (check x u) w → subst1 x w u ≡ w
substCheck {n} x u w c = join (subst1 x w u) (check x u) (checkSubst x w u) c
  where
  join : (t : Tm n) (cm : Maybe (Tm n)) → Eqm t cm → checked n cm w → t ≡ w
  join t nothing _ ()
  join t (just v) p q = p ∙ q


mguUnifies : (n : ℕ) (ps : Stack n) (d : Sol n ps)
  → Unif (applyA (mgu n ps d)) ps
mguFlatU : (n : ℕ) (fl : Maybe (FStack n)) (ps : Stack n) (d : onFlat n fl ps)
  → UnifM (applyA (mguFlat n fl ps d)) fl
  × Unif (applyA (mguFlat n fl ps d)) ps
mguFlexU : (n : ℕ) (x : Fin n) (u : Tm n) (qs : FStack n) (ps : Stack n)
  (d : flexAt n x u qs ps)
  → (applyA (mguFlexAt n x u qs ps d) (var x)
     ≡ applyA (mguFlexAt n x u qs ps d) u)
  × Unif (applyA (mguFlexAt n x u qs ps d)) (unflexAll qs)
  × Unif (applyA (mguFlexAt n x u qs ps d)) ps

mguUnifies n [] d = tt
mguUnifies n (p ∷ ps) d =
    flatSound (applyA s) (applyFork (s .snd .snd))
      (p .fst) (p .snd) (just []) (r .fst) .fst
  , r .snd
  where
  s = mguFlat n (flat1 p) ps d
  r = mguFlatU n (flat1 p) ps d

mguFlatU n (just []) ps d = tt , mguUnifies n ps d
mguFlatU n (just (e ∷ qs)) ps d = (r .fst , r .snd .fst) , r .snd .snd
  where r = mguFlexU n (e .fst) (e .snd) qs ps d

mguFlexU (suc n) x u qs ps (assign w c d) = headEq , sp .fst , sp .snd
  where
  rest : Stack n
  rest = applyStack x w (unflexAll qs ++ ps)

  τ = mgu n rest d

  sp = unifSplit (λ t → applyA τ (subst1 x w t)) (unflexAll qs) ps
    (unifStack (applyA τ) x w (unflexAll qs ++ ps) (mguUnifies n rest d))

  headEq : applyA τ (subst1 x w (var x)) ≡ applyA τ (subst1 x w u)
  headEq = cong (applyA τ) (substVar x w ∙ sym (substCheck x u w c))


Unifier : (n : ℕ) → Stack n → Type ℓ-zero
Unifier n ps = Σ[ σ ∈ AList n ] Unif (applyA σ) ps

verified : (n : ℕ) (ps : Stack n) → Sol n ps → Unifier n ps
verified n ps d = mgu n ps d , mguUnifies n ps d


-- Known gap: the converse (`Unifier → Sol`) is owed rule by rule (`Ans-map&` is divariant).
--   CLASH: `flat1 p ≡ nothing` must refute `Unifier n (p ∷ ps)` — a page, no obstruction.
--   OCCURS: fails as stated — `u ≡ var x` makes both the check fail and the equation hold;
--     fix means `Flex n` carrying `u ≡ var x → ⊥`, which changes `Term`.
--   RESTRICTION: does not go through — an `AList` is a chain of scope-dropping assignments,
--     and `applyA σ ∘ var ∘ thin x` need not be one; at `n = 1` the restriction can be
--     `fork (var 0) (var 0)` while `AList 1` with target 1 is only the identity chain.
-- `Solvable` quantifies the spec over `Fin n → Tm m` instead of `AList n`, discharging all three;
-- the `n = 1` counterexample then refutes only chain-representability, not solvability.
