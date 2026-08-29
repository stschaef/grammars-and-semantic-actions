{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- The first verified thing in the development: the substitution a
   derivation carries really does unify the stack the derivation is about.

   Everything here is ordinary Agda, as in `Term`.  Nothing in it is a
   fixpoint, a cover or an answer -- it is a fold over the same recursion
   `Sol` and `mgu` were defined by, and it is written here rather than in
   `Term` because `Term` is what the framework client reads and this is
   what the client's user reads.

   Three techniques carry the whole file.

   The predicate is `Unif`, defined by RECURSION -- "the head equation
   holds and so does the tail" -- which is the `All` of the statement, and
   the recursion is what makes `Unif f (applyStack x w rs)` and
   `Unif (f ∘ subst1 x w) rs` the same type up to a one-line induction
   rather than a transport.

   Every lemma about a partial function is stated over a `Maybe`-valued
   PREDICATE rather than over an equation: `Eqm t (check x u)` says "if the
   check succeeded its answer is `t`", `UnifM f (flatA t u acc)` says "if
   the flattening succeeded `f` unifies it".  A failing case is then `⊥` or
   `Unit` *definitionally*, and no clause ever inverts `just v ≡ just v'`
   or refutes `nothing ≡ just v`.  This is why `Term` names `sucM`, `varM`,
   `forkM`, `forM` and `sameF`: each lemma is a `cong` over one of them.

   The two McBride facts are `thick x x ≡ nothing` -- so the assignment's
   own variable really is replaced -- and `check x u ≡ just w` implies
   `subst1 x w u ≡ w` -- so the checked term really is the term with the
   variable gone.  Together they are the flexible rule's head equation, and
   the congruence closure's contribution is `flatSound`, which is
   derivation-independent: it holds for every `f` that commutes with
   `fork`.

   What is NOT here is the converse; see the end of the file, and the
   header of `Check` for why the converse cannot simply be added to the
   judgment. -}
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

-- `All` for a stack, by recursion: `f` makes both sides of every equation
-- equal.  The `Maybe`-lifted form is what every lemma about `flatA` is
-- stated over, and its failing case is `⊥` -- a flattening that clashed
-- has no unifier to talk about, and saying so definitionally is what keeps
-- the clauses below free of transports.
Unif : (Tm n → Tm m) → Stack n → Type ℓ-zero
Unif f [] = Unit
Unif f (p ∷ ps) = (f (p .fst) ≡ f (p .snd)) × Unif f ps

UnifM : (Tm n → Tm m) → Maybe (FStack n) → Type ℓ-zero
UnifM f nothing = Empty.⊥
UnifM f (just qs) = Unif f (unflexAll qs)


-- A chain acts by a composite of `bind`s, so it commutes with `fork`.
-- That is the only structural fact `flatSound` needs of it.
applyFork : (τ : Steps k n m) (a b : Tm n)
  → applySteps τ (fork a b) ≡ fork (applySteps τ a) (applySteps τ b)
applyFork {k = zero} Eq.refl a b = refl
applyFork {k = suc k} {n = suc n} (x , w , τ) a b =
  applyFork τ (subst1 x w a) (subst1 x w b)


-- Congruence closure is sound, for every `f` that commutes with `fork`:
-- solve the variable-headed equations `flatA` produced and the equation it
-- came from is solved.  No derivation appears -- this is a fact about the
-- decomposition, not about the machine.
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


-- `Unif` along the two things the flexible rule does to the stack.
unifStack : (g : Tm n → Tm m) (x : Fin (suc n)) (w : Tm n) (rs : Stack (suc n))
  → Unif g (applyStack x w rs) → Unif (λ t → g (subst1 x w t)) rs
unifStack g x w [] h = h
unifStack g x w (p ∷ rs) h = h .fst , unifStack g x w rs (h .snd)

unifSplit : (f : Tm n → Tm m) (as bs : Stack n)
  → Unif f (as ++ bs) → Unif f as × Unif f bs
unifSplit f [] bs h = tt , h
unifSplit f (p ∷ as) bs h = (h .fst , r .fst) , r .snd
  where r = unifSplit f as bs (h .snd)


-- McBride's two facts about the occurs check, in the `Maybe`-predicate
-- style: `thick` loses exactly its own variable, and what `check` returns
-- is what substituting for that variable produces.
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


-- The theorem, by the recursion `mgu` was defined by.  Each clause is the
-- corresponding clause of `mgu` with its obligation discharged: the
-- trivial rule owes `flatSound` on an empty flattening, the flexible rule
-- owes the head equation -- which is exactly the two McBride facts -- and
-- the tail is the induction hypothesis, reindexed by `unifStack`.
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


-- The readout the front end wants: a substitution TOGETHER with the proof
-- that it unifies the stack.  Read as a grammar -- `Unifier n : Stack n →
-- Type` -- `verified n` is a `⊢`-term, and it is the dependent form of the
-- semantic action `Check` exports.
Unifier : (n : ℕ) → Stack n → Type ℓ-zero
Unifier n ps = Σ[ σ ∈ AList n ] Unif (applyA σ) ps

verified : (n : ℕ) (ps : Stack n) → Sol n ps → Unifier n ps
verified n ps d = mgu n ps d , mguUnifies n ps d


-- WHAT IS STILL MISSING, PRECISELY.
--
-- `Sol n ps → Unifier n ps` is soundness.  The judgment would BE the
-- specification -- `mgu` its first projection and `mguUnifies` its second,
-- both definitional -- if `Sol` were `Unifier`, and the reason it is not
-- is not laziness: `Ans-map&` is divariant, so a checker for `Unifier`
-- owes `Unifier n ps → Sol n ps` as well, rule by rule.  Three obligations
-- come out of that, and they are of quite different sizes.
--
--   CLASH.  `flat1 p ≡ nothing` must refute `Unifier n (p ∷ ps)`.  This is
--   the exact mirror of `flatSound` -- `(f t ≡ f u) → UnifM f acc →
--   UnifM f (flatA t u acc)`, whose `⊥` case is `leaf ≡ fork _ _` under a
--   `bind` -- and it is a page.  No obstruction.
--
--   OCCURS.  `check x u ≡ nothing` must refute `f (var x) ≡ f u`, and it
--   does NOT, as stated: `u ≡ var x` makes both the check fail and the
--   equation hold.  The machine never reaches the flexible rule with such
--   a `u`, because `sameF` discards `x ≟ x` first -- but `flatA`'s result
--   type does not record that, so the checker cannot use it.  Fixing this
--   means strengthening `Flex n` to carry `u ≡ var x → ⊥`, after which the
--   refutation is a size argument on `bind ρ`.  A day, and it changes
--   `Term`.
--
--   RESTRICTION.  This is the one that does not go through.  The flexible
--   rule would owe: from an `AList (suc n)` unifying `p ∷ ps`, produce an
--   `AList n` unifying `applyStack x w (unflexAll qs ++ ps)`.  The
--   substitution one wants is `applyA σ ∘ var ∘ thin x`, and it does unify
--   it -- but an `AList` is a CHAIN of scope-dropping assignments, not an
--   arbitrary substitution, and that composite need not be one.  Take
--   `n = 1`: `AList 1` with target `1` is the identity chain alone, while
--   the restriction can be `fork (var 0) (var 0)`.  So the premise's chain
--   has to be *computed*, by the very algorithm the answer under
--   construction is running.
--
-- The escape is to carry a substitution rather than a chain -- `Fin n →
-- Tm m`, where restriction is composition and the map goes through.  That
-- is a different development: `mgu` would return a function, and the
-- `refl` tests, which compare chains, would have nothing to compare.
