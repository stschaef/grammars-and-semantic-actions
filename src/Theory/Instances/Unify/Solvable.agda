{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- The converse of `Correct`, and what it costs.

   `Correct` ends by saying the backward map does not go through: the
   flexible rule would owe, from an `AList (suc n)` unifying `p ∷ ps`, an
   `AList n` unifying the substituted stack, and an `AList` is a CHAIN of
   scope-dropping assignments, which restriction along `thin x` does not
   preserve.  That is true, and it is a fact about the CARRIED ANSWER, not
   about solvability.  This file is the same statement with the chain
   replaced by a plain substitution `Fin n → Tm m`, where restriction IS
   composition -- the escape `Correct` names in its last paragraph -- and
   under that replacement every obligation is dischargeable.

   `Solvable n ps` is therefore the SPECIFICATION: some substitution, into
   some scope, makes every equation of `ps` hold.  `complete` says the
   machine reaches it, so `Sol` and `Solvable` are logically equivalent and
   a refusal of the checker really does mean "no unifier exists".

   THREE LEMMAS CARRY IT, and they are exactly the three `Correct` named.

   CLASH is `flatComp`, the mirror of `flatSound`, and it is stated over
   `bind ρ` rather than over an abstract `f`: an abstract map commuting
   with `fork` may send `leaf` anywhere, so `leaf ≟ fork _ _` is refutable
   only for a substitution.  That asymmetry is why soundness could be
   proved for every `f` and completeness cannot.

   OCCURS is `sizeLt`.  `Correct` says the refutation fails as stated
   because `u ≡ var x` makes the check fail and the equation hold, and that
   the repair is to record `u ≢ var x`.  It is recorded here rather than in
   `Flex`: `flatNoSelf` proves that `flatA` never PUSHES such an equation,
   because `sameF` discards `x ≟ x` first, so the side condition is a
   theorem about the decomposition and `Term` does not move.

   RESTRICTION is `restrict`, and it is the one that was blocked.  `check
   x u ≡ just w` says exactly that `w` is `u` with `x` thinned out
   (`checkThin`), so `bind ρ' w ≡ bind ρ u` for `ρ' = ρ ∘ thin x` and every
   `ρ` whatever; the head equation turns that into `bind ρ' w ≡ ρ x`, which
   is the one hypothesis `bind ρ' ∘ subst1 x w ≡ bind ρ` needs.  No chain
   is ever constructed, so the `n = 1` counterexample -- `fork (var 0)
   (var 0)` is not an `AList 1` -- does not arise: it was a counterexample
   to the restricted ANSWER being representable, never to the premise being
   solvable.

   Everything here is ordinary Agda, as in `Term` and `Correct`.  The
   framework-facing corollary is `Cover`. -}
open import Cubical.Foundations.Prelude
module Theory.Instances.Unify.Solvable where

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.Properties using (discreteFin)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Unify.Correct public

private variable k n m : ℕ

-- NO CONFUSION, by a total predicate rather than by a code, since only the
-- three head shapes are ever needed.
isLeaf : Tm n → Type ℓ-zero
isLeaf (var _) = Empty.⊥
isLeaf leaf = Unit
isLeaf (fork _ _) = Empty.⊥

isVar : Tm n → Type ℓ-zero
isVar (var _) = Unit
isVar leaf = Empty.⊥
isVar (fork _ _) = Empty.⊥

leafNotFork : {a b : Tm n} → leaf ≡ fork a b → Empty.⊥
leafNotFork e = subst isLeaf e tt

forkNotLeaf : {a b : Tm n} → fork a b ≡ leaf → Empty.⊥
forkNotLeaf e = leafNotFork (sym e)

varNotFork : {x : Fin n} {a b : Tm n} → var x ≡ fork a b → Empty.⊥
varNotFork e = subst isVar e tt

leafNotVar : {x : Fin n} → leaf ≡ var x → Empty.⊥
leafNotVar e = subst isVar (sym e) tt

unVar : Fin n → Tm n → Fin n
unVar d (var x) = x
unVar d leaf = d
unVar d (fork _ _) = d

varInj : {x y : Fin n} → var x ≡ var y → x ≡ y
varInj {x = x} e = cong (unVar x) e


-- SUBSTITUTIONS, and solvability.  `Subst n m` is what an `AList n` acts as
-- and is not: `applyA` is a composite of `bind`s, so it is one of these,
-- while an arbitrary one is not a chain.  Solvability quantifies over
-- these, which is the whole difference.
Subst : ℕ → ℕ → Type ℓ-zero
Subst n m = Fin n → Tm m

Solvable : (n : ℕ) → Stack n → Type ℓ-zero
Solvable n ps = Σ[ m ∈ ℕ ] Σ[ ρ ∈ Subst n m ] Unif (bind ρ) ps

bindBind : (f : Subst n k) (g : Subst k m) (t : Tm n)
  → bind g (bind f t) ≡ bind (λ y → bind g (f y)) t
bindBind f g (var y) = refl
bindBind f g leaf = refl
bindBind f g (fork a b) = cong₂ fork (bindBind f g a) (bindBind f g b)

unifExt : (f g : Tm n → Tm m) → ((t : Tm n) → f t ≡ g t)
  → (ps : Stack n) → Unif f ps → Unif g ps
unifExt f g h [] u = tt
unifExt f g h (p ∷ ps) u =
  sym (h (p .fst)) ∙∙ u .fst ∙∙ h (p .snd) , unifExt f g h ps (u .snd)

unifJoin : (f : Tm n → Tm m) (as bs : Stack n)
  → Unif f as → Unif f bs → Unif f (as ++ bs)
unifJoin f [] bs _ v = v
unifJoin f (p ∷ as) bs u v = u .fst , unifJoin f as bs (u .snd) v

-- A chain acts as a substitution, so the machine's answer is one of the
-- objects `Solvable` quantifies over.
stepsLeaf : (τ : Steps k n m) → applySteps τ leaf ≡ leaf
stepsLeaf {k = zero} Eq.refl = refl
stepsLeaf {k = suc k} {n = suc n} (x , w , τ) = stepsLeaf τ

stepsBind : (τ : Steps k n m) (t : Tm n)
  → applySteps τ t ≡ bind (λ y → applySteps τ (var y)) t
stepsBind τ (var y) = refl
stepsBind τ leaf = stepsLeaf τ
stepsBind τ (fork a b) =
  applyFork τ a b ∙ cong₂ fork (stepsBind τ a) (stepsBind τ b)

solvableOf : (n : ℕ) (ps : Stack n) → Sol n ps → Solvable n ps
solvableOf n ps d =
    σ .fst , (λ y → applyA σ (var y))
  , unifExt (applyA σ) (bind (λ y → applyA σ (var y)))
      (stepsBind (σ .snd .snd)) ps (mguUnifies n ps d)
  where σ = mgu n ps d


-- THINNING, in the `Maybe`-predicate style `Correct` argues for: `Thicked
-- x y c` says what `c` being `thick x y` tells us, so no clause below
-- inverts an equation between `Maybe`s.
Thicked : (x y : Fin (suc n)) → Maybe (Fin n) → Type ℓ-zero
Thicked x y nothing = x ≡ y
Thicked {n} x y (just y') = thin x y' ≡ y

private
  sucThicked : {x y : Fin (suc n)} (c : Maybe (Fin n))
    → Thicked x y c → Thicked (suc x) (suc y) (sucM c)
  sucThicked nothing e = cong suc e
  sucThicked (just y') e = cong suc e

thickOK : (x y : Fin (suc n)) → Thicked x y (thick x y)
thickOK zero zero = refl
thickOK zero (suc y) = refl
thickOK {suc n} (suc x) zero = refl
thickOK {suc n} (suc x) (suc y) = sucThicked (thick x y) (thickOK x y)


-- WHAT THE OCCURS CHECK RETURNS.  `check x u ≡ just w` is not merely "the
-- check succeeded": it says `w` is `u` with `x` thinned out, and that is
-- what makes the restricted substitution agree with the original.
Thinned : (x : Fin (suc n)) (u : Tm (suc n)) → Maybe (Tm n) → Type ℓ-zero
Thinned x u nothing = Unit
Thinned x u (just w) = bind (λ y → var (thin x y)) w ≡ u

private
  varThinned : {x y : Fin (suc n)} (c : Maybe (Fin n))
    → Thicked x y c → Thinned x (var y) (varM c)
  varThinned nothing e = tt
  varThinned (just y') e = cong var e

  forkThinned : {x : Fin (suc n)} {s t : Tm (suc n)} (cs ct : Maybe (Tm n))
    → Thinned x s cs → Thinned x t ct → Thinned x (fork s t) (forkM cs ct)
  forkThinned nothing ct _ _ = tt
  forkThinned (just _) nothing _ _ = tt
  forkThinned (just a) (just b) p q = cong₂ fork p q

checkThin : (x : Fin (suc n)) (u : Tm (suc n)) → Thinned x u (check x u)
checkThin x (var y) = varThinned (thick x y) (thickOK x y)
checkThin x leaf = refl
checkThin x (fork s t) =
  forkThinned (check x s) (check x t) (checkThin x s) (checkThin x t)


-- RESTRICTION.  This is the step `Correct` could not take for a chain.
-- `ρ' = ρ ∘ thin x` is a substitution by construction, and `hx` is the one
-- hypothesis it needs -- which the head equation supplies, since `w` is
-- `u` thinned.
module _ {n m : ℕ} (x : Fin (suc n)) (w : Tm n) (ρ : Subst (suc n) m) where

  thinSub : Subst n m
  thinSub y = ρ (thin x y)

  module _ (hx : ρ x ≡ bind thinSub w) where

    forSub : (y : Fin (suc n)) → bind thinSub (for x w y) ≡ ρ y
    forSub y = go (thick x y) (thickOK x y)
      where
      go : (c : Maybe (Fin n)) → Thicked x y c
        → bind thinSub (forM w c) ≡ ρ y
      go nothing e = sym hx ∙ cong ρ e
      go (just y') e = cong ρ e

    restrict : (t : Tm (suc n)) → bind thinSub (subst1 x w t) ≡ bind ρ t
    restrict t = bindBind (for x w) thinSub t ∙ go t
      where
      go : (t : Tm (suc n)) → bind (λ y → bind thinSub (for x w y)) t
                            ≡ bind ρ t
      go (var y) = forSub y
      go leaf = refl
      go (fork a b) = cong₂ fork (go a) (go b)

    unifApply : (rs : Stack (suc n))
      → Unif (bind ρ) rs → Unif (bind thinSub) (applyStack x w rs)
    unifApply [] _ = tt
    unifApply (p ∷ rs) u =
        restrict (p .fst) ∙∙ u .fst ∙∙ sym (restrict (p .snd))
      , unifApply rs (u .snd)


-- CLASH, which is `flatSound` run backwards.  It is stated over `bind ρ`
-- and not over an abstract `f` commuting with `fork`, because that is what
-- the `leaf ≟ fork _ _` clause needs: a substitution sends `leaf` to
-- `leaf`, an arbitrary such `f` need not.
private
  forkL forkR : Tm n → Tm n
  forkL (fork a _) = a
  forkL t = t
  forkR (fork _ b) = b
  forkR t = t

  forkInjL : {a b c d : Tm n} → fork a b ≡ fork c d → a ≡ c
  forkInjL = cong forkL

  forkInjR : {a b c d : Tm n} → fork a b ≡ fork c d → b ≡ d
  forkInjR = cong forkR

module _ {n m : ℕ} (ρ : Subst n m) where

  pushComp : (e : Flex n) (acc : Maybe (FStack n))
    → (bind ρ (var (e .fst)) ≡ bind ρ (e .snd)) → UnifM (bind ρ) acc
    → UnifM (bind ρ) (pushF e acc)
  pushComp e nothing _ ()
  pushComp e (just as) h u = h , u

  flatComp : (t u : Tm n) (acc : Maybe (FStack n))
    → bind ρ t ≡ bind ρ u → UnifM (bind ρ) acc
    → UnifM (bind ρ) (flatA t u acc)
  flatComp (var x) (var y) acc h u = onSame (discreteFin x y)
    where
    onSame : (d : Dec (x ≡ y)) → UnifM (bind ρ) (sameF x y d acc)
    onSame (yes _) = u
    onSame (no _) = pushComp (x , var y) acc h u
  flatComp (var x) leaf acc h u = pushComp (x , leaf) acc h u
  flatComp (var x) (fork a b) acc h u = pushComp (x , fork a b) acc h u
  flatComp leaf (var y) acc h u = pushComp (y , leaf) acc (sym h) u
  flatComp (fork a b) (var y) acc h u = pushComp (y , fork a b) acc (sym h) u
  flatComp leaf leaf acc h u = u
  flatComp leaf (fork a b) acc h u = Empty.rec (leafNotFork h)
  flatComp (fork a b) leaf acc h u = Empty.rec (forkNotLeaf h)
  flatComp (fork s₁ t₁) (fork s₂ t₂) acc h u =
    flatComp s₁ s₂ (flatA t₁ t₂ acc) (forkInjL h)
      (flatComp t₁ t₂ acc (forkInjR h) u)


-- OCCURS, part one: the equation `flatA` pushes is never `x ≟ var x`,
-- because `sameF` discards that case before pushing anything.  `Correct`
-- proposed recording this in `Flex n`; it is a theorem about the
-- decomposition instead, so `Term` does not move.
NoSelf : FStack n → Type ℓ-zero
NoSelf [] = Unit
NoSelf (e ∷ qs) = ((e .snd ≡ var (e .fst)) → Empty.⊥) × NoSelf qs

NoSelfM : Maybe (FStack n) → Type ℓ-zero
NoSelfM nothing = Unit
NoSelfM (just qs) = NoSelf qs

private
  pushNoSelf : (e : Flex n) (acc : Maybe (FStack n))
    → ((e .snd ≡ var (e .fst)) → Empty.⊥) → NoSelfM acc → NoSelfM (pushF e acc)
  pushNoSelf e nothing ne u = tt
  pushNoSelf e (just as) ne u = ne , u

flatNoSelf : (t u : Tm n) (acc : Maybe (FStack n))
  → NoSelfM acc → NoSelfM (flatA t u acc)
flatNoSelf (var x) (var y) acc u = onSame (discreteFin x y)
  where
  onSame : (d : Dec (x ≡ y)) → NoSelfM (sameF x y d acc)
  onSame (yes _) = u
  onSame (no ¬p) = pushNoSelf (x , var y) acc (λ e → ¬p (sym (varInj e))) u
flatNoSelf (var x) leaf acc u = pushNoSelf (x , leaf) acc leafNotVar u
flatNoSelf (var x) (fork a b) acc u =
  pushNoSelf (x , fork a b) acc (λ e → varNotFork (sym e)) u
flatNoSelf leaf (var y) acc u = pushNoSelf (y , leaf) acc leafNotVar u
flatNoSelf (fork a b) (var y) acc u =
  pushNoSelf (y , fork a b) acc (λ e → varNotFork (sym e)) u
flatNoSelf leaf leaf acc u = u
flatNoSelf leaf (fork a b) acc u = tt
flatNoSelf (fork a b) leaf acc u = tt
flatNoSelf (fork s₁ t₁) (fork s₂ t₂) acc u =
  flatNoSelf s₁ s₂ (flatA t₁ t₂ acc) (flatNoSelf t₁ t₂ acc u)


-- OCCURS, part two: the size argument.  A failed check means `x` occurs in
-- `u`, so `ρ x` is a subterm of `bind ρ u` -- properly, once `u` is known
-- not to be `var x` itself, which is exactly what part one supplies.
Failed : Maybe (Tm n) → Type ℓ-zero
Failed nothing = Unit
Failed (just _) = Empty.⊥

private
  leL : (a b : ℕ) → a NO.≤ (a + b)
  leL a b = b , +-comm b a

  leR : (a b : ℕ) → b NO.≤ (a + b)
  leR a b = a , refl

module _ {n m : ℕ} (ρ : Subst (suc n) m) where

  sizeLe : (x : Fin (suc n)) (u : Tm (suc n)) → Failed (check x u)
    → tmSize (ρ x) NO.≤ tmSize (bind ρ u)
  sizeLe x (var y) f = onV (thick x y) (thickOK x y) f
    where
    onV : (c : Maybe (Fin n)) → Thicked x y c → Failed (varM c)
      → tmSize (ρ x) NO.≤ tmSize (ρ y)
    onV nothing e _ = subst (λ z → tmSize (ρ x) NO.≤ tmSize (ρ z)) e NO.≤-refl
    onV (just _) _ ()
  sizeLe x leaf ()
  sizeLe x (fork s t) f =
    onF (check x s) (check x t) (sizeLe x s) (sizeLe x t) f
    where
    a b : ℕ
    a = tmSize (bind ρ s)
    b = tmSize (bind ρ t)

    onF : (cs ct : Maybe (Tm n))
      → (Failed cs → tmSize (ρ x) NO.≤ a)
      → (Failed ct → tmSize (ρ x) NO.≤ b)
      → Failed (forkM cs ct) → tmSize (ρ x) NO.≤ suc (a + b)
    onF nothing ct hs ht _ = NO.≤-suc (NO.≤-trans (hs tt) (leL a b))
    onF (just _) nothing hs ht _ = NO.≤-suc (NO.≤-trans (ht tt) (leR a b))
    onF (just _) (just _) _ _ ()

  sizeLt : (x : Fin (suc n)) (u : Tm (suc n)) → Failed (check x u)
    → ((u ≡ var x) → Empty.⊥) → tmSize (ρ x) NO.< tmSize (bind ρ u)
  sizeLt x (var y) f ne = Empty.rec (onV (thick x y) (thickOK x y) f)
    where
    onV : (c : Maybe (Fin n)) → Thicked x y c → Failed (varM c) → Empty.⊥
    onV nothing e _ = ne (cong var (sym e))
    onV (just _) _ ()
  sizeLt x leaf () ne
  sizeLt x (fork s t) f ne =
    NO.suc-≤-suc (onF (check x s) (check x t) (sizeLe x s) (sizeLe x t) f)
    where
    a b : ℕ
    a = tmSize (bind ρ s)
    b = tmSize (bind ρ t)

    onF : (cs ct : Maybe (Tm n))
      → (Failed cs → tmSize (ρ x) NO.≤ a)
      → (Failed ct → tmSize (ρ x) NO.≤ b)
      → Failed (forkM cs ct) → tmSize (ρ x) NO.≤ (a + b)
    onF nothing ct hs ht _ = NO.≤-trans (hs tt) (leL a b)
    onF (just _) nothing hs ht _ = NO.≤-trans (ht tt) (leR a b)
    onF (just _) (just _) _ _ ()

occursRefute : {n m : ℕ} (ρ : Subst (suc n) m)
  (x : Fin (suc n)) (u : Tm (suc n))
  → ((u ≡ var x) → Empty.⊥) → bind ρ (var x) ≡ bind ρ u
  → Failed (check x u) → Empty.⊥
occursRefute ρ x u ne heq f =
  NO.¬m<m (subst (λ z → tmSize z NO.< tmSize (bind ρ u)) heq (sizeLt ρ x u f ne))


-- THE CONVERSE, by the recursion `Sol` was defined by.  Each clause is the
-- corresponding clause of `Sol` with its obligation discharged by one of
-- the three lemmas: the clash rule owes `flatComp`, the flexible rule owes
-- `occursRefute` for the check and `unifApply` for the premise, and the
-- trivial rule owes nothing.  The recursion is `Sol`'s own -- the scope
-- drops at the flexible rule and the stack shortens everywhere else -- so
-- no well-founded machinery appears here either.
SolvableF : (n : ℕ) → Maybe (FStack n) → Stack n → Type ℓ-zero
SolvableF n fl ps = Σ[ m ∈ ℕ ] Σ[ ρ ∈ Subst n m ]
  (UnifM (bind ρ) fl × Unif (bind ρ) ps)

SolvableX : (n : ℕ) → Fin n → Tm n → FStack n → Stack n → Type ℓ-zero
SolvableX n x u qs ps = Σ[ m ∈ ℕ ] Σ[ ρ ∈ Subst n m ]
  ( (bind ρ (var x) ≡ bind ρ u)
  × Unif (bind ρ) (unflexAll qs)
  × Unif (bind ρ) ps )

complete : (n : ℕ) (ps : Stack n) → Solvable n ps → Sol n ps
completeFlat : (n : ℕ) (fl : Maybe (FStack n)) (ps : Stack n)
  → NoSelfM fl → SolvableF n fl ps → onFlat n fl ps
completeFlex : (n : ℕ) (x : Fin n) (u : Tm n) (qs : FStack n) (ps : Stack n)
  → ((u ≡ var x) → Empty.⊥) → SolvableX n x u qs ps → flexAt n x u qs ps

complete n [] _ = tt
complete n (p ∷ ps) (m , ρ , h , hs) =
  completeFlat n (flat1 p) ps (flatNoSelf (p .fst) (p .snd) (just []) tt)
    (m , ρ , flatComp ρ (p .fst) (p .snd) (just []) h tt , hs)

completeFlat n nothing ps ns (m , ρ , bad , _) = bad
completeFlat n (just []) ps ns (m , ρ , _ , hs) = complete n ps (m , ρ , hs)
completeFlat n (just (e ∷ qs)) ps ns (m , ρ , hq , hs) =
  completeFlex n (e .fst) (e .snd) qs ps (ns .fst)
    (m , ρ , hq .fst , hq .snd , hs)

completeFlex (suc n) x u qs ps ne (m , ρ , heq , hq , hs) =
  go (check x u) (checkThin x u) (occursRefute ρ x u ne heq)
  where
  go : (c : Maybe (Tm n)) → Thinned x u c → (Failed c → Empty.⊥)
    → onCheck n x u qs ps c
  go nothing _ absurd = Empty.rec (absurd tt)
  go (just w) thinned _ = assign w refl
    (complete n (applyStack x w (unflexAll qs ++ ps))
      ( m , thinSub x w ρ
      , unifApply x w ρ hx (unflexAll qs ++ ps)
          (unifJoin (bind ρ) (unflexAll qs) ps hq hs) ))
    where
    hx : ρ x ≡ bind (thinSub x w ρ) w
    hx = heq ∙∙ cong (bind ρ) (sym thinned)
             ∙∙ bindBind (λ y → var (thin x y)) ρ w


-- ...and the two together.  `Sol` is the machine and `Solvable` is the
-- specification; they are logically equivalent, so the checker's `no` is
-- "no substitution unifies this stack" and not merely "the machine
-- stopped".  This is the statement `Correct` says is missing.
solEquiv : (n : ℕ) (ps : Stack n) → (Sol n ps → Solvable n ps)
                                   × (Solvable n ps → Sol n ps)
solEquiv n ps = solvableOf n ps , complete n ps
