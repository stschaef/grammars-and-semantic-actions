{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Types with unknowns, the constraints an unannotated term generates, and
   the intrinsically typed core they elaborate to.

   Everything here is ordinary Agda: this file knows nothing about the
   framework, exactly as `Unify/Term` and `Unify/Correct` know nothing
   about it.  It is the external layer a rule's index is computed by, plus
   the soundness theorem the front end reads out.

   FOUR DECISIONS SHAPE THE WHOLE DEVELOPMENT.

   TYPES ARE `Unify`'s TERMS.  `Ty n` is `Tm n` -- `leaf` is the base type,
   `fork` is the arrow, `var` is a metavariable -- so the unifier is not
   re-instantiated, re-proved or even re-read: the occurs check that makes
   `λx. x x` fail is `Unify/Term`'s `check`, verbatim, and `Correct`'s
   `mguUnifies` is what the soundness proof below consumes.  A type
   constructor with a different arity would need a new signature; a
   different set of BASE types would not, since `leaf` is only ever
   compared for equality.

   FRESH METAVARIABLES ARE ALLOCATED BY POSITION, NOT BY A COUNTER.  The
   textbook presentation threads a counter through the premises, so the
   argument of an application is generated at the state the function left
   behind -- a premise index that is a previous premise's OUTPUT, which no
   combinator provides.  `mv t` is instead the number of unknowns the
   subtree `t` needs, computed structurally, so the argument's block starts
   at `k + 1 + mv f`: an index computed from the conclusion's and from slot
   ZERO'S VALUE, which is precisely what `⊗ᴰ` gives.  This is `Linear`'s
   `keep Γ f` promoted -- the leftover discipline again -- and it is what
   makes constraint generation syntax-directed in this framework's sense.

   Nothing below depends on the allocation being INJECTIVE.  `mvar` clamps
   out of range rather than carrying a bound, so no clause owes a `Fin`
   arithmetic lemma.  The clamp is in fact unreachable -- `mv` counts
   exactly the unknowns each rule takes, and `Elaborate`'s `closed` starts
   the walk at offset one in a scope of `suc (mv t)` -- but that remark is
   deliberately not load-bearing, and it is not formalised.  A collision
   would make the generated constraint set STRONGER, so it could cost
   completeness and could not cost soundness, and soundness is what this
   file proves.

   THE SCOPE IS GLOBAL.  Every type in one run lives in `Tm n` for a single
   `n` fixed before the walk begins, and the constraint stacks of sibling
   subterms are therefore CONCATENATED rather than composed.  This is
   forced by the previous decision and by `Unify`'s `AList`: an `AList` is
   a chain of scope-DROPPING assignments, so solving after the function
   would renumber the unknowns the argument's block was allocated in, and
   positional allocation would be meaningless.  Incremental unification and
   positional freshness are incompatible; the fixed scope is which one this
   client keeps.

   THE CORE IS INTRINSIC, AS IN `Annotated`.  `Core m Γ A` is inhabited by
   well-typed terms and nothing else, its variable case carries a `Lookup`
   rather than a numeral, and `sound` below produces one together with the
   evidence that it erases to the source.  So a successful run does not
   merely report a type: it hands back a typing derivation for the term at
   that type, and "the inferred type is a type of the term" is the type of
   a projection. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
module Theory.Instances.Infer.Base where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ ; discreteℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum using (isProp⊎)
import Cubical.Data.Empty as Empty

open import Theory.Instances.Lambda.TermPresentation ℕ isSetℕ
  using (RawTm ; tvar ; tapp ; tlam) public

open import Theory.Instances.Unify.Check public using
  ( Tm ; var ; leaf ; fork ; discreteTm ; isSetTm
  ; Prob ; Stack ; isSetStack
  ; Sol ; isPropSol ; isSetSol ; mgu ; AList ; applyA
  ; Unif ; unifSplit ; applyFork ; mguUnifies ; Unifier )

private variable n m : ℕ

-- The arrow, which is `fork` under a name that reads like a type.
infixr 25 _⇛_
_⇛_ : Tm n → Tm n → Tm n
_⇛_ = fork


-- CONTEXTS, over a fixed scope of unknowns.
Ctx : ℕ → Type ℓ-zero
Ctx n = List (ℕ × Tm n)

isSetCtx : isSet (Ctx n)
isSetCtx = isOfHLevelList 0 (isSetΣ isSetℕ λ _ → isSetTm)

-- Applying a substitution to a context, by recursion, so that
-- `mapCtx f ((x , B) ∷ Γ)` is `(x , f B) ∷ mapCtx f Γ` DEFINITIONALLY --
-- which is the one fact the `lam` case of `sound` needs.
mapCtx : (Tm n → Tm m) → Ctx n → Ctx m
mapCtx f [] = []
mapCtx f ((y , B) ∷ Γ) = (y , f B) ∷ mapCtx f Γ

-- Lookup, carrying the POSITION: a chain of "not here" steps ending in a
-- hit, exactly as in `Annotated/Typing`.  The summands are mutually
-- exclusive, so it is a proposition and shadowing resolves inwards.
Lookup : Ctx n → Tm n → ℕ → Type ℓ-zero
Lookup [] A x = Empty.⊥
Lookup ((y , B) ∷ Γ) A x =
  ((x ≡ y) × (A ≡ B)) Sum.⊎ ((x ≡ y → Empty.⊥) × Lookup Γ A x)

private
  isPropNeq : {x y : ℕ} → isProp (x ≡ y → Empty.⊥)
  isPropNeq f g = funExt λ z → Empty.rec (f z)

isPropLookup : (Γ : Ctx n) (A : Tm n) (x : ℕ) → isProp (Lookup Γ A x)
isPropLookup [] A x = λ ()
isPropLookup ((y , B) ∷ Γ) A x =
  isProp⊎ (isProp× (isSetℕ _ _) (isSetTm _ _))
          (isProp× isPropNeq (isPropLookup Γ A x))
          (λ hit miss → miss .fst (hit .fst))

deBruijn : (Γ : Ctx n) (A : Tm n) (x : ℕ) → Lookup Γ A x → ℕ
deBruijn ((y , B) ∷ Γ) A x (Sum.inl _) = 0
deBruijn ((y , B) ∷ Γ) A x (Sum.inr (_ , v)) = suc (deBruijn Γ A x v)

-- A `Lookup` survives a substitution: the hit's equation is `cong`ed and
-- the misses are names, which no substitution touches.
lookMap : (f : Tm n → Tm m) (Γ : Ctx n) (A : Tm n) (x : ℕ)
  → Lookup Γ A x → Lookup (mapCtx f Γ) (f A) x
lookMap f ((y , B) ∷ Γ) A x (Sum.inl (p , q)) = Sum.inl (p , cong f q)
lookMap f ((y , B) ∷ Γ) A x (Sum.inr (ne , v)) =
  Sum.inr (ne , lookMap f Γ A x v)

-- The type the constraint generator READS OFF a context, total, with a
-- default that is never consulted on a derivation: `lookDef` says the
-- default is reached only where no `Lookup` exists at all.
hitOr : {ℓp : Level} {P : Type ℓp} → Dec P → Tm n → Tm n → Tm n
hitOr (yes _) B r = B
hitOr (no _) B r = r

lookD : Ctx n → ℕ → Tm n
lookD [] x = leaf
lookD ((y , B) ∷ Γ) x = hitOr (discreteℕ x y) B (lookD Γ x)

lookDef : (Γ : Ctx n) (A : Tm n) (x : ℕ) → Lookup Γ A x → A ≡ lookD Γ x
lookDef ((y , B) ∷ Γ) A x v = go (discreteℕ x y) v
  where
  go : (d : Dec (x ≡ y)) → Lookup ((y , B) ∷ Γ) A x → A ≡ hitOr d B (lookD Γ x)
  go (yes _) (Sum.inl (_ , q)) = q
  go (yes p) (Sum.inr (ne , _)) = Empty.rec (ne p)
  go (no ¬p) (Sum.inl (p , _)) = Empty.rec (¬p p)
  go (no _) (Sum.inr (_ , v)) = lookDef Γ A x v


-- FRESHNESS, POSITIONALLY.  `mv t` is how many unknowns the subtree `t`
-- needs -- one for an application's domain, two for an abstraction's
-- domain and codomain -- and `mvar n k` is the `k`th unknown of a scope of
-- `n`, clamped rather than bounded.  See the header: soundness does not
-- depend on the clamp being unreachable.
mv : RawTm → ℕ
mv (tvar _) = 0
mv (tapp f a) = suc (mv f + mv a)
mv (tlam _ t) = suc (suc (mv t))

fin : (n : ℕ) → ℕ → Fin (suc n)
fin n zero = zero
fin zero (suc k) = zero
fin (suc n) (suc k) = suc (fin n k)

mvar : (n : ℕ) → ℕ → Tm n
mvar zero k = leaf
mvar (suc n) k = var (fin n k)

-- The scope one run needs: one unknown for the goal type, then the term's.
scopeOf : RawTm → ℕ
scopeOf t = suc (mv t)


-- CONSTRAINT GENERATION.  Read it as the typing rules with every equation
-- between types POSTPONED:
--
--   Γ ⊢ x        ⇐ A   ⇝   Γ(x) ≐ A
--   Γ ⊢ f a      ⇐ A   ⇝   [Γ ⊢ f ⇐ βₖ ⇛ A] ++ [Γ ⊢ a ⇐ βₖ]
--   Γ ⊢ λx. t    ⇐ A   ⇝   A ≐ βₖ ⇛ βₖ₊₁ , [Γ,x:βₖ ⊢ t ⇐ βₖ₊₁]
--
-- Every recursive call's arguments are functions of this call's arguments
-- and of the node's own slot values -- `mv f` reads slot zero, `x` IS slot
-- zero -- which is the rule of thumb in `Combinator/README` II, satisfied.
gen : (n : ℕ) (Γ : Ctx n) (A : Tm n) (k : ℕ) → RawTm → Stack n
gen n Γ A k (tvar x) = (lookD Γ x , A) ∷ []
gen n Γ A k (tapp f a) =
     gen n Γ (mvar n k ⇛ A) (suc k) f
  ++ gen n Γ (mvar n k) (suc (k + mv f)) a
gen n Γ A k (tlam x t) =
    (A , mvar n k ⇛ mvar n (suc k))
  ∷ gen n ((x , mvar n k) ∷ Γ) (mvar n (suc k)) (suc (suc k)) t


-- THE CORE LANGUAGE, INTRINSICALLY TYPED, over types WITHOUT unknowns left
-- to solve -- that is, over whatever scope the unifier landed in.  This is
-- `Annotated`'s `Core` with `Ty` replaced by `Tm m`; the argument for
-- `cvar` carrying a `Lookup` rather than a numeral is unchanged and is
-- restated there.
data Core (m : ℕ) : Ctx m → Tm m → Type ℓ-zero where
  cvar : {Γ : Ctx m} {A : Tm m} (x : ℕ) → Lookup Γ A x → Core m Γ A
  capp : {Γ : Ctx m} {A B : Tm m} → Core m Γ (B ⇛ A) → Core m Γ B → Core m Γ A
  clam : {Γ : Ctx m} {A B : Tm m} (x : ℕ) → Core m ((x , B) ∷ Γ) A
       → Core m Γ (B ⇛ A)

erase : {Γ : Ctx m} {A : Tm m} → Core m Γ A → RawTm
erase (cvar x _) = tvar x
erase (capp f a) = tapp (erase f) (erase a)
erase (clam x t) = tlam x (erase t)

eraseSubst : {Γ : Ctx m} {A A' : Tm m} (e : A ≡ A') (c : Core m Γ A)
  → erase (subst (Core m Γ) e c) ≡ erase c
eraseSubst {m = m} {Γ = Γ} e c i = erase (subst-filler (Core m Γ) e c (~ i))


-- THE SHAPE JUDGMENT.  What is left of typing once every equation between
-- types has been postponed to `gen`: which names are bound, and where.
-- Defined by recursion on the term, as house convention 1 asks.
--
-- It is deliberately thin, and saying so is half of this client's report.
-- The type-theoretic content of inference does not live in the judgment
-- over the TERM theory at all; it lives in `gen` and is discharged by the
-- judgment over the UNIFICATION theory.  `Typing`'s `Inf` is the conjunction
-- of the two, and the conjunction is the only place both are visible.
Gen : (n : ℕ) (Γ : Ctx n) (A : Tm n) (k : ℕ) → RawTm → Type ℓ-zero
Gen n Γ A k (tvar x) = Lookup Γ (lookD Γ x) x
Gen n Γ A k (tapp f a) =
    Gen n Γ (mvar n k ⇛ A) (suc k) f
  × Gen n Γ (mvar n k) (suc (k + mv f)) a
Gen n Γ A k (tlam x t) =
  Gen n ((x , mvar n k) ∷ Γ) (mvar n (suc k)) (suc (suc k)) t

isPropGen : (n : ℕ) (Γ : Ctx n) (A : Tm n) (k : ℕ) (t : RawTm)
  → isProp (Gen n Γ A k t)
isPropGen n Γ A k (tvar x) = isPropLookup Γ (lookD Γ x) x
isPropGen n Γ A k (tapp f a) =
  isProp× (isPropGen n Γ (mvar n k ⇛ A) (suc k) f)
          (isPropGen n Γ (mvar n k) (suc (k + mv f)) a)
isPropGen n Γ A k (tlam x t) =
  isPropGen n ((x , mvar n k) ∷ Γ) (mvar n (suc k)) (suc (suc k)) t


-- SOUNDNESS, by the recursion `gen` and `Gen` were defined by.  Given a
-- substitution that solves everything the term generated, the shape
-- derivation elaborates to an intrinsically typed core term -- and the
-- core term erases to the source, so the pair is a typing derivation for
-- THIS term and not merely for one of its shape.
--
-- `f` is any map commuting with `fork`; the front end instantiates it at
-- `applyA (mgu ...)`, whose commutation is `Correct`'s `applyFork`.  Each
-- clause discharges exactly the equation its rule postponed: the variable
-- owes `Γ(x) ≐ A`, which `lookDef` and the unifier together supply; the
-- application owes nothing of its own and pays only the commutation; the
-- abstraction owes `A ≐ β ⇛ β'`, which is its head constraint.
module _ {m : ℕ} (f : Tm n → Tm m)
  (hfork : (a b : Tm n) → f (fork a b) ≡ fork (f a) (f b)) where

  Elab : (Γ : Ctx n) (A : Tm n) → RawTm → Type ℓ-zero
  Elab Γ A t = Σ[ c ∈ Core m (mapCtx f Γ) (f A) ] (erase c ≡ t)

  sound : (Γ : Ctx n) (A : Tm n) (k : ℕ) (t : RawTm)
    → Gen n Γ A k t → Unif f (gen n Γ A k t) → Elab Γ A t
  sound Γ A k (tvar x) d u =
      cvar x (subst (λ z → Lookup (mapCtx f Γ) z x) (u .fst)
                (lookMap f Γ (lookD Γ x) x d))
    , refl
  sound Γ A k (tapp g a) d u = capp gc (ac .fst) , cong₂ tapp ge (ac .snd)
    where
    sp = unifSplit f (gen _ Γ (mvar _ k ⇛ A) (suc k) g)
                     (gen _ Γ (mvar _ k) (suc (k + mv g)) a) u

    gc' = sound Γ (mvar _ k ⇛ A) (suc k) g (d .fst) (sp .fst)
    ac  = sound Γ (mvar _ k) (suc (k + mv g)) a (d .snd) (sp .snd)

    gc : Core m (mapCtx f Γ) (f (mvar _ k) ⇛ f A)
    gc = subst (Core m (mapCtx f Γ)) (hfork (mvar _ k) A) (gc' .fst)

    ge : erase gc ≡ g
    ge = eraseSubst (hfork (mvar _ k) A) (gc' .fst) ∙ gc' .snd
  sound Γ A k (tlam x t) d u =
      subst (Core m (mapCtx f Γ)) shape (clam x (bc .fst))
    , eraseSubst shape (clam x (bc .fst)) ∙ cong (tlam x) (bc .snd)
    where
    bc = sound ((x , mvar _ k) ∷ Γ) (mvar _ (suc k)) (suc (suc k)) t d (u .snd)

    shape : f (mvar _ k) ⇛ f (mvar _ (suc k)) ≡ f A
    shape = sym (u .fst ∙ hfork (mvar _ k) (mvar _ (suc k)))


-- COMPLETENESS, FOR THE HALF OF THE COMPOSITE THAT HAS IT.
--
-- `sound` says a derivation yields a typing.  The converse is the question
-- `Typing`'s header is about, and it splits: the SHAPE judgment has it,
-- outright and by induction, and the side condition does not.  This is
-- that half, and stating it here is what makes the other half's absence a
-- located gap rather than a silence.
--
-- `Agree` is the hypothesis, and it is the right one: `Gen` reads only the
-- NAMES of the context, so two contexts it cannot tell apart are two with
-- the same names in the same order -- at unrelated scopes, and carrying
-- unrelated types.  So the theorem says: if ANY intrinsically typed core
-- term, over ANY scope of unknowns, at ANY type, erases to `t`, then `Gen`
-- holds of `t` at EVERY goal type and offset.  Contrapositively, a refusal
-- at the `genM` mode really is "no typing derivation exists, whatever the
-- types" -- a universal over infinitely many types, discharged, because
-- the shape judgment quantifies over none of them.
Agree : {n m : ℕ} → Ctx n → Ctx m → Type ℓ-zero
Agree [] [] = Unit
Agree [] (_ ∷ _) = Empty.⊥
Agree (_ ∷ _) [] = Empty.⊥
Agree ((y , _) ∷ Γ) ((y' , _) ∷ Γ') = (y ≡ y') × Agree Γ Γ'

-- The variable case, which is the only one with content: a hit anywhere in
-- the second context is a hit at the same depth in the first, and the type
-- the first one holds there is by definition what `lookD` reads.
lookAgree : (n m : ℕ) (Γ : Ctx n) (Γ' : Ctx m) → Agree Γ Γ'
  → (A' : Tm m) (x : ℕ) → Lookup Γ' A' x → Lookup Γ (lookD Γ x) x
lookAgree n m [] [] ag A' x ()
lookAgree n m ((y , B) ∷ Γ) ((y' , B') ∷ Γ') (e , ag) A' x v =
  step (discreteℕ x y) v
  where
  step : (d : Dec (x ≡ y)) → Lookup ((y' , B') ∷ Γ') A' x
    → Lookup ((y , B) ∷ Γ) (hitOr d B (lookD Γ x)) x
  step (yes q) _ = Sum.inl (q , refl)
  step (no ¬q) (Sum.inl (p , _)) = Empty.rec (¬q (p ∙ sym e))
  step (no ¬q) (Sum.inr (_ , v')) = Sum.inr (¬q , lookAgree n m Γ Γ' ag A' x v')

genOf : (n : ℕ) {m : ℕ} {Γ' : Ctx m} {A' : Tm m} (c : Core m Γ' A')
  (Γ : Ctx n) → Agree Γ Γ' → (A : Tm n) (k : ℕ) → Gen n Γ A k (erase c)
genOf n (cvar x v) Γ ag A k = lookAgree n _ Γ _ ag _ x v
genOf n (capp f a) Γ ag A k =
    genOf n f Γ ag (mvar n k ⇛ A) (suc k)
  , genOf n a Γ ag (mvar n k) (suc (k + mv (erase f)))
genOf n (clam x c) Γ ag A k =
  genOf n c ((x , mvar n k) ∷ Γ) (refl , ag) (mvar n (suc k)) (suc (suc k))

-- ...and the same statement about a SOURCE term rather than about an
-- erasure, which is the form a refutation is used in.
genComplete : (n : ℕ) (Γ : Ctx n) (A : Tm n) (k : ℕ) (t : RawTm)
  {m : ℕ} {Γ' : Ctx m} {A' : Tm m} (c : Core m Γ' A')
  → Agree Γ Γ' → erase c ≡ t → Gen n Γ A k t
genComplete n Γ A k t c ag e = subst (Gen n Γ A k) e (genOf n c Γ ag A k)
