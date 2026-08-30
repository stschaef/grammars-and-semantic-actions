{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Parsing with derivatives (Might-Darais-Spiewak), at the repo's own grammar
   codes: a parser for *every* context-free grammar, ambiguous ones included.

   WHAT THIS IS NOT.  It is not an LR parser, and the state here is the reason
   the two get confused.  An LR(0) state is the item set live after a prefix
   `u`, which as a language *is* the derivative by `u`; the dot-advance and
   closure rules are `δ`s two clauses below.  But LR's content is that those
   item sets are *finitely many*, so they form a table, and that at each one a
   bounded lookahead picks a unique action.  Neither holds here.  Nothing
   identifies `D* w` with `D* w'` when they denote the same language --
   `levOf` raises the universe level once per letter -- and dead items are
   never dropped, because `δ` emits `k (Dl c (literal d))` for `d ≠ c`, an
   empty grammar that nothing marks as empty.  So: no automaton, no table, no
   conflicts, no determinism.  This is the Earley/GLR regime, strictly more
   general than LR and correspondingly slower.  `Combinator/Ascent` has the
   other half -- commitment, a stack, a machine-checked no-conflict condition
   -- but chooses its states by hand.  Neither line alone is LR.

   `Derivative/OneStep` takes the derivative of a body but hands the recursion
   back to the caller: `δ (var x) = dv x`, and `δ-sound` assumes a `step` for
   every nonterminal.  Nullability is likewise an oracle `X → Bool`.  So it is
   one step of the method, not the algorithm: its whole content is
   that the derivative of a recursive nonterminal is *itself* recursive, and
   that nullability is a fixed point over the cycle.

   Here the knot is tied.  Given a grammar `F : (x : X) → Functor _ X xs tt`
   with `A = μ F`, the derivative grammar is another `μ` over the *same*
   nonterminals:

     D = μ (λ x → δ (F x))

   `δ` sends `Var x` to `Var x` -- the derivative nonterminal -- and freezes
   the undifferentiated occurrences as constants `k ⟦ G ⟧`, which is legal
   because `μ F` already exists.  That is what `Derivative/OneStep` needed a
   second variable constructor `dv` for.

   Two things fall out that the `Bool` version cannot state:

   * Nullability is the *grammar* `⟦ G ⟧ & εTy` -- every null parse, not a
     yes/no and not one chosen witness.  So the `⊗` rule keeps all
     derivations of an ambiguous left factor.
   * Completeness holds, not just soundness.  `Dl c (μ F x) ⊢ D x` is not of
     the shape `μ F x ⊢ _` that `rec` eliminates, but the derivative's right
     adjoint from `Derivative/General` converts it to one:
     `∂[ ⌈ c ⌉ ] ⊣ √[ ⌈ c ⌉ ]` and `∂[ ⌈ w ⌉ ] ≅ Dl-string w`, so the
     statement becomes `μ F x ⊢ √[ ⌈ c ⌉ ] (D x)`, which is a fold.  This is
     the one place the adjunction earns its keep.

   What is still missing for an *implementation*: compaction.  Adams-
   Hollenbeck-Might's complexity result depends on simplifying `⊥ ⊗ x`,
   `ε ⊗ x` and degenerate nodes away as the derivative graph is built.  `δ`
   here builds the graph faithfully and normalises nothing, so this is the
   specification that a real implementation optimises, not the optimisation. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Derivative.Parser
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.List using ([] ; _∷_ ; _++_)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_
open import Theory.Instances.Monoid.Regex.Derivative Alphabet _≟_ ℓ-zero
  using ( Dl-⊗-out⁺ ; Dl-⊗-in-l ; Dl-⊗-in-r⁺ )
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
  using (Dl ; Dl-map ; Dl-string ; Dl-string-map)
open import Theory.Instances.Monoid.Derivative.General Alphabet isSetAlphabet
  using ( ∂[_]_ ; √[_]_ ; ∂-intro ; ∂-intro⁻ ; ∂-counit ; ∂⌈⌉→⊸ ; ⊸→∂⌈⌉
        ; ∂⌈⌉→Dl ; Dl→∂⌈⌉ )
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using ( ⊗ᵘ→⊗ ; ⊗→⊗ᵘ ; ⟦⊗e⟧ ; ⟦⊗e⟧⁻
        ; _⊸_ ; ⊸-lam ; ⊸-app ; ⊗ε-unit-r ; ⊗ε-unit-r⁻ )

private variable ℓA ℓX : Level

-- The null parses of a grammar: `εTy` cuts it down to the empty word, and
-- nothing is truncated away.  `Regex/Derivative`s `¬Nullable` is the
-- refutation of this, and `Dl-⊗-in-r`s section argument is one point of it.
Nu : TheoryTy ℓA tt → TheoryTy _ tt
Nu A = A & εTy

-- A grammar is a system of bodies over its nonterminals, and `μ F` is the
-- family it generates.  Everything below is at a fixed letter `c`.
module _ {X : Type ℓX} {xs : X → Unit}
  (F : (x : X) → Functor ℓA X xs tt) (c : Alphabet) where

  private
    ℓD : Level
    ℓD = ℓ-max (ℓF ℓA) ℓX

    -- the branch tag on the `⊗` rule, at the nonterminal level
    Two : Type ℓX
    Two = Lift ℓX Bool

    A : (x : X) → TheoryTy ℓD tt
    A = μ F

    ⟦_⟧A : Functor ℓA X xs tt → TheoryTy ℓD tt
    ⟦ G ⟧A = ⟦ G ⟧TheoryTy A

  -- THE DERIVATIVE OF A BODY.  `Var x` stays a variable -- it now names the
  -- *derivative* nonterminal -- and the occurrences that must not be
  -- differentiated are frozen as constants, which is possible only because
  -- `μ F` is already built.  That freezing is what `Derivative/OneStep` paid for
  -- with a second variable constructor `dv`, and it is why this `δ` can be
  -- iterated where that one cannot.
  δ : Functor ℓA X xs tt → Functor ℓD X xs tt
  δ (k B) = k (LiftTheoryTy ℓD (Dl c B))
  δ (Var x) = Var x
  δ (⊕e Y G) = ⊕e Y λ y → δ (G y)
  δ (&e Y G) = &e Y λ y → δ (G y)
  δ (G &e2 G') = δ G &e2 δ G'
  -- the unit has no subterm to descend into, so its derivative is itself
  δ (⊗e ε· G) = k (LiftTheoryTy ℓD (Dl c ⟦ ⊗e ε· G ⟧A))
  -- ...and the product rule, with the nullable-left case carrying `Nu`, so
  -- an ambiguous left factor contributes every null parse it has
  δ (⊗e _⊙_ G) = ⊕e Two λ where
    (lift true) →
      ⊗e _⊙_ (two (δ (G zero)) (k (LiftTheoryTy ℓD ⟦ G (suc zero) ⟧A)))
    (lift false) →
      ⊗e _⊙_ (two (k (LiftTheoryTy ℓD (Nu ⟦ G zero ⟧A))) (δ (G (suc zero))))

  -- THE DERIVATIVE GRAMMAR: the same nonterminals, the differentiated
  -- bodies, and a genuine least fixed point.  This is the knot
  -- `OneStep.δ-sound` had to assume as `step`.
  D : (x : X) → TheoryTy (ℓ-max (ℓF ℓD) ℓX) tt
  D = μ λ x → δ (F x)

  -- SOUNDNESS: every parse the derivative grammar finds is a parse of the
  -- original, one letter in.  A fold, with the body-level statement by
  -- induction on the code -- and no `step` hypothesis anywhere, because the
  -- recursive occurrence is `Var x` and the motive supplies it.
  private
    sound' : (G : Functor ℓA X xs tt)
      → ⟦ δ G ⟧TheoryTy (λ y → Dl c (A y)) ⊢ Dl c ⟦ G ⟧A
    sound' (k B) = liftTy ∘⊢ lowerTy ∘⊢ lowerTy
    sound' (Var x) = liftTy ∘⊢ lowerTy
    sound' (⊕e Y G) = ⊕ᴰ-elim λ y → σ⊕ y ∘⊢ sound' (G y)
    sound' (&e Y G) = &ᴰ-intro λ y → sound' (G y) ∘⊢ π y
    sound' (G &e2 G') = sound' G ,&p sound' G'
    sound' (⊗e ε· G) = lowerTy ∘⊢ lowerTy
    sound' (⊗e _⊙_ G) = ⊕ᴰ-elim λ where
      (lift true) →
        Dl-map c (⊗→⊗ᵘ λ i → ⟦ G i ⟧A)
        ∘⊢ Dl-⊗-in-l c
        ∘⊢ (sound' (G zero) ,⊗ (lowerTy ∘⊢ lowerTy))
        ∘⊢ ⟦⊗e⟧ (δ (G zero)) (k (LiftTheoryTy ℓD ⟦ G (suc zero) ⟧A))
      (lift false) →
        Dl-map c (⊗→⊗ᵘ λ i → ⟦ G i ⟧A)
        ∘⊢ Dl-⊗-in-r⁺ c
        ∘⊢ ((lowerTy ∘⊢ lowerTy) ,⊗ sound' (G (suc zero)))
        ∘⊢ ⟦⊗e⟧ (k (LiftTheoryTy ℓD (Nu ⟦ G zero ⟧A))) (δ (G (suc zero)))

  sound : (x : X) → D x ⊢ Dl c (A x)
  sound = rec _ λ x → Dl-map c roll ∘⊢ sound' (F x)

  -- COMPLETENESS: every parse of the original, one letter in, is found by
  -- the derivative grammar.  `Dl c (A x) ⊢ D x` is not of the shape
  -- `μ F x ⊢ _` that `rec` eliminates -- the derivative shifts the index --
  -- so the fold cannot see it.  The adjunction `∂[ ⌈ c ⌉ ] ⊣ √[ ⌈ c ⌉ ]`
  -- from `Derivative/General` moves the derivative to the other side and
  -- turns it into `A x ⊢ √[ ⌈ c ⌉ ] (D x)`, which *is* a fold.  That is the
  -- one place the right adjoint earns its keep.
  --
  -- The motive carries the original parse alongside, because `δ` freezes
  -- undifferentiated occurrences at `μ F` while the fold has replaced `μ F`
  -- by the motive; `forget` is the projection back.
  private
    w : String
    w = ⌈gen c ⌉

    Mot : (x : X) → TheoryTy _ tt
    Mot x = A x & (√[ ⌈ w ⌉ ] (D x))

    forget : (G : Functor ℓA X xs tt) → ⟦ G ⟧TheoryTy Mot ⊢ ⟦ G ⟧A
    forget G = map G λ y → π₁

    comp' : (G : Functor ℓA X xs tt)
      → Dl c (⟦ G ⟧TheoryTy Mot) ⊢ ⟦ δ G ⟧TheoryTy D
    comp' (k B) = liftTy ∘⊢ liftTy ∘⊢ lowerTy
    comp' (Var x) =
      liftTy ∘⊢ ∂-counit ∘⊢ Dl→∂⌈⌉ w
      ∘⊢ Dl-map c (π₂ {A = A x} {B = √[ ⌈ w ⌉ ] (D x)})
      ∘⊢ lowerTy
    comp' (⊕e Y G) = ⊕ᴰ-elim λ y → σ⊕ y ∘⊢ comp' (G y)
    comp' (&e Y G) = &ᴰ-intro λ y → comp' (G y) ∘⊢ π y
    comp' (G &e2 G') = comp' G ,&p comp' G'
    comp' (⊗e ε· G) = liftTy ∘⊢ liftTy ∘⊢ Dl-map c (forget (⊗e ε· G))
    comp' (⊗e _⊙_ G) =
      ⊕-elim
        (σ⊕ (lift true)
         ∘⊢ ⟦⊗e⟧⁻ (δ (G zero)) (k (LiftTheoryTy ℓD ⟦ G (suc zero) ⟧A))
         ∘⊢ (comp' (G zero) ,⊗ (liftTy ∘⊢ liftTy ∘⊢ forget (G (suc zero)))))
        (σ⊕ (lift false)
         ∘⊢ ⟦⊗e⟧⁻ (k (LiftTheoryTy ℓD (Nu ⟦ G zero ⟧A))) (δ (G (suc zero)))
         ∘⊢ ((liftTy ∘⊢ liftTy ∘⊢ (forget (G zero) ,&p id⊢))
             ,⊗ comp' (G (suc zero))))
      ∘⊢ Dl-⊗-out⁺ c
      ∘⊢ Dl-map c (⊗ᵘ→⊗ λ i → ⟦ G i ⟧TheoryTy Mot)

    αc : (x : X) → ⟦ F x ⟧TheoryTy Mot ⊢ Mot x
    αc x = (roll ∘⊢ forget (F x))
        ,& ∂-intro (roll ∘⊢ comp' (F x) ∘⊢ ∂⌈⌉→Dl w)

  complete : (x : X) → Dl c (A x) ⊢ D x
  complete x = ∂-intro⁻ (π₂ ∘⊢ rec _ αc x) ∘⊢ Dl→∂⌈⌉ w

-- ---------------------------------------------------------------------------
-- ITERATION.  One letter is not a parser.  `δ` freezes its undifferentiated
-- occurrences at `μ F`, so the *next* derivative must freeze at `μ (δ ∘ F)`
-- -- which is exactly what taking `δ` of the already-differentiated system
-- does.  That is the thing `Derivative/OneStep`s `δ` cannot do: there
-- `δ (dv x) = ⊥̂`, so a second derivative annihilates every recursive
-- occurrence.
--
-- The level grows by one `ℓF` per letter, so it is indexed by the word.
module _ {X : Type ℓX} {xs : X → Unit} where

  levOf : Level → String → Level
  levOf ℓ [] = ℓ
  levOf ℓ (c ∷ w) = levOf (ℓ-max (ℓF ℓ) ℓX) w

  -- `Dl-string (c ∷ w) = Dl-string w ∘ Dl c`, so the letters are consumed
  -- left to right and each `δ` is taken at the system the previous one built.
  δ* : {ℓ : Level} (w : String) (F : (x : X) → Functor ℓ X xs tt)
     → (x : X) → Functor (levOf ℓ w) X xs tt
  δ* [] F = F
  δ* (c ∷ w) F = δ* w λ x → δ F c (F x)

  D* : {ℓ : Level} (w : String) (F : (x : X) → Functor ℓ X xs tt)
     → (x : X) → TheoryTy _ tt
  D* w F = μ (δ* w F)

  -- Both directions transport along the word, one letter at a time.
  sound* : {ℓ : Level} (w : String) (F : (x : X) → Functor ℓ X xs tt)
    → (x : X) → D* w F x ⊢ Dl-string w (μ F x)
  sound* [] F x = id⊢
  sound* (c ∷ w) F x =
    Dl-string-map w (sound F c x) ∘⊢ sound* w (λ y → δ F c (F y)) x

  complete* : {ℓ : Level} (w : String) (F : (x : X) → Functor ℓ X xs tt)
    → (x : X) → Dl-string w (μ F x) ⊢ D* w F x
  complete* [] F x = id⊢
  complete* (c ∷ w) F x =
    complete* w (λ y → δ F c (F y)) x ∘⊢ Dl-string-map w (complete F c x)

  -- THE PARSER.  Consume the input by differentiating, once per letter, and
  -- read the answer off the empty word: a null parse of `D* w F` is a parse
  -- of `w`, and conversely.  Both directions are `sound*`/`complete*` moved
  -- across `∂[ ⌈ w ⌉ ] ≅ Dl-string w` and out to the residual, where `⌈ w ⌉`
  -- makes them statements about the word rather than about a derivative.
  fromNull : {ℓ : Level} (w : String) (F : (x : X) → Functor ℓ X xs tt)
    (x : X) → εTy ⊢ D* w F x → ⌈ w ⌉ ⊢ μ F x
  fromNull w F x nul =
    ⊸-app {A = ⌈ w ⌉} {C = μ F x}
    ∘⊢ (id⊢ ,⊗ (∂⌈⌉→⊸ w {B = μ F x} ∘⊢ Dl→∂⌈⌉ w ∘⊢ sound* w F x ∘⊢ nul))
    ∘⊢ ⊗ε-unit-r⁻

  toNull : {ℓ : Level} (w : String) (F : (x : X) → Functor ℓ X xs tt)
    (x : X) → ⌈ w ⌉ ⊢ μ F x → εTy ⊢ D* w F x
  toNull w F x p =
    complete* w F x ∘⊢ ∂⌈⌉→Dl w ∘⊢ ⊸→∂⌈⌉ w {B = μ F x}
    ∘⊢ ⊸-lam {A = ⌈ w ⌉} {B = εTy} {C = μ F x} (p ∘⊢ ⊗ε-unit-r)
