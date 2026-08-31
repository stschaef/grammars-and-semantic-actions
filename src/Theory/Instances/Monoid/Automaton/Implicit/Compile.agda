{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Compiling a regular-expression syntax tree to an implicit automaton.

   `Implicit/RegExp` gives five constructions, each demanding the
   determinism side conditions as arguments, so there is no total
   deterministic regular expressions to automata.  `DetReg`, ported from
   `Grammar/RegularExpression/Deterministic.agda`, is the fragment that
   does compile: a regex indexed by the complements of its follow-last
   and first sets and by the negation of its nullability, with the
   disjointness conditions carried on the `⊗`, `⊕` and `*` nodes.

   `compile` is total on `DetReg`, and is mutually recursive with the
   three facts that turn a `DetReg` index into the argument the next
   construction up wants: `nullOf` reads the nullability index off
   `null`, `δᵢ-fail` reads the first set off `δᵢ`, `δq-fail` reads the
   follow-last set off `δq`.  Those are the syntactic counterparts of
   `¬NullableAut`/`¬FirstAut`/`¬FollowLastAut`, which say the same
   things about `Parse M` rather than about the state table; composing
   the two layers is what will give `Parse (compile dr) ≅ ⟦ r ⟧r`.

   Everything here is automaton *data* -- `Q`, `acc`, `null`, `δ` -- so
   nothing in this file is grammar-valued and nothing is a `⊢`-term. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Implicit.Compile
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; _and_ ; _or_ ; if_then_else_
        ; true≢false ; false≢true ; isSetBool)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit* ; tt* ; isSetUnit*)
open import Cubical.Relation.Nullary.Base using (Discrete ; yes ; no)
import Cubical.Data.Sum as Sum
open Sum using (_⊎_)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit.RegExp
  Alphabet isSetAlphabet public

open ImplicitDeterministicAutomaton

private variable
  ℓ : Level
  b b' : Bool

-- Sets of letters.
--
-- `Cubical.Foundations.Powerset.More`, which the old `DetReg` used for
-- `ℙ`, is not in this cubical, and its `ℙ` is `ℓ-zero`-only anyway.
-- Nothing below inspects a membership proof, so the h-level the old
-- development kept is not needed and a bare predicate does.

ℙ : Type (ℓ-suc ℓAlph)
ℙ = Alphabet → Type ℓAlph

_∈ℙ_ : Alphabet → ℙ → Type ℓAlph
c ∈ℙ P = P c

⊤ℙ : ℙ
⊤ℙ _ = Unit*

_∩ℙ_ : ℙ → ℙ → ℙ
(P ∩ℙ P') c = P c × P' c

⟦_⟧ℙ : Alphabet → ℙ
⟦ c ⟧ℙ c' = c ≡ c'

-- a decidable character class, as the set it denotes
⟦_⟧sat : (Alphabet → Bool) → ℙ
⟦ P ⟧sat c = Lift ℓAlph (P c ≡ true)

¬ℙ_ : ℙ → ℙ
(¬ℙ P) c = P c → Empty.⊥* {ℓAlph}

infixr 22 _∩ℙ_
infix 25 ¬ℙ_

-- Deterministic regular expressions: the constructors are the
-- deterministic combinators, so a `DetReg` is one term rather than a
-- syntax tree plus a proof about it.  Indexed by the complements of the
-- follow-last and first sets and by the negation of nullability, so that
-- all three indices are propositions.

data DetReg : ℙ → ℙ → Bool → Type (ℓ-suc ℓAlph) where
  εdr : DetReg ⊤ℙ ⊤ℙ false
  ⊥dr : DetReg ⊤ℙ ⊤ℙ true
  ＂_＂dr : (c : Alphabet) → DetReg ⊤ℙ (¬ℙ ⟦ c ⟧ℙ) true
  -- A class needs no more than a literal does.  Its follow-last set is
  -- empty (`⊤ℙ` is its complement), so sequencing and starring a class
  -- carry exactly the trivial side condition that a literal carries;
  -- only *alternation* of two classes asks for anything, namely that
  -- they are disjoint.
  satdr : (P : Alphabet → Bool) → DetReg ⊤ℙ (¬ℙ ⟦ P ⟧sat) true
  _⊗DR[_]_ :
    {¬FL ¬FL' ¬F ¬F' : ℙ} →
    (dr : DetReg ¬FL ¬F true) →
    (seq-unambig : (c : Alphabet) → (c ∈ℙ ¬FL) ⊎ (c ∈ℙ ¬F')) →
    (dr' : DetReg ¬FL' ¬F' b') →
    DetReg
      (if b' then ¬FL' else ¬FL ∩ℙ ¬F' ∩ℙ ¬FL')
      ¬F
      true
  _⊕DR[_]_ :
    {¬FL ¬FL' ¬F ¬F' : ℙ} →
    {notBothNull : b or b' Eq.≡ true} →
    (dr : DetReg ¬FL ¬F b) →
    (sep : (c : Alphabet) → (c ∈ℙ ¬F) ⊎ (c ∈ℙ ¬F')) →
    (dr' : DetReg ¬FL' ¬F' b') →
    DetReg
      (¬FL ∩ℙ ¬FL' ∩ℙ (if (b and b') then ⊤ℙ else ¬F ∩ℙ ¬F'))
      (¬F ∩ℙ ¬F')
      (b and b')
  _*DR[_] :
    {¬FL ¬F : ℙ} →
    (dr : DetReg ¬FL ¬F true) →
    (seq-unambig : (c : Alphabet) → (c ∈ℙ ¬FL) ⊎ (c ∈ℙ ¬F)) →
    DetReg (¬F ∩ℙ ¬FL) ¬F false

infixr 20 _⊗DR[_]_
infixr 20 _⊕DR[_]_
infix 30 _*DR[_]
infix 30 ＂_＂dr

-- The state set is the set of positions -- one per literal.  It is read
-- off the *regex*, not off the `DetReg`, so two determinism proofs for
-- the same regex compile to automata of the same type.

States : {¬FL ¬F : ℙ} {b : Bool} → DetReg ¬FL ¬F b → Type ℓAlph
States εdr = Empty.⊥*
States ⊥dr = Empty.⊥*
States ＂ c ＂dr = Unit*
States (satdr P) = Unit*
States (dr ⊗DR[ _ ] dr') = States dr ⊎ States dr'
States (dr ⊕DR[ _ ] dr') = States dr ⊎ States dr'
States (dr *DR[ _ ]) = States dr

isSetStates : {¬FL ¬F : ℙ} {b : Bool} (dr : DetReg ¬FL ¬F b) → isSet (States dr)
isSetStates εdr x = Empty.rec* x
isSetStates ⊥dr x = Empty.rec* x
isSetStates ＂ c ＂dr = isSetUnit*
isSetStates (satdr P) = isSetUnit*
isSetStates (dr ⊗DR[ _ ] dr') = Sum.isSet⊎ (isSetStates dr) (isSetStates dr')
isSetStates (dr ⊕DR[ _ ] dr') = Sum.isSet⊎ (isSetStates dr) (isSetStates dr')
isSetStates (dr *DR[ _ ]) = isSetStates dr

-- Bool scaffolding.  `if-true` is the only way the `if (M .acc q)` in
-- `⊗Aut`/`*Aut` gets out of the way, since `acc q ≡ true` is a path.

private
  and-elim-l : {x y : Bool} → x and y ≡ true → x ≡ true
  and-elim-l {true} _ = refl
  and-elim-l {false} p = Empty.rec (false≢true p)

  and-elim-r : {x y : Bool} → x and y ≡ true → y ≡ true
  and-elim-r {true} p = p
  and-elim-r {false} p = Empty.rec (false≢true p)

  if-true : {X : Type ℓ} {x : Bool} {A B : X}
    → x ≡ true → A ≡ (if x then A else B)
  if-true {A = A} {B = B} p = sym (cong (λ y → if y then A else B) p)

  -- `⊕Aut` wants one of the two branches marked non-nullable; the index
  -- says at least one is, and which one decides `⊕Aut .null`.
  notBoth : {N N' : Bool} → b or b' Eq.≡ true
    → N ≡ not b → N' ≡ not b' → (N ≡ false) ⊎ (N' ≡ false)
  notBoth {b = true} _ p _ = Sum.inl p
  notBoth {b = false} {b' = true} _ _ q = Sum.inr q
  notBoth {b = false} {b' = false} () _ _

-- The compiler.
--
-- `compile` cannot be defined before the three index-reading lemmas,
-- because the side conditions it must hand to `⊗Aut` and friends *are*
-- those lemmas at the subexpressions; and the lemmas cannot be stated
-- before `compile`, because they are about its output.  Hence the
-- mutual block.

module _ (discAlpha : Discrete Alphabet) where

  compile : {¬FL ¬F : ℙ}
    → (dr : DetReg ¬FL ¬F b) → ImplicitDeterministicAutomaton (States dr)

  -- `b` is the *negation* of nullability, so `null` is `not b`.
  nullOf : {¬FL ¬F : ℙ}
    → (dr : DetReg ¬FL ¬F b) → compile dr .null ≡ not b

  -- a letter outside the first set never leaves the initial state
  δᵢ-fail : {¬FL ¬F : ℙ}
    → (dr : DetReg ¬FL ¬F b) (c : Alphabet) → c ∈ℙ ¬F
    → fail ≡ compile dr .δᵢ c

  -- ...and outside the follow-last set never leaves an accepting one
  δq-fail : {¬FL ¬F : ℙ}
    → (dr : DetReg ¬FL ¬F b) (c : Alphabet) → c ∈ℙ ¬FL
    → (q : States dr) → compile dr .acc q ≡ true → fail ≡ compile dr .δq q c

  -- The two packaged side conditions, in exactly the shape `⊗Aut`,
  -- `*Aut` and `⊕Aut` ask for.
  private
    seqOf : {¬FL ¬FL' ¬F ¬F' : ℙ}
      (dr : DetReg ¬FL ¬F b) (dr' : DetReg ¬FL' ¬F' b')
      → ((c : Alphabet) → (c ∈ℙ ¬FL) ⊎ (c ∈ℙ ¬F'))
      → (c : Alphabet)
      → ((q : States dr) → compile dr .acc q ≡ true
           → fail ≡ compile dr .δq q c)
        ⊎ (fail ≡ compile dr' .δᵢ c)
    seqOf dr dr' su c =
      Sum.map (δq-fail dr c) (δᵢ-fail dr' c) (su c)

    firstsOf : {¬FL ¬FL' ¬F ¬F' : ℙ}
      (dr : DetReg ¬FL ¬F b) (dr' : DetReg ¬FL' ¬F' b')
      → ((c : Alphabet) → (c ∈ℙ ¬F) ⊎ (c ∈ℙ ¬F'))
      → (c : Alphabet)
      → (fail ≡ compile dr .δᵢ c) ⊎ (fail ≡ compile dr' .δᵢ c)
    firstsOf dr dr' sep c =
      Sum.map (δᵢ-fail dr c) (δᵢ-fail dr' c) (sep c)

  compile εdr = εAut discAlpha
  compile ⊥dr = ⊥Aut discAlpha
  compile ＂ c ＂dr = litAut discAlpha c
  compile (satdr P) = satAut discAlpha P
  compile (dr ⊗DR[ su ] dr') =
    ⊗Aut discAlpha (compile dr) (compile dr')
      (nullOf dr) (seqOf dr dr' su)
  compile (_⊕DR[_]_ {notBothNull = nbn} dr sep dr') =
    ⊕Aut discAlpha (compile dr) (compile dr')
      (notBoth nbn (nullOf dr) (nullOf dr'))
      (firstsOf dr dr' sep)
  compile (dr *DR[ su ]) =
    *Aut discAlpha (compile dr) (nullOf dr) (seqOf dr dr su)

  nullOf εdr = refl
  nullOf ⊥dr = refl
  nullOf ＂ c ＂dr = refl
  nullOf (satdr P) = refl
  nullOf (dr ⊗DR[ su ] dr') = refl
  nullOf (_⊕DR[_]_ {b = true} {notBothNull = nbn} dr sep dr') = nullOf dr'
  nullOf (_⊕DR[_]_ {b = false} {b' = true} {notBothNull = nbn} dr sep dr') =
    nullOf dr
  nullOf (_⊕DR[_]_ {b = false} {b' = false} {notBothNull = ()} dr sep dr')
  nullOf (dr *DR[ su ]) = refl

  δᵢ-fail εdr c _ = refl
  δᵢ-fail ⊥dr c _ = refl
  δᵢ-fail ＂ c' ＂dr c c∉F with discAlpha c' c
  ... | yes c'≡c = Empty.rec* (c∉F c'≡c)
  ... | no _ = refl
  δᵢ-fail (satdr P) c c∉F with P c
  ... | true = Empty.rec* (c∉F (lift refl))
  ... | false = refl
  δᵢ-fail (dr ⊗DR[ su ] dr') c c∉F =
    cong (mapFreelyAddFail Sum.inl) (δᵢ-fail dr c c∉F)
  δᵢ-fail (dr ⊕DR[ sep ] dr') c (c∉F , c∉F') with sep c
  ... | Sum.inl _ = cong (mapFreelyAddFail Sum.inr) (δᵢ-fail dr' c c∉F')
  ... | Sum.inr _ = cong (mapFreelyAddFail Sum.inl) (δᵢ-fail dr c c∉F)
  δᵢ-fail (dr *DR[ su ]) c c∉F = δᵢ-fail dr c c∉F

  δq-fail εdr c _ ()
  δq-fail ⊥dr c _ ()
  δq-fail ＂ c' ＂dr c _ _ _ = refl
  δq-fail (satdr P) c _ _ _ = refl
  -- `b' ≡ true`: the right factor is not nullable, so no state of the
  -- left factor accepts and there is nothing to prove there.
  δq-fail (_⊗DR[_]_ {b' = true} dr su dr') c c∉FL' (Sum.inl q) accq =
    Empty.rec (true≢false
      (sym (and-elim-r {x = compile dr .acc q} {y = compile dr' .null} accq)
       ∙ nullOf dr'))
  δq-fail (_⊗DR[_]_ {b' = true} dr su dr') c c∉FL' (Sum.inr q') accq =
    cong (mapFreelyAddFail Sum.inr) (δq-fail dr' c c∉FL' q' accq)
  -- `b' ≡ false`: a state of the left factor can accept, and the letter
  -- must miss both the left's follow-last and the right's first set.
  δq-fail (_⊗DR[_]_ {b' = false} dr su dr') c
    (c∉FL , c∉F' , c∉FL') (Sum.inl q) accq =
    stepInl ∙ if-true (and-elim-l accq)
    where
    stepInl :
      fail ≡
      Sum.rec
        (λ _ → mapFreelyAddFail Sum.inr (compile dr' .δᵢ c))
        (λ _ → mapFreelyAddFail Sum.inl (compile dr .δq q c))
        (seqOf dr dr' su c)
    stepInl with su c
    ... | Sum.inl _ = cong (mapFreelyAddFail Sum.inr) (δᵢ-fail dr' c c∉F')
    ... | Sum.inr _ =
      cong (mapFreelyAddFail Sum.inl)
        (δq-fail dr c c∉FL q (and-elim-l accq))
  δq-fail (_⊗DR[_]_ {b' = false} dr su dr') c
    (c∉FL , c∉F' , c∉FL') (Sum.inr q') accq =
    cong (mapFreelyAddFail Sum.inr) (δq-fail dr' c c∉FL' q' accq)
  -- `⊕Aut` never crosses between the branches, so the follow-last of
  -- each branch on its own is all that is wanted.
  δq-fail (dr ⊕DR[ sep ] dr') c (c∉FL , c∉FL' , _) (Sum.inl q) accq =
    cong (mapFreelyAddFail Sum.inl) (δq-fail dr c c∉FL q accq)
  δq-fail (dr ⊕DR[ sep ] dr') c (c∉FL , c∉FL' , _) (Sum.inr q') accq =
    cong (mapFreelyAddFail Sum.inr) (δq-fail dr' c c∉FL' q' accq)
  δq-fail (dr *DR[ su ]) c (c∉F , c∉FL) q accq =
    stepLoop ∙ if-true accq
    where
    stepLoop :
      fail ≡
      Sum.rec
        (λ _ → compile dr .δᵢ c)
        (λ _ → compile dr .δq q c)
        (seqOf dr dr su c)
    stepLoop with su c
    ... | Sum.inl _ = δᵢ-fail dr c c∉F
    ... | Sum.inr _ = δq-fail dr c c∉FL q accq

  -- What the semantic layer consumes.
  --
  -- `¬NullableAut`, `¬FirstAut` and `¬FollowLastAut` take precisely
  -- these three, and turn them into the disjointness facts about
  -- `Parse (compile dr)` that `⊕Aut≅`/`⊗Aut≅` need.  Nothing here
  -- mentions a grammar, so that port can land on top without touching
  -- this file.

  compileNotNull : {¬FL ¬F : ℙ}
    → (dr : DetReg ¬FL ¬F true) → compile dr .null ≡ false
  compileNotNull = nullOf

  compileNullable : {¬FL ¬F : ℙ}
    → (dr : DetReg ¬FL ¬F false) → compile dr .null ≡ true
  compileNullable = nullOf

  -- ...and the DFA, by relabelling.  No subset construction: `DetReg`
  -- is exactly the fragment whose positions are already deterministic.

  compileDA : {¬FL ¬F : ℙ}
    → (dr : DetReg ¬FL ¬F b)
    → DeterministicAutomaton (FreelyAddFail+Initial (States dr))
  compileDA dr = IDA→DA (compile dr)

  -- ...and its dead state, which is the freely added `fail`
  compileDead : {¬FL ¬F : ℙ} (dr : DetReg ¬FL ¬F b) → Deadness (compileDA dr)
  compileDead dr = failDead (compile dr)

  isSetCompileStates : {¬FL ¬F : ℙ} (dr : DetReg ¬FL ¬F b)
    → isSet (FreelyAddFail+Initial (States dr))
  isSetCompileStates dr = isSetFreelyAddFail+Initial _ (isSetStates dr)
