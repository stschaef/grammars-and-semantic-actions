{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Brzozowski derivatives: matching in one left-to-right pass.

   `decide-r` builds a *decision over every parse*, so its cost tracks the
   number of parses: `(a|a)*b` on 14 letters has 2¹⁴ of them and refuting
   them all does not finish.  Enumerating parses is the wrong algorithm for
   a regular language.

   A derivative does not enumerate.  `δ r c` is another regex -- the one
   matching what may follow `c` -- so membership is a fold of `δ` along the
   input, ending in a nullability test.  That is one step per character,
   whatever the ambiguity.

   The smart constructors are what keep the *regex* from growing as it is
   differentiated; without them the derivative of a star doubles at every
   step and linear time in steps is not linear time in work. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Regex.Derivative
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (tt*)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
import Cubical.Data.List.Properties as LP

open import Theory.Instances.Monoid.Regex.Notation Alphabet _≟_ ℓ public

RE? : Type ℓAlph
RE? = Σ[ n ∈ Nullability ] RE n

isNullable : Nullability → Bool
isNullable nullable = true
isNullable notNullable = false

∅? ε? : RE?
∅? = notNullable , ⊥r
ε? = nullable , εr

------------------------------------------------------------------------
-- Smart constructors.  `⊥` annihilates, `ε` is the unit; without these
-- the derivative of a star doubles in size at every character.

infixr 20 _⊗s_
infixr 19 _⊕s_

_⊗s_ : RE? → RE? → RE?
(_ , ⊥r) ⊗s _ = ∅?
(_ , εr) ⊗s y = y
_ ⊗s (_ , ⊥r) = ∅?
(n , r) ⊗s (n' , r') = n ·ν n' , r ⊗r r'

_⊕s_ : RE? → RE? → RE?
(_ , ⊥r) ⊕s y = y
x ⊕s (_ , ⊥r) = x
(n , r) ⊕s (n' , r') = n +ν n' , r ⊕r r'

------------------------------------------------------------------------
-- The derivative itself

δ : ∀ {n} → RE n → Alphabet → RE?
δ εr c = ∅?
δ ⊥r c = ∅?
δ ⟨ d ⟩r c = Sum.rec (λ _ → ε?) (λ _ → ∅?) (d ≟ c)
δ (satr P) c with P c
... | true = ε?
... | false = ∅?
δ (_⊗r_ {nullable} {n'} r r') c = (δ r c ⊗s (n' , r')) ⊕s δ r' c
δ (_⊗r_ {notNullable} {n'} r r') c = δ r c ⊗s (n' , r')
δ (r ⊕r r') c = δ r c ⊕s δ r' c
δ (r *r) c = δ r c ⊗s (nullable , r *r)

δ? : RE? → Alphabet → RE?
δ? (n , r) c = δ r c

------------------------------------------------------------------------
-- The residual after a prefix.  This is syntax-to-syntax, like `⟦_⟧` or
-- `anyOfr`: it computes *which regex* to try next, not whether anything
-- matched.  Nothing here decides.

residual : ∀ {n} → RE n → List Alphabet → RE?
residual r [] = _ , r
residual r (c ∷ w) = residual (δ r c .snd) w

------------------------------------------------------------------------
-- What is still owed, and where it plugs in.
--
-- `Grammar/Greedy/Regex.agda` (branch `feat/lex`) has the shape.  Its
-- carrier is a *table*:
--
--     RunResult q = Greedy (Trace true q) ⊕ ¬G (Trace true q ⊗ ⊤)
--     scan : string ⊢ &[ q ∈ States ] RunResult q
--
-- folded once over the input -- `scan-nil` dispatching on `isAcc q` at ε,
-- `scan-cons` consulting `RunResult (δ q c)`.  One pass, whatever the
-- ambiguity, because the table holds every state at once rather than
-- every parse.
--
-- Ours is the same with the automaton deleted, indexing by the residual
-- regex instead of by a DFA state:
--
--     RunResult x = Greedy (ty ⟦ x .snd ⟧) ⊕ ¬Ty (ty ⟦ x .snd ⟧ ⊗ ⊤Ty)
--     scan : ⊤Ty ⊢ &[ x ∈ RE? ] RunResult x
--
-- Three of the four pieces exist:
--
--   * `scan-nil`'s dispatch is `decNullable` (Regex/Base) -- ε matches
--     exactly the nullable regexes, and the index decides which.
--   * `scan-cons`'s refutation step is `noExt-step` (Greedy/Base): a
--     nonempty prefix must start with `c`, by the precision of
--     `literal c`.
--   * `Greedy` and its projections are stated (Greedy/Base).
--
-- The fourth is the derivative theorem, stated below against `Dl` -- the
-- semantic derivative that already exists.  Both directions are needed
-- and neither is an iso: an ambiguous `r` matches ε in several ways, so
-- the two maps are a retraction, not an equivalence.  That is enough,
-- because a decision only needs the witness forward and the refutation
-- back.
--
-- Until then there is deliberately no `match` here.  A `Bool`-valued
-- matcher would decide in the metalanguage and carry neither witness nor
-- refutation, which is the thing this development is for.

------------------------------------------------------------------------
-- The syntactic derivative computes the semantic one.
--
-- `Dl c A m = A (c ∷ m)` (Monoid/Derivative), so this says: stripping a
-- leading `c` from the language of `r` is the language of `δ r c`.  It is
-- an *iso*, which is the point -- one statement gives both the transfer
-- of witnesses and the transfer of refutations, and decidability of every
-- derivative follows from it by löb.

open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
  using (Dl)

-- `Dl c A m` is `A (c ∷ m)`, so these are all statements about what a
-- word beginning with `c` can be.

δ-sound : ∀ {n} (r : RE n) (c : Alphabet)
  → ty ⟦ δ r c .snd ⟧ ⊢ Dl c (ty ⟦ r ⟧)
δ-sound εr c = ⊥Ty-elim
δ-sound ⊥r c = ⊥Ty-elim
-- an `εTy` element carries `[] Eq.≡ m`, so `c ∷ m` is `c ∷ []`
δ-sound ⟨ d ⟩r c with d ≟ c
... | Sum.inl Eq.refl = λ m x → Eq.ap (d ∷_) (Eq.sym (x .snd .fst))
... | Sum.inr _ = ⊥Ty-elim
δ-sound (satr P) c with P c in eq
... | true = λ m x → (c , Eq.eqToPath eq) , Eq.ap (c ∷_) (Eq.sym (x .snd .fst))
... | false = ⊥Ty-elim
δ-sound (r ⊗r r') c = {!!}
δ-sound (r ⊕r r') c = {!!}
δ-sound (r *r) c = {!!}

δ-complete : ∀ {n} (r : RE n) (c : Alphabet)
  → Dl c (ty ⟦ r ⟧) ⊢ ty ⟦ δ r c .snd ⟧
-- `εTy (c ∷ m)` would make `[]` a cons
δ-complete εr c m x = Empty.rec (LP.¬nil≡cons (Eq.eqToPath (x .snd .fst)))
δ-complete ⊥r c m x = Empty.rec (x .lower)
δ-complete ⟨ d ⟩r c with d ≟ c
... | Sum.inl Eq.refl =
      λ m x → (λ ()) , Eq.sym (Eq.pathToEq (LP.cons-inj₂ (Eq.eqToPath x))) , tt*
... | Sum.inr ne =
      λ m x → Empty.rec (ne (Eq.pathToEq (sym (LP.cons-inj₁ (Eq.eqToPath x)))))
δ-complete (satr P) c = {!!}
δ-complete (r ⊗r r') c = {!!}
δ-complete (r ⊕r r') c = {!!}
δ-complete (r *r) c = {!!}
