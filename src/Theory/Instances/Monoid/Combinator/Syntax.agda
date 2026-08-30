{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Grammars, written once, for every answer.

   `Core` makes the *combinators* answer-generic.  This module makes the
   things one builds out of them answer-generic: repetition, and a compiler
   from regular expressions to parsers.  Instantiating at `DecAnswer`,
   `MaybeAnswer` or `NDAnswer` gives a decider, a `Maybe`-parser or an
   enumerator from the same text.

   Nothing beyond `AnswerFunctor` is needed.  A grammar is a `μ` and `many`
   relabels along its `roll`/`unroll` pair, which `KleeneStar` proves to be an
   isomorphism (`roll↑≅`) -- so `mapP≅` suffices and no variance leaks in. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns
import Theory.Instances.Monoid.Combinator.Core as C

module Theory.Instances.Monoid.Combinator.Syntax
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (𝒯 : C.AnswerFunctor Alphabet _≟_)
  where

open import Cubical.Data.List using (List)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit* ; tt ; tt*)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet public
-- NOT public: `Reg`'s constructors would collide with other regex syntaxes
open import Theory.Instances.Monoid.Combinator.Grammars.Regex Alphabet _≟_

open Combinators 𝒯

private variable ℓA ℓB ℓD ℓK : Level

module _ (ℓK : Level) (A : TheorySet ℓA tt) where
  private
    module P = Fix ℓK (StarSet A)

    ℓE : Level
    ℓE = ℓ⊗ (ℓF ℓA) P.ℓ𝒦

  -- `A *`, right-nested.  `many` cannot be given a nullable element parser:
  -- `seq` puts it in the guarded slot and `nil : Parser ⟨□⟩ ⟨□⟩` has no
  -- `⟨▷⟩` codomain to go there.  agdarsec carries that as a side condition;
  -- here it is a type error.
  many : ⊤Ty ⊢ Parser ℓE ⟨▷⟩ ⟨□⟩ A
       → ⊤Ty ⊢ Parser P.ℓ𝒦 ⟨□⟩ ⟨□⟩ (StarSet A)
  many p = P.fix
    (mapP≅ roll↑≅
      ∘⊢ ((pmore ∘⊢ seq (StarSet A) (p ∘⊢ ⊤Ty-intro) P.call) <|> nil))

  some : ⊤Ty ⊢ Parser ℓE ⟨▷⟩ ⟨□⟩ A
       → ⊤Ty ⊢ Parser P.ℓ𝒦 ⟨▷⟩ ⟨□⟩ (A ⊗Set StarSet A)
  some p = seq (StarSet A) p (box (many p))

module _ {D : TheoryTy ℓD tt} where

  option : {ℓK : Level} {A : TheorySet ℓA tt}
    → D ⊢ Parser ℓK ⟨▷⟩ ⟨□⟩ A
    → D ⊢ Parser ℓK ⟨□⟩ ⟨□⟩ (A ⊕Set εSet)
  option p = (pmore ∘⊢ p) <|> nil

  between : {ℓK : Level} {a b c : ParserTag}
    {L : TheorySet ℓA tt} {A : TheorySet ℓB tt} {R : TheorySet ℓD tt}
    → D ⊢ Parser (ℓ⊗ ℓB (ℓ⊗ ℓD ℓK)) b c L
    → D ⊢ Parser (ℓ⊗ ℓD ℓK) a b A → D ⊢ Parser ℓK ⟨▷⟩ a R
    → D ⊢ Parser ℓK ⟨▷⟩ c ((L ⊗Set A) ⊗Set R)
  between {A = A} {R = R} l p r = seq R (seq A l p) r

-- `p (s p)*`.  The element parsers are used at several continuation levels,
-- so here the rank-2 level quantification is real -- unlike quantifying over
-- the hypothesis, which `⊤Ty` being terminal makes free.
sepBy : (ℓK : Level) {A : TheorySet ℓA tt} {S : TheorySet ℓB tt}
  → (∀ {ℓ'} → ⊤Ty ⊢ Parser ℓ' ⟨▷⟩ ⟨□⟩ A)
  → (∀ {ℓ'} → ⊤Ty ⊢ Parser ℓ' ⟨▷⟩ ⟨□⟩ S)
  → ⊤Ty ⊢ Parser (ℓ-max ℓM ℓK) ⟨▷⟩ ⟨□⟩ (A ⊗Set StarSet (S ⊗Set A))
sepBy ℓK {A = A} {S = S} p s =
  seq (StarSet (S ⊗Set A)) p (box (many ℓK (S ⊗Set A) (seq A s (pless ∘⊢ p))))

-- Regular expressions, compiled to parsers.  This is the counterpart of
-- `Thompson.Base`'s `regex→NFA`: the same induction over the same six
-- cases, landing in a parser rather than a machine -- and, unlike the
-- machine, at whatever answer `𝒯` is.

private variable t : ParserTag

-- `ℓK` is the continuation's level: `seq` asks its head for a continuation
-- that already carries the tail, and `many` for one that carries the star,
-- so the recursion is level-polymorphic rather than level-fixed.
⟦_⟧P : (r : Reg t) (ℓK : Level) → ⊤Ty ⊢ Parser (ℓ-max ℓM ℓK) t ⟨□⟩ ⟦ r ⟧
⟦ ＂ c ＂r ⟧P ℓK = tok c
⟦ εr ⟧P ℓK = nil
⟦ r ⊗r s ⟧P ℓK =
  seq ⟦ s ⟧ (⟦ r ⟧P (ℓ-max ℓAlph (ℓ-max (ℓReg s) ℓK)))
            (box (pw ∘⊢ ⟦ s ⟧P ℓK))
⟦ r ⊕r s ⟧P ℓK = ⟦ r ⟧P ℓK <|> ⟦ s ⟧P ℓK
⟦ r *r ⟧P ℓK = many ℓK ⟦ r ⟧ (⟦ r ⟧P (ℓ-max ℓAlph (ℓ-max (ℓF (ℓReg r)) ℓK)))
⟦ ↑r r ⟧P ℓK = pmore ∘⊢ ⟦ r ⟧P ℓK

regex : (r : Reg t) → ⊤Ty ⊢ ty (Ans ⟦ r ⟧)
regex r = runP ℓ-zero (pw ∘⊢ ⟦ r ⟧P ℓ-zero)

