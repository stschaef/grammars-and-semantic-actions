{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Derivative/Parser` at the expression grammar, unchanged.

   `E → E + T | T`, `T → ( E ) | x` is the grammar `Ascent/Expr` parses by
   recursive ascent and `LeftCorner/Expr` parses by left-factoring.  It is
   left-recursive, mutually recursive, and non-regular -- and `ExprGrammar`
   already presents it as a `Functor` system `G`, which is exactly the shape
   `Derivative/Parser` takes.  So the derivative construction applies to it with no
   transformation at all: no left-corner transform, no left-factoring, no
   lookahead table.

   That is the claim `Derivative/OneStep` could not make -- its `CF` was a
   private code language, so `δ` did not reach the `μ F` families the rest of
   the tree is built on. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Derivative.ParserExpr where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

open import Theory.Instances.Monoid.Combinator.ExprGrammar
open import Theory.Instances.Monoid.Combinator.Core Tk _≟K_
open import Theory.Instances.Monoid.Derivative Tk isSetAlphabet
  using (Dl ; Dl-string)
open import Theory.Instances.Monoid.Derivative.General Tk isSetAlphabet
  using (∂-intro ; ∂-intro⁻ ; ∂⌈⌉→Dl ; Dl→∂⌈⌉ ; ∂⌈⌉→⊸ ; ⊸→∂⌈⌉)
open import Theory.Instances.Monoid.Combinator.Derivative.Parser Tk _≟K_

-- The derivative of the expression grammar by a word, as a grammar.
DG : (w : String) → NT → TheoryTy _ tt
DG w = D* w G

-- Both directions, at the real grammar and at any word.
E-sound : (w : String) → DG w nE ⊢ Dl-string w E
E-sound w = sound* w G nE

E-complete : (w : String) → Dl-string w E ⊢ DG w nE
E-complete w = complete* w G nE

-- ...and the parser: differentiate through the word, read off the empty word.
E-fromNull : (w : String) → εTy ⊢ DG w nE → ⌈ w ⌉ ⊢ E
E-fromNull w = fromNull w G nE

E-toNull : (w : String) → ⌈ w ⌉ ⊢ E → εTy ⊢ DG w nE
E-toNull w = toNull w G nE

-- A worked word.  `x` is `E → T → x`, three nodes deep in the real grammar.
private
  varX : Trm (‵x ∷ [])
  varX = roll _ (true , lift Eq.refl)

  exX : E (‵x ∷ [])
  exX = roll _ (true , lift varX)

  parsedX : ⌈ ‵x ∷ [] ⌉ ⊢ E
  parsedX _ Eq.refl = exX

-- Differentiating by `x` turns that parse into a null parse of `DG`...
nullX : εTy ⊢ DG (‵x ∷ []) nE
nullX = E-toNull (‵x ∷ []) parsedX

-- ...and reading it back off the empty word, then through the grammar's own
-- algebra, gives the expression tree.  This is the whole parsing-with-derivatives loop on the
-- grammar the rest of the tree parses.
treeX : ⌈ ‵x ∷ [] ⌉ ⊢ KG nE
treeX = readG nE ∘⊢ E-fromNull (‵x ∷ []) nullX


-- Does the *value* survive, or only the types?  `fromNull`/`toNull` go
-- through the adjunction, whose formers are `opaque`, so this does not reduce
-- on its own -- that is a deliberate boundary in `Derivative/General`, not a
-- stuck transport.  `unfolding` is the sanctioned way to look through it, and
-- with it the loop computes: the parse of `x` really is carried through two
-- derivative constructions and back out as `emb var`.
opaque
  unfolding ∂-intro ∂-intro⁻ ∂⌈⌉→Dl Dl→∂⌈⌉ ∂⌈⌉→⊸ ⊸→∂⌈⌉

  treeX-computes : treeX (‵x ∷ []) Eq.refl Eq.≡ emb var
  treeX-computes = Eq.refl
