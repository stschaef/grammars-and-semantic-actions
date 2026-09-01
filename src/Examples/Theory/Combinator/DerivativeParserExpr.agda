{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `Derivative/Parser` at `E → E + T | T`, `T → ( E ) | x`: left-recursive,
   mutually recursive, non-regular, applied with no grammar transformation.
   `Derivative/OneStep` could not: its `CF` was a private code language. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Examples.Theory.Combinator.DerivativeParserExpr where

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

DG : (w : String) → NT → TheoryTy _ tt
DG w = D* w G

E-sound : (w : String) → DG w nE ⊢ Dl-string w E
E-sound w = sound* w G nE

E-complete : (w : String) → Dl-string w E ⊢ DG w nE
E-complete w = complete* w G nE

-- the parser: differentiate through the word, read off the empty word
E-fromNull : (w : String) → εTy ⊢ DG w nE → ⌈ w ⌉ ⊢ E
E-fromNull w = fromNull w G nE

E-toNull : (w : String) → ⌈ w ⌉ ⊢ E → εTy ⊢ DG w nE
E-toNull w = toNull w G nE

-- A worked word: `x` is `E → T → x`, three nodes deep.
private
  varX : Trm (‵x ∷ [])
  varX = roll _ (true , lift Eq.refl)

  exX : E (‵x ∷ [])
  exX = roll _ (true , lift varX)

  parsedX : ⌈ ‵x ∷ [] ⌉ ⊢ E
  parsedX _ Eq.refl = exX

nullX : εTy ⊢ DG (‵x ∷ []) nE
nullX = E-toNull (‵x ∷ []) parsedX

-- read back off the empty word, through the grammar's own algebra: the
-- whole parsing-with-derivatives loop
treeX : ⌈ ‵x ∷ [] ⌉ ⊢ KG nE
treeX = readG nE ∘⊢ E-fromNull (‵x ∷ []) nullX


-- The value survives, not only the types: `fromNull`/`toNull` cross the
-- adjunction, whose formers are `opaque` (a deliberate boundary in
-- `Derivative/General`); `unfolding` is the sanctioned way through, and
-- with it the parse of `x` comes back out as `emb var`.
opaque
  unfolding ∂-intro ∂-intro⁻ ∂⌈⌉→Dl Dl→∂⌈⌉ ∂⌈⌉→⊸ ⊸→∂⌈⌉

  treeX-computes : treeX (‵x ∷ []) Eq.refl Eq.≡ emb var
  treeX-computes = Eq.refl
