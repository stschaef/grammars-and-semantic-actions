{- A model-generic version of the Lambekᴰ grammar DSL.

   `Grammar.*` interprets the connectives concretely, as set-valued
   families over strings. The modules below instead state what
   structure a category must carry to interpret them, and derive the
   theory from universal properties alone; the families semantics is
   recovered as one model.

   Structure
     Semantics.Signature                    algebraic signatures; the theory of monoids
     Semantics.Structure.IndexedCoproduct   set-indexed coproducts (dual to ccl's IndexedProduct)
     Semantics.Structure.Biclosed           ⊸ and ⟜ as right adjoints of the partial tensors
     Semantics.Structure.Operation          a signature acting on a category, closed slot by slot
     Semantics.Structure.Preservation       left adjoints preserve set-indexed coproducts
     Semantics.Structure.CartesianClosed    ⇒, the closure of & (a mixin, not a Model field)

   The DSL
     Semantics.Model                        what a model is
     Semantics.Notation                     ⊗ ε ⊕ᴰ &ᴰ ⊸ ⟜, and ⊤ ⊥ & ⊕ derived from them
     Semantics.Distributivity               ⊗ over ⊕ᴰ, as instances of Preservation
     Semantics.Inductive.Functor            strictly positive functor codes
     Semantics.Inductive.Algebra            algebras; initial algebra = initial object; Lambek
     Semantics.Inductive.KleeneStar         the star as an initial algebra
     Semantics.Later                        the later modality and guarded fixed points

   Displayed models (for gluing)
     Semantics.Displayed.IndexedProduct     displayed indexed products; coproducts by ^op duality
     Semantics.Displayed.IndexedProductV    the vertical case (what survives reindexing)
     Semantics.Displayed.RightAdjoint       displayed right adjoints, ported to uncurried style
     Semantics.Displayed.Model              displayed models: what a gluing argument is stated against
     Semantics.Displayed.ModelV             vertical displayed models: what reindexes
     Semantics.Displayed.IsoLift            displayed isos from cartesian lifts
     Semantics.Displayed.CatLemmas          cancellation and conjugation in a category
     Semantics.Displayed.ReindexMonoidal    proof-relevant monoidal reindexing
     Semantics.Displayed.Weaken             any model is displayed over any other, with constant fibres

   The free model
     Semantics.Free.Syntax                  objects inductively, morphisms as a QIT (infinitary)
     Semantics.Free.Model                   that syntax as a Model, one universe up
     Semantics.Free.Recursor                interpreting the syntax in any model, via elim
     Semantics.Free.Eliminator              the eliminator into a displayed model
     Semantics.Free.EliminatorLocal         the same, from fibrewise data only

   Example
     Semantics.Examples.StarParser          a Kleene star parser, written once for all models
     Semantics.Examples.StarParserDemo      the same parser elaborated in both models below
     Semantics.Examples.StarParserRun       and run, on a two-letter alphabet
     Semantics.Examples.ChartDemo           the chart model at a fixed input word

   Models
     Semantics.Instances.Families           families of sets over strings
     Semantics.Instances.Recovered          the derived distributor is the hand-written one
     Semantics.Instances.MonoidSignature    monoidal biclosed = monoid theory, all slots closed
     Semantics.Instances.FamiliesInductive  initial algebras, and the star, in the families model
     Semantics.Instances.FamiliesLater      the later modality in the families model
     Semantics.Instances.Sets               grammars as plain sets, terms as plain functions
     Semantics.Instances.SetsInductive      the star in that model is List
     Semantics.Instances.Languages          languages: proof-irrelevant grammars, i.e. subsets of String
     Semantics.Instances.Day                Day convolution over an arbitrary monoid
     Semantics.Instances.Spans              grammars as span-indexed matrices; the CYK chart
-}
module Semantics where

open import Semantics.Signature
open import Semantics.Structure.IndexedCoproduct
open import Semantics.Structure.Biclosed
open import Semantics.Structure.Preservation
open import Semantics.Structure.CartesianClosed
open import Semantics.Structure.Operation

open import Semantics.Model
open import Semantics.Notation
open import Semantics.Distributivity
open import Semantics.Inductive.Functor
open import Semantics.Inductive.Algebra
open import Semantics.Inductive.KleeneStar
open import Semantics.Later

open import Semantics.Displayed.IndexedProduct
open import Semantics.Displayed.IndexedProductV
open import Semantics.Displayed.RightAdjoint
open import Semantics.Displayed.Model
open import Semantics.Displayed.ModelV
open import Semantics.Displayed.IsoLift
open import Semantics.Displayed.CatLemmas
open import Semantics.Displayed.ReindexMonoidal
open import Semantics.Displayed.Weaken

open import Semantics.Free.Syntax
open import Semantics.Free.Model
open import Semantics.Free.Recursor
open import Semantics.Free.Eliminator
open import Semantics.Free.EliminatorLocal

open import Semantics.Instances.Families
open import Semantics.Instances.Recovered
open import Semantics.Instances.MonoidSignature
open import Semantics.Instances.FamiliesInductive
open import Semantics.Instances.FamiliesLater
open import Semantics.Instances.Sets
open import Semantics.Instances.SetsInductive
open import Semantics.Instances.Languages
open import Semantics.Instances.Day
open import Semantics.Instances.Spans

open import Semantics.Examples.StarParser
import Semantics.Examples.StarParserDemo
open import Semantics.Examples.StarParserRun
open import Semantics.Examples.ChartDemo
