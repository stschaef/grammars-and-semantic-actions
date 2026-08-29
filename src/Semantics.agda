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

   The DSL
     Semantics.Model                        what a model is
     Semantics.Notation                     ⊗ ε ⊕ᴰ &ᴰ ⊸ ⟜, and ⊤ ⊥ & ⊕ derived from them
     Semantics.Distributivity               ⊗ over ⊕ᴰ, as instances of Preservation
     Semantics.Inductive.Functor            strictly positive functor codes
     Semantics.Inductive.Algebra            algebras; initial algebra = initial object; Lambek
     Semantics.Inductive.KleeneStar         the star as an initial algebra
     Semantics.Later                        the later modality and guarded fixed points

   Example
     Semantics.Examples.StarParser          a Kleene star parser, written once for all models
     Semantics.Examples.StarParserDemo      the same parser elaborated in both models below
     Semantics.Examples.StarParserRun       and run, on a two-letter alphabet

   Models
     Semantics.Instances.Families           families of sets over strings
     Semantics.Instances.Recovered          the derived distributor is the hand-written one
     Semantics.Instances.MonoidSignature    monoidal biclosed = monoid theory, all slots closed
     Semantics.Instances.FamiliesInductive  initial algebras, and the star, in the families model
     Semantics.Instances.FamiliesLater      the later modality in the families model
     Semantics.Instances.Sets               grammars as plain sets, terms as plain functions
     Semantics.Instances.SetsInductive      the star in that model is List
-}
module Semantics where

open import Semantics.Signature
open import Semantics.Structure.IndexedCoproduct
open import Semantics.Structure.Biclosed
open import Semantics.Structure.Preservation
open import Semantics.Structure.Operation

open import Semantics.Model
open import Semantics.Notation
open import Semantics.Distributivity
open import Semantics.Inductive.Functor
open import Semantics.Inductive.Algebra
open import Semantics.Inductive.KleeneStar
open import Semantics.Later

open import Semantics.Instances.Families
open import Semantics.Instances.Recovered
open import Semantics.Instances.MonoidSignature
open import Semantics.Instances.FamiliesInductive
open import Semantics.Instances.FamiliesLater
open import Semantics.Instances.Sets
open import Semantics.Instances.SetsInductive

open import Semantics.Examples.StarParser
import Semantics.Examples.StarParserDemo
open import Semantics.Examples.StarParserRun
