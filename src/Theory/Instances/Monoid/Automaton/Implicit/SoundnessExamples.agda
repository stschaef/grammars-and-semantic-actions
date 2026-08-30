{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `compile-sound` at a two-letter alphabet, on one expression per
   constructor.  Nothing is computed: these only witness that the
   statement instantiates. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Automaton.Implicit.SoundnessExamples where

open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false ; false≢true)
open import Cubical.Data.Unit using (tt*)

private
  _≟B_ : (x y : Bool) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
  true ≟B true = Sum.inl Eq.refl
  true ≟B false = Sum.inr λ ()
  false ≟B true = Sum.inr λ ()
  false ≟B false = Sum.inl Eq.refl

open import Theory.Instances.Monoid.Types Bool _≟B_
  using (isSetAlphabet ; _≅_ ; ty)
open import Theory.Instances.Monoid.Automaton.Implicit.Disjointness
  Bool isSetAlphabet using (Parse)
open import Theory.Instances.Monoid.Automaton.Implicit.Soundness
  Bool _≟B_ ℓ-zero
open import Theory.Instances.Monoid.Regex.Base Bool _≟B_ ℓ-zero using (⟦_⟧)

lit : DetReg ⊤ℙ (¬ℙ ⟦ true ⟧ℙ) true
lit = ＂ true ＂dr

lit-sound : Parse (compile discAlphabet lit) ≅ ty ⟦ erase lit ⟧
lit-sound = compile-sound lit

star : DetReg (¬ℙ ⟦ true ⟧ℙ ∩ℙ ⊤ℙ) (¬ℙ ⟦ true ⟧ℙ) false
star = ＂ true ＂dr *DR[ (λ _ → Sum.inl tt*) ]

star-sound : Parse (compile discAlphabet star) ≅ ty ⟦ erase star ⟧
star-sound = compile-sound star

seq : DetReg _ (¬ℙ ⟦ true ⟧ℙ) true
seq =
  ＂ true ＂dr ⊗DR[ (λ _ → Sum.inl tt*) ]
    (＂ false ＂dr *DR[ (λ _ → Sum.inl tt*) ])

seq-sound : Parse (compile discAlphabet seq) ≅ ty ⟦ erase seq ⟧
seq-sound = compile-sound seq

alt : DetReg _ _ true
alt =
  _⊕DR[_]_ {notBothNull = Eq.refl} ＂ true ＂dr sep ＂ false ＂dr
  where
  sep : (c : Bool)
    → (c ∈ℙ (¬ℙ ⟦ true ⟧ℙ)) Sum.⊎ (c ∈ℙ (¬ℙ ⟦ false ⟧ℙ))
  sep true = Sum.inr λ p → Empty.rec (false≢true p)
  sep false = Sum.inl λ p → Empty.rec (true≢false p)

alt-sound : Parse (compile discAlphabet alt) ≅ ty ⟦ erase alt ⟧
alt-sound = compile-sound alt
