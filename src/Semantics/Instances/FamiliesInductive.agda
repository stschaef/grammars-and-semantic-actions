{-# OPTIONS --lossy-unification #-}
{- Relating the model-generic functor codes to `Grammar.Inductive`.

   `Semantics.Inductive.Functor` has a code `∘e` for postcomposition
   with an arbitrary endofunctor, which `Grammar.Inductive.Functor` has
   no counterpart for — and rightly so, since an arbitrary endofunctor
   need not have an initial algebra. `isPoly` cuts out the fragment
   that does correspond: the purely polynomial codes.

   On that fragment the two interpretations agree up to the `LiftG`s
   that `Grammar.Inductive` needs for universe polymorphism and that a
   model, having a single level of objects, does not. That isomorphism
   is `tr`, and `isSetValued⌊⌋` supplies what
   `Grammar.Inductive.HLevels.isSetGrammarμ` needs to conclude that the
   corresponding fixed point is set-valued — which is what makes it an
   object of the families model at all.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Instances.FamiliesInductive (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool using (true; false)
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet hiding (⟨_⟩)
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Sum.Properties Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.Product.Properties Alphabet
open import Term.Base Alphabet

import Grammar.Inductive.Indexed
import Grammar.Inductive.HLevels
import Semantics.Inductive.Functor
import Semantics.Inductive.Algebra
import Semantics.Inductive.KleeneStar

open import Semantics.Instances.Families Alphabet

module Ind = Grammar.Inductive.Indexed Alphabet
module IndH = Grammar.Inductive.HLevels Alphabet

open StrongEquivalence

module _ (ℓ : Level) (Gen : hSet ℓ) (lit : ⟨ Gen ⟩ → SetGrammar ℓ) where
  private
    M = FamiliesOn ℓ Gen lit

  module Sem = Semantics.Inductive.Functor M
  module SemA = Semantics.Inductive.Algebra M
  module SemK = Semantics.Inductive.KleeneStar M

  private
    variable
      X : Type ℓ

  -- | The polynomial fragment: no `∘e` nodes.
  isPoly : Sem.Functor X → Type ℓ
  isPoly (Sem.k A) = Unit*
  isPoly (Sem.Var x) = Unit*
  isPoly (Sem.&e Y F) = ∀ y → isPoly (F y)
  isPoly (Sem.⊕e Y F) = ∀ y → isPoly (F y)
  isPoly (F Sem.⊗e F') = isPoly F × isPoly F'
  isPoly (Sem.∘e E F) = Empty.⊥*

  -- | Translation into the codes of `Grammar.Inductive`.
  ⌊_⌋ : (F : Sem.Functor X) → isPoly F → Ind.Functor X
  ⌊ Sem.k A ⌋ p = Ind.k (A .fst)
  ⌊ Sem.Var x ⌋ p = Ind.Var x
  ⌊ Sem.&e Y F ⌋ p = Ind.&e ⟨ Y ⟩ λ y → ⌊ F y ⌋ (p y)
  ⌊ Sem.⊕e Y F ⌋ p = Ind.⊕e ⟨ Y ⟩ λ y → ⌊ F y ⌋ (p y)
  ⌊ F Sem.⊗e F' ⌋ p = ⌊ F ⌋ (p .fst) Ind.⊗e ⌊ F' ⌋ (p .snd)
  ⌊ Sem.∘e E F ⌋ p = Empty.rec* p

  -- | The translated code is set-valued, so its fixed point is a
  --   legitimate object of the families model.
  isSetValued⌊⌋ : (F : Sem.Functor X) (p : isPoly F)
                → IndH.isSetValued (⌊ F ⌋ p)
  isSetValued⌊⌋ (Sem.k A) p = A .snd
  isSetValued⌊⌋ (Sem.Var x) p = tt*
  isSetValued⌊⌋ (Sem.&e Y F) p = λ y → isSetValued⌊⌋ (F y) (p y)
  isSetValued⌊⌋ (Sem.⊕e Y F) p = Y .snd , λ y → isSetValued⌊⌋ (F y) (p y)
  isSetValued⌊⌋ (F Sem.⊗e F') p =
    isSetValued⌊⌋ F (p .fst) , isSetValued⌊⌋ F' (p .snd)
  isSetValued⌊⌋ (Sem.∘e E F) p = Empty.rec* p

  -- | The two interpretations agree up to LiftG.
  tr : (F : Sem.Functor X) (p : isPoly F) (A : X → SetGrammar ℓ)
     → Sem.⟦ F ⟧ A .fst ≅ Ind.⟦ ⌊ F ⌋ p ⟧ (λ x → A x .fst)
  tr (Sem.k A) p _ = LiftG≅ ℓ (A .fst)
  tr (Sem.Var x) p A = LiftG≅ ℓ (A x .fst)
  tr (Sem.&e Y F) p A = &ᴰ≅ λ y → tr (F y) (p y) A
  tr (Sem.⊕e Y F) p A = ⊕ᴰ≅ λ y → tr (F y) (p y) A
  tr (F Sem.⊗e F') p A = ⊗≅ (tr F (p .fst) A) (tr F' (p .snd) A)
  tr (Sem.∘e E F) p A = Empty.rec* p

  -- | `tr` is natural: it intertwines the two functorial actions.
  tr-nat : (F : Sem.Functor X) (p : isPoly F) {A B : X → SetGrammar ℓ}
    (f : ∀ x → A x .fst ⊢ B x .fst)
    → tr F p B .fun ∘g Sem.map F f ≡ Ind.map (⌊ F ⌋ p) f ∘g tr F p A .fun
  tr-nat (Sem.k A) p f = refl
  tr-nat (Sem.Var x) p f = refl
  tr-nat (Sem.&e Y F) p f =
    &ᴰ≡ _ _ λ y → cong (_∘g π y) (tr-nat (F y) (p y) f)
  tr-nat (Sem.⊕e Y F) p f =
    ⊕ᴰ≡ _ _ λ y → cong (σ y ∘g_) (tr-nat (F y) (p y) f)
  tr-nat (F Sem.⊗e F') p f =
    ⊗-intro⊗-intro
    ∙ cong₂ _,⊗_ (tr-nat F (p .fst) f) (tr-nat F' (p .snd) f)
    ∙ sym ⊗-intro⊗-intro
  tr-nat (Sem.∘e E F) p f = Empty.rec* p

  ------------------------------------------------------------------
  -- The families model has initial algebras for the polynomial codes.
  ------------------------------------------------------------------
  module _ {X : Type ℓ} (F : X → Sem.Functor X)
    (p : ∀ x → isPoly (F x)) where

    private
      ⌊F⌋ : X → Ind.Functor X
      ⌊F⌋ x = ⌊ F x ⌋ (p x)

    -- The carrier: `Grammar.Inductive`'s fixed point, which
    -- `isSetGrammarμ` shows is set-valued and hence an object here.
    μSet : X → SetGrammar ℓ
    μSet x =
      Ind.μ ⌊F⌋ x , IndH.isSetGrammarμ ⌊F⌋ (λ y → isSetValued⌊⌋ (F y) (p y)) x

    algSem : SemA.Algebra F μSet
    algSem x = Ind.roll ∘g tr (F x) (p x) μSet .fun

    module _ {A : X → SetGrammar ℓ} (α : SemA.Algebra F A) where
      private
        αInd : Ind.Algebra ⌊F⌋ (λ x → A x .fst)
        αInd x = α x ∘g tr (F x) (p x) A .inv

      recSem : ∀ x → Ind.μ ⌊F⌋ x ⊢ A x .fst
      recSem = Ind.rec ⌊F⌋ αInd

      -- Transporting a map along `tr` in either direction.
      private
        push : ∀ x (ϕ : ∀ y → Ind.μ ⌊F⌋ y ⊢ A y .fst)
             → tr (F x) (p x) A .inv ∘g Ind.map (⌊F⌋ x) ϕ
                 ∘g tr (F x) (p x) μSet .fun
             ≡ Sem.map (F x) ϕ
        push x ϕ =
          cong (tr (F x) (p x) A .inv ∘g_) (sym (tr-nat (F x) (p x) ϕ))
          ∙ cong (_∘g Sem.map (F x) ϕ) (tr (F x) (p x) A .ret)

        pull : ∀ x (ϕ : ∀ y → Ind.μ ⌊F⌋ y ⊢ A y .fst)
             → Sem.map (F x) ϕ ∘g tr (F x) (p x) μSet .inv
             ≡ tr (F x) (p x) A .inv ∘g Ind.map (⌊F⌋ x) ϕ
        pull x ϕ =
          sym (cong (_∘g (Sem.map (F x) ϕ ∘g tr (F x) (p x) μSet .inv))
                    (tr (F x) (p x) A .ret))
          ∙ cong (λ z → tr (F x) (p x) A .inv ∘g z
                          ∘g tr (F x) (p x) μSet .inv)
                 (tr-nat (F x) (p x) ϕ)
          ∙ cong (λ z → tr (F x) (p x) A .inv
                          ∘g Ind.map (⌊F⌋ x) ϕ ∘g z)
                 (tr (F x) (p x) μSet .sec)

      recHomoSem : ∀ x → recSem x ∘g algSem x ≡ α x ∘g Sem.map (F x) recSem
      recHomoSem x = cong (α x ∘g_) (push x recSem)

      -- Any homomorphism out of the initial algebra is `recSem`.
      indSem : (ϕ : SemA.AlgHom F (μSet , algSem) (A , α))
             → recSem ≡ ϕ .fst
      indSem ϕ =
        Ind.ind ⌊F⌋ αInd (Ind.recHomo ⌊F⌋ αInd) (ϕ .fst , ϕInd)
        where
        ϕInd : ∀ x → ϕ .fst x ∘g Ind.roll
                   ≡ αInd x ∘g Ind.map (⌊F⌋ x) (ϕ .fst)
        ϕInd x =
          sym (cong (λ z → ϕ .fst x ∘g Ind.roll ∘g z)
                    (tr (F x) (p x) μSet .sec))
          ∙ cong (_∘g tr (F x) (p x) μSet .inv) (ϕ .snd x)
          ∙ cong (α x ∘g_) (pull x (ϕ .fst))

    FamiliesInitialAlgebra : SemA.InitialAlgebra F
    FamiliesInitialAlgebra .fst = μSet , algSem
    FamiliesInitialAlgebra .snd (A , α) .fst = recSem α , recHomoSem α
    FamiliesInitialAlgebra .snd (A , α) .snd ϕ =
      SemA.AlgHom≡ F (indSem α ϕ)

  ------------------------------------------------------------------
  -- End to end: the generic Kleene star, built in this model.
  ------------------------------------------------------------------
  module _ (A : SetGrammar ℓ) where
    module S = SemK.Star A

    private
      *isPoly : ∀ u → isPoly (S.*Ty u)
      *isPoly u (lift true) = tt*
      *isPoly u (lift false) = tt* , tt*

    ⋆Alg : SemA.InitialAlgebra S.*Ty
    ⋆Alg = FamiliesInitialAlgebra S.*Ty *isPoly

    -- `A *` with its constructors and the three laws that
    -- `Semantics.Inductive.KleeneStar` derives from initiality.
    open S.WithFix ⋆Alg public
      using (_*; NIL; CONS; fold*; fold*-nil; fold*-cons; fold*-unique)
