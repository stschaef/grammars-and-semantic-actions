{-# OPTIONS --lossy-unification #-}
{- Small equational lemmas in an arbitrary category.

   The coherence proofs for `Semantics.Displayed.ReindexMonoidal` are
   long chains of associativity plus cancellation of an iso pair. Doing
   that inline makes the elaborated terms enormous — large enough to
   exhaust a 12G heap. Naming the recurring shapes here, with explicit
   types, keeps each obligation small.

   They are used at `∫C Cᴰ`, the total category of the displayed
   category, where a displayed equation `fᴰ ≡[ p ] gᴰ` is an ordinary
   path and the reasoning is ordinary category algebra.
-}
module Semantics.Displayed.CatLemmas where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} where
  private
    module C = Category C

  -- | `k⁻ ⋆ (k ⋆ X) ≡ X` when `k⁻ ⋆ k` is the identity.
  ⋆cancelL : ∀ {a b c}{k⁻ : C [ a , b ]}{k : C [ b , a ]}{X : C [ a , c ]}
    → (k⁻ C.⋆ k) ≡ C.id → (k⁻ C.⋆ (k C.⋆ X)) ≡ X
  ⋆cancelL {k⁻ = k⁻}{k}{X} p =
    sym (C.⋆Assoc k⁻ k X) ∙ cong (C._⋆ X) p ∙ C.⋆IdL X

  -- | `(X ⋆ k) ⋆ k⁻ ≡ X` when `k ⋆ k⁻` is the identity.
  ⋆cancelR : ∀ {a b c}{X : C [ a , b ]}{k : C [ b , c ]}{k⁻ : C [ c , b ]}
    → (k C.⋆ k⁻) ≡ C.id → ((X C.⋆ k) C.⋆ k⁻) ≡ X
  ⋆cancelR {X = X}{k}{k⁻} p =
    C.⋆Assoc X k k⁻ ∙ cong (X C.⋆_) p ∙ C.⋆IdR X

  -- | Conjugation by an iso pair is functorial: two conjugates compose
  --   to the conjugate of the composite.
  conjSeq : ∀ {a b c d e f}
    {k : C [ a , b ]}{x : C [ b , c ]}{l⁻ : C [ c , d ]}
    {l : C [ d , c ]}{y : C [ c , e ]}{m : C [ e , f ]}
    → (l⁻ C.⋆ l) ≡ C.id
    → ((k C.⋆ (x C.⋆ l⁻)) C.⋆ (l C.⋆ (y C.⋆ m)))
      ≡ (k C.⋆ ((x C.⋆ y) C.⋆ m))
  conjSeq {k = k}{x}{l⁻}{l}{y}{m} p =
      C.⋆Assoc k (x C.⋆ l⁻) (l C.⋆ (y C.⋆ m))
    ∙ cong (k C.⋆_)
        ( C.⋆Assoc x l⁻ (l C.⋆ (y C.⋆ m))
        ∙ cong (x C.⋆_) (⋆cancelL p)
        ∙ sym (C.⋆Assoc x y m))

  -- | Regroup a right-nested triple.
  ⋆Assoc⁻ : ∀ {a b c d}(x : C [ a , b ])(y : C [ b , c ])(z : C [ c , d ])
    → (x C.⋆ (y C.⋆ z)) ≡ ((x C.⋆ y) C.⋆ z)
  ⋆Assoc⁻ x y z = sym (C.⋆Assoc x y z)
