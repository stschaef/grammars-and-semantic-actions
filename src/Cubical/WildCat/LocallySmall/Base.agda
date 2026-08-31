-- TODO put in ccl
module Cubical.WildCat.LocallySmall.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.LocallySmall.Variables.Base

open Σω
open Liftω

record WildCat (ob : Typeω) (Hom-ℓ : ob → ob → Level) : Typeω where
  no-eta-equality
  field
    Hom[_,_] : ∀ x y → Type (Hom-ℓ x y)
    id : ∀ {x} → Hom[ x , x ]
    _⋆_ : ∀ {x y z}(f : Hom[ x , y ])(g : Hom[ y , z ]) → Hom[ x , z ]
    ⋆IdL : ∀ {x y}(f : Hom[ x , y ]) → id ⋆ f ≡ f
    ⋆IdR : ∀ {x y}(f : Hom[ x , y ]) → f ⋆ id ≡ f
    ⋆Assoc  : ∀ {w x y z}(f : Hom[ w , x ])(g : Hom[ x , y ])(h : Hom[ y , z ])
      → ((f ⋆ g) ⋆ h) ≡ (f ⋆ (g ⋆ h))
  infixr 9 _⋆_

  ⟨_⟩⋆⟨_⟩ : {x y z : ob} {f f' : Hom[ x , y ]} {g g' : Hom[ y , z ]}
          → f ≡ f' → g ≡ g' → f ⋆ g ≡ f' ⋆ g'
  ⟨ ≡f ⟩⋆⟨ ≡g ⟩ = cong₂ _⋆_ ≡f ≡g

  ⟨⟩⋆⟨_⟩ : ∀ {x y z} {f : Hom[ x , y ]} {g g' : Hom[ y , z ]}
          → g ≡ g' → f ⋆ g ≡ f ⋆ g'
  ⟨⟩⋆⟨ ≡g ⟩ = cong (_ ⋆_) ≡g

  ⟨_⟩⋆⟨⟩ : ∀ {x y z} {f f' : Hom[ x , y ]} {g : Hom[ y , z ]}
          → f ≡ f' → f ⋆ g ≡ f' ⋆ g
  ⟨ ≡f ⟩⋆⟨⟩ = cong (_⋆ _) ≡f

  Ob : Typeω
  Ob = ob

open WildCat

_^op : ∀ {Cob}{CHom-ℓ} → WildCat Cob CHom-ℓ → WildCat Cob λ x y → CHom-ℓ y x
(C ^op) .Hom[_,_] x y = C .Hom[_,_] y x
(C ^op) .id = C .id
(C ^op) ._⋆_ f g = C ._⋆_ g f
(C ^op) .⋆IdL = C .⋆IdR
(C ^op) .⋆IdR = C .⋆IdL
(C ^op) .⋆Assoc f g h = sym (C .⋆Assoc _ _ _)

module WildCatNotation (C : WildCat Cob CHom-ℓ) where
  private
    module C = WildCat C

  record WildCatIso (x y : Cob) : Type (ℓ-max (CHom-ℓ x x) $ ℓ-max (CHom-ℓ y y) $ ℓ-max (CHom-ℓ y x) (CHom-ℓ x y)) where
    no-eta-equality
    constructor wildiso
    field
      fun : C.Hom[ x , y ]
      inv : C.Hom[ y , x ]
      sec : inv C.⋆ fun ≡ C.id
      ret : fun C.⋆ inv ≡ C.id

  isIso : ∀ {x y}(f : C.Hom[ x , y ]) → Type _
  isIso {x}{y} f = (Σ[ inv ∈ C.Hom[ y , x ] ] ((inv C.⋆ f ≡ C.id) × (f C.⋆ inv ≡ C.id)))

  WildCatIsoIsoΣ : ∀ {x y}
    → Iso (WildCatIso x y)
          (Σ[ fun ∈ C.Hom[ x , y ] ] isIso fun)
  unquoteDef WildCatIsoIsoΣ = defineRecordIsoΣ WildCatIsoIsoΣ (quote (WildCatIso))

  idWildCatIso : ∀ {x} → WildCatIso x x
  idWildCatIso = wildiso C.id C.id (C.⋆IdL C.id) (C.⋆IdL C.id)

  ⋆WildCatIso : ∀ {x y z} → WildCatIso x y → WildCatIso y z → WildCatIso x z
  ⋆WildCatIso f g = wildiso
    (f .WildCatIso.fun C.⋆ g .WildCatIso.fun)
    (g .WildCatIso.inv C.⋆ f .WildCatIso.inv)
    (C.⋆Assoc _ _ _ ∙ C.⟨⟩⋆⟨ sym (C.⋆Assoc _ _ _) ∙ C.⟨ f .WildCatIso.sec ⟩⋆⟨⟩ ∙ C.⋆IdL (g .WildCatIso.fun) ⟩ ∙ g .WildCatIso.sec)
    (C.⋆Assoc _ _ _ ∙ C.⟨⟩⋆⟨ sym (C.⋆Assoc _ _ _) ∙ C.⟨ g .WildCatIso.ret ⟩⋆⟨⟩ ∙ C.⋆IdL (f .WildCatIso.inv) ⟩ ∙ f .WildCatIso.ret)

  open WildCat C public
