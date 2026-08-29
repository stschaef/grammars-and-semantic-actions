{-# OPTIONS --lossy-unification #-}
{- Day convolution over an arbitrary monoid.

   `Semantics.Instances.Families` interprets grammars as set-valued
   families over *strings* and `⊗` as splitting a string into two
   halves. Nothing in that construction uses anything about strings
   except that they form a monoid: the free monoid on the alphabet,
   with `[]` and `_++_`. This module carries out the same construction
   over an arbitrary monoid `M`, i.e. it builds the Day convolution
   monoidal structure on `⟨M⟩ → hSet ℓ` and inhabits `Semantics.Model`
   with it.

     objects       families  A : ⟨M⟩ → hSet ℓ
     morphisms     ∀ m → A m → B m
     A ⊗ B         (A ⊗ B) m = Σ[ (m₁ , m₂) ] (m ≡ m₁ · m₂) × A m₁ × B m₂
     ε             ε m       = (m ≡ ⟨ε⟩)
     B ⊸ D         (B ⊸ D) m = ∀ m' → B m' → D (m · m')
     D ⟜ A         (D ⟜ A) m = ∀ m' → A m' → D (m' · m)
     ⊕ᴰ / &ᴰ       Σ / Π, pointwise

   The one design decision that matters is that the *monoid laws are
   stated with `Cubical.Data.Equality`'s inductive equality*, not with
   paths, and so is the `m ≡ m₁ · m₂` carried by the tensor. This
   mirrors `String.Base.SplittingEq` and
   `Grammar.LinearProduct.AsEquality`, and it is what buys the
   definitional equations: an `Eq.refl` can be matched on, which makes
   the whole splitting compute away, so e.g. the η law of `⊸` and both
   round trips of `&ᴰ`/`⊕ᴰ` hold by `refl`.

   Honest accounting of what is and is not definitional (see the
   individual proofs below):

     * `&ᴰ` and `⊕ᴰ`: both round trips are `refl`, so both universal
       properties are given by `strictContrFibers`.
     * `⊸`/`⟜`: the η law is `refl` (this is the payoff of `Eq`), but
       the β law is not — `⊸-app` must transport along the `Eq`-proof
       carried by the splitting, and that transport is stuck until the
       proof is matched against `Eq.refl`. So β is `refl` only *after*
       a pattern match, and the universal property goes through
       `isoToIsEquiv`. This is exactly what
       `Semantics.Instances.Families` does, for exactly this reason
       (cf. the comments on `⟜-β`/`⟜-η` in
       `Grammar.LinearFunction.Base`). If one instead takes the
       "Kripke" form of the object, `(B ⊸ D) m = ∀ m' m'' → (m'' ≡ m · m')
       → B m' → D m''`, absorbing the transport into the function
       space, then both round trips do become `refl` and
       `strictContrFibers` applies; the form used below is the one the
       string model uses, and is kept for that reason.
     * the associator and the unitors: same story; the round trips are
       `refl` after matching the splitting proofs, modulo the fact
       that two `Eq`-proofs of the same equation must be identified,
       which is fine because `⟨M⟩` is an h-set.

   Two instantiations are given at the bottom:

     * the trivial monoid `Unit*`, where the model degenerates to
       something very close to `Semantics.Instances.Sets` (a family
       over `Unit*` is just a set, and the splitting data is
       contractible);
     * the free monoid `List ⟨Gen⟩` on a set of generators, with `[]`
       and `_++_`, whose laws hold in `Eq` form by
       `Cubical.Data.List.More.++-assoc-Eq` / `++-unit-r-Eq`. This is
       the families model of `Semantics.Instances.Families`, up to
       replacing that development's bespoke `Splitting`/`ε`/`⊸`
       definitions by the generic ones here; it is *not* literally the
       same Agda term, since `Grammar.*` has its own definitions with
       their own `opaque` blocks.
-}
module Semantics.Instances.Day where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv.Base using (strictContrFibers; equiv-proof)

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.List.More
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.IndexedProduct.Base

open import Semantics.Model
open import Semantics.Structure.Biclosed
open import Semantics.Structure.IndexedCoproduct

private
  variable
    ℓ : Level

--------------------------------------------------------------------
-- Monoids whose laws are stated in `Eq`.
--------------------------------------------------------------------
-- A `Monoid` in the sense of `Cubical.Algebra.Monoid` would state its
-- laws with paths, and then none of the computation below happens.
record EqMonoid (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Carrier : Type ℓ
    isSetCarrier : isSet Carrier
    ⟨ε⟩ : Carrier
    _·_ : Carrier → Carrier → Carrier
    ·assoc : ∀ x y z → ((x · y) · z) Eq.≡ (x · (y · z))
    ·unit-l : ∀ x → (⟨ε⟩ · x) Eq.≡ x
    ·unit-r : ∀ x → (x · ⟨ε⟩) Eq.≡ x

  infixl 30 _·_

  -- Since the carrier is a set, its `Eq`-equalities are propositions;
  -- this is what lets two different proofs of the same splitting be
  -- identified.
  isPropEq : (x y : Carrier) → isProp (x Eq.≡ y)
  isPropEq x y =
    isPropRetract Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath
      (isSetCarrier x y)

open UniversalElement

module _ (M : EqMonoid ℓ) where
  open EqMonoid M
  open Category
  open Functor
  open NatTrans
  open NatIso
  open isIso
  open MonoidalCategory
  open MonoidalStr
  open TensorStr

  ------------------------------------------------------------------
  -- Families over the monoid.
  ------------------------------------------------------------------
  Fam : Type (ℓ-suc ℓ)
  Fam = Carrier → hSet ℓ

  El : Fam → Carrier → Type ℓ
  El A m = A m .fst

  Homᴰ : Fam → Fam → Type ℓ
  Homᴰ A B = ∀ m → El A m → El B m

  -- Transport along an `Eq`-equality of indices, and the three facts
  -- about it that the coherence proofs need. Each is by matching the
  -- equality against `Eq.refl`, which is possible precisely because
  -- `Eq._≡_` is an inductive family.
  tr : (A : Fam) {x y : Carrier} → x Eq.≡ y → El A x → El A y
  tr A q a = Eq.transport (El A) q a

  trP : (A : Fam) {x y : Carrier} (q : x Eq.≡ y) (a : El A x)
      → PathP (λ i → El A (Eq.eqToPath q i)) a (tr A q a)
  trP A Eq.refl a = refl

  trP⁻ : (A : Fam) {x y : Carrier} (q : x Eq.≡ y) (a : El A x)
       → PathP (λ i → El A (Eq.eqToPath (Eq.sym q) i)) (tr A q a) a
  trP⁻ A Eq.refl a = refl

  trNat : (A B : Fam) (f : Homᴰ A B) {x y : Carrier}
          (q : x Eq.≡ y) (a : El A x)
        → f y (tr A q a) ≡ tr B q (f x a)
  trNat _ _ f Eq.refl a = refl

  ------------------------------------------------------------------
  -- The category of families.
  ------------------------------------------------------------------
  DAYC : Category (ℓ-suc ℓ) ℓ
  DAYC = record
    { ob = Fam
    ; Hom[_,_] = Homᴰ
    ; id = λ _ a → a
    ; _⋆_ = λ f g m a → g m (f m a)
    ; ⋆IdL = λ _ → refl
    ; ⋆IdR = λ _ → refl
    ; ⋆Assoc = λ _ _ _ → refl
    ; isSetHom = λ {_} {B} → isSetΠ λ m → isSet→ (B m .snd)
    }

  ------------------------------------------------------------------
  -- Day convolution. `Split m` is `String.Base.SplittingEq m`,
  -- verbatim, with `_++_` replaced by the monoid multiplication.
  ------------------------------------------------------------------
  Split : Carrier → Type ℓ
  Split m = Σ[ mm ∈ Carrier × Carrier ] (m Eq.≡ (mm .fst · mm .snd))

  isSetSplit : ∀ m → isSet (Split m)
  isSetSplit m =
    isSetΣ (isSet× isSetCarrier isSetCarrier)
      (λ _ → isProp→isSet (isPropEq _ _))

  infixr 25 _⊛_
  _⊛_ : Fam → Fam → Fam
  (A ⊛ B) m =
    (Σ[ s ∈ Split m ] (El A (s .fst .fst) × El B (s .fst .snd)))
    , isSetΣ (isSetSplit m) (λ s → isSet× (A _ .snd) (B _ .snd))

  εᴰ : Fam
  εᴰ m = (m Eq.≡ ⟨ε⟩) , isProp→isSet (isPropEq _ _)

  idᴰ : (A : Fam) → Homᴰ A A
  idᴰ _ _ a = a

  -- All the combinators below take their families as *explicit*
  -- arguments. Neither `_⊛_` nor `Homᴰ` is injective — both compute to
  -- a Σ- or Π-type whose components mention the family only through
  -- `A m .fst` — so leaving them implicit strands the `isSet`
  -- component of the family as an unsolvable metavariable at every use
  -- site. Being explicit costs a little noise and buys metavariable-free
  -- elaboration of the monoidal structure below.
  ⊛h : (A B A' B' : Fam) → Homᴰ A A' → Homᴰ B B'
     → Homᴰ (A ⊛ B) (A' ⊛ B')
  ⊛h _ _ _ _ f g _ (s , a , b) = s , f _ a , g _ b

  ------------------------------------------------------------------
  -- Associator and unitors. Note that none of these matches on the
  -- `Eq`-proofs: they are all "record patterns", so they reduce on
  -- neutral arguments. That is what makes the naturality squares and
  -- the functoriality of `─⊗─` hold by `refl`.
  ------------------------------------------------------------------
  α→ : (A B D : Fam) → Homᴰ (A ⊛ (B ⊛ D)) ((A ⊛ B) ⊛ D)
  α→ _ _ _ _ (((ma , mbd) , e) , a , (((mb , md) , e') , b , d)) =
    ((ma · mb , md)
      , e Eq.∙ Eq.ap (ma ·_) e' Eq.∙ Eq.sym (·assoc ma mb md))
    , (((ma , mb) , Eq.refl) , a , b) , d

  α← : (A B D : Fam) → Homᴰ ((A ⊛ B) ⊛ D) (A ⊛ (B ⊛ D))
  α← _ _ _ _ (((mab , md) , e) , (((ma , mb) , e') , a , b) , d) =
    ((ma , mb · md)
      , e Eq.∙ Eq.ap (_· md) e' Eq.∙ ·assoc ma mb md)
    , a , (((mb , md) , Eq.refl) , b , d)

  lu→ : (A : Fam) → Homᴰ (εᴰ ⊛ A) A
  lu→ A _ (((m₁ , m₂) , e) , p , a) =
    tr A (Eq.sym (Eq.ap (_· m₂) p Eq.∙ ·unit-l m₂) Eq.∙ Eq.sym e) a

  lu← : (A : Fam) → Homᴰ A (εᴰ ⊛ A)
  lu← _ m a = ((⟨ε⟩ , m) , Eq.sym (·unit-l m)) , Eq.refl , a

  ru→ : (A : Fam) → Homᴰ (A ⊛ εᴰ) A
  ru→ A _ (((m₁ , m₂) , e) , a , p) =
    tr A (Eq.sym (Eq.ap (m₁ ·_) p Eq.∙ ·unit-r m₁) Eq.∙ Eq.sym e) a

  ru← : (A : Fam) → Homᴰ A (A ⊛ εᴰ)
  ru← _ m a = ((m , ⟨ε⟩) , Eq.sym (·unit-r m)) , a , Eq.refl

  ------------------------------------------------------------------
  -- Coherence. Every one of these is `refl` once the `Eq`-proofs in
  -- the splitting have been matched against `Eq.refl`, except for the
  -- identification of two proofs of the same equation, which is
  -- `isPropEq`.
  ------------------------------------------------------------------
  αsec : (A B D : Fam) (m : Carrier) (x : El ((A ⊛ B) ⊛ D) m)
       → α→ A B D m (α← A B D m x) ≡ x
  αsec _ _ _ _ (((_ , _) , Eq.refl) , (((_ , _) , Eq.refl) , a , b) , d) =
    ΣPathP ( ΣPathP (refl , isProp→PathP (λ _ → isPropEq _ _) _ _)
           , refl)

  αret : (A B D : Fam) (m : Carrier) (x : El (A ⊛ (B ⊛ D)) m)
       → α← A B D m (α→ A B D m x) ≡ x
  αret _ _ _ _ (((_ , _) , Eq.refl) , a , (((_ , _) , Eq.refl) , b , d)) =
    ΣPathP ( ΣPathP (refl , isProp→PathP (λ _ → isPropEq _ _) _ _)
           , refl)

  lunat : (A B : Fam) (f : Homᴰ A B) (m : Carrier) (x : El (εᴰ ⊛ A) m)
        → lu→ B m (⊛h εᴰ A εᴰ B (idᴰ εᴰ) f m x) ≡ f m (lu→ A m x)
  lunat A B f _ (((_ , m₂) , e) , p , a) =
    sym (trNat A B f
          (Eq.sym (Eq.ap (_· m₂) p Eq.∙ ·unit-l m₂) Eq.∙ Eq.sym e) a)

  runat : (A B : Fam) (f : Homᴰ A B) (m : Carrier) (x : El (A ⊛ εᴰ) m)
        → ru→ B m (⊛h A εᴰ B εᴰ f (idᴰ εᴰ) m x) ≡ f m (ru→ A m x)
  runat A B f _ (((m₁ , _) , e) , a , p) =
    sym (trNat A B f
          (Eq.sym (Eq.ap (m₁ ·_) p Eq.∙ ·unit-r m₁) Eq.∙ Eq.sym e) a)

  lusec : (A : Fam) (m : Carrier) (a : El A m) → lu→ A m (lu← A m a) ≡ a
  lusec A m a = cong (λ q → tr A q a) (isPropEq m m _ Eq.refl)

  luret : (A : Fam) (m : Carrier) (x : El (εᴰ ⊛ A) m)
        → lu← A m (lu→ A m x) ≡ x
  luret A _ (((_ , m₂) , Eq.refl) , Eq.refl , a) =
    ΣPathP ( ΣPathP ( ≡-× refl (Eq.eqToPath (Eq.sym r))
                    , isProp→PathP (λ _ → isPropEq _ _) _ _)
           , ΣPathP ( isProp→PathP (λ _ → isPropEq _ _) _ _
                    , trP⁻ A r a))
    where
    r : m₂ Eq.≡ (⟨ε⟩ · m₂)
    r = Eq.sym (·unit-l m₂) Eq.∙ Eq.refl

  rusec : (A : Fam) (m : Carrier) (a : El A m) → ru→ A m (ru← A m a) ≡ a
  rusec A m a = cong (λ q → tr A q a) (isPropEq m m _ Eq.refl)

  ruret : (A : Fam) (m : Carrier) (x : El (A ⊛ εᴰ) m)
        → ru← A m (ru→ A m x) ≡ x
  ruret A _ (((m₁ , _) , Eq.refl) , a , Eq.refl) =
    ΣPathP ( ΣPathP ( ≡-× (Eq.eqToPath (Eq.sym r)) refl
                    , isProp→PathP (λ _ → isPropEq _ _) _ _)
           , ΣPathP ( trP⁻ A r a
                    , isProp→PathP (λ _ → isPropEq _ _) _ _))
    where
    r : m₁ Eq.≡ (m₁ · ⟨ε⟩)
    r = Eq.sym (·unit-r m₁) Eq.∙ Eq.refl

  tri : (A B : Fam) (m : Carrier) (x : El (A ⊛ (εᴰ ⊛ B)) m)
      → ⊛h (A ⊛ εᴰ) B A B (ru→ A) (idᴰ B) m (α→ A εᴰ B m x)
      ≡ ⊛h A (εᴰ ⊛ B) A B (idᴰ A) (lu→ B) m x
  tri A B _
    (((ma , _) , Eq.refl) , a , (((_ , mb) , Eq.refl) , Eq.refl , b)) =
    ΣPathP ( ΣPathP ( ≡-× (Eq.eqToPath (Eq.sym rA)) (Eq.eqToPath rB)
                    , isProp→PathP (λ _ → isPropEq _ _) _ _)
           , ΣPathP (trP⁻ A rA a , trP B rB b))
    where
    rA : ma Eq.≡ (ma · ⟨ε⟩)
    rA = Eq.sym (·unit-r ma) Eq.∙ Eq.refl
    rB : mb Eq.≡ (⟨ε⟩ · mb)
    rB = Eq.sym (·unit-l mb) Eq.∙ Eq.refl

  pent : (A B C D : Fam) (m : Carrier) (x : El (A ⊛ (B ⊛ (C ⊛ D))) m)
       → ⊛h (A ⊛ (B ⊛ C)) D ((A ⊛ B) ⊛ C) D (α→ A B C) (idᴰ D) m
           (α→ A (B ⊛ C) D m
             (⊛h A (B ⊛ (C ⊛ D)) A ((B ⊛ C) ⊛ D) (idᴰ A) (α→ B C D) m x))
       ≡ α→ (A ⊛ B) C D m (α→ A B (C ⊛ D) m x)
  pent _ _ _ _ _ (((m1 , _) , Eq.refl) , p1
                   , (((m2 , _) , Eq.refl) , p2
                      , (((m3 , _) , Eq.refl) , p3 , p4))) =
    ΣPathP ( ΣPathP ( ≡-× (Eq.eqToPath (Eq.sym (·assoc m1 m2 m3))) refl
                    , isProp→PathP (λ _ → isPropEq _ _) _ _)
           , ΣPathP ( ΣPathP ( ΣPathP ( refl
                                      , isProp→PathP (λ _ → isPropEq _ _) _ _)
                             , refl)
                    , refl))

  ------------------------------------------------------------------
  -- The Day convolution monoidal category.
  --
  -- Given as a record expression rather than by copatterns: the
  -- α/η/ρ coherence fields have types mentioning the sibling fields,
  -- and with `refl` bodies that reads to the termination checker as a
  -- recursive call on the definition being made.
  ------------------------------------------------------------------
  DAYMC : MonoidalCategory (ℓ-suc ℓ) ℓ
  DAYMC = record
    { C = DAYC
    ; monstr = record
      { tenstr = record
        { ─⊗─ = record
          { F-ob = λ AB → AB .fst ⊛ AB .snd
          ; F-hom = λ {x} {y} fg →
              ⊛h (x .fst) (x .snd) (y .fst) (y .snd) (fg .fst) (fg .snd)
          ; F-id = refl
          ; F-seq = λ _ _ → refl
          }
        ; unit = εᴰ
        }
      ; α = record
        { trans = record
          { N-ob = λ x → α→ (x .fst) (x .snd .fst) (x .snd .snd)
          ; N-hom = λ _ → refl
          }
        ; nIso = λ x → record
          { inv = α← (x .fst) (x .snd .fst) (x .snd .snd)
          ; sec = funExt λ m →
              funExt (αsec (x .fst) (x .snd .fst) (x .snd .snd) m)
          ; ret = funExt λ m →
              funExt (αret (x .fst) (x .snd .fst) (x .snd .snd) m)
          }
        }
      ; η = record
        { trans = record
          { N-ob = lu→
          ; N-hom = λ {A} {B} f → funExt λ m → funExt (lunat A B f m)
          }
        ; nIso = λ A → record
          { inv = lu← A
          ; sec = funExt λ m → funExt (lusec A m)
          ; ret = funExt λ m → funExt (luret A m)
          }
        }
      ; ρ = record
        { trans = record
          { N-ob = ru→
          ; N-hom = λ {A} {B} f → funExt λ m → funExt (runat A B f m)
          }
        ; nIso = λ A → record
          { inv = ru← A
          ; sec = funExt λ m → funExt (rusec A m)
          ; ret = funExt λ m → funExt (ruret A m)
          }
        }
      ; pentagon = λ w x y z → funExt λ m → funExt (pent w x y z m)
      ; triangle = λ x y → funExt λ m → funExt (tri x y m)
      }
    }

  ------------------------------------------------------------------
  -- The biclosure.
  --
  -- The η laws hold by `refl` — that is the payoff of stating the
  -- splitting equation in `Eq`, since `⊸intro` produces `Eq.refl` and
  -- the transport in `⊸app` then computes away. The β laws do not:
  -- there the splitting proof is an arbitrary `e`, the transport is
  -- stuck, and one has to match `e` against `Eq.refl` first. So these
  -- two universal properties go through `isoToIsEquiv` rather than
  -- `strictContrFibers`, exactly as in `Semantics.Instances.Families`.
  ------------------------------------------------------------------
  ⊸ᴰ : Fam → Fam → Fam
  ⊸ᴰ B D m =
    (∀ m' → El B m' → El D (m · m'))
    , isSetΠ (λ m' → isSet→ (D (m · m') .snd))

  ⊸app : (B D : Fam) → Homᴰ (⊸ᴰ B D ⊛ B) D
  ⊸app _ D _ (((_ , m₂) , e) , f , b) = tr D (Eq.sym e) (f m₂ b)

  ⊸intro : (A B D : Fam) → Homᴰ (A ⊛ B) D → Homᴰ A (⊸ᴰ B D)
  ⊸intro _ _ _ g m a m' b = g (m · m') (((m , m') , Eq.refl) , a , b)

  ⊸intro⁻ : (A B D : Fam) → Homᴰ A (⊸ᴰ B D) → Homᴰ (A ⊛ B) D
  ⊸intro⁻ A B D f m x = ⊸app B D m (⊛h A B (⊸ᴰ B D) B f (idᴰ B) m x)

  ⊸β : (A B D : Fam) (g : Homᴰ (A ⊛ B) D)
     → ⊸intro⁻ A B D (⊸intro A B D g) ≡ g
  ⊸β A B D g = funExt λ m → funExt (pt m)
    where
    pt : ∀ m x → ⊸intro⁻ A B D (⊸intro A B D g) m x ≡ g m x
    pt _ (((_ , _) , Eq.refl) , _ , _) = refl

  -- Definitional η.
  ⊸η : (A B D : Fam) (f : Homᴰ A (⊸ᴰ B D))
     → ⊸intro A B D (⊸intro⁻ A B D f) ≡ f
  ⊸η _ _ _ _ = refl

  ⟜ᴰ : Fam → Fam → Fam
  ⟜ᴰ A D m =
    (∀ m' → El A m' → El D (m' · m))
    , isSetΠ (λ m' → isSet→ (D (m' · m) .snd))

  ⟜app : (A D : Fam) → Homᴰ (A ⊛ ⟜ᴰ A D) D
  ⟜app _ D _ (((m₁ , _) , e) , a , f) = tr D (Eq.sym e) (f m₁ a)

  ⟜intro : (A B D : Fam) → Homᴰ (A ⊛ B) D → Homᴰ B (⟜ᴰ A D)
  ⟜intro _ _ _ g m b m' a = g (m' · m) (((m' , m) , Eq.refl) , a , b)

  ⟜intro⁻ : (A B D : Fam) → Homᴰ B (⟜ᴰ A D) → Homᴰ (A ⊛ B) D
  ⟜intro⁻ A B D f m x = ⟜app A D m (⊛h A B A (⟜ᴰ A D) (idᴰ A) f m x)

  ⟜β : (A B D : Fam) (g : Homᴰ (A ⊛ B) D)
     → ⟜intro⁻ A B D (⟜intro A B D g) ≡ g
  ⟜β A B D g = funExt λ m → funExt (pt m)
    where
    pt : ∀ m x → ⟜intro⁻ A B D (⟜intro A B D g) m x ≡ g m x
    pt _ (((_ , _) , Eq.refl) , _ , _) = refl

  -- Definitional η.
  ⟜η : (A B D : Fam) (f : Homᴰ B (⟜ᴰ A D))
     → ⟜intro A B D (⟜intro⁻ A B D f) ≡ f
  ⟜η _ _ _ _ = refl

  ⊸DAY : (B D : Fam) → ⊸At DAYMC B D
  ⊸DAY B D .vertex = ⊸ᴰ B D
  ⊸DAY B D .element = ⊸app B D
  ⊸DAY B D .universal A =
    isoToIsEquiv (iso (⊸intro⁻ A B D) (⊸intro A B D) (⊸β A B D) (⊸η A B D))

  ⟜DAY : (A D : Fam) → ⟜At DAYMC A D
  ⟜DAY A D .vertex = ⟜ᴰ A D
  ⟜DAY A D .element = ⟜app A D
  ⟜DAY A D .universal B =
    isoToIsEquiv (iso (⟜intro⁻ A B D) (⟜intro A B D) (⟜β A B D) (⟜η A B D))

  ------------------------------------------------------------------
  -- Set-indexed products and coproducts are pointwise Π and Σ. Both
  -- round trips are `refl`, so `strictContrFibers` applies.
  ------------------------------------------------------------------
  ΠDAY : (X : hSet ℓ) (A : ⟨ X ⟩ → Fam) → ΠTy DAYC A
  ΠDAY X A .vertex m =
    (∀ x → El (A x) m) , isSetΠ (λ x → A x m .snd)
  ΠDAY X A .element x _ f = f x
  ΠDAY X A .universal Γ .equiv-proof =
    strictContrFibers (λ h m γ x → h x m γ)

  ΣDAY : (X : hSet ℓ) (A : ⟨ X ⟩ → Fam) → ΣTy DAYC A
  ΣDAY X A .vertex m =
    (Σ[ x ∈ ⟨ X ⟩ ] El (A x) m) , isSetΣ (X .snd) (λ x → A x m .snd)
  ΣDAY X A .element x _ a = x , a
  ΣDAY X A .universal Γ .equiv-proof =
    strictContrFibers (λ h m (x , a) → h x m a)

  ------------------------------------------------------------------
  Day : Model (ℓ-suc ℓ) ℓ ℓ
  Day .Model.MC = DAYMC
  Day .Model.biclosed .Biclosed.⊸ues = ⊸DAY
  Day .Model.biclosed .Biclosed.⟜ues = ⟜DAY
  Day .Model.Πs = ΠDAY
  Day .Model.Σs = ΣDAY

  DayOn : (Gen : hSet ℓ) (lit : ⟨ Gen ⟩ → Fam)
        → GrammarModel (ℓ-suc ℓ) ℓ ℓ Gen
  DayOn Gen lit .GrammarModel.model = Day
  DayOn Gen lit .GrammarModel.⟦lit⟧ = lit

--------------------------------------------------------------------
-- Instance 1: the trivial monoid.
--------------------------------------------------------------------
-- `Unit*` is a monoid on the nose: all three laws are `Eq.refl`,
-- since `Unit*` has η. A family over `Unit*` is just a set, the
-- splitting data is contractible, and the model degenerates to
-- something equivalent to `Semantics.Instances.Sets` — every
-- character contributes a featureless token.
TrivialEqMonoid : (ℓ : Level) → EqMonoid ℓ
TrivialEqMonoid ℓ = record
  { Carrier = Unit*
  ; isSetCarrier = isSetUnit*
  ; ⟨ε⟩ = tt*
  ; _·_ = λ _ _ → tt*
  ; ·assoc = λ _ _ _ → Eq.refl
  ; ·unit-l = λ _ → Eq.refl
  ; ·unit-r = λ _ → Eq.refl
  }

TrivialDay : Model (ℓ-suc ℓ) ℓ ℓ
TrivialDay {ℓ = ℓ} = Day (TrivialEqMonoid ℓ)

TrivialDayOn : (Gen : hSet ℓ) → GrammarModel (ℓ-suc ℓ) ℓ ℓ Gen
TrivialDayOn {ℓ = ℓ} Gen =
  DayOn (TrivialEqMonoid ℓ) Gen (λ _ _ → Unit* , isSetUnit*)

--------------------------------------------------------------------
-- Instance 2: the free monoid on a set of generators.
--------------------------------------------------------------------
-- `List ⟨Gen⟩` with `[]` and `_++_`. Left unitality is `Eq.refl`
-- because `[] ++ xs` reduces; the other two laws are the `Eq`-valued
-- list lemmas from `Cubical.Data.List.More`, which are exactly the
-- ones `Grammar.LinearProduct.AsEquality` uses.
--
-- Instantiating `Day` at this monoid reproduces the families model of
-- `Semantics.Instances.Families`: `Carrier` is `String`, `Split` is
-- `String.Base.SplittingEq`, `_⊛_` is `Grammar.LinearProduct`'s
-- `_⊗_`, `εᴰ` is `Grammar.Epsilon.AsEquality`'s `ε`, and `⊸ᴰ`/`⟜ᴰ`
-- are `Grammar.LinearFunction`'s `_⊸_`/`_⟜_` — all with the same
-- right-hand sides. It is not literally the same Agda term, since
-- those live behind `opaque` in `Grammar.*` and the monoidal category
-- there is assembled from `Term.Category.GRAMMAR`; but the
-- definitions agree line for line.
FreeEqMonoid : (Gen : hSet ℓ) → EqMonoid ℓ
FreeEqMonoid Gen = record
  { Carrier = List ⟨ Gen ⟩
  ; isSetCarrier = isOfHLevelList 0 (Gen .snd)
  ; ⟨ε⟩ = []
  ; _·_ = _++_
  ; ·assoc = ++-assoc-Eq
  ; ·unit-l = λ _ → Eq.refl
  ; ·unit-r = ++-unit-r-Eq
  }

FreeDay : (Gen : hSet ℓ) → Model (ℓ-suc ℓ) ℓ ℓ
FreeDay Gen = Day (FreeEqMonoid Gen)

-- The intended grammar model: a generator `c` is interpreted by the
-- family that is inhabited exactly at the one-letter word `[ c ]`,
-- i.e. by `Grammar.Literal`'s `literal c`.
FreeDayOn : (Gen : hSet ℓ) → GrammarModel (ℓ-suc ℓ) ℓ ℓ Gen
FreeDayOn Gen =
  DayOn (FreeEqMonoid Gen) Gen
    (λ c w → (w Eq.≡ (c ∷ []))
           , isProp→isSet (EqMonoid.isPropEq (FreeEqMonoid Gen) w (c ∷ [])))
