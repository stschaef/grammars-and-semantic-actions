{-# OPTIONS --lossy-unification #-}
{- The span/matrix model: chart parsing as a semantics of the DSL.

   Fix a set `Pos` of *positions* in an input. A grammar is interpreted
   as a `Pos × Pos`-indexed matrix of sets

     A : Pos → Pos → hSet

   where `A i j` is the set of parse trees of `A` spanning the input
   between positions `i` and `j`. A term is a family of functions, one
   for each span. The connectives are then linear algebra:

     (A ⊗ B) i j  =  Σ[ k ∈ Pos ] A i k × B k j     matrix product
     ε i j        =  (i ≡ j)                        identity matrix
     (B ⊸ D) i k  =  ∀ j → B k j → D i j            left division
     (D ⟜ A) k j  =  ∀ i → A i k → D i j            right division
     (⊕ᴰ A) i j   =  Σ[ x ] A x i j
     (&ᴰ A) i j   =  ∀ x → A x i j

   `⊗` is matrix multiplication over the semiring of sets, `ε` is the
   Kronecker delta, and the derived Kleene star

     A * ≅ ε ⊕ (A ⊗ A *)  =  I + A + A² + A³ + ⋯

   is the reflexive-transitive closure of the matrix `A`: an element of
   `(A *) i j` is a chain of `A`-derivations tiling the span `i…j`.
   Restricted to the concrete chart of a fixed input word (see the
   `Chart` module at the bottom) this is exactly the CYK table, and a
   proof of `⟦ A ⟧ 0 n` is a parse of the whole input. So the very same
   generic DSL code that elaborates to families-over-strings in
   `Semantics.Instances.Families`, and to plain sets in
   `Semantics.Instances.Sets`, elaborates here to chart parsing.

   The unit is `Cubical.Data.Equality`'s *inductive* equality rather
   than a path. That is what makes the unitors compute: `lunit→` may
   pattern match on `Eq.refl`, so `lunit→ ∘ lunit← ≡ id` holds by
   `refl` and the remaining coherences are one case split each. With
   `Path` instead, nothing would reduce.

   Every universal property (⊸, ⟜, Π, Σ) still holds by `refl` in both
   directions, so all four are given by `strictContrFibers`.
-}
module Semantics.Instances.Spans where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv.Base using (strictContrFibers; equiv-proof)

open import Cubical.Data.Sigma

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

open UniversalElement

private
  variable
    ℓ : Level

-- | Inductive equality in a set is again a set. Needed because the
-- unit of the tensor is a matrix of equality types.
isSetEq : {A : Type ℓ} → isSet A → (x y : A) → isSet (x Eq.≡ y)
isSetEq {A = A} isSetA x y =
  isProp→isSet (subst isProp (Eq.PathPathEq {A = A} {x = x} {y = y}) (isSetA x y))

module _ (ℓ : Level) (Pos : hSet ℓ) where
  private
    P : Type ℓ
    P = ⟨ Pos ⟩

  -- | An object is a matrix of sets indexed by spans of positions.
  Span : Type (ℓ-suc ℓ)
  Span = P → P → hSet ℓ

  -- | A morphism is a span-indexed family of functions.
  SpanHom : Span → Span → Type ℓ
  SpanHom A B = ∀ i j → ⟨ A i j ⟩ → ⟨ B i j ⟩

  ----------------------------------------------------------------
  -- The structure maps. Named up front so that the record
  -- expressions below mention no argument patterns.
  ----------------------------------------------------------------
  private
    idSpan : {A : Span} → SpanHom A A
    idSpan i j a = a

    seqSpan : {A B D : Span} → SpanHom A B → SpanHom B D → SpanHom A D
    seqSpan f g i j a = g i j (f i j a)

    -- Morphism equality is pointwise.
    homEq : {A B : Span} {f g : SpanHom A B}
          → (∀ i j x → f i j x ≡ g i j x) → f ≡ g
    homEq p = funExt λ i → funExt λ j → funExt λ x → p i j x

    -- Matrix product.
    ⊗ob : Span → Span → Span
    ⊗ob A B i j =
      (Σ[ k ∈ P ] (⟨ A i k ⟩ × ⟨ B k j ⟩)) ,
      isSetΣ (Pos .snd) (λ k → isSet× (A i k .snd) (B k j .snd))

    ⊗hom : {A B A' B' : Span}
         → SpanHom A A' → SpanHom B B'
         → SpanHom (⊗ob A B) (⊗ob A' B')
    ⊗hom f g i j (k , a , b) = k , f i k a , g k j b

    -- Identity matrix. Inductive equality, not paths.
    εob : Span
    εob i j = (i Eq.≡ j) , isSetEq (Pos .snd) i j

    assoc→ : {A B D : Span} → SpanHom (⊗ob A (⊗ob B D)) (⊗ob (⊗ob A B) D)
    assoc→ i j (k , a , l , b , d) = l , (k , a , b) , d

    assoc← : {A B D : Span} → SpanHom (⊗ob (⊗ob A B) D) (⊗ob A (⊗ob B D))
    assoc← i j (l , (k , a , b) , d) = k , a , l , b , d

    lunit→ : {A : Span} → SpanHom (⊗ob εob A) A
    lunit→ i j (k , Eq.refl , a) = a

    lunit← : {A : Span} → SpanHom A (⊗ob εob A)
    lunit← i j a = i , Eq.refl , a

    runit→ : {A : Span} → SpanHom (⊗ob A εob) A
    runit→ i j (k , a , Eq.refl) = a

    runit← : {A : Span} → SpanHom A (⊗ob A εob)
    runit← i j a = j , a , Eq.refl

    -- The unitors are the only maps that need a case split; each of
    -- their coherences is one.
    -- The object arguments are explicit: an `hSet` is a Σ, so these
    -- statements mention only `A i j .fst`, from which Agda cannot
    -- solve `A`.
    lunitRet : (A : Span) (i j : P) (x : ⟨ ⊗ob εob A i j ⟩)
             → lunit← {A} i j (lunit→ {A} i j x) ≡ x
    lunitRet A i j (k , Eq.refl , a) = refl

    runitRet : (A : Span) (i j : P) (x : ⟨ ⊗ob A εob i j ⟩)
             → runit← {A} i j (runit→ {A} i j x) ≡ x
    runitRet A i j (k , a , Eq.refl) = refl

    lunitNat : (A B : Span) (f : SpanHom A B) (i j : P)
               (x : ⟨ ⊗ob εob A i j ⟩)
             → lunit→ {B} i j (⊗hom (idSpan {εob}) f i j x)
               ≡ f i j (lunit→ {A} i j x)
    lunitNat A B f i j (k , Eq.refl , a) = refl

    runitNat : (A B : Span) (f : SpanHom A B) (i j : P)
               (x : ⟨ ⊗ob A εob i j ⟩)
             → runit→ {B} i j (⊗hom f (idSpan {εob}) i j x)
               ≡ f i j (runit→ {A} i j x)
    runitNat A B f i j (k , a , Eq.refl) = refl

    triangleLem : (A B : Span) (i j : P) (x : ⟨ ⊗ob A (⊗ob εob B) i j ⟩)
      → ⊗hom (runit→ {A}) (idSpan {B}) i j (assoc→ {A} {εob} {B} i j x)
        ≡ ⊗hom (idSpan {A}) (lunit→ {B}) i j x
    triangleLem A B i j (k , a , l , Eq.refl , b) = refl

  ----------------------------------------------------------------
  -- The category of matrices of sets.
  ----------------------------------------------------------------
  SPAN : Category (ℓ-suc ℓ) ℓ
  SPAN = record
    { ob = Span
    ; Hom[_,_] = SpanHom
    ; id = idSpan
    ; _⋆_ = seqSpan
    ; ⋆IdL = λ _ → refl
    ; ⋆IdR = λ _ → refl
    ; ⋆Assoc = λ _ _ _ → refl
    ; isSetHom = λ {_} {B} →
        isSetΠ λ i → isSetΠ λ j → isSet→ (B i j .snd)
    }

  ----------------------------------------------------------------
  -- Matrix multiplication is monoidal, with the identity matrix as
  -- unit. Given as a record expression rather than by copatterns: the
  -- α/η/ρ coherence fields have types mentioning the sibling fields,
  -- and with `refl` bodies that reads to the termination checker as a
  -- recursive call on the definition being made.
  ----------------------------------------------------------------
  SPANMC : MonoidalCategory (ℓ-suc ℓ) ℓ
  SPANMC = record
    { C = SPAN
    ; monstr = record
      { tenstr = record
        { ─⊗─ = record
          { F-ob = λ AB → ⊗ob (AB .fst) (AB .snd)
          ; F-hom = λ fg → ⊗hom (fg .fst) (fg .snd)
          ; F-id = refl
          ; F-seq = λ _ _ → refl
          }
        ; unit = εob
        }
      ; α = record
        { trans = record { N-ob = λ _ → assoc→ ; N-hom = λ _ → refl }
        ; nIso = λ _ → record { inv = assoc← ; sec = refl ; ret = refl }
        }
      ; η = record
        { trans = record
          { N-ob = λ _ → lunit→
          ; N-hom = λ {A} {B} f → homEq (lunitNat A B f)
          }
        ; nIso = λ A → record
          { inv = lunit←
          ; sec = refl
          ; ret = homEq (lunitRet A)
          }
        }
      ; ρ = record
        { trans = record
          { N-ob = λ _ → runit→
          ; N-hom = λ {A} {B} f → homEq (runitNat A B f)
          }
        ; nIso = λ A → record
          { inv = runit←
          ; sec = refl
          ; ret = homEq (runitRet A)
          }
        }
      ; pentagon = λ _ _ _ _ → refl
      ; triangle = λ A B → homEq (triangleLem A B)
      }
    }

  ----------------------------------------------------------------
  -- The two closures are the two matrix divisions. `⊸` is the right
  -- adjoint of `- ⊗ B`: a map `∀ i j → (Σ k. A i k × B k j) → D i j`
  -- is the same as `∀ i k → A i k → (∀ j → B k j → D i j)`, and
  -- symmetrically for `⟜`.
  ----------------------------------------------------------------
  ⊸SPAN : (B D : Span) → ⊸At SPANMC B D
  ⊸SPAN B D .vertex i k =
    ((j : P) → ⟨ B k j ⟩ → ⟨ D i j ⟩) ,
    isSetΠ λ j → isSet→ (D i j .snd)
  ⊸SPAN B D .element i j (k , f , b) = f j b
  ⊸SPAN B D .universal A .equiv-proof =
    strictContrFibers (λ h i k a j b → h i j (k , a , b))

  ⟜SPAN : (A D : Span) → ⟜At SPANMC A D
  ⟜SPAN A D .vertex k j =
    ((i : P) → ⟨ A i k ⟩ → ⟨ D i j ⟩) ,
    isSetΠ λ i → isSet→ (D i j .snd)
  ⟜SPAN A D .element i j (k , a , f) = f i a
  ⟜SPAN A D .universal B .equiv-proof =
    strictContrFibers (λ h k j b i a → h i j (k , a , b))

  ----------------------------------------------------------------
  -- Indexed products and coproducts are Π and Σ, taken entrywise.
  ----------------------------------------------------------------
  ΠSPAN : (X : hSet ℓ) (A : ⟨ X ⟩ → Span) → ΠTy SPAN A
  ΠSPAN X A .vertex i j =
    ((x : ⟨ X ⟩) → ⟨ A x i j ⟩) , isSetΠ λ x → A x i j .snd
  ΠSPAN X A .element x i j f = f x
  ΠSPAN X A .universal Γ .equiv-proof =
    strictContrFibers (λ h i j γ x → h x i j γ)

  ΣSPAN : (X : hSet ℓ) (A : ⟨ X ⟩ → Span) → ΣTy SPAN A
  ΣSPAN X A .vertex i j =
    (Σ[ x ∈ ⟨ X ⟩ ] ⟨ A x i j ⟩) , isSetΣ (X .snd) (λ x → A x i j .snd)
  ΣSPAN X A .element x i j a = x , a
  ΣSPAN X A .universal Γ .equiv-proof =
    strictContrFibers (λ h i j p → h (p .fst) i j (p .snd))

  ----------------------------------------------------------------
  Spans : Model (ℓ-suc ℓ) ℓ ℓ
  Spans .Model.MC = SPANMC
  Spans .Model.biclosed .Biclosed.⊸ues = ⊸SPAN
  Spans .Model.biclosed .Biclosed.⟜ues = ⟜SPAN
  Spans .Model.Πs = ΠSPAN
  Spans .Model.Σs = ΣSPAN

  -- | A span model for any interpretation of the generators as
  -- matrices. In the chart reading, `lit c i j` is the evidence that
  -- the input carries the character `c` across the span `i…j`.
  SpansOn : (Gen : hSet ℓ) (lit : ⟨ Gen ⟩ → Span)
    → GrammarModel (ℓ-suc ℓ) ℓ ℓ Gen
  SpansOn Gen lit .GrammarModel.model = Spans
  SpansOn Gen lit .GrammarModel.⟦lit⟧ = lit

----------------------------------------------------------------
-- The intended instance: the parse chart of a fixed input word.
--
-- Positions are natural numbers (offsets into the input), and the
-- literal `c` holds of the span `i…j` exactly when `j = i + 1` and the
-- `i`th character of the input is `c`. So `⟦ A ⟧ 0 (length w)` is the
-- set of parses of the whole of `w`, and the model *is* the chart.
----------------------------------------------------------------
open import Cubical.Data.Nat using (ℕ; zero; suc; isSetℕ)
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Maybe.Properties using (isOfHLevelMaybe)

module Chart (Gen : hSet ℓ-zero) (w : List ⟨ Gen ⟩) where
  Positions : hSet ℓ-zero
  Positions = ℕ , isSetℕ

  private
    nth : ℕ → List ⟨ Gen ⟩ → Maybe ⟨ Gen ⟩
    nth _ [] = nothing
    nth zero (c ∷ _) = just c
    nth (suc n) (_ ∷ cs) = nth n cs

  -- | `c` spans `i…j` iff `j = i + 1` and `w [ i ] = c`.
  litChart : ⟨ Gen ⟩ → Span ℓ-zero Positions
  litChart c i j =
    ((j Eq.≡ suc i) × (nth i w Eq.≡ just c)) ,
    isSet× (isSetEq isSetℕ j (suc i))
           (isSetEq (isOfHLevelMaybe 0 (Gen .snd)) (nth i w) (just c))

  chart : GrammarModel (ℓ-suc ℓ-zero) ℓ-zero ℓ-zero Gen
  chart = SpansOn ℓ-zero Positions Gen litChart

  -- The span of the whole input: a parse of `A` is an element of
  -- `⟦ A ⟧ 0 (length w)`.
  wholeInput : ℕ
  wholeInput = length w
