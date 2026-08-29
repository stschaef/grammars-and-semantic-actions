{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Nullability and the Brzozowski derivative for a context-free grammar code.

   `Ascent/Lookahead` *chooses* a branch at the decision point, which is what
   caps it at LC(k).  The alternative is not to choose: advance every summand
   at once and let the input kill the ones that no longer fit.  That is the
   derivative, because `Dl` distributes over `⊕` on the nose
   (`Regex/Derivative`s `Dl-⊕-in`), and the dot-advance rule for a production
   body is `Dl-⊗-in-l` / `Dl-⊗-in-r`.

   Not choosing is *more* than LR, not the same thing: an LR machine still
   commits, it just commits later and with a table.  Keeping every branch
   alive is the general-CFG regime -- Earley and GLR -- and it is what
   `Derivative/Parser` builds on this.  See that file's header.

   This file supplies the two prerequisites for that: nullability of a code,
   and the derivative of a code, with soundness.  `Regex/Derivative` has both
   for regular expressions; the point here is that the *context-free* case is
   no harder, because the recursive occurrences are handled by a second family
   rather than by unrolling.

   `CF X` is a grammar body over nonterminals `X`, with two kinds of variable:
   `var x` is the nonterminal itself and `dv x` is its derivative.  The
   interpretation takes both families, so `δ` can put an undifferentiated `G`
   next to a differentiated `δ F` -- which is what the `⊗` rule needs and what
   a renaming into `X ⊎ X` would otherwise cost. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Derivative.OneStep
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Bool using (Bool ; true ; false ; _or_ ; _and_)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Data.Unit using (tt ; tt*)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (Dl-lit-ε)
open import Theory.Instances.Monoid.Regex.Derivative Alphabet _≟_ ℓ-zero
  using ( Dl-⊕-in ; Dl-⊗-in-l ; Dl-⊗-in-r ; Dl-map )
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
  using (Dl)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-l⁻)

private variable ℓX : Level

-- A context-free body over nonterminals `X`.
data CF (X : Type ℓX) : Type (ℓ-max ℓAlph ℓX) where
  lit    : Alphabet → CF X
  ε̂ ⊥̂    : CF X
  var    : X → CF X        -- the nonterminal
  dv     : X → CF X        -- its derivative
  _⊕̂_    : CF X → CF X → CF X
  _⊗̂_    : CF X → CF X → CF X

infixr 20 _⊗̂_
infixr 15 _⊕̂_

-- the interpretation: `var` at the grammar family, `dv` at its derivative
Int : {X : Type ℓX} (A A' : X → TheoryTy ℓM tt) → CF X → TheoryTy ℓM tt
Int A A' (lit c) = literal c
Int A A' ε̂ = εTy
Int A A' ⊥̂ = ⊥Ty↑ ℓM
Int A A' (var x) = A x
Int A A' (dv x) = A' x
Int A A' (F ⊕̂ G) = Int A A' F ⊕ Int A A' G
Int A A' (F ⊗̂ G) = Int A A' F ⊗ Int A A' G
-- NULLABILITY, from an assignment on the nonterminals.
module _ {X : Type ℓX} (νv : X → Bool) where

  ν : CF X → Bool
  ν (lit c) = false
  ν ε̂ = true
  ν ⊥̂ = false
  ν (var x) = νv x
  ν (dv x) = false          -- `δ` is only ever applied to `dv`-free bodies
  ν (F ⊕̂ G) = ν F or ν G
  ν (F ⊗̂ G) = ν F and ν G

  -- taking a disjunction / conjunction apart
  orTrue : (a b : Bool) → (a or b) Eq.≡ true
    → (a Eq.≡ true) Sum.⊎ (b Eq.≡ true)
  orTrue true b p = Sum.inl Eq.refl
  orTrue false b p = Sum.inr p

  andTrue : (a b : Bool) → (a and b) Eq.≡ true
    → (a Eq.≡ true) Sum.⊎ ((a Eq.≡ true) → Empty.⊥)
  andTrue true true p = Sum.inl Eq.refl
  andTrue true false ()
  andTrue false b ()

  andTrue₂ : (a b : Bool) → (a and b) Eq.≡ true → b Eq.≡ true
  andTrue₂ true true p = Eq.refl
  andTrue₂ true false ()
  andTrue₂ false b ()

  andTrue₁ : (a b : Bool) → (a and b) Eq.≡ true → a Eq.≡ true
  andTrue₁ true b p = Eq.refl
  andTrue₁ false b ()

-- THE DERIVATIVE of a body.  `var x` becomes `dv x`: the recursion is handed
-- to the derivative family rather than unrolled, which is the only thing
-- that differs from the regular case.  Both choices are made by a helper
-- taking the decision as an argument, so that they refine in the proofs.
module _ {X : Type ℓX} (νv : X → Bool) where

  litD : (d c : Alphabet)
    → (d Eq.≡ c) Sum.⊎ ((d Eq.≡ c) → Empty.⊥) → CF X
  litD d c (Sum.inl _) = ε̂
  litD d c (Sum.inr _) = ⊥̂

  nullOf : Bool → CF X → CF X
  nullOf true H = H
  nullOf false H = ⊥̂

  δ : CF X → Alphabet → CF X
  δ (lit d) c = litD d c (d ≟ c)
  δ ε̂ c = ⊥̂
  δ ⊥̂ c = ⊥̂
  δ (var x) c = dv x
  δ (dv x) c = ⊥̂
  δ (F ⊕̂ G) c = δ F c ⊕̂ δ G c
  δ (F ⊗̂ G) c = (δ F c ⊗̂ G) ⊕̂ nullOf (ν νv F) (δ G c)

-- SOUNDNESS.  `ν` really does witness the empty word, and `δ` really is the
-- derivative -- the recursive case discharged by the derivative family, not
-- by unrolling.
module _ {X : Type ℓX} (A A' : X → TheoryTy ℓM tt) (νv : X → Bool) where

  ν-sound : (nulW : (x : X) → νv x Eq.≡ true → εTy ⊢ A x)
    → (F : CF X) → ν νv F Eq.≡ true → εTy ⊢ Int A A' F
  ν-sound nulW (lit c) ()
  ν-sound nulW ε̂ p = id⊢
  ν-sound nulW ⊥̂ ()
  ν-sound nulW (var x) p = nulW x p
  ν-sound nulW (dv x) ()
  ν-sound nulW (F ⊕̂ G) p = go (orTrue νv (ν νv F) (ν νv G) p)
    where
    go : (ν νv F Eq.≡ true) Sum.⊎ (ν νv G Eq.≡ true) → εTy ⊢ Int A A' (F ⊕̂ G)
    go (Sum.inl q) = inl ∘⊢ ν-sound nulW F q
    go (Sum.inr q) = inr ∘⊢ ν-sound nulW G q
  ν-sound nulW (F ⊗̂ G) p =
    (ν-sound nulW F (andTrue₁ νv (ν νv F) (ν νv G) p)
     ,⊗ ν-sound nulW G (andTrue₂ νv (ν νv F) (ν νv G) p))
    ∘⊢ ⊗ε-unit-l⁻

  module _ (c : Alphabet)
    (nulW : (x : X) → νv x Eq.≡ true → εTy ⊢ A x)
    (step : (x : X) → A' x ⊢ Dl c (A x)) where

    private
      -- a literal's derivative: `ε` when the letter matches, `⊥` otherwise
      litSound : (d : Alphabet)
        (e : (d Eq.≡ c) Sum.⊎ ((d Eq.≡ c) → Empty.⊥))
        → Int A A' (litD νv d c e) ⊢ Dl c (literal d)
      litSound d (Sum.inl Eq.refl) = Dl-lit-ε d
      litSound d (Sum.inr _) = ⊥Ty↑-elim

    δ-sound : (F : CF X) → Int A A' (δ νv F c) ⊢ Dl c (Int A A' F)
    δ-sound (lit d) = litSound d (d ≟ c)
    δ-sound ε̂ = ⊥Ty↑-elim
    δ-sound ⊥̂ = ⊥Ty↑-elim
    δ-sound (var x) = step x
    δ-sound (dv x) = ⊥Ty↑-elim
    δ-sound (F ⊕̂ G) = Dl-⊕-in c {A = Int A A' F} {B = Int A A' G}
      ∘⊢ ⊕-elim (inl ∘⊢ δ-sound F) (inr ∘⊢ δ-sound G)
    δ-sound (F ⊗̂ G) =
      ⊕-elim (Dl-⊗-in-l c {A = Int A A' F} {B = Int A A' G} ∘⊢ (δ-sound F ,⊗ id⊢))
             (nullSound (ν νv F) (ν-sound nulW F))
      where
      nullSound : (b : Bool) → (b Eq.≡ true → εTy ⊢ Int A A' F)
        → Int A A' (nullOf νv b (δ νv G c))
        ⊢ Dl c (Int A A' F ⊗ Int A A' G)
      nullSound true w = Dl-⊗-in-r c {A = Int A A' F} {B = Int A A' G} (w Eq.refl)
        ∘⊢ δ-sound G
      nullSound false _ = ⊥Ty↑-elim
