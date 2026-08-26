{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The Kleene fold by guarded recursion, so no `TERMINATING` is asserted.

   `KleeneStar.fold*r` is `Inductive/Base.rec`, whose descent runs through
   `map`; Agda cannot see into it, hence the pragma.  `Guard` cannot rescue
   it either: its `⊗e` clause quantifies over *all* splittings of the input,
   including the empty one, so it demands `m < m`.

   The missing hypothesis is that the head of a cons really consumes.  That
   is `PayR`'s shape exactly -- it receives the head's inhabitant before it
   owes the order fact -- so non-nullability is all that has to be supplied,
   and the recursion is `löbG`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.KleeneStar.Guarded
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
import Cubical.Data.Empty as Empty
import Cubical.Data.List.Properties as L
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Suffix.Base Alphabet isSetAlphabet
open import Theory.Instances.Monoid.GuardedSplit MonEqns Alphabet (λ _ → tt)
  listPresentation
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt)
  listPresentation

private variable ℓA ℓB : Level

-- Non-nullability, internally: nothing that is an `A` is the empty word.
-- A `⊢`-term -- no model element, no splitting, no order.
¬Nullable : TheoryTy ℓA tt → Type _
¬Nullable A = A & εTy ⊢ ⊥Ty

-- What a cons owes `PayR`: its head, being inhabited, puts the tail strictly
-- below.  This is the external reading of the same fact, and it is what the
-- order needs; clients state `¬Nullable` and never see this.
NonNull : TheoryTy ℓA tt → Type _
NonNull A = (m : String) (ms : interpIn _⊙_ ↓M) → op _⊙_ ms Eq.≡ m
  → A (ms zero) → ms (suc zero) ◂ m

-- A letter is never empty, so every literal-headed production pays for
-- itself.  This is the LL fragment, discharged once.
literal-¬Nullable : (c : Alphabet) → ¬Nullable (literal c)
literal-¬Nullable c m (lc , (_ , ee , _)) =
  Empty.rec (L.¬cons≡nil (sym (Eq.eqToPath ee ∙ Eq.eqToPath lc)))

-- Non-nullability is compositional, so a token grammar states it the same
-- way it is built.
⊗-¬Nullable : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → ¬Nullable A → ¬Nullable (A ⊗ B)
⊗-¬Nullable {A = A} nu m (t , eps) =
  go (t .fst zero) (t .fst (suc zero)) (t .snd .snd .fst)
     (Eq.eqToPath (t .snd .fst) ∙ sym (Eq.eqToPath (eps .snd .fst)))
  where
  go : (u v : String) → A u → (u ++ v) ≡ [] → ⊥Ty m
  go [] v a p = nu [] (a , εTy-pt)
  go (c ∷ u) v a p = Empty.rec (L.¬cons≡nil p)

⊕-¬Nullable : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → ¬Nullable A → ¬Nullable B → ¬Nullable (A ⊕ B)
⊕-¬Nullable nuA nuB =
  ⊕-elim& (nuA ∘⊢ &-swap) (nuB ∘⊢ &-swap) ∘⊢ &-swap

char-¬Nullable : ¬Nullable char
char-¬Nullable m ((c , lc) , eps) = literal-¬Nullable c m (lc , eps)

-- ...and the bridge.  A head that is an `A` cannot be `[]`, so what follows
-- it is a *proper* suffix.  This is the only place the two readings meet.
¬Nullable→NonNull : {A : TheoryTy ℓA tt} → ¬Nullable A → NonNull A
¬Nullable→NonNull {A = A} nu m ms e =
  Eq.transport (ms (suc zero) ◂_) e ∘ go (ms zero) (ms (suc zero))
  where
  go : (u v : String) → A u → v ◂ (u ++ v)
  go [] v h = Empty.rec (lower (nu [] (h , εTy-pt)))
  go (c ∷ u) v h = ◂-cons c u v

module _ {A : TheoryTy ℓA tt} (B : TheorySet ℓB tt) (nu : ¬Nullable A) where
  private
    -- the family being fixed: the fold itself, as an internal function
    Fam : TheorySet _ tt
    Fam = (A * ⇒ ty B) , isSet⇒ (isSetTy B)

    module GB = Guarded▷ (λ _ → ty Fam) (λ _ → isSetTy Fam)

    pay : PayR GB.suffixLöb {X = A}
    pay = ¬Nullable→NonNull nu

    unroll↑ : A * ⊢ (A ⊗ (A *)) ⊕ εTy
    unroll↑ = ⊕-elim inl (inr ∘⊢ lowerTy) ∘⊢ unroll*

  module _ (nil : εTy ⊢ ty B) (cons : A ⊗ ty B ⊢ ty B) where
    private
      -- the delayed fold reaches the tail because the head was paid for
      step : (A ⊗ (A *)) & GB.▷ tt ⊢ ty B
      step = cons ∘⊢ (id⊢ ,⊗ (⇒-app ∘⊢ &-swap)) ∘⊢ ▷⊛r GB.suffixLöb pay

      body : GB.▷ tt & (A *) ⊢ ty B
      body = ⊕-elim& (step ∘⊢ &-swap) (nil ∘⊢ π₂) ∘⊢ (id& unroll↑)

    -- ...and Löb closes it.  One combinator, no pragma.
    fold*g : A * ⊢ ty B
    fold*g = ⇒-app ∘⊢ ((GB.löb (λ _ → ⇒-intro body) tt ∘⊢ ⊤Ty-intro) ,& id⊢)

------------------------------------------------------------------------
-- The two star actions, by löb.  `SemanticAction.semact-*` and
-- `semact-skip*` are `rec`, so the pragma sits under every action; these
-- are the same folds with `fold*g` underneath.
--
-- The price is `isSet X`: löb fixes a family and wants it set-valued,
-- where `rec` did not.

open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
import Theory.Instances.Monoid.SemanticAction Alphabet isSetAlphabet as Act

private variable ℓX : Level

private
  ΔSet : {X : Type ℓX} → isSet X → TheorySet ℓX tt
  ΔSet {X = X} isSetX = Act.Δ X , isSet⊕ᴰ isSetX λ _ → isSet⊤Ty

semact-*g : {A : TheoryTy ℓA tt} {X : Type ℓX}
  → isSet X → ¬Nullable A
  → Act.SemanticAction A X → Act.SemanticAction (A *) (List X)
semact-*g {X = X} isSetX nu a =
  fold*g (ΔSet (isOfHLevelList 0 isSetX)) nu (Act.semact-pure [])
    (Act.semact-map (λ p → p .fst ∷ p .snd) (Act.semact-⊗₂ a Act.semact-Δ))

semact-skip*g : {A : TheoryTy ℓA tt} {X : Type ℓX}
  → isSet X → ¬Nullable A
  → Act.SemanticAction A (Maybe X) → Act.SemanticAction (A *) (List X)
semact-skip*g {X = X} isSetX nu a =
  fold*g (ΔSet (isOfHLevelList 0 isSetX)) nu (Act.semact-pure [])
    (Act.semact-map push (Act.semact-⊗₂ a Act.semact-Δ))
  where
  push : Maybe X × List X → List X
  push (nothing , ys) = ys
  push (just x , ys) = x ∷ ys
