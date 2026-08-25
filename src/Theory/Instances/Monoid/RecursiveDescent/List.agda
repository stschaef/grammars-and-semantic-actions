{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.RecursiveDescent.List
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)) where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using ([] ; _∷_ ; _++_)
import Cubical.Data.List.Properties as L
import Cubical.Data.Maybe as M
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (Unit ; Unit* ; tt ; tt*)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
-- the theory's types at this alphabet; nothing below is about them
open import Theory.Instances.Monoid.Types Alphabet _≟_ public
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet public

private variable ℓA ℓB ℓC ℓD : Level

Test : TheoryTy ℓA tt → Type _
Test A = ⊤Ty ⊢ Maybe A

Parser : TheoryTy ℓA tt → Type _
Parser A = Test (A ⊗ ⊤Ty)

mapT : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊢ B → Test A → Test B
mapT f p = Monad.fmap MaybeMonad f ∘⊢ p

altMaybe : {A : TheoryTy ℓA tt} → Maybe A & Maybe A ⊢ Maybe A
altMaybe m (Sum.inl a , _) = Sum.inl a
altMaybe m (Sum.inr _ , r) = r

_<|>_ : {A : TheoryTy ℓA tt} → Test A → Test A → Test A
p <|> q = altMaybe ∘⊢ (p ,& q)

infixr 15 _<|>_

Maybe& : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → Maybe A & Maybe B ⊢ Maybe (A & B)
Maybe& m (Sum.inl a , Sum.inl b) = Sum.inl (a , b)
Maybe& m (Sum.inl a , Sum.inr _) = Sum.inr tt
Maybe& m (Sum.inr _ , _) = Sum.inr tt

_&T_ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → Test A → Test B → Test (A & B)
p &T q = Maybe& ∘⊢ (p ,& q)

Maybe⊗r : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → A ⊗ Maybe B ⊢ Maybe (A ⊗ B)
Maybe⊗r m (ms , e , (a , (Sum.inl b , _))) = Sum.inl (ms , e , (a , (b , tt*)))
Maybe⊗r m (ms , e , (a , (Sum.inr _ , _))) = Sum.inr tt

onSuccess : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → (A ⊢ Maybe B) → Maybe A ⊢ Maybe B
onSuccess = Monad.bind MaybeMonad

mapP : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} → A ⊢ B → Parser A → Parser B
mapP f p = Monad.fmap MaybeMonad (f ,⊗ id⊢) ∘⊢ p

pureP : {A : TheoryTy ℓA tt} → εTy ⊢ A → Parser A
pureP f m _ = Sum.inl (two [] m , Eq.refl , (f [] εTy-pt , (tt , tt*)))

failT : {A : TheoryTy ℓA tt} → Test A
failT = nothing ∘⊢ ⊤Ty-intro

failP : {A : TheoryTy ℓA tt} → Parser A
failP = failT

seqP : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → Parser A → Parser B → Parser (A ⊗ B)
seqP p q =
  onSuccess (Monad.fmap MaybeMonad ⊗-assoc⁻ ∘⊢ Maybe⊗r ∘⊢ (id⊢ ,⊗ q)) ∘⊢ p

seqT : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → Parser A → Test B → Test (A ⊗ B)
seqT p q = onSuccess (Maybe⊗r ∘⊢ (id⊢ ,⊗ q)) ∘⊢ p

anyChar : Parser char
anyChar = ⊕ᴰ-elim step ∘⊢ Λ-total
  where
  step : ∀ o → Λ₁ o ⊢ Maybe (char ⊗ ⊤Ty)
  step ε₁ = nothing ∘⊢ ⊤Ty-intro
  step (tk c) = just ∘⊢ (σ⊕ c ,⊗ id⊢)

lookBy : {A : TheoryTy ℓA tt} → ((o : M₁) → Λ₁ o ⊢ Maybe A) → Test A
lookBy f = ⊕ᴰ-elim f ∘⊢ Λ-total

lookCase : (o o' : M₁) → (o' Eq.≡ o) Sum.⊎ ((o' Eq.≡ o) → Empty.⊥)
  → Λ₁ o' ⊢ Maybe (Λ₁ o)
lookCase o o' (Sum.inl Eq.refl) = just
lookCase o o' (Sum.inr _) = nothing ∘⊢ ⊤Ty-intro

lookStep : (o o' : M₁) → Λ₁ o' ⊢ Maybe (Λ₁ o)
lookStep o o' = lookCase o o' (o' ≟M o)

look : (o : M₁) → Test (Λ₁ o)
look o = lookBy (lookStep o)

litP : (c : Alphabet) → Parser (literal c)
litP c = look (tk c)

-- `look`, with the fibres it did not observe refuted: the cover's
-- disjointness is exactly the refutation, so this replaces `look-ok`.
dec-look : (o : M₁) → Decidable (Λ₁ o)
dec-look = dec-cover _≟M_ lookaheadCover

-- The one-token derivative.  Reading `c` off the front leaves exactly `B`
-- on the tail, so `literal c ⊗ B` is decided wherever `B` is.  The split is
-- passed component-wise -- a projection is not a pattern -- so that
-- `Eq.refl` has variables to unify.  The word-level lemmas are in `Precise`.

-- the empty word has no letter to read
dec-lit⊗-nil : {B : TheoryTy ℓA tt} (c : Alphabet)
  → DecTy (literal c ⊗ B) []
dec-lit⊗-nil c = Sum.inr λ where
  (ms , e , (lc , _)) → lit⊗-nil c (ms zero) (ms (suc zero)) lc e

-- ...and a non-empty one reads it, then asks about the tail
dec-lit⊗-cons : {B : TheoryTy ℓA tt} (c a : Alphabet) (as : ↓M tt)
  → DecTy B as → DecTy (literal c ⊗ B) (a ∷ as)
dec-lit⊗-cons {B = B} c a as = step a as (a ≟ c)
  where
  step : (a : Alphabet) (as : ↓M tt)
    → (a Eq.≡ c) Sum.⊎ ((a Eq.≡ c) → Empty.⊥) → DecTy B as
    → DecTy (literal c ⊗ B) (a ∷ as)
  step .c as (Sum.inl Eq.refl) (Sum.inl b) =
    Sum.inl (two (c ∷ []) as , Eq.refl , (Eq.refl , (b , tt*)))
  step .c as (Sum.inl Eq.refl) (Sum.inr nb) = Sum.inr λ where
    (ms , e , (lc , (b , _))) →
      nb (lit⊗-tail c (ms zero) (ms (suc zero)) as lc e b)
  step a as (Sum.inr ne) _ = Sum.inr λ where
    (ms , e , (lc , _)) →
      lit⊗-head c a (ms zero) (ms (suc zero)) as ne lc e

dec-lit⊗ : {B : TheoryTy ℓA tt} (c : Alphabet)
  → Decidable B → Decidable (literal c ⊗ B)
dec-lit⊗ {B = B} c d [] _ = dec-lit⊗-nil c
dec-lit⊗ {B = B} c d (a ∷ as) _ = dec-lit⊗-cons c a as (d as tt)

-- The same, at `char`: no letter has to be compared, so only the tail's
-- decision is spent.
dec-char⊗-nil : {B : TheoryTy ℓA tt} → DecTy (char ⊗ B) []
dec-char⊗-nil = Sum.inr λ where
  ((ms , e , ((d , lc) , _))) → lit⊗-nil d (ms zero) (ms (suc zero)) lc e

dec-char⊗-cons : {B : TheoryTy ℓA tt} (a : Alphabet) (as : ↓M tt)
  → DecTy B as → DecTy (char ⊗ B) (a ∷ as)
dec-char⊗-cons {B = B} a as (Sum.inl b) =
  Sum.inl (two (a ∷ []) as , Eq.refl , ((a , Eq.refl) , (b , tt*)))
dec-char⊗-cons {B = B} a as (Sum.inr nb) = Sum.inr λ where
  (ms , e , ((d , lc) , (b , _))) →
    nb (subst B (L.cons-inj₂ (flat d (ms zero) (ms (suc zero)) (a ∷ as) lc e)) b)

-- The end of input, as a parser: succeeds only on the empty suffix.
eofP : Parser εTy
eofP = ⊕ᴰ-elim step ∘⊢ Λ-total
  where
  step : ∀ o → Λ₁ o ⊢ Maybe (εTy ⊗ ⊤Ty)
  step ε₁ = just ∘⊢ ⊗-unit-r⁻ ∘⊢ lowerTy
  step (tk c) = nothing ∘⊢ ⊤Ty-intro

-- A whole-input parse: demand that nothing is left over.
completeP : {A : TheoryTy ℓA tt} → Parser A → Parser (A ⊗ εTy)
completeP p = seqP p eofP

-- The coarsest observation of a parse: did it succeed?
semact-ok : {A : TheoryTy ℓA tt} → SemanticAction (Maybe A) Bool
semact-ok = semact-⊕ (semact-pure true) (semact-pure false)

-- Observing a parse: `nothing` on failure, otherwise the tree's value.
-- The `⊗`-projections drop the empty residual and the outer `⊤Ty`.
semact-complete : {A : TheoryTy ℓA tt} {X : Type ℓB}
  → SemanticAction A X → SemanticAction (Maybe ((A ⊗ εTy) ⊗ ⊤Ty)) (M.Maybe X)
semact-complete a =
  semact-⊕ (semact-map M.just (semact-⊗₁ (semact-⊗₁ a)))
           (semact-pure M.nothing)
