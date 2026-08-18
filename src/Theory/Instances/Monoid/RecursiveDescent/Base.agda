{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Internal recursive-descent combinators for the free-monoid instance.

   A parser keeps the unconsumed suffix alongside its result.  This is the
   same interface as the old Grammar recursive-descent library; importantly,
   it is a map of TheoryTy's, not an Agda function over external lists. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.LocallySmall.Base
open WildCatNotation
open WildCatIso
import Cubical.Data.Equality as Eq
open import Cubical.Data.Equality.More using (isSet→isSetEq)
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.RecursiveDescent.Base
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Bool using (true ; false ; isSetBool)
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (_×_)
import Cubical.Data.Sum as Sum
import Cubical.Data.Maybe as M

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.SemanticAction Alphabet isSetAlphabet using
  (SemanticAction ; semact-String* ; semact-map ; semact-map-g)
open import Theory.Instances.Monoid.Rank Alphabet isSetAlphabet hiding (String)
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Monad.Base MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Monad.Maybe MonEqns Alphabet (λ _ → tt) listPresentation

private variable ℓA ℓB ℓC : Level

MaybeLeft : TheoryTy ℓA tt → TheoryTy _ tt
MaybeLeft A = Maybe (A ⊗ String*)

-- A parser is an internal map on canonical input strings.  `run` below will
-- expose such parsers at `⊤Ty` once the normal-form section is installed.
Parser : TheoryTy ℓA tt → Type _
Parser A = String* ⊢ MaybeLeft A

onSuccess : {ℓA ℓB : Level} {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → (A ⊗ String* ⊢ MaybeLeft B) → MaybeLeft A ⊢ MaybeLeft B
onSuccess {B = B} = λ k m → λ where
  (Sum.inl p) → k m p
  (Sum.inr _) → nothing {A = B ⊗ String*} m tt

mapResult : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → A ⊢ B → MaybeLeft A ⊢ MaybeLeft B
mapResult f = Monad.fmap MaybeMonad (f ,⊗ id⊢)

-- Sequencing only continues on success.  This is the binary instance of
-- tensor distributing over the error sum, written directly so it retains
-- the independently chosen tensor levels.
Maybe⊗r : {ℓA ℓB : Level} {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → A ⊗ Maybe B ⊢ Maybe (A ⊗ B)
Maybe⊗r m (ms , e , (a , Sum.inl b , tt*)) = Sum.inl (ms , e , (a , b , tt*))
Maybe⊗r m (ms , e , (a , Sum.inr _ , tt*)) = Sum.inr tt

-- The primitive token parser is entirely structural: observe one `String*`
-- layer, retain its tail on the successful branch, and fail on the empty
-- branch.  No external list or decidable equality is involved.
anyChar : Parser char
anyChar = step ∘⊢ unrollString
  where
  step : StringLayer ⊢ MaybeLeft char
  step m (false , _) = Sum.inr tt
  step m (true , (ms , e , cs)) =
    Sum.inl (ms , e , (cs zero .lower , cs (suc zero) .lower , tt*))

-- Tensor coherence belongs to the monoid theory, not to parsing: `⊗-assoc⁻`
-- comes from `Strings`.
seqP : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  → Parser A → Parser B → Parser (A ⊗ B)
seqP p q = onSuccess (Monad.fmap MaybeMonad ⊗-assoc⁻ ∘⊢ Maybe⊗r ∘⊢ (id⊢ ,⊗ q)) ∘⊢ p

_∨P_ : {A : TheoryTy ℓA tt} → Parser A → Parser A → Parser A
(p ∨P q) m s with p m s
... | Sum.inl x = Sum.inl x
... | Sum.inr _ = q m s

infixr 16 _∨P_

-- A parser's externally visible result is a semantic action: it observes
-- both the successful value and the unconsumed canonical string.
parser-output : {A : TheoryTy ℓA tt} {X : Type ℓB}
  → SemanticAction A X
  → SemanticAction (MaybeLeft A) (M.Maybe (X × List Alphabet))
parser-output a m (Sum.inl (ms , e , (x , rest , tt*))) =
  M.just (a (ms zero) x .fst , semact-String* (ms (suc zero)) rest .fst) , tt
parser-output a m (Sum.inr _) = M.nothing , tt

-- The executable boundary used by compiler drivers and regression suites.
parse : {A : TheoryTy ℓA tt} {X : Type ℓB}
  → Parser A → SemanticAction A X → List Alphabet → M.Maybe (X × List Alphabet)
parse p a cs = parser-output a cs (p cs (read cs tt)) .fst

complete : {X : Type ℓA} → M.Maybe (X × List Alphabet) → M.Maybe X
complete M.nothing = M.nothing
complete (M.just (x , [])) = M.just x
complete (M.just (x , _ ∷ _)) = M.nothing

-- The internal parser-to-next-stage hand-off.  Its action receives the
-- parsed AST directly, before any external reification; requiring an empty
-- suffix makes it a complete-program parser.
parse-complete : {A : TheoryTy ℓA tt} {X : Type ℓB}
  → Parser A → SemanticAction A X → SemanticAction String* (M.Maybe X)
parse-complete p a = semact-map complete (semact-map-g p (parser-output a))

-- Guarded recursive descent.  A recursive parser is not an Agda recursive
-- definition: `body` receives it only under the well-founded later modality
-- induced by free-monoid length.  A client may apply that value only after
-- proving its input is a strict suffix.
module GuardedParser where
  private
    isSetChar : isSetTheoryTy char
    isSetChar = isSet⊕ᴰ isSetAlphabet λ _ m →
      isProp→isSet (isSet→isSetEq (M .fst tt .snd))

    isSetKleene : isSetValued KleeneCode
    isSetKleene .fst = lift isSetBool
    isSetKleene .snd false = λ ()
    isSetKleene .snd true zero = lift isSetChar
    isSetKleene .snd true (suc zero) = lift tt*

    isSetString* : isSetTheoryTy String*
    isSetString* = isSetμ (λ _ → KleeneCode) (λ _ → isSetKleene) tt

  module _ {A : TheoryTy ℓA tt} (isSetA : isSetTheoryTy A) where
    private
      isSetResult : isSetTheoryTy (MaybeLeft A)
      isSetResult = isSetMaybe (isSet⊗ _ (two _ _) (A , String* , tt*)
        λ where zero → isSetA ; (suc zero) → isSetString*)

      module R▷ = Guarded▷ (λ _ → MaybeLeft A) (λ _ → isSetResult)

    fixP : (R▷.▷ tt ⊢ MaybeLeft A) → Parser A
    fixP body = R▷.löb (λ _ → body) tt ∘⊢ ⊤Ty-intro
