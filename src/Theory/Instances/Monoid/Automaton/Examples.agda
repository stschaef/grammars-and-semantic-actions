{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A derivative automaton, scanned.

   Two states over {a,b}: "every character so far was an `a`", and dead.
   The language is written by recursion on the word, so every derivative
   square holds *definitionally* -- `Dl a alive m` is `alive (a ∷ m)` is
   `alive m` once `a ≟ a` reduces, and all four transition maps are
   `id⊢`.  That is what the interface is for: an automaton is not a
   transition table with a correctness proof bolted on, it is a family
   whose transition already is the derivative.

   `scan` then gives, for every state at once, either a greedy match
   tagged with the state it ended in or a refutation of every match. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Examples where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Unit using (Unit* ; tt ; tt*)
open import Cubical.Data.FinData using () renaming (zero to fz ; suc to fs)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

data L2 : Type ℓ-zero where
  a b : L2

_≟L2_ : (x y : L2) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
a ≟L2 a = Sum.inl Eq.refl
b ≟L2 b = Sum.inl Eq.refl
a ≟L2 b = Sum.inr λ ()
b ≟L2 a = Sum.inr λ ()

open import Theory.Instances.Monoid.Types L2 _≟L2_
open import Theory.Instances.Monoid.KleeneStar L2 isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Base L2 isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Scan L2 isSetAlphabet
open import Theory.Instances.Monoid.Derivative.General L2 isSetAlphabet
open import Theory.Instances.Monoid.Derivative L2 isSetAlphabet using (Dl)

------------------------------------------------------------------------
-- The two languages, by recursion on the word.

alive : TheoryTy ℓ-zero tt
alive [] = Unit*
alive (c ∷ w) = Sum.rec (λ _ → alive w) (λ _ → Empty.⊥) (c ≟L2 a)

dead : TheoryTy ℓ-zero tt
dead _ = Empty.⊥

Lang : Bool → TheoryTy ℓ-zero tt
Lang true = alive
Lang false = dead

isSetAlive : (m : String) → isSet (alive m)
isSetAlive [] = isProp→isSet (λ _ _ _ → tt*)
isSetAlive (c ∷ w) = go (c ≟L2 a)
  where
  go : (d : (c Eq.≡ a) Sum.⊎ ((c Eq.≡ a) → Empty.⊥))
     → isSet (Sum.rec (λ _ → alive w) (λ _ → Empty.⊥) d)
  go (Sum.inl _) = isSetAlive w
  go (Sum.inr _) = isProp→isSet (λ x → Empty.rec x)

------------------------------------------------------------------------
-- ...and the automaton.  Every square is `id⊢`.

trans : Bool → L2 → Bool
trans true a = true
trans true b = false
trans false _ = false

aStar : DerivAutomaton ℓ-zero ℓ-zero
aStar = record
  { Q = Bool
  ; δ = trans
  ; L = Lang
  ; δ-∂  = λ q c → fwd q c ∘⊢ ∂⌈⌉→Dl (⌈gen c ⌉)
  ; δ-∂⁻ = λ q c → Dl→∂⌈⌉ (⌈gen c ⌉) ∘⊢ bwd q c
  ; isSetQ = isSetBool
  ; isSetL = λ where
      true → isSetAlive
      false → λ m → isProp→isSet λ x → Empty.rec x
  ; acc = λ q → q
  ; accY = λ where true _ m e → Eq.transport alive (e .snd .fst) tt*
  ; accN = λ where false _ m (x , _) → Empty.rec x
  }
  where
  fwd : (q : Bool) (c : L2) → Dl c (Lang q) ⊢ Lang (trans q c)
  fwd true a = id⊢
  fwd true b = id⊢
  fwd false _ = id⊢

  bwd : (q : Bool) (c : L2) → Lang (trans q c) ⊢ Dl c (Lang q)
  bwd true a = id⊢
  bwd true b = id⊢
  bwd false _ = id⊢

------------------------------------------------------------------------
-- Running it.  The input has to be presented as a `char *`; this is the
-- `read` of `Strings`, at the star rather than at `String*`.

readChars : ⊤Ty ⊢ char *
readChars [] _ = NIL _ (lift εTy-pt)
readChars (c ∷ w) _ =
  CONS _ (two (c ∷ []) w , Eq.refl , ((c , Eq.refl) , (readChars w _ , tt*)))

input : String
input = a ∷ a ∷ a ∷ b ∷ []

table : Table aStar input
table = scan aStar input (readChars input tt)

-- the matched prefix, read off the greedy witness from the live state
matched : String
matched = Sum.rec (λ x → x .snd .fst fz) (λ _ → []) (table true)

_ : matched ≡ a ∷ a ∷ a ∷ []
_ = refl

-- ...and the dead state matches nothing, which is the `inr` branch
deadIsNo : Bool
deadIsNo = Sum.rec (λ _ → false) (λ _ → true) (table false)

_ : deadIsNo ≡ true
_ = refl
