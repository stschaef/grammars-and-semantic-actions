{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A deterministic regular expression, compiled and run.

   `a b*` over {a,b}, built by the constructions of `Implicit/RegExp`:
   `⊗Aut (litAut a) (*Aut (litAut b) …)`.  Its states are the two
   positions of the expression, so no determinisation happens anywhere;
   the side conditions the constructions demand are discharged by `refl`
   because `litAut`'s follow set is empty.

   `parse` then reads the whole state table in one pass, and
   `⊕[ b ] Trace b init` is total: an accepting run is `Trace true`, a
   rejecting run is `Trace false`, and reading the tag off says which. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Automaton.Implicit.RegExpExamples where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (Unit* ; tt ; tt*)
open import Cubical.Relation.Nullary.Base using (Discrete ; yes ; no)
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

discL2 : Discrete L2
discL2 a a = yes refl
discL2 b b = yes refl
discL2 a b = no λ p → Empty.rec (subst (λ where a → Unit* ; b → Empty.⊥) p tt*)
discL2 b a = no λ p → Empty.rec (subst (λ where b → Unit* ; a → Empty.⊥) p tt*)

open import Theory.Instances.Monoid.Types L2 _≟L2_
open import Theory.Instances.Monoid.KleeneStar L2 isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Deterministic L2 isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit.RegExp L2 isSetAlphabet

open ImplicitDeterministicAutomaton

private
  -- `litAut c` never steps once it has accepted, so its follow set is
  -- empty and every sequencing condition holds on the left.
  litFollows : {c : L2} (d : L2)
    → ((q : Unit*) → litAut discL2 c .acc q ≡ true
         → fail ≡ litAut discL2 c .δq q d)
      Sum.⊎ (fail ≡ litAut discL2 c .δᵢ d)
  litFollows d = Sum.inl λ _ _ → refl

bStar : ImplicitDeterministicAutomaton (Unit* {ℓ-zero})
bStar = *Aut discL2 (litAut discL2 b) refl litFollows

abStar : ImplicitDeterministicAutomaton (Unit* {ℓ-zero} Sum.⊎ Unit* {ℓ-zero})
abStar = ⊗Aut discL2 (litAut discL2 a) bStar refl litFollows

DA : DeterministicAutomaton _
DA = IDA→DA abStar

DADead : Deadness DA
DADead = failDead abStar

isSetU : isSet (Unit* {ℓ-zero})
isSetU = isProp→isSet λ _ _ → refl

isSetQ : isSet _
isSetQ = isSetFreelyAddFail+Initial _ (Sum.isSet⊎ isSetU isSetU)

open DeterministicAutomaton DA using (parseInit ; Trace ; init)

-- Running it.  `readChars` presents the input as a `char *`.
--
-- `⊕[ b ] Trace b init` is total, so the parse always returns a run;
-- its tag says whether that run accepts.  The tests below exhibit the
-- run itself rather than comparing a `Bool`: `Trace true init w` *is*
-- the accepting parse tree, and `Trace false init w` is the witness
-- that the automaton ran to a non-accepting state.

endsAccepting : String → Bool
endsAccepting w = parseInit isSetQ w (readChars w tt) .fst

traceOf : (w : String) → Trace (endsAccepting w) init w
traceOf w = parseInit isSetQ w (readChars w tt) .snd

_ : Trace true init (a ∷ [])
_ = traceOf _

_ : Trace true init (a ∷ b ∷ b ∷ b ∷ [])
_ = traceOf _

_ : Trace false init []
_ = traceOf _

_ : Trace false init (b ∷ [])
_ = traceOf _

_ : Trace false init (a ∷ a ∷ [])
_ = traceOf _

_ : Trace false init (a ∷ b ∷ a ∷ [])
_ = traceOf _

-- At scale, in both directions: an accepting run of length n and a
-- rejecting one of length n+1, built at typechecking time.  The parse is
-- linear in the input.

bs : ℕ → String
bs zero = []
bs (suc n) = b ∷ bs n

_ : Trace true init (a ∷ bs 800)
_ = traceOf _

_ : Trace false init (a ∷ bs 800 ++ (a ∷ []))
_ = traceOf _
