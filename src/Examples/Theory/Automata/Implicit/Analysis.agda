{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- POSIX pattern to deterministic automaton, end to end; the last section
   records what `detOf` rejects and why. -}
open import Cubical.Foundations.Prelude

module Examples.Theory.Automata.Implicit.Analysis where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit* ; tt ; tt*)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Maybe as Mb
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Regex.Parse
open import Theory.Instances.Monoid.Automaton.Deterministic UChar isSetUChar
open import Theory.Instances.Monoid.Automaton.Implicit.Analysis
  UChar _≟U_ (ℓ-suc ℓ-zero)

-- `p`/`q` are solved by eta on a literal: a bad pattern is a type error.

detOfPOSIX : (s : AS.String) {p : IsJust (parseRE s)} → Mb.Maybe DetOf
detOfPOSIX s {p} = detOf (reOf s {p})

module POSIX (s : AS.String)
  {p : IsJust (parseRE s)} {q : IsDet (detOfPOSIX s {p})} where

  D : DetOf
  D = theDet (detOfPOSIX s {p}) q

  Q : Type ℓ-zero
  Q = FreelyAddFail+Initial (States (D .snd .dr))

  DA : DeterministicAutomaton Q
  DA = compileDA discAlphabet (D .snd .dr)

  open DeterministicAutomaton DA public using (Trace ; init ; parseInit)

  isSetQ : isSet Q
  isSetQ = isSetCompileStates discAlphabet (D .snd .dr)

  Dead : Deadness DA
  Dead = compileDead discAlphabet (D .snd .dr)

  accepts : String → Bool
  accepts w = parseInit isSetQ w (readChars w tt) .fst

  traceOf : (w : String) → Trace (accepts w) init w
  traceOf w = parseInit isSetQ w (readChars w tt) .snd

-- `ab*`: the unit clauses of `detOf` let `⊗DR` (non-nullable left factor) apply.

module M1 = POSIX "ab*"

_ : erase (M1.D .snd .dr) ≡ ⟨ ch 'a' ⟩r ⊗r ⟨ ch 'b' ⟩r *r
_ = refl

_ : States (M1.D .snd .dr) ≡ (Unit* Sum.⊎ Unit*)
_ = refl

_ : M1.Trace true M1.init (text "a")
_ = M1.traceOf _

_ : M1.Trace true M1.init (text "abbb")
_ = M1.traceOf _

_ : M1.Trace false M1.init (text "")
_ = M1.traceOf _

_ : M1.Trace false M1.init (text "b")
_ = M1.traceOf _

_ : M1.Trace false M1.init (text "aab")
_ = M1.traceOf _

_ : M1.Trace false M1.init (text "abba")
_ = M1.traceOf _

-- `a(b|c)*`: exercises `⊕DR` (disjoint first sets) and `*DR` re-entry.

module M2 = POSIX "a(b|c)*"

_ : M2.Trace true M2.init (text "a")
_ = M2.traceOf _

_ : M2.Trace true M2.init (text "abcbcc")
_ = M2.traceOf _

_ : M2.Trace false M2.init (text "abcd")
_ = M2.traceOf _

_ : M2.Trace false M2.init (text "bc")
_ = M2.traceOf _

-- Classes: `satdr` has empty follow-last, so nothing is enumerated.

module M3 = POSIX "[a-z][a-z0-9]*"

_ : M3.Trace true M3.init (text "x")
_ = M3.traceOf _

_ : M3.Trace true M3.init (text "foo42")
_ = M3.traceOf _

_ : M3.Trace false M3.init (text "")
_ = M3.traceOf _

_ : M3.Trace false M3.init (text "4x")
_ = M3.traceOf _

_ : M3.Trace false M3.init (text "ab-c")
_ = M3.traceOf _

-- `\d+`, i.e. `satr isDigit ⊗r satr isDigit *r`
module M4 = POSIX "\\d+"

_ : M4.Trace true M4.init (text "2026")
_ = M4.traceOf _

_ : M4.Trace false M4.init (text "")
_ = M4.traceOf _

_ : M4.Trace false M4.init (text "20a")
_ = M4.traceOf _

-- letter vs class *is* decidable: one predicate application
module M5 = POSIX "(a|[0-9])*"

_ : M5.Trace true M5.init (text "a1a22")
_ = M5.traceOf _

_ : M5.Trace false M5.init (text "a1b")
_ = M5.traceOf _

-- at length 100: each step evaluates one support of size at most two

bs : ℕ → String
bs zero = []
bs (suc n) = ch 'b' ∷ bs n

_ : M1.Trace true M1.init (ch 'a' ∷ bs 100)
_ = M1.traceOf _

_ : M1.Trace false M1.init ((ch 'a' ∷ bs 100) ++ (ch 'a' ∷ []))
_ = M1.traceOf _

-- `IsDet m` is `⊥` iff `m` is `nothing`, so `λ x → x` proves rejection.

private
  Rejects : (s : AS.String) {p : IsJust (parseRE s)} → Type ℓ-zero
  Rejects s {p} = IsDet (detOfPOSIX s {p}) → Empty.⊥

-- first/first clash: `⊕DR`'s `sep` cannot be built
_ : Rejects "ab|ac"
_ = λ x → x

-- follow-last/first clash: `⊗DR`'s `seq-unambig` cannot be built
_ : Rejects "ab*b"
_ = λ x → x

-- `a|a` -- the same clash, at its smallest
_ : Rejects "a|a"
_ = λ x → x

-- not a determinism failure: `⊗DR` demands a non-nullable left factor
_ : Rejects "a*b*"
_ = λ x → x

-- both branches nullable, which `⊕DR`'s `notBothNull` forbids
_ : Rejects "a?|b?"
_ = λ x → x

-- class vs class: predicates not enumerable, so refused though deterministic
_ : Rejects "[a-z]|[0-9]"
_ = λ x → x

_ : Rejects "\\d|\\w"
_ = λ x → x
