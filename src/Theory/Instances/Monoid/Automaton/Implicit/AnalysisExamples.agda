{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- POSIX source text to a deterministic automaton, end to end.

   `reOf` elaborates the string to an `RE`, `detOf` runs the first/follow
   analysis on it, and `compileDA` turns the resulting `DetReg` into a
   deterministic automaton -- so the only thing written below is a pattern
   and a word, and the trace is computed.

   `POSIX` is the entry point: it lives here rather than in `Analysis`
   because `Regex.Parse` fixes the alphabet at `UChar` while the analysis
   is alphabet-generic.

   The last section is the other half of the claim: `detOf` says `nothing`
   exactly where the fragment is not a `DetReg`, and each rejection below
   is a different reason. -}
open import Cubical.Foundations.Prelude

module Theory.Instances.Monoid.Automaton.Implicit.AnalysisExamples where

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
open import Theory.Instances.Monoid.Automaton.Deterministic UChar isSetAlphabet
open import Theory.Instances.Monoid.Automaton.Implicit.Analysis
  UChar _≟U_ (ℓ-suc ℓ-zero)

-- The entry point.  `p` says the pattern parses, `q` says the analysis
-- accepted it; both are `Unit` and solved by eta on a literal, so a bad
-- pattern is a type error at the module application.

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

  accepts : String → Bool
  accepts w = parseInit isSetQ w (readChars w tt) .fst

  traceOf : (w : String) → Trace (accepts w) init w
  traceOf w = parseInit isSetQ w (readChars w tt) .snd

-- `ab*`.  `Regex.Parse` builds this as `εr ⊗r ⟨a⟩r ⊗r ⟨b⟩r *r`, and the
-- unit clauses of `detOf` are what let `⊗DR`, which refuses a nullable
-- left factor, apply at all -- which is exactly what `erase` reports.

module M1 = POSIX "ab*"

_ : erase (M1.D .snd .dr) ≡ ⟨ ch 'a' ⟩r ⊗r ⟨ ch 'b' ⟩r *r
_ = refl

-- one position per literal, and nothing merged
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

-- `a(b|c)*`, which exercises the other two nodes: `⊕DR` on two
-- non-nullable branches with disjoint first sets, and `*DR` whose loop
-- re-entry is decided against `{b, c}`.

module M2 = POSIX "a(b|c)*"

_ : M2.Trace true M2.init (text "a")
_ = M2.traceOf _

_ : M2.Trace true M2.init (text "abcbcc")
_ = M2.traceOf _

_ : M2.Trace false M2.init (text "abcd")
_ = M2.traceOf _

_ : M2.Trace false M2.init (text "bc")
_ = M2.traceOf _

-- Character classes.  `satdr`'s follow-last set is empty, so a class
-- sequences and stars on the trivial side condition -- an identifier is
-- deterministic and nothing about it is enumerated.

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

-- ...and a letter against a class, which *is* decidable: one application
-- of the predicate at that letter
module M5 = POSIX "(a|[0-9])*"

_ : M5.Trace true M5.init (text "a1a22")
_ = M5.traceOf _

_ : M5.Trace false M5.init (text "a1b")
_ = M5.traceOf _

-- ...and at length, to check that the side conditions did not put
-- anything expensive on the transition path.  Each step evaluates one
-- support of size at most two.

bs : ℕ → String
bs zero = []
bs (suc n) = ch 'b' ∷ bs n

_ : M1.Trace true M1.init (ch 'a' ∷ bs 100)
_ = M1.traceOf _

_ : M1.Trace false M1.init ((ch 'a' ∷ bs 100) ++ (ch 'a' ∷ []))
_ = M1.traceOf _

-- What `detOf` refuses.  `IsDet m` is `⊥` exactly when `m` is `nothing`,
-- so `λ x → x` typechecks only if the analysis rejected the pattern.

private
  Rejects : (s : AS.String) {p : IsJust (parseRE s)} → Type ℓ-zero
  Rejects s {p} = IsDet (detOfPOSIX s {p}) → Empty.⊥

-- first/first clash: both branches begin with `a`, so `⊕DR`'s `sep`
-- cannot be built
_ : Rejects "ab|ac"
_ = λ x → x

-- follow-last/first clash: `b` both continues the star and starts the
-- next factor, so `⊗DR`'s `seq-unambig` cannot be built
_ : Rejects "ab*b"
_ = λ x → x

-- `a|a` -- the same clash, at its smallest
_ : Rejects "a|a"
_ = λ x → x

-- not a determinism failure but a `DetReg` one: `⊗DR` demands a
-- non-nullable left factor, so a leading star is out even though the
-- language is deterministic
_ : Rejects "a*b*"
_ = λ x → x

-- both branches nullable, which `⊕DR`'s `notBothNull` forbids
_ : Rejects "a?|b?"
_ = λ x → x

-- class against class: `⊕DR`'s `sep` would need `[a-z]` and `[0-9]`
-- pointwise disjoint, and neither predicate is enumerable -- so this is
-- refused although the language is deterministic
_ : Rejects "[a-z]|[0-9]"
_ = λ x → x

_ : Rejects "\\d|\\w"
_ = λ x → x
