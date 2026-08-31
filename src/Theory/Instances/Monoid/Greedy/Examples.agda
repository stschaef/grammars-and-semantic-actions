{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Greedy matching, run.

   A `GreedyAt A R` over `w` is two things at once: a parse of `A` over
   some prefix of `w`, and a refutation that anything longer matches --
   where "longer" is `R`, what is left of `A` after the prefix.  §1 builds
   one for a real regex and reads both halves back out.

   §2 is `extendAt`, the reason the residual index is there at all: one
   more character costs an associativity and one substitution, so a match
   of length n costs O(n) rather than the O(n²) that `Greedy`'s
   `⊕[ w ] ⌈ w ⌉` forces.

   What is *not* here is the scan -- the fold over the input that finds
   the match boundary instead of being told it.  Both examples below
   place the boundary by hand.  `Regex/Derivative.agda` states the scan
   and its four ingredients, all of which now exist. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Greedy.Examples where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.FinData using () renaming (zero to fz ; suc to fs)
import Cubical.Data.List.Properties as LP
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Unicode.Base
open import Theory.Instances.Monoid.Regex.Parse
open import Theory.Instances.Monoid.Greedy.Base UChar isSetAlphabet
open import Theory.Instances.Monoid.Derivative UChar isSetAlphabet using (Dl)
open import Theory.Instances.Monoid.Residual UChar isSetAlphabet using (_⊸_)
open import Theory.Instances.Monoid.Lex.Regex UChar _≟U_ (ℓ-suc ℓ-zero)
  using (yield)

private
  ℓr : Level
  ℓr = ℓ-suc ℓ-zero

  a : UChar
  a = ch 'a'

-- 1. A greedy match: `a+` against "aaab".
--
-- The match is "aaa" and the rest is "b".  It is greedy because of the
-- second component: after "aaa" the regex could still continue as `a*`,
-- and "b" refutes every nonempty way of doing so.

aPlus : RE notNullable
aPlus = reOf "a+"

-- what is left of `a+` once it has matched: the residual
aStar : RE nullable
aStar = reOf "a*"

Rest : TheoryTy ℓr tt
Rest = ty ⟦ aStar ⟧

-- the match itself, decided rather than asserted
match : ty ⟦ aPlus ⟧ (text "aaa")
match = theYes (decide-r aPlus ℓr (text "aaa") tt) Eq.refl

-- ...and the refutation: "b" starts no continuation.  `noExt-step`
-- reduces "no nonempty extension" to "no derivative after this letter",
-- which is where the precision of `literal` does the work.
private
  noRest : Rest (text "b") → Empty.⊥
  noRest r = theNo (decide-r aStar ℓr (text "b") tt) Eq.refl r .lower

  nilL : (u v : String) → u ++ v ≡ [] → u ≡ []
  nilL [] v p = refl
  nilL (x ∷ u) v p = Empty.rec (LP.¬cons≡nil p)

  noDeriv : ¬Ty ((literal (ch 'b') ⊸ Rest) ⊗ ⊤Ty) []
  noDeriv (ms , e , (f , _)) = Empty.rec (noRest
    (subst (λ u → Rest (text "b" ++ u))
           (nilL (ms fz) (ms (fs fz)) (Eq.eqToPath e))
           (f (text "b") Eq.refl)))

noLonger : ¬Ty ((Rest & char⁺) ⊗ ⊤Ty) (text "b")
noLonger = noExt-step (ch 'b') (text "b")
  (two (text "b") [] , Eq.refl , (Eq.refl , (noDeriv , tt*)))

greedily : GreedyAt (ty ⟦ aPlus ⟧) Rest (text "aaab")
greedily = two (text "aaa") (text "b") , Eq.refl , (match , (noLonger , tt*))

-- ...and what it matched, read back out
_ : untext (greedily .fst fz) ≡ "aaa"
_ = refl

_ : untext (greedily .fst (fs fz)) ≡ "b"
_ = refl

-- the parse tree agrees with the splitting
_ : untext (yield aPlus (text "aaa") (greedily .snd .snd .fst) .fst) ≡ "aaa"
_ = refl

-- 2. Extending a match, one character at a time.
--
-- `extendAt` moves a letter out of the input and into the match.  `A` is
-- ⊗-shaped on purpose: its witness carries a splitting, and it is that
-- splitting the substitution inside `lit⊗Dl` has to carry.  With a
-- `⊤Ty` there is nothing to carry and the step is trivially cheap,
-- which is exactly the case that hid a stuck `transp` here once.

private
  A₀ : TheoryTy ℓM tt
  A₀ = literal a ⊗ ⊤Ty

  Dln : ∀ {ℓ} → ℕ → TheoryTy ℓ tt → TheoryTy ℓ tt
  Dln zero A = A
  Dln (suc n) A = Dl a (Dln n A)

  reps : ℕ → String
  reps zero = []
  reps (suc n) = a ∷ reps n

  -- n applications of `extendAt`, each O(1)
  go : (dep : ℕ) {A : TheoryTy ℓM tt} {w : String}
     → GreedyAt (Dln dep A) Rest w → Σ String (GreedyAt A Rest)
  go zero {w = w} g = w , g
  go (suc dep) {w = w} g =
    go dep (extendAt a (a ∷ w) (two (a ∷ []) w , Eq.refl , (Eq.refl , (g , tt*))))

  -- the far end of the chain: the match sits at aⁿ, the rest is "b"
  seed : (n : ℕ) → Dln (suc n) A₀ [] → GreedyAt (Dln (suc n) A₀) Rest (text "b")
  seed n x = two [] (text "b") , Eq.refl , (x , (noLonger , tt*))

  at200 : Dln 200 A₀ []
  at200 = two (a ∷ []) (reps 199) , Eq.refl , (Eq.refl , (tt , tt*))

  built : Σ String (GreedyAt A₀ Rest)
  built = go 200 (seed 199 at200)

-- 200 characters into the match, and the transported witness still
-- projects: the inner splitting is the leading `a`, and the refutation
-- has been carried through untouched.
_ : untext (built .snd .snd .snd .fst .fst fz) ≡ "a"
_ = refl

_ : built .fst ≡ reps 200 ++ text "b"
_ = refl
