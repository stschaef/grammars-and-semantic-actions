{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
-- Greedy matching, run.  `extendAt` makes a length-n match O(n), not the
-- O(n²) of `Greedy`'s `⊕[ w ] ⌈ w ⌉`.  The scan that finds the boundary is
-- NOT here (both examples place it by hand); `Regex/Derivative.agda` states it.
open import Cubical.Foundations.Prelude
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Examples.Theory.Greedy.Examples where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.FinData using () renaming (zero to fz ; suc to fs)
import Cubical.Data.List.Properties as LP
import Agda.Builtin.String as AS

open import Cubical.Data.Unicode
open import Theory.Instances.Monoid.Regex.Parse
open import Theory.Instances.Monoid.Greedy.Base UChar isSetUChar
open import Theory.Instances.Monoid.Derivative UChar isSetUChar using (Dl)
open import Theory.Instances.Monoid.Residual UChar isSetUChar using (_⊸_)
open import Theory.Instances.Monoid.Lex.Regex UChar _≟U_ (ℓ-suc ℓ-zero)
  using (yield)

private
  ℓr : Level
  ℓr = ℓ-suc ℓ-zero

  a : UChar
  a = ch 'a'

-- 1. `a+` against "aaab": match "aaa", and "b" refutes any extension.

aPlus : RE notNullable
aPlus = reOf "a+"

aStar : RE nullable
aStar = reOf "a*"

Rest : TheoryTy ℓr tt
Rest = ty ⟦ aStar ⟧

match : ty ⟦ aPlus ⟧ (text "aaa")
match = theYes (decide-r aPlus ℓr (text "aaa") tt) Eq.refl

-- `noExt-step` reduces "no nonempty extension" to "no derivative after
-- this letter".
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

_ : untext (greedily .fst fz) ≡ "aaa"
_ = refl

_ : untext (greedily .fst (fs fz)) ≡ "b"
_ = refl

_ : untext (yield aPlus (text "aaa") (greedily .snd .snd .fst) .fst) ≡ "aaa"
_ = refl

-- 2. Extending a match one character at a time.  `A` is ⊗-shaped on
-- purpose: a `⊤Ty` carries no splitting, the case that once hid a stuck
-- `transp` here.

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

  seed : (n : ℕ) → Dln (suc n) A₀ [] → GreedyAt (Dln (suc n) A₀) Rest (text "b")
  seed n x = two [] (text "b") , Eq.refl , (x , (noLonger , tt*))

  at200 : Dln 200 A₀ []
  at200 = two (a ∷ []) (reps 199) , Eq.refl , (Eq.refl , (tt , tt*))

  built : Σ String (GreedyAt A₀ Rest)
  built = go 200 (seed 199 at200)

-- after 200 extensions the transported witness still projects
_ : untext (built .snd .snd .snd .fst .fst fz) ≡ "a"
_ = refl

_ : built .fst ≡ reps 200 ++ text "b"
_ = refl
