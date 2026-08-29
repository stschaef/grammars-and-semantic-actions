{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- First-order terms, the occurs check, and the judgment `Sol`.

   Everything here is ordinary Agda: this file knows nothing about the
   framework.  It is the analogue of `Annotated/Base`'s `ATm` together with
   `Linear`'s `keep`/`freeIn` -- the external recursive functions a rule's
   index is computed by.

   Two decisions shape the whole development.

   The scope is an *index*, as in McBride: `Tm n` has `n` unknowns and
   solving one lands in `Tm n'` with `n = suc n'`.  So "the substitution
   eliminates a variable" is a typing fact rather than a theorem about
   variable sets, and the guard gets its first component for free.

   The problem is a *stack*, not a tree.  McBride's `go (fork s₁ t₁)
   (fork s₂ t₂)` unifies `s₁ ≟ s₂`, then unifies `t₁ ≟ t₂` *under the
   substitution the first call returned*; that is a premise whose index is
   the previous premise's answer, and no combinator provides it.  A stack
   of equations removes the dependency: decomposition pushes the two
   subproblems and the substitution is threaded through the whole stack,
   one step at a time, exactly as `Linear` threads a context.  This is
   Martelli--Montanari's presentation of the same algorithm and it is the
   one that fits.

   `flatA` is what makes the type-level recursion structural.  Congruence
   -- "`fork s₁ t₁ ≟ fork s₂ t₂` is `s₁ ≟ s₂` and `t₁ ≟ t₂`" -- grows the
   stack, so a definition of `Sol` that decomposed in place would not be
   accepted.  `flatA` does the whole congruence closure of *one* equation
   in a separate pass, by structural recursion on its first term, and hands
   back a list of variable-headed equations.  `Sol` then descends
   lexicographically on `(scope, stack)`, and both components are
   structural. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
module Theory.Instances.Unify.Term where

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.Properties using (discreteFin ; isSetFin)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit ; isSetUnit)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no ; Discrete)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

private variable k n m : ℕ

-- Terms over `n` unknowns.
data Tm (n : ℕ) : Type ℓ-zero where
  var : Fin n → Tm n
  leaf : Tm n
  fork : Tm n → Tm n → Tm n

-- No confusion, by a code.  This is the only h-level work in the file:
-- `Tm n` is discrete, so everything built from it is a set.
private
  Code : Tm n → Tm n → Type ℓ-zero
  Code (var x) (var y) = x ≡ y
  Code leaf leaf = Unit
  Code (fork a b) (fork c d) = Code a c × Code b d
  Code (var _) leaf = Empty.⊥
  Code (var _) (fork _ _) = Empty.⊥
  Code leaf (var _) = Empty.⊥
  Code leaf (fork _ _) = Empty.⊥
  Code (fork _ _) (var _) = Empty.⊥
  Code (fork _ _) leaf = Empty.⊥

  reflCode : (t : Tm n) → Code t t
  reflCode (var x) = refl
  reflCode leaf = tt
  reflCode (fork a b) = reflCode a , reflCode b

  encode : {t u : Tm n} → t ≡ u → Code t u
  encode {t = t} e = subst (Code t) e (reflCode t)

  decode : (t u : Tm n) → Code t u → t ≡ u
  decode (var x) (var y) c = cong var c
  decode leaf leaf _ = refl
  decode (fork a b) (fork c d) (p , q) =
    cong₂ fork (decode a c p) (decode b d q)

  decCode : (t u : Tm n) → Dec (Code t u)
  decCode (var x) (var y) = discreteFin x y
  decCode (var _) leaf = no λ ()
  decCode (var _) (fork _ _) = no λ ()
  decCode leaf (var _) = no λ ()
  decCode leaf leaf = yes tt
  decCode leaf (fork _ _) = no λ ()
  decCode (fork _ _) (var _) = no λ ()
  decCode (fork _ _) leaf = no λ ()
  decCode (fork a b) (fork c d) = onParts (decCode a c) (decCode b d)
    where
    onParts : Dec (Code a c) → Dec (Code b d) → Dec (Code (fork a b) (fork c d))
    onParts (yes p) (yes q) = yes (p , q)
    onParts (no ¬p) _ = no λ z → ¬p (z .fst)
    onParts _ (no ¬q) = no λ z → ¬q (z .snd)

discreteTm : Discrete (Tm n)
discreteTm t u = onCode (decCode t u)
  where
  onCode : Dec (Code t u) → Dec (t ≡ u)
  onCode (yes c) = yes (decode t u c)
  onCode (no ¬c) = no λ e → ¬c (encode e)

isSetTm : isSet (Tm n)
isSetTm = Discrete→isSet discreteTm

-- McBride's thinning and its partial inverse.  `thick x y` is `y` seen
-- from a world without `x`, and `nothing` exactly when `y` is `x`.
thin : Fin (suc n) → Fin n → Fin (suc n)
thin zero y = suc y
thin (suc x) zero = zero
thin (suc x) (suc y) = suc (thin x y)

thick : Fin (suc n) → Fin (suc n) → Maybe (Fin n)
thick zero zero = nothing
thick zero (suc y) = just y
thick {suc _} (suc x) zero = just zero
thick {suc _} (suc x) (suc y) = onRec (thick x y)
  where
  onRec : Maybe (Fin _) → Maybe (Fin (suc _))
  onRec nothing = nothing
  onRec (just y') = just (suc y')

-- The occurs check: `check x t` is `t` in a world without `x`, and fails
-- exactly when `x` occurs in `t`.
check : Fin (suc n) → Tm (suc n) → Maybe (Tm n)
check x (var y) = onVar (thick x y)
  where
  onVar : Maybe (Fin _) → Maybe (Tm _)
  onVar nothing = nothing
  onVar (just y') = just (var y')
check x leaf = just leaf
check x (fork s t) = onBoth (check x s) (check x t)
  where
  onBoth : Maybe (Tm _) → Maybe (Tm _) → Maybe (Tm _)
  onBoth (just s') (just t') = just (fork s' t')
  onBoth _ _ = nothing

bind : (Fin n → Tm m) → Tm n → Tm m
bind f (var y) = f y
bind f leaf = leaf
bind f (fork s t) = fork (bind f s) (bind f t)

for : Fin (suc n) → Tm n → Fin (suc n) → Tm n
for x w y = onThick (thick x y)
  where
  onThick : Maybe (Fin _) → Tm _
  onThick nothing = w
  onThick (just y') = var y'

subst1 : Fin (suc n) → Tm n → Tm (suc n) → Tm n
subst1 x w = bind (for x w)


-- Problems, stacks of them, and the variable-headed equations a stack
-- decomposes to.
Prob : ℕ → Type ℓ-zero
Prob n = Tm n × Tm n

Stack : ℕ → Type ℓ-zero
Stack n = List (Prob n)

Flex : ℕ → Type ℓ-zero
Flex n = Fin n × Tm n

FStack : ℕ → Type ℓ-zero
FStack n = List (Flex n)

isSetProb : isSet (Prob n)
isSetProb = isSetΣ isSetTm λ _ → isSetTm

isSetStack : isSet (Stack n)
isSetStack = isOfHLevelList 0 isSetProb

discreteProb : Discrete (Prob n)
discreteProb (t , u) (t' , u') = onParts (discreteTm t t') (discreteTm u u')
  where
  onParts : Dec (t ≡ t') → Dec (u ≡ u') → Dec ((t , u) ≡ (t' , u'))
  onParts (yes p) (yes q) = yes (ΣPathP (p , q))
  onParts (no ¬p) _ = no λ e → ¬p (cong fst e)
  onParts _ (no ¬q) = no λ e → ¬q (cong snd e)

unflex : Flex n → Prob n
unflex (x , u) = var x , u

applyProb : Fin (suc n) → Tm n → Prob (suc n) → Prob n
applyProb x w (t , u) = subst1 x w t , subst1 x w u

applyStack : Fin (suc n) → Tm n → Stack (suc n) → Stack n
applyStack x w [] = []
applyStack x w (p ∷ ps) = applyProb x w p ∷ applyStack x w ps

unflexAll : FStack n → Stack n
unflexAll [] = []
unflexAll (e ∷ qs) = unflex e ∷ unflexAll qs


-- Congruence closure of one equation, with an accumulator.  Structural in
-- the first term, which is the whole point: the fork clause recurses on
-- `s₁` and on `t₁`, never on a stack that has grown.
pushF : Flex n → Maybe (FStack n) → Maybe (FStack n)
pushF e nothing = nothing
pushF e (just qs) = just (e ∷ qs)

flatA : Tm n → Tm n → Maybe (FStack n) → Maybe (FStack n)
flatA (var x) (var y) acc = onSame (discreteFin x y)
  where
  onSame : Dec (x ≡ y) → Maybe (FStack _)
  onSame (yes _) = acc
  onSame (no _) = pushF (x , var y) acc
flatA (var x) leaf acc = pushF (x , leaf) acc
flatA (var x) (fork a b) acc = pushF (x , fork a b) acc
flatA leaf (var y) acc = pushF (y , leaf) acc
flatA (fork a b) (var y) acc = pushF (y , fork a b) acc
flatA leaf leaf acc = acc
flatA leaf (fork _ _) acc = nothing
flatA (fork _ _) leaf acc = nothing
flatA (fork s₁ t₁) (fork s₂ t₂) acc = flatA s₁ s₂ (flatA t₁ t₂ acc)

flat1 : Prob n → Maybe (FStack n)
flat1 (t , u) = flatA t u (just [])


-- The judgment.  `Sol n ps` says the stack `ps` of equations over `n`
-- unknowns has a most general unifier -- equivalently, that the machine
-- below runs to completion.
--
-- Read as a machine: `flat1` decomposes the head equation; failure is a
-- clash, no equations left means the head was trivial and the tail is all
-- that remains, and a variable-headed equation `x ≟ u` is solved by the
-- occurs check and then applied to everything that is left.  The scope
-- drops by one at exactly that step, which is why the recursion is
-- structural on `(n , ps)`.
--
-- It is a *proposition*: the machine is deterministic, so there is nothing
-- to choose and `Sol` carries no data.  Uniqueness of the most general
-- unifier is that determinism, and here it is definitional.  What the
-- derivation does not carry, `mgu` below recomputes -- by the same
-- recursion, from the same `check`.
Sol : (n : ℕ) → Stack n → Type ℓ-zero
onFlat : (n : ℕ) → Maybe (FStack n) → Stack n → Type ℓ-zero
flexAt : (n : ℕ) → Fin n → Tm n → FStack n → Stack n → Type ℓ-zero
onCheck : (n : ℕ) → Fin (suc n) → Tm (suc n) → FStack (suc n) → Stack (suc n)
        → Maybe (Tm n) → Type ℓ-zero

Sol n [] = Unit
Sol n (p ∷ ps) = onFlat n (flat1 p) ps

onFlat n nothing ps = Empty.⊥
onFlat n (just []) ps = Sol n ps
onFlat n (just (e ∷ qs)) ps = flexAt n (e .fst) (e .snd) qs ps

flexAt (suc n) x u qs ps = onCheck n x u qs ps (check x u)

onCheck n x u qs ps nothing = Empty.⊥
onCheck n x u qs ps (just w) =
  Sol n (applyStack x w (unflexAll qs ++ ps))

isPropSol : (n : ℕ) (ps : Stack n) → isProp (Sol n ps)
isPropOnFlat : (n : ℕ) (fl : Maybe (FStack n)) (ps : Stack n)
             → isProp (onFlat n fl ps)
isPropFlexAt : (n : ℕ) (x : Fin n) (u : Tm n) (qs : FStack n) (ps : Stack n)
             → isProp (flexAt n x u qs ps)
isPropOnCheck : (n : ℕ) (x : Fin (suc n)) (u : Tm (suc n))
  (qs : FStack (suc n)) (ps : Stack (suc n)) (c : Maybe (Tm n))
  → isProp (onCheck n x u qs ps c)

isPropSol n [] = isPropUnit
isPropSol n (p ∷ ps) = isPropOnFlat n (flat1 p) ps

isPropOnFlat n nothing ps = λ ()
isPropOnFlat n (just []) ps = isPropSol n ps
isPropOnFlat n (just (e ∷ qs)) ps = isPropFlexAt n (e .fst) (e .snd) qs ps

isPropFlexAt (suc n) x u qs ps = isPropOnCheck n x u qs ps (check x u)

isPropOnCheck n x u qs ps nothing = λ ()
isPropOnCheck n x u qs ps (just w) =
  isPropSol n (applyStack x w (unflexAll qs ++ ps))

isSetSol : (n : ℕ) (ps : Stack n) → isSet (Sol n ps)
isSetSol n ps = isProp→isSet (isPropSol n ps)


-- The measure: the second component of the guard's order.  Only the head
-- equation's contribution matters -- every rule but the flexible one
-- leaves the scope alone and shortens the stack by a head.
tmSize : Tm n → ℕ
tmSize (var _) = 1
tmSize leaf = 1
tmSize (fork s t) = suc (tmSize s + tmSize t)

stackSize : Stack n → ℕ
stackSize [] = 0
stackSize (p ∷ ps) = suc (stackSize ps)

tail< : (p : Prob n) (ps : Stack n) → stackSize ps NO.< stackSize (p ∷ ps)
tail< p ps = 0 , refl


-- The answer, when there is one: a triangular substitution, as in the
-- source -- a chain of `k` assignments taking `n` unknowns down to `m`.
Steps : ℕ → ℕ → ℕ → Type ℓ-zero
Steps zero n m = n Eq.≡ m
Steps (suc k) zero m = Empty.⊥
Steps (suc k) (suc n) m = Fin (suc n) × Tm n × Steps k n m

AList : ℕ → Type ℓ-zero
AList n = Σ[ m ∈ ℕ ] Σ[ k ∈ ℕ ] Steps k n m

-- ...and the readout, by the recursion `Sol` was defined by.  The
-- derivation says only that the machine finished; the assignment at each
-- step is `check`'s answer, recomputed here exactly as `Elaborate`'s
-- `deBruijn` recomputes nothing and reads instead.
mgu : (n : ℕ) (ps : Stack n) → Sol n ps → AList n
mguFlat : (n : ℕ) (fl : Maybe (FStack n)) (ps : Stack n)
        → onFlat n fl ps → AList n
mguFlexAt : (n : ℕ) (x : Fin n) (u : Tm n) (qs : FStack n) (ps : Stack n)
          → flexAt n x u qs ps → AList n
mguCheck : (n : ℕ) (x : Fin (suc n)) (u : Tm (suc n)) (qs : FStack (suc n))
  (ps : Stack (suc n)) (c : Maybe (Tm n)) → onCheck n x u qs ps c
  → AList (suc n)

mgu n [] _ = n , 0 , Eq.refl
mgu n (p ∷ ps) d = mguFlat n (flat1 p) ps d

mguFlat n (just []) ps d = mgu n ps d
mguFlat n (just (e ∷ qs)) ps d = mguFlexAt n (e .fst) (e .snd) qs ps d

mguFlexAt (suc n) x u qs ps d = mguCheck n x u qs ps (check x u) d

mguCheck n x u qs ps (just w) d =
  onRest (mgu n (applyStack x w (unflexAll qs ++ ps)) d)
  where
  onRest : AList n → AList (suc n)
  onRest (m , k , τ) = m , suc k , x , w , τ

-- Applying a chain, for the tests: a most general unifier is only worth
-- the name if it makes the two sides equal.
applySteps : {k n m : ℕ} → Steps k n m → Tm n → Tm m
applySteps {k = zero} Eq.refl t = t
applySteps {k = suc k} {n = suc n} (x , w , τ) t = applySteps τ (subst1 x w t)
