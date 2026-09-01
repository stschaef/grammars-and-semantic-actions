{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Unification à la McBride (scope as index), problem as a Martelli--Montanari
   stack; a `Sol` derivation carries its assignments, so it IS the triangular
   substitution and `mgu` is a projection. -}
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
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit ; isSetUnit)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no ; Discrete)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

private variable k n m : ℕ

data Tm (n : ℕ) : Type ℓ-zero where
  var : Fin n → Tm n
  leaf : Tm n
  fork : Tm n → Tm n → Tm n

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

-- Maybe-eliminators are named top-level functions so lemmas can `cong` over them.
sucM : Maybe (Fin n) → Maybe (Fin (suc n))
sucM nothing = nothing
sucM (just y) = just (suc y)

varM : Maybe (Fin n) → Maybe (Tm n)
varM nothing = nothing
varM (just y) = just (var y)

forkM : Maybe (Tm n) → Maybe (Tm n) → Maybe (Tm n)
forkM (just s) (just t) = just (fork s t)
forkM nothing _ = nothing
forkM (just _) nothing = nothing

forM : Tm n → Maybe (Fin n) → Tm n
forM w nothing = w
forM w (just y) = var y

-- McBride's thinning; `thick x y` fails exactly when `y` is `x`.
thin : Fin (suc n) → Fin n → Fin (suc n)
thin zero y = suc y
thin (suc x) zero = zero
thin (suc x) (suc y) = suc (thin x y)

thick : Fin (suc n) → Fin (suc n) → Maybe (Fin n)
thick zero zero = nothing
thick zero (suc y) = just y
thick {suc _} (suc x) zero = just zero
thick {suc _} (suc x) (suc y) = sucM (thick x y)

-- Occurs check: fails exactly when `x` occurs in `t`.
check : Fin (suc n) → Tm (suc n) → Maybe (Tm n)
check x (var y) = varM (thick x y)
check x leaf = just leaf
check x (fork s t) = forkM (check x s) (check x t)

bind : (Fin n → Tm m) → Tm n → Tm m
bind f (var y) = f y
bind f leaf = leaf
bind f (fork s t) = fork (bind f s) (bind f t)

for : Fin (suc n) → Tm n → Fin (suc n) → Tm n
for x w y = forM w (thick x y)

subst1 : Fin (suc n) → Tm n → Tm (suc n) → Tm n
subst1 x w = bind (for x w)


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


-- Congruence closure of one equation: structural in the terms, never in a grown stack.
pushF : Flex n → Maybe (FStack n) → Maybe (FStack n)
pushF e nothing = nothing
pushF e (just qs) = just (e ∷ qs)

sameF : (x y : Fin n) → Dec (x ≡ y) → Maybe (FStack n) → Maybe (FStack n)
sameF x y (yes _) acc = acc
sameF x y (no _) acc = pushF (x , var y) acc

flatA : Tm n → Tm n → Maybe (FStack n) → Maybe (FStack n)
flatA (var x) (var y) acc = sameF x y (discreteFin x y) acc
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


-- `Sol n ps`: the stack has an mgu.  The flexible rule CARRIES its assignment
-- `w` (pinned uniquely by `checked`, so still a prop); `mgu` just projects.
Sol : (n : ℕ) → Stack n → Type ℓ-zero
onFlat : (n : ℕ) → Maybe (FStack n) → Stack n → Type ℓ-zero
flexAt : (n : ℕ) → Fin n → Tm n → FStack n → Stack n → Type ℓ-zero
onCheck : (n : ℕ) → Fin (suc n) → Tm (suc n) → FStack (suc n) → Stack (suc n)
        → Maybe (Tm n) → Type ℓ-zero

-- `c ≡ just w` by recursion, so the failing case is `⊥` definitionally.
checked : (n : ℕ) → Maybe (Tm n) → Tm n → Type ℓ-zero
checked n nothing w = Empty.⊥
checked n (just v) w = v ≡ w

Sol n [] = Unit
Sol n (p ∷ ps) = onFlat n (flat1 p) ps

onFlat n nothing ps = Empty.⊥
onFlat n (just []) ps = Sol n ps
onFlat n (just (e ∷ qs)) ps = flexAt n (e .fst) (e .snd) qs ps

flexAt (suc n) x u qs ps = onCheck n x u qs ps (check x u)

onCheck n x u qs ps c = Σ[ w ∈ Tm n ]
  checked n c w × Sol n (applyStack x w (unflexAll qs ++ ps))

pattern assign w c d = w , c , d

isPropChecked : (n : ℕ) (c : Maybe (Tm n)) (w : Tm n) → isProp (checked n c w)
isPropChecked n nothing w = λ ()
isPropChecked n (just v) w = isSetTm v w

checkedInj : (n : ℕ) (c : Maybe (Tm n)) (w w' : Tm n)
           → checked n c w → checked n c w' → w ≡ w'
checkedInj n nothing w w' ()
checkedInj n (just v) w w' e e' = sym e ∙ e'

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

isPropOnCheck n x u qs ps c (assign w e d) (assign w' e' d') =
  ΣPathP (same , ΣPathP
    ( isProp→PathP (λ i → isPropChecked n c (same i)) e e'
    , isProp→PathP
        (λ i → isPropSol n (applyStack x (same i) (unflexAll qs ++ ps))) d d'))
  where
  same : w ≡ w'
  same = checkedInj n c w w' e e'

isSetSol : (n : ℕ) (ps : Stack n) → isSet (Sol n ps)
isSetSol n ps = isProp→isSet (isPropSol n ps)


tmSize : Tm n → ℕ
tmSize (var _) = 1
tmSize leaf = 1
tmSize (fork s t) = suc (tmSize s + tmSize t)

stackSize : Stack n → ℕ
stackSize [] = 0
stackSize (p ∷ ps) = suc (stackSize ps)

tail< : (p : Prob n) (ps : Stack n) → stackSize ps NO.< stackSize (p ∷ ps)
tail< p ps = 0 , refl


-- Triangular substitution: `k` assignments taking `n` unknowns down to `m`.
Steps : ℕ → ℕ → ℕ → Type ℓ-zero
Steps zero n m = n Eq.≡ m
Steps (suc k) zero m = Empty.⊥
Steps (suc k) (suc n) m = Fin (suc n) × Tm n × Steps k n m

AList : ℕ → Type ℓ-zero
AList n = Σ[ m ∈ ℕ ] Σ[ k ∈ ℕ ] Steps k n m

-- By projection, not a match: `consA x w σ .fst` reduces without inspecting `σ`.
consA : Fin (suc n) → Tm n → AList n → AList (suc n)
consA x w σ = σ .fst , suc (σ .snd .fst) , x , w , σ .snd .snd

-- Projects the carried assignments; no clause mentions `check`.
mgu : (n : ℕ) (ps : Stack n) → Sol n ps → AList n
mguFlat : (n : ℕ) (fl : Maybe (FStack n)) (ps : Stack n)
        → onFlat n fl ps → AList n
mguFlexAt : (n : ℕ) (x : Fin n) (u : Tm n) (qs : FStack n) (ps : Stack n)
          → flexAt n x u qs ps → AList n

mgu n [] _ = n , 0 , Eq.refl
mgu n (p ∷ ps) d = mguFlat n (flat1 p) ps d

mguFlat n (just []) ps d = mgu n ps d
mguFlat n (just (e ∷ qs)) ps d = mguFlexAt n (e .fst) (e .snd) qs ps d

mguFlexAt (suc n) x u qs ps (assign w _ d) =
  consA x w (mgu n (applyStack x w (unflexAll qs ++ ps)) d)

applySteps : {k n m : ℕ} → Steps k n m → Tm n → Tm m
applySteps {k = zero} Eq.refl t = t
applySteps {k = suc k} {n = suc n} (x , w , τ) t = applySteps τ (subst1 x w t)

applyA : (σ : AList n) → Tm n → Tm (σ .fst)
applyA σ = applySteps (σ .snd .snd)
