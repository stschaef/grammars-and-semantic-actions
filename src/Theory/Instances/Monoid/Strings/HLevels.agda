{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Instances.Monoid.Strings.HLevels
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

private variable ℓA ℓB ℓC ℓD ℓY : Level

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; ++-assoc ; ++-unit-r)
import Cubical.Data.List as L
import Cubical.Data.Empty as Emp
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
open import Cubical.Data.Equality.More using (isSet→isSetEq)

open import Cubical.WildCat.LocallySmall.Base

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings.Base Alphabet isSetAlphabet
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Top.Properties MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Instances.Monoid.Strings.LinearProduct Alphabet isSetAlphabet

open WildCatNotation
open WildCatIso

lits : String → TheoryTy ℓM tt
lits [] = εTy
lits (c ∷ w) = ＂ c ＂ ⊗ lits w

lits→⌈⌉ : (w : String) → lits w ⊢ ⌈ w ⌉
lits→⌈⌉ [] m (ms , e , _) = Eq.sym e
lits→⌈⌉ (c ∷ w) m (ms , e , (lc , (r , _))) =
  go (ms zero) (ms (suc zero)) m lc (lits→⌈⌉ w (ms (suc zero)) r) e
  where
  go : (x y n : String) → x Eq.≡ (c ∷ []) → y Eq.≡ w → (x ++ y) Eq.≡ n
     → n Eq.≡ (c ∷ w)
  go .(c ∷ []) .w n Eq.refl Eq.refl q = Eq.sym q

⌈⌉→lits : (w : String) → ⌈ w ⌉ ⊢ lits w
⌈⌉→lits [] m p = go p
  where
  go : m Eq.≡ [] → εTy m
  go Eq.refl = εTy-pt
⌈⌉→lits (c ∷ w) m p = go p
  where
  go : m Eq.≡ (c ∷ w) → (＂ c ＂ ⊗ lits w) m
  go Eq.refl =
    two (c ∷ []) w , Eq.refl , (Eq.refl , (⌈⌉→lits w w Eq.refl , tt*))

-- the carrier is a set, so a splitting's index equation is a proposition
isSetString : isSet String
isSetString = M .fst tt .snd

isPropEqString : {x y : String} → isProp (x Eq.≡ y)
isPropEqString = isSet→isSetEq isSetString

-- `Fin 2` has no definitional η, so a rebuilt splitting reaches an arbitrary
-- one only through this path.
two≡ : {ms : arities MonSig _⊙_ → String} {x y : String}
  → x ≡ ms zero → y ≡ ms (suc zero) → two x y ≡ ms
two≡ p q = funExt λ where
  zero → p
  (suc zero) → q

⊗PathP' : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {x y : String}
  (r : x ≡ y) {ms ns : arities MonSig _⊙_ → String} (s : ms ≡ ns)
  {ex : op _⊙_ ms Eq.≡ x} {ey : op _⊙_ ns Eq.≡ y}
  {a : A (ms zero)} {a' : A (ns zero)}
  {b : B (ms (suc zero))} {b' : B (ns (suc zero))}
  → PathP (λ j → A (s j zero)) a a'
  → PathP (λ j → B (s j (suc zero))) b b'
  → PathP (λ j → (A ⊗ B) (r j))
      (ms , ex , (a , (b , tt*))) (ns , ey , (a' , (b' , tt*)))
⊗PathP' r s {ex = ex} {ey = ey} pa pb j =
  s j
  , isProp→PathP (λ i → isPropEqString {x = op _⊙_ (s i)} {y = r i}) ex ey j
  , (pa j , (pb j , tt*))

transportEq : {A : TheoryTy ℓA tt} {x y : String} (p : x ≡ y) (a : A x)
  → PathP (λ j → A (p j)) a (Eq.transport A (Eq.pathToEq p) a)
transportEq {A = A} p a = J
  (λ _ p' → PathP (λ j → A (p' j)) a (Eq.transport A (Eq.pathToEq p') a))
  (sym (cong (λ q → Eq.transport A q a)
          (isPropEqString (Eq.pathToEq refl) Eq.refl)))
  p

unit-l≡ : {A : TheoryTy ℓA tt} (m : String) (t : (εTy ⊗ A) m)
  (p : t .fst (suc zero) ≡ m)
  → PathP (λ j → A (p j)) (t .snd .snd .snd .fst) (⊗-unit-l {A = A} m t)
unit-l≡ {A = A} m t p =
  subst (λ r → PathP (λ j → A (r j)) a (⊗-unit-l {A = A} m t))
    (isSetString _ _ upath p) (transportEq {A = A} upath a)
  where
  a = t .snd .snd .snd .fst

  upath : t .fst (suc zero) ≡ m
  upath = unit-lPath (t .fst) (t .snd .snd .fst) (t .snd .fst)
