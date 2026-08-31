{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Theory.Finitary
import Cubical.Algebra.Theory.Finitary.Free.Closing as Cl
import Cubical.Algebra.Theory.Finitary.Free.ClosingElim as CE
import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open SortedSig
open SortedEqns
module Theory.Instances.Bags.Order
  (El : Type ℓ-zero) (le : El → El → Bool) where

open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.Maybe using (Maybe ; nothing ; just)
open import Cubical.Functions.Logic using (_⊓_ ; ⊓-assoc ; ⊓-comm
  ; ⊓-identityˡ ; ⊓-identityʳ ; ⇔toPath) renaming (⊤ to ⊤P ; ⊥ to ⊥P)
open import Cubical.Data.Sigma

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Bags.Base El

isPropBoolEq : {b c : Bool} → isProp (b Eq.≡ c)
isPropBoolEq =
  isOfHLevelRetractFromIso 1 (invIso Eq.PathIsoEq) (isSetBool _ _)

Ω : Sorts → Type (ℓ-suc ℓ-zero)
Ω _ = hProp ℓ-zero

⊓Ops : Ops {σ = MonSig} Ω
⊓Ops ε· f = ⊤P
⊓Ops _⊙_ f = f zero ⊓ f (suc zero)

⊓Sat : (e : BagEqns .eqns)
       (ρ : (w : vars BagEqns e) → Ω (BagEqns .varSort e w))
     → TmRec Ω ⊓Ops ρ (BagEqns .lhs e) ≡ TmRec Ω ⊓Ops ρ (BagEqns .rhs e)
⊓Sat (mon assoc) ρ = sym (⊓-assoc (ρ zero) (ρ (suc zero)) (ρ (suc (suc zero))))
⊓Sat (mon unitL) ρ = ⊓-identityˡ (ρ zero)
⊓Sat (mon unitR) ρ = ⊓-identityʳ (ρ zero)
⊓Sat (ext comm) ρ = ⊓-comm (ρ zero) (ρ (suc zero))

bagAllP : (El → hProp ℓ-zero) → Bag → hProp ℓ-zero
bagAllP p m = Cl.rec BagEqns (λ _ → isSetHProp) ⊓Ops ⊓Sat p m

-- ⊤ at ε, a pair at ⊙, p at a generator -- all on the nose, since
-- `Cl.rec` reduces at `var` and at `node`
bagAll : (El → hProp ℓ-zero) → TheoryTy ℓ-zero tt
bagAll p m = ⟨ bagAllP p m ⟩

isPropBagAll : ∀ p m → isProp (bagAll p m)
isPropBagAll p m = bagAllP p m .snd

aboveEl belowEl : El → El → hProp ℓ-zero
aboveEl x y = (le x y Eq.≡ true) , isPropBoolEq
belowEl x y = (le y x Eq.≡ true) , isPropBoolEq

Above Below : El → TheoryTy ℓ-zero tt
Above x = bagAll (aboveEl x)
Below x = bagAll (belowEl x)

-- `nothing` is +∞: an upper bound for the input, and a lower bound that
-- only the empty bag can meet.  That is what pins the accumulator to `ε`
-- at the top call, and it is what makes the step case go through.
belowElM aboveElM : Maybe El → El → hProp ℓ-zero
belowElM nothing y = ⊤P
belowElM (just x) y = belowEl x y
aboveElM nothing y = ⊥P
aboveElM (just x) y = aboveEl x y

BelowM AboveM : Maybe El → TheoryTy ℓ-zero tt
BelowM b = bagAll (belowElM b)
AboveM b = bagAll (aboveElM b)

-- `bagAll` is a fold, so it splits along a tensor, is trivial at the unit,
-- and is `p` itself at a generator -- all on the nose, so these are the
-- intro and elim rules and nothing is transported.
private variable ℓA ℓB : Level

module _ (p : El → hProp ℓ-zero) where
  -- the witness is carried, never matched: `bagAll p` is prop-valued and a
  -- fold, so it moves along the splitting by transport and splits on the nose
  bagAll-⊗ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
    → (A ⊎B B) & bagAll p ⊢ (A & bagAll p) ⊎B (B & bagAll p)
  bagAll-⊗ m ((ms , e , (a , b , tt*)) , q) =
    ms , e , ((a , sp .fst) , (b , sp .snd) , tt*)
    where
    sp : bagAll p (op _⊙_ ms)
    sp = subst (bagAll p) (sym (Eq.eqToPath e)) q

  ⊗-bagAll : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
    → (A & bagAll p) ⊎B (B & bagAll p) ⊢ (A ⊎B B) & bagAll p
  ⊗-bagAll m (ms , e , ((a , qa) , (b , qb) , tt*)) =
    (ms , e , (a , b , tt*)) , subst (bagAll p) (Eq.eqToPath e) (qa , qb)

  bagAll-ε : ⌈ εᵖ ⌉ ⊢ bagAll p
  bagAll-ε m Eq.refl = tt*

  bagAll-gen : (y : El) → ⟨ p y ⟩ → ⌈ ⌈gen y ⌉ ⌉ ⊢ bagAll p
  bagAll-gen y q m Eq.refl = q

  -- and backwards: at a generator the fold *is* `p`, so the witness can be
  -- read back out as a constant
  bagAll-atGen : (y : El) → ⌈ ⌈gen y ⌉ ⌉ & bagAll p ⊢ K ⟨ p y ⟩ & ⌈ ⌈gen y ⌉ ⌉
  bagAll-atGen y m (Eq.refl , q) = q , Eq.refl

-- Two folds that agree on generators are equal, so `bagAll` commutes with
-- ⊓ -- by uniqueness of homomorphisms, with no induction over bags.
bagAll-⊓ : (p q : El → hProp ℓ-zero) (m : Bag)
  → bagAllP p m ⊓ bagAllP q m ≡ bagAllP (λ y → p y ⊓ q y) m
bagAll-⊓ p q m =
  Cl.recUniq BagEqns (λ _ → isSetHProp) ⊓Ops ⊓Sat (λ y → p y ⊓ q y)
    (λ _ z → bagAllP p z ⊓ bagAllP q z)
    (λ where
      ε· x y eq → cong (λ z → bagAllP p z ⊓ bagAllP q z) eq
                  ∙ ⊓-identityˡ ⊤P
      _⊙_ x y eq → cong (λ z → bagAllP p z ⊓ bagAllP q z) eq
                  ∙ ⇔toPath (λ ((pa , pb) , (qa , qb)) → (pa , qa) , (pb , qb))
                            (λ ((pa , qa) , (pb , qb)) → (pa , pb) , (qa , qb)))
    (λ _ → refl)
    m

-- and so it is monotone.  Structurally, by the prop-eliminator: going
-- through `bagAll-⊓` instead would mean transporting along a `⇔toPath`, and
-- that transport does not reduce even at a single generator.
private
  tmMono : {W : Type ℓ-zero} {ws : W → Sorts}
    (P Q : (w : W) → Ω (ws w)) → (∀ w → ⟨ P w ⟩ → ⟨ Q w ⟩)
    → (t : Tm MonSig W ws tt)
    → ⟨ TmRec Ω ⊓Ops P t ⟩ → ⟨ TmRec Ω ⊓Ops Q t ⟩
  tmMono P Q h (var w) = h w
  tmMono P Q h (node ε· ts) _ = tt*
  tmMono P Q h (node _⊙_ ts) (a , b) =
    tmMono P Q h (ts zero) a , tmMono P Q h (ts (suc zero)) b

-- opaque: its result is a bound, never something an answer is read from
opaque
  bagAll-mono : (p q : El → hProp ℓ-zero)
    → (∀ y → ⟨ p y ⟩ → ⟨ q y ⟩) → bagAll p ⊢ bagAll q
  bagAll-mono p q imp m =
    CE.elimProp BagEqns
      {P = λ z → bagAll p z → bagAll q z}
      (λ z → isPropΠ λ _ → isPropBagAll q z)
      imp
      (λ where
        ε· f ih _ → tt*
        _⊙_ f ih (a , b) → ih zero a , ih (suc zero) b)
      (λ e t ρ ih → tmMono (λ w → bagAllP p (ρ w)) (λ w → bagAllP q (ρ w)) ih t)
      m

private
  tmTrue : {W : Type ℓ-zero} {ws : W → Sorts} (P : (w : W) → Ω (ws w))
    → (∀ w → ⟨ P w ⟩) → (t : Tm MonSig W ws tt) → ⟨ TmRec Ω ⊓Ops P t ⟩
  tmTrue P h (var w) = h w
  tmTrue P h (node ε· ts) = tt*
  tmTrue P h (node _⊙_ ts) = tmTrue P h (ts zero) , tmTrue P h (ts (suc zero))

-- a fold that is ⊤ at every generator is ⊤ everywhere
bagAll-⊤ : (m : Bag) → bagAll (λ _ → ⊤P) m
bagAll-⊤ =
  CE.elimProp BagEqns
    {P = λ z → bagAll (λ _ → ⊤P) z}
    (λ z → isPropBagAll (λ _ → ⊤P) z)
    (λ _ → tt*)
    (λ where
      ε· f ih → tt*
      _⊙_ f ih → ih zero , ih (suc zero))
    (λ e t ρ ih → tmTrue (λ w → bagAllP (λ _ → ⊤P) (ρ w)) ih t)
