open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Equality as Eq
open Category
open SortedSig
open SortedEqns
module Theory.Instances.Monoid.ListPresentation
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.List as L using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.FinData using (Fin ; zero ; suc)

open import Theory.Instances.Monoid.Base
open import Theory.Free.Base MonEqns Alphabet (λ _ → tt)

private variable ℓX : Level

private
  C : Sorts → Type _
  C _ = List Alphabet

  isSetC : (s : Sorts) → isSet (C s)
  isSetC _ = L.isOfHLevelList 0 isSetAlphabet

  listOps : Ops {σ = MonSig} C
  listOps ε· _ = []
  listOps _⊙_ xs = xs zero ++ xs (suc zero)

  listSat : (e : MonEqns .eqns)
    (ρ : (w : vars MonEqns e) → C (MonEqns .varSort e w))
    → TmRec C listOps ρ (MonEqns .lhs e) ≡ TmRec C listOps ρ (MonEqns .rhs e)
  listSat assoc ρ = L.++-assoc (ρ zero) (ρ (suc zero)) (ρ (suc (suc zero)))
  listSat unitL ρ = refl
  listSat unitR ρ = L.++-unit-r (ρ zero)

  ListModel : MOD MonEqns _ .ob
  ListModel = (λ s → C s , isSetC s) , listOps , listSat

-- The fold.  Unlike the quotient's recursor this is structural on the
-- carrier, which is the whole point of choosing this presentation.
fold : {X : Sorts → Type ℓX} (α : Ops {σ = MonSig} X)
  → (Alphabet → X tt) → List Alphabet → X tt
fold α ρ [] = α ε· (λ ())
fold α ρ (c ∷ cs) = α _⊙_ (two (ρ c) (fold α ρ cs))

-- The equations as stated by `sat` quantify over a `Tm`, so `TmRec` builds
-- each argument tuple by recursion; `two`/`three` build it by pattern match.
-- `Fin n` has no definitional η, so every law below opens by transporting
-- across that mismatch -- pointwise refl, but not refl.
module Laws {X : Sorts → Type ℓX} (α : Ops {σ = MonSig} X)
  (sat : (e : MonEqns .eqns)
         (ρ' : (w : vars MonEqns e) → X (MonEqns .varSort e w))
       → TmRec X α ρ' (MonEqns .lhs e) ≡ TmRec X α ρ' (MonEqns .rhs e))
  (ρ : Alphabet → X tt)
  where

  private
    _⊛_ : X tt → X tt → X tt
    x ⊛ y = α _⊙_ (two x y)

    unit : X tt
    unit = α ε· (λ ())

    ⊛unitL : (x : X tt) → unit ⊛ x ≡ x
    ⊛unitL x = cong (α _⊙_) (funExt (two (cong (α ε·) (funExt λ ())) refl))
             ∙ sat unitL (λ _ → x)

    ⊛assoc : (x y z : X tt) → (x ⊛ y) ⊛ z ≡ x ⊛ (y ⊛ z)
    ⊛assoc x y z =
        cong (α _⊙_)
          (funExt (two (cong (α _⊙_) (funExt (two refl refl))) refl))
      ∙ sat assoc (three x y z)
      ∙ cong (α _⊙_)
          (funExt (two refl (cong (α _⊙_) (funExt (two refl refl)))))

  ⊛unitR : (x : X tt) → x ⊛ unit ≡ x
  ⊛unitR x = cong (α _⊙_) (funExt (two refl (cong (α ε·) (funExt λ ()))))
           ∙ sat unitR (λ _ → x)

  -- fold is a monoid homomorphism.
  fold-++ : (xs ys : List Alphabet)
    → fold α ρ (xs ++ ys) ≡ fold α ρ xs ⊛ fold α ρ ys
  fold-++ [] ys = sym (⊛unitL (fold α ρ ys))
  fold-++ (c ∷ cs) ys =
      cong (λ z → ρ c ⊛ z) (fold-++ cs ys)
    ∙ sym (⊛assoc (ρ c) (fold α ρ cs) (fold α ρ ys))

  -- Any algebra map agreeing on singletons is the fold; induction on the list.
  uniq : (f : (s : Sorts) → List Alphabet → X s)
    → ((o : MonOp) (ms : arities MonSig o → List Alphabet)
        → f tt (listOps o ms) ≡ α o (λ a → f tt (ms a)))
    → ((v : Alphabet) → f tt (v ∷ []) ≡ ρ v)
    → (m : List Alphabet) → f tt m ≡ fold α ρ m
  uniq f homf fβ [] = homf ε· (λ ()) ∙ cong (α ε·) (funExt λ ())
  uniq f homf fβ (c ∷ cs) =
      homf _⊙_ (two (c ∷ []) cs)
    ∙ cong (α _⊙_) (funExt (two (fβ c) (uniq f homf fβ cs)))

-- The equations again in `Eq`-world.  Both recurse on the left list, so at a
-- concrete list they reduce to `Eq.refl` -- which is what lets the ⊗ rules,
-- which match on the index witness, keep firing.
private
  ++-assocEq : (xs ys zs : List Alphabet)
    → ((xs ++ ys) ++ zs) Eq.≡ (xs ++ (ys ++ zs))
  ++-assocEq [] ys zs = Eq.refl
  ++-assocEq (x ∷ xs) ys zs = Eq.ap (x ∷_) (++-assocEq xs ys zs)

  ++-unit-rEq : (xs : List Alphabet) → (xs ++ []) Eq.≡ xs
  ++-unit-rEq [] = Eq.refl
  ++-unit-rEq (x ∷ xs) = Eq.ap (x ∷_) (++-unit-rEq xs)

listPresentation : FreePresentation _
listPresentation .P = ListModel
listPresentation .satStrict assoc ρ =
  ++-assocEq (ρ zero) (ρ (suc zero)) (ρ (suc (suc zero)))
listPresentation .satStrict unitL ρ = Eq.refl
listPresentation .satStrict unitR ρ = ++-unit-rEq (ρ zero)
listPresentation .gen v = v ∷ []
listPresentation .rec isSetX α sat ρ = fold α ρ
-- `gen v = v ∷ []` folds to `ρ v ⊙ ε`, so this is the unit law, not refl.
listPresentation .recGen isSetX α sat ρ v = Laws.⊛unitR α sat ρ (ρ v)
listPresentation .recOp isSetX α sat ρ ε· ms =
  cong (α ε·) (funExt λ ())
listPresentation .recOp isSetX α sat ρ _⊙_ ms =
    Laws.fold-++ α sat ρ (ms zero) (ms (suc zero))
  ∙ cong (α _⊙_) (funExt (two refl refl))
listPresentation .recUniq isSetX α sat ρ f homf fβ m =
  Laws.uniq α sat ρ f homf fβ m
