{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- EXPERIMENT: shift converse fails whenever `B ⟜ literal c` is empty, at EVERY Goal;
   rescued by `B ends-in c` plus lookahead; dropping the lookahead needs a Goal condition. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Ascent.ShiftConverse
  {ℓAlph} (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)) where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
import Cubical.Data.List.Properties as L
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt ; tt*)

open import Theory.Instances.Monoid.Combinator.Core Alphabet _≟_
open import Theory.Instances.Monoid.SequentialUnambiguity.Nullable Alphabet isSetAlphabet
  using (¬Nullable ; ¬Nullable-map)
open import Theory.Instances.Monoid.SequentialUnambiguity.First Alphabet isSetAlphabet
  using (¬Nullable-startsWith)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using ( _⟜_ ; _⊸_ ; ⟜-intro ; ⊸-lam ; ⊗ε-unit-r ; castEq
        ; ⊸⟜-swap )
import Theory.Instances.Monoid.Combinator.Ascent.Base Alphabet _≟_ as A
import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ-zero as D

private variable ℓ ℓ' ℓA ℓB ℓD ℓG : Level

lookAt : {D : TheoryTy ℓ tt} {C : TheoryTy ℓ' tt}
  → ((o : M₁) → D & Λ₁ o ⊢ C) → D ⊢ C
lookAt br = ⊕ᴰ-elim br ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,& (Λ-total ∘⊢ ⊤Ty-intro))

-- Sharper than `Decidability.noShiftConverse`: only `B ⟜ literal c` empty is used; `Goal` arbitrary.

module Vacuity (c : Alphabet) {B : TheoryTy ℓB tt} {G : TheoryTy ℓG tt}
  (noShift : B ⟜ literal c ⊢ ⊥Ty) where

  vacuous : εTy ⊢ (B ⟜ literal c) ⊸ G
  vacuous = ⊸-lam {A = B ⟜ literal c} {B = εTy} {C = G}
              (⊥Ty-elim ∘⊢ noShift ∘⊢ ⊗ε-unit-r)

  notThere : ¬Nullable (literal c ⊗ (B ⊸ G))
  notThere = ¬Nullable-map (⊗-map id⊢ ⊤Ty-intro) (¬Nullable-startsWith {c})

  noConverse : ((B ⟜ literal c) ⊸ G ⊢ literal c ⊗ (B ⊸ G)) → εTy ⊢ ⊥Ty
  noConverse f = notThere ∘⊢ ((f ∘⊢ vacuous) ,& id⊢)

-- `noShift` holds at non-degenerate stacks: the empty stack (accept state) and a mismatched
-- terminal — so the converse fails there for every `Goal`; neither `B` nor `Goal` need be empty.
ε-noShift : (c : Alphabet) → εTy ⟜ literal c ⊢ ⊥Ty
ε-noShift c l s = go (s (c ∷ []) Eq.refl)
  where
  go : εTy (l ++ (c ∷ [])) → ⊥Ty l
  go (ns , e , _) =
    Empty.rec (L.¬snoc≡nil {xs = l} {x = c} (sym (Eq.eqToPath e)))

lit-noShift : (c d : Alphabet) → (c Eq.≡ d → Empty.⊥)
  → literal d ⟜ literal c ⊢ ⊥Ty
lit-noShift c d ne l s = go l (Eq.eqToPath (s (c ∷ []) Eq.refl))
  where
  go : (u : String) → (u ++ (c ∷ [])) ≡ (d ∷ []) → ⊥Ty l
  go [] p = Empty.rec (ne (Eq.pathToEq (L.cons-inj₁ p)))
  go (x ∷ u) p = Empty.rec (L.¬snoc≡nil {xs = u} {x = c} (L.cons-inj₂ p))

noConverse-ε : (c : Alphabet) {G : TheoryTy ℓG tt}
  → ((εTy ⟜ literal c) ⊸ G ⊢ literal c ⊗ (εTy ⊸ G)) → εTy ⊢ ⊥Ty
noConverse-ε c {G = G} = Vacuity.noConverse c {G = G} (ε-noShift c)

noConverse-lit : (c d : Alphabet) (ne : c Eq.≡ d → Empty.⊥)
  {G : TheoryTy ℓG tt}
  → ((literal d ⟜ literal c) ⊸ G ⊢ literal c ⊗ (literal d ⊸ G)) → εTy ⊢ ⊥Ty
noConverse-lit c d ne {G = G} = Vacuity.noConverse c {G = G} (lit-noShift c d ne)

-- Side condition: `B` is `c`-terminated — exactly what the vacuity above denies.
_ends-in_ : TheoryTy ℓB tt → Alphabet → Type _
B ends-in c = B ⊢ (B ⟜ literal c) ⊗ literal c

⊗-ends-in : {B' : TheoryTy ℓB tt} (c : Alphabet) → (B' ⊗ literal c) ends-in c
⊗-ends-in {B' = B'} c =
  ⟜-intro {A = B'} {B = literal c} {C = B' ⊗ literal c} id⊢ ,⊗ id⊢

module ShiftBack (c : Alphabet) {B : TheoryTy ℓB tt} {G : TheoryTy ℓG tt}
  (endsIn : B ends-in c) where

  private
    onLeft : {u u' v w : String} → u Eq.≡ u' → (u ++ v) Eq.≡ w → (u' ++ v) Eq.≡ w
    onLeft Eq.refl q = q

    onRight : {u v v' w : String} → v Eq.≡ v' → (u ++ v) Eq.≡ w → (u ++ v') Eq.≡ w
    onRight Eq.refl q = q

    -- shift arithmetic: n₀ ++ m = n₀ ++ (c ∷ m') = (n₀ ++ [c]) ++ m' = l ++ m'
    joinEq : (n₀ m' l m : String)
      → (n₀ ++ (c ∷ [])) Eq.≡ l → ((c ∷ []) ++ m') Eq.≡ m
      → (n₀ ++ m) Eq.≡ (l ++ m')
    joinEq n₀ m' _ _ Eq.refl Eq.refl = Eq.sym (++-assocEq n₀ (c ∷ []) m')

  shiftConverse : Λ₁ (tk c) & ((B ⟜ literal c) ⊸ G) ⊢ literal c ⊗ (B ⊸ G)
  shiftConverse m ((ms , e , (lc , _)) , f) = ms , e , (lc , (back , tt*))
    where
    back : (B ⊸ G) (ms (suc zero))
    back l b with endsIn l b
    ... | (ns , e2 , (h , (lc2 , _))) =
      castEq {A = G}
        (joinEq (ns zero) (ms (suc zero)) l m
          (onRight lc2 e2) (onLeft lc e))
        (f (ns zero) h)

-- Lookahead cannot be dropped: `literal c` is `c`-terminated, yet `G = ⊤Ty` refutes the converse.
lookaheadNeeded : (c : Alphabet)
  → ((literal c ⟜ literal c) ⊸ ⊤Ty ⊢ literal c ⊗ (literal c ⊸ ⊤Ty))
  → εTy ⊢ ⊥Ty
lookaheadNeeded c f = notThere ∘⊢ ((f ∘⊢ vac) ,& id⊢)
  where
  vac : εTy ⊢ (literal c ⟜ literal c) ⊸ ⊤Ty
  vac = ⊸-lam {A = literal c ⟜ literal c} {B = εTy} {C = ⊤Ty} ⊤Ty-intro
  notThere : ¬Nullable (literal c ⊗ (literal c ⊸ ⊤Ty))
  notThere = ¬Nullable-map (⊗-map id⊢ ⊤Ty-intro) (¬Nullable-startsWith {c})

-- Bare converse (as `Ans-dimap` demands) needs `offClass`: off `tk c` the answer type is
-- refutable — a condition on `Goal`, not `B`.
module ShiftBackFull (c : Alphabet) {B : TheoryTy ℓB tt} {G : TheoryTy ℓG tt}
  (endsIn : B ends-in c)
  (offClass : (o : M₁) → (o Eq.≡ tk c → Empty.⊥)
            → Λ₁ o & ((B ⟜ literal c) ⊸ G) ⊢ ⊥Ty) where

  open ShiftBack c {B = B} {G = G} endsIn public

  shiftBack : (B ⟜ literal c) ⊸ G ⊢ literal c ⊗ (B ⊸ G)
  shiftBack = lookAt br
    where
    br : (o : M₁) → ((B ⟜ literal c) ⊸ G) & Λ₁ o ⊢ literal c ⊗ (B ⊸ G)
    br ε₁ = ⊥Ty-elim ∘⊢ offClass ε₁ (λ ()) ∘⊢ (π₂ ,& π₁)
    br (tk d) = go (d ≟ c)
      where
      go : (d Eq.≡ c) Sum.⊎ ((d Eq.≡ c) → Empty.⊥)
        → ((B ⟜ literal c) ⊸ G) & Λ₁ (tk d) ⊢ literal c ⊗ (B ⊸ G)
      go (Sum.inl Eq.refl) = shiftConverse ∘⊢ (π₂ ,& π₁)
      go (Sum.inr ne) =
        ⊥Ty-elim ∘⊢ offClass (tk d) (λ where Eq.refl → ne Eq.refl)
        ∘⊢ (π₂ ,& π₁)

-- Q2: bounding the quantifier to a finite family. Finiteness itself contributes nothing;
-- it merely gives a place to hang the `ShiftBackFull` hypotheses.
module Q2 {ℓB' ℓG' : Level} {n : ℕ} (Ks : Fin n → TheorySet ℓB' tt)
  (Goal : TheorySet ℓG' tt) where

  open A.Ascent D.DecAnswer Goal
  open DivariantAnswer D.DecDiv

  AscFin : ParserTag → ParserTag → TheorySet ℓA tt → TheoryTy _ tt
  AscFin a c₀ A₀ =
    &[ i ∈ Fin n ]
      (ty (▷? a (Ans (Owes (Ks i))))
       ⇒ ty (▷? c₀ (Ans (Owes (A._⟜Set_ (Ks i) A₀)))))

  shiftFin : (c : Alphabet)
    → (ends : (i : Fin n) → ty (Ks i) ends-in c)
    → (off : (i : Fin n) (o : M₁) → (o Eq.≡ tk c → Empty.⊥)
             → Λ₁ o & ((ty (Ks i) ⟜ literal c) ⊸ ty Goal) ⊢ ⊥Ty)
    → {D₀ : TheoryTy ℓD tt} → D₀ ⊢ AscFin ⟨▷⟩ ⟨□⟩ (litSet c)
  shiftFin c ends off = &ᴰ-intro λ i → ⇒-intro
    (▷□ (Ans-dimap
           {A = litSet c ⊗Set Owes (Ks i)}
           {B = Owes (A._⟜Set_ (Ks i) (litSet c))}
           (⊸⟜-swap {A = literal c} {B = ty (Ks i)} {C = ty Goal})
           (ShiftBackFull.shiftBack c {B = ty (Ks i)} {G = ty Goal}
              (ends i) (off i))
         ∘⊢ Ans-lit c)
     ∘⊢ π₂)

-- `offClass` is not free: `B = literal c` (c-terminated) with `Goal = εSet` (what `DecReduce`
-- instantiates) refutes it, so `ends-in` alone does NOT rescue `shift`.
litc-⟜-ε : (c : Alphabet) → literal c ⟜ literal c ⊢ εTy
litc-⟜-ε c l s = subst εTy (sym (nilOf l (Eq.eqToPath (s (c ∷ []) Eq.refl))))
                   εTy-pt
  where
  nilOf : (u : String) → (u ++ (c ∷ [])) ≡ (c ∷ []) → u ≡ []
  nilOf [] _ = refl
  nilOf (x ∷ u) p = Empty.rec (L.¬snoc≡nil {xs = u} {x = c} (L.cons-inj₂ p))

ε-inhabits : (c : Alphabet) → εTy ⊢ (literal c ⟜ literal c) ⊸ εTy
ε-inhabits c = ⊸-lam {A = literal c ⟜ literal c} {B = εTy} {C = εTy}
                 (litc-⟜-ε c ∘⊢ ⊗ε-unit-r)

no-offClass-ε : (c : Alphabet)
  → (Λ₁ ε₁ & ((literal c ⟜ literal c) ⊸ εTy) ⊢ ⊥Ty) → εTy ⊢ ⊥Ty
no-offClass-ε c f = f ∘⊢ (liftTy ,& ε-inhabits c)

noConverse-at-ε-goal : (c : Alphabet)
  → ((literal c ⟜ literal c) ⊸ εTy ⊢ literal c ⊗ (literal c ⊸ εTy))
  → εTy ⊢ ⊥Ty
noConverse-at-ε-goal c f = notThere ∘⊢ ((f ∘⊢ ε-inhabits c) ,& id⊢)
  where
  notThere : ¬Nullable (literal c ⊗ (literal c ⊸ εTy))
  notThere = ¬Nullable-map (⊗-map id⊢ ⊤Ty-intro) (¬Nullable-startsWith {c})

-- `shiftFin` is not vacuous: `Goal = litSet c` with family `λ _ → litSet c` satisfies both
-- hypotheses, so `shift` really does instantiate at `Dec`.
module Demo (c : Alphabet) where

  unitStack : (literal c ⟜ literal c) []
  unitStack r lr = lr

  litc-ends : literal c ends-in c
  litc-ends m lc = two [] m , Eq.refl , (unitStack , (lc , tt*))

  -- the goal pins the class: at `m` it says `m` IS the word `c`
  pinned : ((literal c ⟜ literal c) ⊸ literal c) ⊢ Λ₁ (tk c)
  pinned m f = two m [] , ++-unit-rEq m , (f [] unitStack , (tt , tt*))

  litc-off : (o : M₁) → (o Eq.≡ tk c → Empty.⊥)
    → Λ₁ o & ((literal c ⟜ literal c) ⊸ literal c) ⊢ ⊥Ty
  litc-off o ne = Λ-disjoint o (tk c) ne ∘⊢ (π₁ ,& (pinned ∘⊢ π₂))

  open Q2 {n = 1} (λ _ → litSet c) (litSet c)

  shiftDec : {D₀ : TheoryTy ℓD tt} → D₀ ⊢ AscFin ⟨▷⟩ ⟨□⟩ (litSet c)
  shiftDec = shiftFin c (λ _ → litc-ends) (λ _ → litc-off)
