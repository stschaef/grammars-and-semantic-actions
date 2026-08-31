{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- EXPERIMENT: is the missing shift converse an artifact of quantifying over
   *all* stacks?  Three questions, in order.

   (1) Is the counterexample really about `B` being empty?  No.  The vacuity
       only needs `B ⟜ literal c` to be empty -- i.e. *no word of `B` ends in
       `c`* -- and it then defeats the converse at EVERY `Goal`.
   (2) Is there a side condition that rescues it?  Yes, and it is
       `B ⊢ (B ⟜ literal c) ⊗ literal c` -- every stack in `B` ends in the
       token being shifted -- plus a lookahead conjunct.
   (3) Can the lookahead be dropped?  Only by a condition on `Goal`.        -}
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
  using ( _⟜_ ; _⊸_ ; ⟜-intro ; ⊸-lam ; ⊗ε-unit-r ; castEq ; &⊕ᴰ-distR
        ; ⊸⟜-swap )
import Theory.Instances.Monoid.Combinator.Ascent.Base Alphabet _≟_ as A
import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ-zero as D

private variable ℓ ℓ' ℓA ℓB ℓD ℓG : Level

-- ---------------------------------------------------------------------------
-- 0.  A `look⊗` that does not insist its source is a `▷`.

lookAt : {D : TheoryTy ℓ tt} {C : TheoryTy ℓ' tt}
  → ((o : M₁) → D & Λ₁ o ⊢ C) → D ⊢ C
lookAt br = ⊕ᴰ-elim br ∘⊢ &⊕ᴰ-distR ∘⊢ (id⊢ ,& (Λ-total ∘⊢ ⊤Ty-intro))

-- ---------------------------------------------------------------------------
-- 1.  The counterexample, sharpened.  `Decidability.noShiftConverse` takes
--     `B = ⊥Ty` and `Goal = ⊥Ty`.  Neither is needed: all that is used is
--     that `B ⟜ literal c` is empty, and `Goal` is arbitrary.

module Vacuity (c : Alphabet) {B : TheoryTy ℓB tt} {G : TheoryTy ℓG tt}
  (noShift : B ⟜ literal c ⊢ ⊥Ty) where

  -- the left side is inhabited at the empty word, vacuously, whatever `G` is
  vacuous : εTy ⊢ (B ⟜ literal c) ⊸ G
  vacuous = ⊸-lam {A = B ⟜ literal c} {B = εTy} {C = G}
              (⊥Ty-elim ∘⊢ noShift ∘⊢ ⊗ε-unit-r)

  -- ...and the right side is not, because it is headed by a letter
  notThere : ¬Nullable (literal c ⊗ (B ⊸ G))
  notThere = ¬Nullable-map (⊗-map id⊢ ⊤Ty-intro) (¬Nullable-startsWith {c})

  noConverse : ((B ⟜ literal c) ⊸ G ⊢ literal c ⊗ (B ⊸ G)) → εTy ⊢ ⊥Ty
  noConverse f = notThere ∘⊢ ((f ∘⊢ vacuous) ,& id⊢)

-- ---------------------------------------------------------------------------
-- 2.  Two entirely non-degenerate stacks at which `noShift` holds.

-- (a) the EMPTY STACK -- the accept state.  It is inhabited, it is a set, it
--     is as real as a parser state gets.
ε-noShift : (c : Alphabet) → εTy ⟜ literal c ⊢ ⊥Ty
ε-noShift c l s = go (s (c ∷ []) Eq.refl)
  where
  go : εTy (l ++ (c ∷ [])) → ⊥Ty l
  go (ns , e , _) =
    Empty.rec (L.¬snoc≡nil {xs = l} {x = c} (sym (Eq.eqToPath e)))

-- (b) a SINGLE TERMINAL on the stack, at a token other than the one shifted.
lit-noShift : (c d : Alphabet) → (c Eq.≡ d → Empty.⊥)
  → literal d ⟜ literal c ⊢ ⊥Ty
lit-noShift c d ne l s = go l (Eq.eqToPath (s (c ∷ []) Eq.refl))
  where
  go : (u : String) → (u ++ (c ∷ [])) ≡ (d ∷ []) → ⊥Ty l
  go [] p = Empty.rec (ne (Eq.pathToEq (L.cons-inj₁ p)))
  go (x ∷ u) p = Empty.rec (L.¬snoc≡nil {xs = u} {x = c} (L.cons-inj₂ p))

-- ...so the converse fails at the empty stack, and at a mismatched terminal,
-- FOR EVERY GOAL.  Neither `B` nor `Goal` needs to be empty.
noConverse-ε : (c : Alphabet) {G : TheoryTy ℓG tt}
  → ((εTy ⟜ literal c) ⊸ G ⊢ literal c ⊗ (εTy ⊸ G)) → εTy ⊢ ⊥Ty
noConverse-ε c {G = G} = Vacuity.noConverse c {G = G} (ε-noShift c)

noConverse-lit : (c d : Alphabet) (ne : c Eq.≡ d → Empty.⊥)
  {G : TheoryTy ℓG tt}
  → ((literal d ⟜ literal c) ⊸ G ⊢ literal c ⊗ (literal d ⊸ G)) → εTy ⊢ ⊥Ty
noConverse-lit c d ne {G = G} = Vacuity.noConverse c {G = G} (lit-noShift c d ne)

-- ---------------------------------------------------------------------------
-- 3.  THE SIDE CONDITION.  `B` is `c`-terminated: every stack in it ends in
--     the token being shifted.  This is exactly what the vacuity above
--     denies, and it is what makes the converse go through.

_ends-in_ : TheoryTy ℓB tt → Alphabet → Type _
B ends-in c = B ⊢ (B ⟜ literal c) ⊗ literal c

-- ...and `B' ⊗ literal c` is `c`-terminated, by `⟜`'s own introduction rule.
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

    -- the whole arithmetic of the shift, in one matched equation:
    --   n₀ ++ m = n₀ ++ (c ∷ m') = (n₀ ++ [c]) ++ m' = l ++ m'
    joinEq : (n₀ m' l m : String)
      → (n₀ ++ (c ∷ [])) Eq.≡ l → ((c ∷ []) ++ m') Eq.≡ m
      → (n₀ ++ m) Eq.≡ (l ++ m')
    joinEq n₀ m' _ _ Eq.refl Eq.refl = Eq.sym (++-assocEq n₀ (c ∷ []) m')

  -- THE CONVERSE, under the side condition and one token of lookahead.
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

-- ---------------------------------------------------------------------------
-- 4.  The lookahead cannot be dropped, even at a `c`-terminated stack.
--     `literal c` is `c`-terminated, yet at `G = ⊤Ty` the left side is
--     inhabited everywhere while the right side is headed by a letter.

lookaheadNeeded : (c : Alphabet)
  → ((literal c ⟜ literal c) ⊸ ⊤Ty ⊢ literal c ⊗ (literal c ⊸ ⊤Ty))
  → εTy ⊢ ⊥Ty
lookaheadNeeded c f = notThere ∘⊢ ((f ∘⊢ vac) ,& id⊢)
  where
  vac : εTy ⊢ (literal c ⟜ literal c) ⊸ ⊤Ty
  vac = ⊸-lam {A = literal c ⟜ literal c} {B = εTy} {C = ⊤Ty} ⊤Ty-intro
  notThere : ¬Nullable (literal c ⊗ (literal c ⊸ ⊤Ty))
  notThere = ¬Nullable-map (⊗-map id⊢ ⊤Ty-intro) (¬Nullable-startsWith {c})

-- ---------------------------------------------------------------------------
-- 5.  So the *bare* converse -- the one `Ans-dimap` demands, with no
--     lookahead conjunct to feed it -- needs a second hypothesis: off the
--     class `tk c`, the answer type must be refutable.  That is a condition
--     on `Goal`, not on `B`: it says the goal forces a `c` here.

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

-- ---------------------------------------------------------------------------
-- 6.  Q2: BOUNDING THE QUANTIFIER.  `AscFin` ranges over a finite family of
--     concrete stacks instead of over all of `TheorySet`.  `shift` then
--     instantiates at `Dec` -- but only because the two hypotheses of
--     `ShiftBackFull` are *assumed* at every member of the family.  The
--     finiteness itself contributes nothing; it merely gives a place to hang
--     the side condition.

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

-- ---------------------------------------------------------------------------
-- 7.  ...and the second hypothesis is not free, even at a family of
--     `c`-terminated stacks.  Take `B = literal c`, which IS `c`-terminated
--     (`literal c ⟜ literal c ≅ εTy`, so this is the accept configuration),
--     and `Goal = εSet`, which is exactly what `DecReduce` instantiates.

litc-⟜-ε : (c : Alphabet) → literal c ⟜ literal c ⊢ εTy
litc-⟜-ε c l s = subst εTy (sym (nilOf l (Eq.eqToPath (s (c ∷ []) Eq.refl))))
                   εTy-pt
  where
  nilOf : (u : String) → (u ++ (c ∷ [])) ≡ (c ∷ []) → u ≡ []
  nilOf [] _ = refl
  nilOf (x ∷ u) p = Empty.rec (L.¬snoc≡nil {xs = u} {x = c} (L.cons-inj₂ p))

-- the left side is inhabited at the empty word -- not vacuously this time,
-- but because the empty stack really does owe the empty goal nothing
ε-inhabits : (c : Alphabet) → εTy ⊢ (literal c ⟜ literal c) ⊸ εTy
ε-inhabits c = ⊸-lam {A = literal c ⟜ literal c} {B = εTy} {C = εTy}
                 (litc-⟜-ε c ∘⊢ ⊗ε-unit-r)

-- so `offClass ε₁` is refuted...
no-offClass-ε : (c : Alphabet)
  → (Λ₁ ε₁ & ((literal c ⟜ literal c) ⊸ εTy) ⊢ ⊥Ty) → εTy ⊢ ⊥Ty
no-offClass-ε c f = f ∘⊢ (liftTy ,& ε-inhabits c)

-- ...and with it the bare converse, at a `c`-terminated stack and the goal
-- `DecReduce` actually uses.  `ends-in` alone does NOT rescue `shift`.
noConverse-at-ε-goal : (c : Alphabet)
  → ((literal c ⟜ literal c) ⊸ εTy ⊢ literal c ⊗ (literal c ⊸ εTy))
  → εTy ⊢ ⊥Ty
noConverse-at-ε-goal c f = notThere ∘⊢ ((f ∘⊢ ε-inhabits c) ,& id⊢)
  where
  notThere : ¬Nullable (literal c ⊗ (literal c ⊸ εTy))
  notThere = ¬Nullable-map (⊗-map id⊢ ⊤Ty-intro) (¬Nullable-startsWith {c})

-- ---------------------------------------------------------------------------
-- 8.  ...but `shiftFin` is not vacuous either: at `Goal = litSet c` -- not
--     `⊥`, not `⊤` -- the one-element family `λ _ → litSet c` satisfies both
--     hypotheses, and `shift` really does instantiate at `Dec`.

module Demo (c : Alphabet) where

  unitStack : (literal c ⟜ literal c) []
  unitStack r lr = lr

  litc-ends : literal c ends-in c
  litc-ends m lc = two [] m , Eq.refl , (unitStack , (lc , tt*))

  -- the goal pins the class: `(literal c ⟜ literal c) ⊸ literal c` at `m`
  -- says `m` IS the word `c`, so every other class is refuted
  pinned : ((literal c ⟜ literal c) ⊸ literal c) ⊢ Λ₁ (tk c)
  pinned m f = two m [] , ++-unit-rEq m , (f [] unitStack , (tt , tt*))

  litc-off : (o : M₁) → (o Eq.≡ tk c → Empty.⊥)
    → Λ₁ o & ((literal c ⟜ literal c) ⊸ literal c) ⊢ ⊥Ty
  litc-off o ne = Λ-disjoint o (tk c) ne ∘⊢ (π₁ ,& (pinned ∘⊢ π₂))

  open Q2 {n = 1} (λ _ → litSet c) (litSet c)

  shiftDec : {D₀ : TheoryTy ℓD tt} → D₀ ⊢ AscFin ⟨▷⟩ ⟨□⟩ (litSet c)
  shiftDec = shiftFin c (λ _ → litc-ends) (λ _ → litc-off)
