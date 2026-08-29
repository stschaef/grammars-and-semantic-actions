{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The bound in the type: an answer that cannot be built unless it is linear.

   `Theory/Combinator/Cost` grades an answer with a step count, and
   `Lambda/CostTests` reads six rows off it as `refl`.  It also records why
   the rows stop being evidence for anything general: the universal
   recurrences are true and not `refl`, because with the subterms free
   `tmSize` is stuck, `<-wellfounded` yields no `Acc`, and `löb-unfold` is
   propositional and never definitional.  A "this checker is linear"
   theorem had to reason through the fixpoint by hand.

   It does not, if the bound rides INSIDE the answer rather than being
   asserted about the checker afterwards:

       Ans A m = Σ[ c ∈ ℕ ] (c ≤ k · size m) × ty (T.Ans A) m

   Now `AnsFam` is a family of sets whose elements carry their own
   certificate, `fix` is `löb` at that family, and `löb`'s typing
   transports the certificate across the recursion for free.  Nothing is
   ever unfolded.  The obligations are all LOCAL -- one per operation of
   the interface -- and the resulting theorem is quantified over every
   model element, which is exactly what the table could not say.

   WHAT THE CLIENT OWES.  `size` is a measure on the model at every sort,
   with

     sizePos   1 ≤ size m                              -- a step costs a size
     sizeNode  1 + Σₐ size (ms a) ≤ size (op o ms)     -- superadditive

   `sizeNode` bounds `size` from BELOW, so it does not by itself make the
   bound linear in anything: `size = 2 ^ tmSize` satisfies it.  What the
   interface guarantees is `cost ≤ k · size`; that this is a LINEAR bound
   is the client's obligation, discharged by exhibiting `size` as a linear
   function of the term's size.  `Lambda/Bounded` does exactly that and
   says so.

   WHAT DOES NOT SURVIVE, and the reason is arithmetic rather than
   squeamishness: `Ans-⊕&` and `Ans-&&` take two answers AT THE SAME MODEL
   ELEMENT and add their costs, so the conclusion wants twice the budget
   its premises were each allowed.  `⊕&-impossible` below is that as a
   term: feed two answers that each spend the whole budget, and the
   certificate the combinator must produce says `2n ≤ n` at `n ≥ 1`.
   `Ans-re` dies for a different reason -- it moves to `f m`, and nothing
   relates `size (f m)` to `size m`.

   The impossibility is relative to HONESTY, and it has to be: an
   `AnswerFunctor` is law-free, so a combinator is free to report a cost
   that is not the cost of the computation.  `⊕&-byLying` exhibits one, so
   that the scope of the negative result is on the record rather than
   implied.  What is impossible is an alternation that charges what
   `Cost` charges. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Combinator.Linear
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _·_ ; isSetℕ
        ; +-zero ; ·-suc ; ·-comm ; ·-identityʳ ; ·-distribˡ)
open import Cubical.Data.Nat.Order
  using (_≤_ ; isProp≤ ; ≤-refl ; ≤-trans ; ≤-+k ; ≤-·k ; ≤-+-≤
        ; suc-≤-suc ; ¬m<m)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.HLevels σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Product.Binary.Base σeq V vs 𝒫
open import Theory.Type.Sum.Binary.Base σeq V vs 𝒫
open import Theory.Type.Decidable.Base σeq V vs 𝒫
open import Theory.Combinator.Core σeq V vs 𝒫

private variable ℓA ℓB : Level

-- `Cost`'s sum over the slots of a node, repeated here because that one is
-- private.  The two definitions agree clause for clause, which is what
-- makes `Lambda/Bounded`'s cross-check against `Costed` a `refl`.
sumFin : {n : ℕ} → (Fin n → ℕ) → ℕ
sumFin {zero} f = 0
sumFin {suc n} f = f zero + sumFin (λ i → f (suc i))

private
  sumFin-mono : {n : ℕ} {f g : Fin n → ℕ}
    → ((a : Fin n) → f a ≤ g a) → sumFin f ≤ sumFin g
  sumFin-mono {zero} h = ≤-refl
  sumFin-mono {suc n} h = ≤-+-≤ (h zero) (sumFin-mono (λ i → h (suc i)))

  sumFin-· : (k : ℕ) {n : ℕ} (f : Fin n → ℕ)
    → sumFin (λ a → k · f a) ≡ k · sumFin f
  sumFin-· k {zero} f = sym (lem k)
    where
    lem : (j : ℕ) → j · 0 ≡ 0
    lem zero = refl
    lem (suc j) = lem j
  sumFin-· k {suc n} f =
    cong (k · f zero +_) (sumFin-· k (λ i → f (suc i)))
    ∙ ·-distribˡ k (f zero) (sumFin (λ i → f (suc i)))

  ≤-k· : (k : ℕ) {m n : ℕ} → m ≤ n → k · m ≤ k · n
  ≤-k· k {m} {n} p = subst2 _≤_ (·-comm m k) (·-comm n k) (≤-·k p)

  -- the whole of the negative result, as arithmetic
  no-double : (n : ℕ) → 1 ≤ n → n + n ≤ n → Empty.⊥
  no-double n p q = ¬m<m (≤-trans (≤-+k {m = 1} {n = n} {k = n} p) q)


module Bounded (𝒯 : AnswerFunctor)
  (k : ℕ) (size : {s : S} → ↓M s → ℕ)
  (k≥1 : 1 ≤ k)
  (sizePos : {s : S} (m : ↓M s) → 1 ≤ size m)
  (sizeNode : (o : σ .ops) (ms : interpIn o ↓M)
    → suc (sumFin (λ a → size (ms a))) ≤ size (op o ms))
  where

  private module T = AnswerFunctor 𝒯

  budget : {s : S} → ↓M s → ℕ
  budget m = k · size m

  -- The graded answer.  `≤` is a proposition, so this adds no h-level
  -- obligation the underlying answer did not already discharge, and adds
  -- no level either: `ℕ` and `≤` are both at `ℓ-zero`.
  BAns : {s : S} → TheorySet ℓA s → TheorySet (T.ℓAns ℓA) s
  BAns A = (λ m → Σ[ c ∈ ℕ ] ((c ≤ budget m) × ty (T.Ans A) m))
         , λ m → isSetΣ isSetℕ λ _ →
             isSet× (isProp→isSet isProp≤) (isSetTy (T.Ans A) m)

  -- one step is affordable anywhere, because every model element has size
  ofDec≤ : {s : S} (m : ↓M s) → 1 ≤ budget m
  ofDec≤ m = ≤-trans (subst (1 ≤_) (sym (·-identityʳ k)) k≥1)
                     (≤-k· k (sizePos m))

  -- ...and a node costs one more than its slots, which `sizeNode` pays for
  -- provided `k ≥ 1`: the slack `k · size (op o ms) ∸ k · Σₐ size (ms a)`
  -- is at least `k`, and the node needs 1 of it.
  node≤ : (o : σ .ops) (ms : interpIn o ↓M) {cs : arities σ o → ℕ}
    → ((a : arities σ o) → cs a ≤ budget (ms a))
    → suc (sumFin cs) ≤ budget (op o ms)
  node≤ o ms {cs} bs =
    ≤-trans (suc-≤-suc slots) (≤-trans pay (≤-k· k (sizeNode o ms)))
    where
    Σs : ℕ
    Σs = sumFin (λ a → size (ms a))

    slots : sumFin cs ≤ k · Σs
    slots = subst (sumFin cs ≤_) (sumFin-· k (λ a → size (ms a)))
                  (sumFin-mono bs)

    pay : suc (k · Σs) ≤ k · suc Σs
    pay = subst (suc (k · Σs) ≤_) (sym (·-suc k Σs))
                (≤-+k {m = 1} {n = k} {k = k · Σs} k≥1)

  bounded : LinearAnswer
  bounded .LinearAnswer.ℓAns = T.ℓAns
  bounded .LinearAnswer.Ans = BAns
  bounded .LinearAnswer.Ans-map& f g m ((c , b , r) , h) =
    c , b , T.Ans-map& f g m (r , h)
  bounded .LinearAnswer.Ans-ofDec m d = 1 , ofDec≤ m , T.Ans-ofDec m d
  bounded .LinearAnswer.Ans-node o prec {As} {ms} ws =
    suc (sumFin (λ a → ws a .fst))
    , node≤ o ms (λ a → ws a .snd .fst)
    , T.Ans-node o prec (λ a → ws a .snd .snd)

  -- `k` is not extra generality.  If `(k , size)` is admissible then so is
  -- `(1 , budget)`, with the same bound: these two lines are the proof,
  -- and they are `ofDec≤` and `node≤` at `cs = budget ∘ ms`.  So a client
  -- may always take `k = 1` and fold the per-node constant into `size`,
  -- which is what `Lambda/Bounded` does.
  absorb-sizePos : {s : S} (m : ↓M s) → 1 ≤ budget m
  absorb-sizePos = ofDec≤

  absorb-sizeNode : (o : σ .ops) (ms : interpIn o ↓M)
    → suc (sumFin (λ a → budget (ms a))) ≤ budget (op o ms)
  absorb-sizeNode o ms = node≤ o ms (λ a → ≤-refl)


  -- THE MISSING FIELD.  `Ans-⊕&` and `Ans-&&` have the same premise --
  -- two answers at the same `m` -- and `Cost` charges both the sum.  Here
  -- is what that costs, at the smallest grammar there is.
  ⊤Set : {s : S} → TheorySet ℓ-zero s
  ⊤Set = ⊤Ty , isSet⊤Ty

  module _ {s : S} (m₀ : ↓M s) where
    private
      trivial : ty (T.Ans ⊤Set) m₀
      trivial = T.Ans-ofDec m₀ (dec-yes m₀ tt)

    -- an answer that has spent exactly its budget: admissible, since `≤`
    -- is reflexive, and nothing in the record forbids it
    full : ty (BAns ⊤Set) m₀
    full = budget m₀ , ≤-refl , trivial

    both : (ty (BAns ⊤Set) & ty (BAns ⊤Set)) m₀
    both = full , full

    -- No alternation charging `c₁ + c₂` -- what `Cost` charges -- exists.
    -- This is a derivation of `⊥`, not a failure to find an inhabitant:
    -- the certificate the combinator returns is a proof of `2n ≤ n`.
    ⊕&-impossible :
      (alt : ty (BAns ⊤Set) & ty (BAns ⊤Set) ⊢ ty (BAns (⊤Set ⊕Set ⊤Set)))
      → alt m₀ both .fst ≡ budget m₀ + budget m₀
      → Empty.⊥
    ⊕&-impossible alt honest =
      no-double (budget m₀) (ofDec≤ m₀)
        (subst (_≤ budget m₀) honest (alt m₀ both .snd .fst))

    -- ...and conjunction is the same combinator with a different output,
    -- so it is the same refutation.  The convention "hang the side
    -- condition on the node with `Ans-&&`" is therefore safe only because
    -- the condition happens to cost 1; the type never said so.
    &&-impossible :
      (cnj : ty (BAns ⊤Set) & ty (BAns ⊤Set) ⊢ ty (BAns (⊤Set &Set ⊤Set)))
      → cnj m₀ both .fst ≡ budget m₀ + budget m₀
      → Empty.⊥
    &&-impossible cnj honest =
      no-double (budget m₀) (ofDec≤ m₀)
        (subst (_≤ budget m₀) honest (cnj m₀ both .snd .fst))

  -- The scope of that negative, stated rather than left to be discovered.
  -- `AnswerFunctor` has no laws, so a combinator may report any cost it
  -- likes; this one reports 0 and typechecks.  Which is why the grading is
  -- a construction on a FIXED set of operations -- the three of
  -- `LinearAnswer`, whose costs are pinned by `Cost` -- and not a property
  -- one could ask an arbitrary answer to satisfy.
  ⊕&-byLying : {s : S} {A : TheorySet ℓA s} {B : TheorySet ℓB s}
    → ty (BAns A) & ty (BAns B) ⊢ ty (BAns (A ⊕Set B))
  ⊕&-byLying m ((_ , _ , a) , (_ , _ , b)) =
    0 , (budget m , +-zero (budget m)) , T.Ans-⊕& m (a , b)
