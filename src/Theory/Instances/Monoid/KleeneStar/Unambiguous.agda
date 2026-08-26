{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Is the star of a deterministic factor unambiguous?

   `*Aut≅` -- that an automaton built by `*Aut` parses exactly `KL* A` --
   is commented out in `Automata/Implicit/RegExp/StrongEquivalences.agda`
   with a note that it needs "an unambiguous-* external lemma akin to the
   ⊗ one".  Nothing in either codebase has it.  This file is the attempt.

   The statement, in the hypotheses `*Aut` already demands:

     ¬Nullable A  →  (∀ c → c ∉FollowLast A ⊎ c ∉First A)  →  unambiguous A
       →  unambiguous (A *)

   It is TRUE, and the argument is short.  Suppose `w` has two
   decompositions into `A`-pieces and take the first place they differ:
   one has a piece `u`, the other a piece `u'` with `u` a proper prefix
   of `u'`.  Write `c` for the letter of `u'` just past `u`.  Then

     - the first decomposition continues after `u` with another piece,
       which begins with `c`, so `c ∈ First A`;
     - `u ∈ A` and `u' = u ++ c… ∈ A`, so `c ∈ FollowLast A`.

   Contradiction with the hypothesis.  The two degenerate cases are
   `¬Nullable A` (no empty piece, so nil-vs-cons is impossible) and
   `unambiguous A` (equal pieces have equal parses). -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.KleeneStar.Unambiguous
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.List using ([] ; _∷_ ; _++_ ; ++-unit-r)
open import Cubical.Data.List.Properties
  using (cons-inj₁ ; cons-inj₂ ; ¬cons≡nil ; ¬nil≡cons)
open import Cubical.Data.Sigma using (Σ ; _×_ ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Unit using (tt ; tt*)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar Alphabet isSetAlphabet
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet
  using (¬Nullable)
private variable ℓA ℓB ℓX : Level

-- `∀ m → isProp (A m)`, as `Theory/Type/Unambiguity/Base` states it; named
-- locally because that module reaches here by two paths.
Unambig : TheoryTy ℓA tt → Type _
Unambig A = (m : String) → isProp (A m)

------------------------------------------------------------------------
-- The two letter-set predicates, as the old `SequentialUnambiguity`
-- states them: a refutation rather than a set.

startsWith : Alphabet → TheoryTy ℓM tt
startsWith c = literal c ⊗ ⊤Ty

_∉First_ : Alphabet → TheoryTy ℓA tt → Type _
c ∉First A = startsWith c & A ⊢ ⊥Ty

-- `c` never continues a complete `A` into a longer `A`
_∉FollowLast_ : Alphabet → TheoryTy ℓA tt → Type _
c ∉FollowLast A = ((A ⊗ startsWith c) & A) ⊢ ⊥Ty

-- ...and the pairing the star construction actually demands
SeqUnambig : TheoryTy ℓA tt → Type _
SeqUnambig A = (c : Alphabet) → (c ∉FollowLast A) Sum.⊎ (c ∉First A)

------------------------------------------------------------------------
-- Levi's lemma: two factorisations of one word are nested.
--
-- Not in the codebase anywhere, and it is the combinatorial half of the
-- argument -- it is what produces the letter `c` that the hypothesis
-- then contradicts.

levi : (u v u' v' : String) → u ++ v ≡ u' ++ v'
  → (Σ[ d ∈ String ] ((u' ≡ u ++ d) × (v ≡ d ++ v')))
  Sum.⊎ (Σ[ d ∈ String ] ((u ≡ u' ++ d) × (v' ≡ d ++ v)))
levi [] v u' v' p = Sum.inl (u' , refl , p)
levi (c ∷ u) v [] v' p = Sum.inr (c ∷ u , refl , sym p)
levi (c ∷ u) v (d ∷ u') v' p with levi u v u' v' (cons-inj₂ p)
... | Sum.inl (e , q , r) =
  Sum.inl (e , cong₂ _∷_ (sym (cons-inj₁ p)) q , r)
... | Sum.inr (e , q , r) =
  Sum.inr (e , cong₂ _∷_ (cons-inj₁ p) q , r)

------------------------------------------------------------------------
-- The proof.  `A *` is a real `data`, so both arguments are matched as
-- `roll m (b , payload)` and the tail `f (suc zero) .lower` descends
-- structurally -- no `rec`, no pragma.  This is `Automaton/Unambiguous`'s
-- `unambiguous-Trace` technique; the `PathP`s are built inline, so no
-- tensor-extensionality lemma is needed after all.

-- a proposition at one end of a line of types fills the whole line
isPropPathP : (T : I → Type ℓA) → isProp (T i0)
  → (x : T i0) (y : T i1) → PathP T x y
isPropPathP T pr =
  isProp→PathP (λ i → transport (λ j → isProp (T (i ∧ j))) pr)

module Star* {A : TheoryTy ℓA tt}
  (nu : ¬Nullable A) (su : SeqUnambig A) (ua : Unambig A) where

  private
    -- an `A` piece is never empty, so a nil layer never meets a cons layer
    nil-cons : {X : Type ℓX} (u v : String) → A u → (u ++ v) ≡ [] → X
    nil-cons [] v a p = Empty.rec (nu [] (a , εTy-pt) .lower)
    nil-cons (c ∷ u) v a p = Empty.rec (¬cons≡nil p)

    -- a nonempty `A` head of a word beginning `c` begins with `c`
    headStarts : (c : Alphabet) (hd tl v : String)
      → A hd → (hd ++ tl) ≡ (c ∷ v) → startsWith c hd
    headStarts c [] tl v a p = Empty.rec (nu [] (a , εTy-pt) .lower)
    headStarts c (b ∷ hd) tl v a p =
      two (b ∷ []) hd , Eq.refl
      , (Eq.pathToEq (cong (_∷ []) (cons-inj₁ p)) , (tt , tt*))

    -- The letter just past the shorter of two first pieces.  It follows a
    -- complete `A` inside a longer `A`, and it opens the next piece of the
    -- other decomposition -- so `SeqUnambig` refutes it either way.
    clash : {X : Type ℓX} (c : Alphabet) (d x v : String)
      → (c ∉FollowLast A) Sum.⊎ (c ∉First A)
      → A x → A (x ++ c ∷ d) → (A *) (c ∷ v) → X
    clash c d x v (Sum.inl nfl) a a2 as =
      Empty.rec (nfl (x ++ c ∷ d)
        ( (two x (c ∷ d) , Eq.refl
          , (a , ((two (c ∷ []) d , Eq.refl , (Eq.refl , (tt , tt*))) , tt*)))
        , a2) .lower)
    clash c d x v (Sum.inr nf) a a2 (roll ._ (false , ps , ep , _)) =
      Empty.rec (¬nil≡cons (Eq.eqToPath ep))
    clash c d x v (Sum.inr nf) a a2 (roll ._ (true , ps , ep , g)) =
      Empty.rec (nf (ps zero)
        ( headStarts c (ps zero) (ps (suc zero)) v (g zero .lower)
            (Eq.eqToPath ep)
        , g zero .lower) .lower)

    -- Levi, with the two degenerate ends read off and the two proper ones
    -- refuted: the first pieces, and hence the tails, agree.
    piecesFrom : (u w u' w' : String) → A u → (A *) w → A u' → (A *) w'
      → (Σ[ d ∈ String ] ((u' ≡ u ++ d) × (w ≡ d ++ w')))
        Sum.⊎ (Σ[ d ∈ String ] ((u ≡ u' ++ d) × (w' ≡ d ++ w)))
      → (u ≡ u') × (w ≡ w')
    piecesFrom u w u' w' a as a' as' (Sum.inl ([] , q , r)) =
      sym (++-unit-r u) ∙ sym q , r
    piecesFrom u w u' w' a as a' as' (Sum.inl (c ∷ d , q , r)) =
      clash c d u (d ++ w') (su c) a (subst A q a') (subst (A *) r as)
    piecesFrom u w u' w' a as a' as' (Sum.inr ([] , q , r)) =
      q ∙ ++-unit-r u' , sym r
    piecesFrom u w u' w' a as a' as' (Sum.inr (c ∷ d , q , r)) =
      clash c d u' (d ++ w) (su c) a' (subst A q a) (subst (A *) r as')

    -- the nil layer is nullary, and its index equation is a proposition
    isPropNil : (m : String)
      → isProp (⟦ starBranch A false ⟧TheoryTy (λ _ → A *) m)
    isPropNil m (ms , e , u) (ns , e' , u') =
      ΣPathP (funExt (λ ())
        , ΣPathP ( isProp→PathP (λ _ → isPropEqString) e e'
                 , isPropPathP _ (λ p q → funExt λ ()) u u'))

  unambig : (m : String) (x y : (A *) m) → x ≡ y
  -- nil / nil
  unambig m (roll .m (false , z)) (roll .m (false , z')) =
    cong (roll m) (ΣPathP (refl , isPropNil m z z'))
  -- nil / cons
  unambig m (roll .m (false , ms , e , f)) (roll .m (true , ns , e' , f')) =
    nil-cons (ns zero) (ns (suc zero)) (f' zero .lower)
      (Eq.eqToPath e' ∙ sym (Eq.eqToPath e))
  -- cons / nil
  unambig m (roll .m (true , ms , e , f)) (roll .m (false , ns , e' , f')) =
    nil-cons (ms zero) (ms (suc zero)) (f zero .lower)
      (Eq.eqToPath e ∙ sym (Eq.eqToPath e'))
  -- cons / cons.  The recursive call stands in the clause body: through a
  -- `where` binding the checker compares the tail against the parameter
  -- rather than against the constructor pattern, and loses the descent.
  unambig m (roll .m (true , ms , e , f)) (roll .m (true , ns , e' , f')) =
    main (unambig (ns (suc zero))
           (transport (λ i → (A *) (tails i)) (f (suc zero) .lower))
           (f' (suc zero) .lower))
    where
    split : ms zero ++ ms (suc zero) ≡ ns zero ++ ns (suc zero)
    split = Eq.eqToPath e ∙ sym (Eq.eqToPath e')

    pieces : (ms zero ≡ ns zero) × (ms (suc zero) ≡ ns (suc zero))
    pieces =
      piecesFrom (ms zero) (ms (suc zero)) (ns zero) (ns (suc zero))
        (f zero .lower) (f (suc zero) .lower)
        (f' zero .lower) (f' (suc zero) .lower)
        (levi (ms zero) (ms (suc zero)) (ns zero) (ns (suc zero)) split)

    heads : ms zero ≡ ns zero
    heads = pieces .fst

    tails : ms (suc zero) ≡ ns (suc zero)
    tails = pieces .snd

    sp : ms ≡ ns
    sp = funExt λ where
      zero → heads
      (suc zero) → tails

    main : transport (λ i → (A *) (tails i)) (f (suc zero) .lower)
             ≡ f' (suc zero) .lower
         → roll m (true , ms , e , f) ≡ roll m (true , ns , e' , f')
    main h =
      cong (roll m) (ΣPathP (refl , λ i → sp i , eqP i , λ a → gP a i))
      where
      eqP : PathP (λ i → op _⊙_ (sp i) Eq.≡ m) e e'
      eqP = isProp→PathP (λ i → isPropEqString) e e'

      tP : PathP (λ i → (A *) (tails i))
             (f (suc zero) .lower) (f' (suc zero) .lower)
      tP = toPathP h

      gP : (a : Fin 2)
        → PathP (λ i → ⟦ two (k A) (Var tt) a ⟧TheoryTy (λ _ → A *) (sp i a))
            (f a) (f' a)
      gP zero =
        isPropPathP _ (isOfHLevelLift 1 (ua (ms zero))) (f zero) (f' zero)
      gP (suc zero) = λ i → lift (tP i)

unambiguous-* : {A : TheoryTy ℓA tt}
  → ¬Nullable A → SeqUnambig A → Unambig A → Unambig (A *)
unambiguous-* nu su ua = Star*.unambig nu su ua
