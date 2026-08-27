{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `unambiguous (A *)`, from `¬Nullable A`, `SeqUnambig A` and
   `unambiguous A` -- the hypotheses `*Aut` already demands.

   Two decompositions of `w` into `A`-pieces that differ have a first
   difference: one piece `u` is a proper prefix of the other `u'`.  The
   letter `c` just past `u` then both opens the next piece (`c ∈ First A`)
   and continues `u` into `u'` (`c ∈ FollowLast A`), which `SeqUnambig`
   refutes.  `¬Nullable A` kills nil-vs-cons and `unambiguous A` equal
   pieces. -}
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
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (splitAgree)
open import Theory.Instances.Monoid.SequentialUnambiguity.FollowLast
  Alphabet isSetAlphabet
  using (startsWith ; _∉First_ ; _∉FollowLast_ ; ∉First*) public
private variable ℓA ℓB ℓX : Level

-- `∀ m → isProp (A m)`, as `Theory/Type/Unambiguity/Base` states it; named
-- locally because that module reaches here by two paths.
Unambig : TheoryTy ℓA tt → Type _
Unambig A = (m : String) → isProp (A m)

-- The pairing the star construction demands.  `_∉First_`,
-- `_∉FollowLast_` and `startsWith` come from `SequentialUnambiguity`; the
-- combinatorial half -- Levi, and the clash it produces -- is
-- `Precise.splitAgree`.

SeqUnambig : TheoryTy ℓA tt → Type _
SeqUnambig A = (c : Alphabet) → (c ∉FollowLast A) Sum.⊎ (c ∉First A)

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

    -- the two decompositions cut in the same place: `c` would have to
    -- both follow a complete `A` and open the next piece
    pieces : SeqUnambig A → (u w u' w' : String)
      → A u → (A *) w → A u' → (A *) w' → u ++ w ≡ u' ++ w'
      → (u ≡ u') × (w ≡ w')
    pieces su u w u' w' a as a' as' p =
      splitAgree sep sep u w u' w' p a as a' as'
      where
      sep : (g : Alphabet)
        → (g ∉FollowLast A) Sum.⊎ (g ∉First (A *))
      sep g = Sum.map (λ z → z) ∉First* (su g)

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

    parts : (ms zero ≡ ns zero) × (ms (suc zero) ≡ ns (suc zero))
    parts =
      pieces su (ms zero) (ms (suc zero)) (ns zero) (ns (suc zero))
        (f zero .lower) (f (suc zero) .lower)
        (f' zero .lower) (f' (suc zero) .lower) split

    heads : ms zero ≡ ns zero
    heads = parts .fst

    tails : ms (suc zero) ≡ ns (suc zero)
    tails = parts .snd

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
