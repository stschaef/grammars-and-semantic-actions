{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Unambiguity of a deterministic automaton's traces: at a fixed state and
   word there is at most one trace.

   Proved by direct induction on the trace, not through `Trace≅string`: a
   splitting here is a `Fin 2 → String`, which has no η, so the algebra
   squares of a retraction would all need explicit `PathP`s anyway.  The
   induction is the one of `Implicit/Disjointness`'s `TraceDisj`, one level
   stronger: both `stop` -- the payloads and the acceptance equations are
   propositions; `stop` against `step` -- refuted by `lit⊗-nil`; both `step`
   -- the letters and the splittings agree by the precision of `literal`
   (`flat` + cons-injectivity) and the tails by the inductive hypothesis. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Automaton.Unambiguous
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Bool using (Bool ; isSetBool)
open import Cubical.Data.Unit using (tt ; tt* ; Unit* ; isPropUnit*)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
import Cubical.Data.List.Properties as L
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Equality.More using (isSet→isSetEq)

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.Strings Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet
  using (flat ; lit⊗-nil)
open import Theory.Instances.Monoid.Automaton.Deterministic
  Alphabet isSetAlphabet

private variable ℓA : Level

-- a proposition at one end of a line of types fills the whole line
isPropPathP : (T : I → Type ℓA) → isProp (T i0)
  → (x : T i0) (y : T i1) → PathP T x y
isPropPathP T pr =
  isProp→PathP (λ i → transport (λ j → isProp (T (i ∧ j))) pr)

-- the empty splitting is nullary, and its index equation is a proposition
isPropεTy : (m : String) → isProp (εTy m)
isPropεTy m =
  isPropΣ (λ f g → funExt λ ()) λ _ → isProp× isPropEqString isPropUnit*

module _ {Q : Type ℓAlph} (Aut : DeterministicAutomaton Q) where
  open DeterministicAutomaton Aut

  unambiguous-Trace : (b : Bool) (q : Q) (w : String)
    (t t' : Trace b q w) → t ≡ t'
  -- stop / stop
  unambiguous-Trace b q w (roll .w (stop p , x)) (roll .w (stop p' , x')) =
    cong (roll w)
      (ΣPathP
        ( cong stop (isSet→isSetEq isSetBool p p')
        , isPropPathP _ (isOfHLevelLift 1 (isPropεTy w)) x x'))
  -- stop / step
  unambiguous-Trace b q w (roll .w (stop p , x)) (roll .w (step d , ns , e' , f')) =
    Empty.rec (lit⊗-nil d (ns zero) (ns (suc zero))
                 (f' zero .lower)
                 (e' Eq.∙ Eq.sym (x .lower .snd .fst)))
  -- step / stop
  unambiguous-Trace b q w (roll .w (step c , ms , e , f)) (roll .w (stop p' , x')) =
    Empty.rec (lit⊗-nil c (ms zero) (ms (suc zero))
                 (f zero .lower)
                 (e Eq.∙ Eq.sym (x' .lower .snd .fst)))
  -- step / step
  unambiguous-Trace b q w (roll .w (step c , ms , e , f)) (roll .w (step d , ns , e' , f')) =
    -- the recursive call stands in the clause body: a `where` binding would
    -- hide the structural descent on `f' (suc zero)` from the checker
    main (unambiguous-Trace b (δ q d) (ns (suc zero))
           (transport (λ i → Fam i) (f (suc zero) .lower))
           (f' (suc zero) .lower))
    where
    headc : c ∷ ms (suc zero) ≡ w
    headc = flat c (ms zero) (ms (suc zero)) w (f zero .lower) e

    headd : d ∷ ns (suc zero) ≡ w
    headd = flat d (ns zero) (ns (suc zero)) w (f' zero .lower) e'

    heads : c ∷ ms (suc zero) ≡ d ∷ ns (suc zero)
    heads = headc ∙ sym headd

    c≡d : c ≡ d
    c≡d = L.cons-inj₁ heads

    tails : ms (suc zero) ≡ ns (suc zero)
    tails = L.cons-inj₂ heads

    sp : ms ≡ ns
    sp = funExt λ where
      zero →
        Eq.eqToPath (f zero .lower)
        ∙ cong (_∷ []) c≡d
        ∙ sym (Eq.eqToPath (f' zero .lower))
      (suc zero) → tails

    eqP : PathP (λ i → op _⊙_ (sp i) Eq.≡ w) e e'
    eqP = isProp→PathP (λ i → isPropEqString) e e'

    -- the line of types the two tails live over
    Fam : I → Type (ℓ-max (ℓF ℓM) ℓAlph)
    Fam i = Trace b (δ q (c≡d i)) (sp i (suc zero))

    main : transport (λ i → Fam i) (f (suc zero) .lower) ≡ f' (suc zero) .lower
      → roll w (step c , ms , e , f) ≡ roll w (step d , ns , e' , f')
    main h =
      cong (roll w) (ΣPathP (cong step c≡d , λ i → sp i , eqP i , λ a → gP a i))
      where
      tP : PathP Fam (f (suc zero) .lower) (f' (suc zero) .lower)
      tP = toPathP h

      gP : (a : Fin 2)
        → PathP (λ i → ⟦ two (k (literal (c≡d i))) (Var (δ q (c≡d i))) a ⟧TheoryTy
                         (Trace b) (sp i a))
            (f a) (f' a)
      gP zero = isPropPathP _ (isOfHLevelLift 1 isPropEqString) (f zero) (f' zero)
      gP (suc zero) = λ i → lift (tP i)

  -- ...i.e. `Trace b q` is unambiguous in the sense of `Unambiguity/Base`
  unambiguousTrace : (b : Bool) (q : Q) → unambiguous (Trace b q)
  unambiguousTrace b q m = unambiguous-Trace b q m

  -- and therefore subterminal: any two maps into it agree
  subterminalTrace : (b : Bool) (q : Q) → subterminal (Trace b q)
  subterminalTrace b q = unambiguous→subterminal (unambiguousTrace b q)
