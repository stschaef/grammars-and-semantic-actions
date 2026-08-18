{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Dyck where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Maybe as M

open import Theory.Instances.Monoid.Grammars.Dyck
  using (Br ; lp ; rp ; _≟_ ; dyckBranch ; dyckF ; isSetDyckF
        ; Dyck ; done ; nest)
open import Theory.Instances.Monoid.Combinator.Base Br _≟_ (ℓ-suc ℓ-zero)
open import Theory.Instances.Monoid.Residual Br isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻)
import Theory.Instances.Monoid.SemanticAction Br isSetAlphabet as SemAct

------------------------------------------------------------------------
-- Everything between these delimiters is boilerplate and should be
-- moved
------------------------------------------------------------------------
S : TheoryTy _ tt
S = μ dyckF tt

isSetS : isSetTheoryTy S
isSetS = isSetμ dyckF isSetDyckF tt

Node : TheoryTy _ tt
Node = literal lp ⊗ (S ⊗ (literal rp ⊗ S))

Body : TheoryTy _ tt
Body = Node ⊕ εTy

private
  NodeCode : TheoryTy _ tt
  NodeCode = ⟦ dyckBranch true ⟧TheoryTy (μ dyckF)

  nodeIn : Node ⊢ NodeCode
  nodeIn =
    ⟦⊗e⟧⁻ _ _ ∘⊢ (liftTy ,⊗ (⟦⊗e⟧⁻ _ _ ∘⊢ (liftTy ,⊗
      (⟦⊗e⟧⁻ _ _ ∘⊢ (liftTy ,⊗ liftTy)))))

  nodeOut : NodeCode ⊢ Node
  nodeOut =
    (lowerTy ,⊗ ((lowerTy ,⊗ ((lowerTy ,⊗ lowerTy) ∘⊢ ⟦⊗e⟧ _ _)) ∘⊢ ⟦⊗e⟧ _ _))
    ∘⊢ ⟦⊗e⟧ _ _

rollS : Body ⊢ S
rollS = ⊕-elim (roll ∘⊢ σ⊕ true ∘⊢ nodeIn) (roll ∘⊢ σ⊕ false ∘⊢ liftTy)

unrollS : S ⊢ Body
unrollS = fromF ∘⊢ unroll dyckF tt
  where
  fromF : ⟦ dyckF tt ⟧TheoryTy (μ dyckF) ⊢ Body
  fromF = ⊕ᴰ-elim λ where
    true → inl ∘⊢ nodeOut
    false → inr ∘⊢ lowerTy

Sset : TheorySet ℓG tt
Sset = S , isSetS

module P = Fix Sset

-- what the inner `S` is followed by
afterS : TheorySet ℓG tt
afterS = litSet rp ⊗Set Sset

-- what a `(` is followed by
afterLp : TheorySet ℓG tt
afterLp = Sset ⊗Set afterS

------------------------------------------------------------------------
-- End boilerplate
------------------------------------------------------------------------

-- Using parser combinators to get a sound and complete Dyck parser
step : ty (▷ (ParserSet false false Sset)) ⊢ Parser false false Sset
step = mapP rollS unrollS ∘⊢ ((pmore ∘⊢ nodeP) <|> nil)
  where
  -- `) S`
  tail′ : ty (▷ (ParserSet false false Sset)) ⊢ Parser true false afterS
  tail′ = seq Sset (tok rp) P.call

  -- `S ) S`
  mid : ty (▷ (ParserSet false false Sset)) ⊢ Parser true true afterLp
  mid = seq afterS P.call (pless ∘⊢ tail′)

  -- `( S ) S`
  nodeP : ty (▷ (ParserSet false false Sset))
    ⊢ Parser true false (litSet lp ⊗Set afterLp)
  nodeP = seq afterLp (tok lp) mid

decDyck : Decidable S
decDyck = P.decide step

-- Some tests running it

no-lp : ¬Ty S (lp ∷ [])
no-lp = theNo (decDyck (lp ∷ []) tt) Eq.refl

no-rp : ¬Ty S (rp ∷ [])
no-rp = theNo (decDyck (rp ∷ []) tt) Eq.refl

dyck-cover : Cover Bool (DecCover S)
dyck-cover = decisionCover decDyck

nilTree : S []
nilTree = (rollS ∘⊢ inr) [] εTy-pt

nil-not-refuted : ¬Ty S [] → Empty.⊥*
nil-not-refuted no = no nilTree

semactS : SemanticAction S Dyck
semactS = semact-rec alg tt
  where
  ΔD : Unit → TheoryTy ℓ-zero tt
  ΔD _ = SemAct.Δ Dyck

  nodeVal : ⟦ dyckBranch true ⟧TheoryTy ΔD ⊢ SemAct.Δ Dyck
  nodeVal m (ms , e , xs) =
    nest (xs (suc zero) .snd .snd zero .lower .fst)
         (xs (suc zero) .snd .snd (suc zero) .snd .snd (suc zero) .lower .fst)
    , tt

  alg : (x : Unit) → ⟦ dyckF x ⟧TheoryTy ΔD ⊢ ΔD x
  alg _ = ⊕ᴰ-elim λ where
    true → nodeVal
    false → semact-pure done

parseDyck : String → M.Maybe Dyck
parseDyck = observe decDyck (semact-dec semactS)

dyck-trees : passes
  (parseDyck at
    ( []                                 ↦ M.just done
    ∷ (lp ∷ rp ∷ [])                     ↦ M.just (nest done done)
    ∷ (lp ∷ rp ∷ lp ∷ rp ∷ [])           ↦ M.just (nest done (nest done done))
    ∷ (lp ∷ lp ∷ rp ∷ rp ∷ [])           ↦ M.just (nest (nest done done) done)
    ∷ (lp ∷ lp ∷ rp ∷ lp ∷ rp ∷ rp ∷ []) ↦
        M.just (nest (nest done (nest done done)) done)
    ∷ (lp ∷ lp ∷ lp ∷ rp ∷ rp ∷ rp ∷ []) ↦
        M.just (nest (nest (nest done done) done) done)
    ∷ [] ))
dyck-trees = refl

dyck-no-trees : passes
  (parseDyck at
    ( (lp ∷ [])                   ↦ M.nothing
    ∷ (rp ∷ [])                   ↦ M.nothing
    ∷ (lp ∷ lp ∷ rp ∷ [])         ↦ M.nothing
    ∷ (lp ∷ rp ∷ rp ∷ [])         ↦ M.nothing
    ∷ [] ))
dyck-no-trees = refl
