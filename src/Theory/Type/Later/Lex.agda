-- TODO how much of this actually used?
-- See `Theory/Type/Later/Indexed` for what this directory is for and how
-- settled it is.
{- The lexicographic product of two well-founded orders. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSet× ; isProp×)
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr ; isProp⊎)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no ; Discrete)
open import Cubical.Categories.Direct.Base using (WFOrder)

module Theory.Type.Later.Lex where

private variable ℓA ℓ<A ℓB ℓ<B : Level

module _ {ℓA ℓ<A ℓB ℓ<B} (WA : WFOrder ℓA ℓ<A) (WB : WFOrder ℓB ℓ<B) where
  private
    module A = WFOrder WA
    module B = WFOrder WB

  -- the first component drops, or it does not and the second drops
  _<lex_ : A.D × B.D → A.D × B.D → Type (ℓ-max ℓ<A (ℓ-max ℓA ℓ<B))
  p <lex q = (p .fst A.< q .fst) ⊎ ((p .fst ≡ q .fst) × (p .snd B.< q .snd))

  -- the two disjuncts exclude each other, so the sum is a prop
  isProp<lex : ∀ p q → isProp (p <lex q)
  isProp<lex p q = isProp⊎ (A.isProp< _ _)
    (isProp× (A.isSetD _ _) (B.isProp< _ _))
    λ lt (e , _) → A.¬<refl (subst (p .fst A.<_) (sym e) lt)

  trans<lex : ∀ {p q r} → p <lex q → q <lex r → p <lex r
  trans<lex (inl u) (inl v) = inl (A.trans< u v)
  trans<lex (inl u) (inr (e , _)) = inl (subst (_ A.<_) e u)
  trans<lex (inr (e , _)) (inl v) = inl (subst (A._< _) (sym e) v)
  trans<lex (inr (e , u)) (inr (e' , v)) = inr (e ∙ e' , B.trans< u v)

  -- the double `Acc` induction: outer on the first component, inner on the
  -- second, which is restarted whenever the first one drops
  wf<lex : WellFounded _<lex_
  wf<lex p = goA (p .fst) (A.wf< (p .fst)) (p .snd) (B.wf< (p .snd))
    where
    goB : (a : A.D) → (∀ a' → a' A.< a → ∀ b' → Acc _<lex_ (a' , b'))
        → ∀ b → Acc B._<_ b → Acc _<lex_ (a , b)
    goB a ih b (acc rb) = acc λ where
      q (inl lt) → ih (q .fst) lt (q .snd)
      q (inr (e , lt)) → subst (λ z → Acc _<lex_ (z , q .snd)) (sym e)
        (goB a ih (q .snd) (rb (q .snd) lt))

    goA : (a : A.D) → Acc A._<_ a → ∀ b → Acc B._<_ b → Acc _<lex_ (a , b)
    goA a (acc ra) = goB a λ a' lt b' → goA a' (ra a' lt) b' (B.wf< b')

  lexWFOrder : WFOrder (ℓ-max ℓA ℓB) (ℓ-max ℓ<A (ℓ-max ℓA ℓ<B))
  lexWFOrder = record
    { D = A.D × B.D ; isSetD = isSet× A.isSetD B.isSetD ; _<_ = _<lex_
    ; isProp< = isProp<lex ; trans< = trans<lex ; wf< = wf<lex }

  -- decidable when each comparison is, plus equality on the first component
  dec<lex : Discrete A.D → (∀ a a' → Dec (a A.< a'))
    → (∀ b b' → Dec (b B.< b')) → ∀ p q → Dec (p <lex q)
  dec<lex dA decA decB p q with decA (p .fst) (q .fst)
  ... | yes lt = yes (inl lt)
  ... | no ¬lt with dA (p .fst) (q .fst)
  ...   | no ¬e = no (Sum.rec ¬lt λ z → ¬e (z .fst))
  ...   | yes e with decB (p .snd) (q .snd)
  ...     | yes lt' = yes (inr (e , lt'))
  ...     | no ¬lt' = no (Sum.rec ¬lt λ z → ¬lt' (z .snd))
