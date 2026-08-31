{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Arithmetic expressions, as one recursive-descent parser, for every answer.

   Two mutually recursive nonterminals tied by Löb at their `&ᴰ`, and two
   ways of choosing a production: `Exp` is *routed* -- one token names the
   branch -- while `Exp'` is nullable, so its ε-branch cannot be predicted
   and is `_<|>_`d instead.  Both are answer-generic: the route is a plain
   table in `ArithGrammar`, and what an answer must supply to commit on one
   is `CommittingAnswer`.

   Instantiating gives a decider, a `Maybe`-parser or an enumeration of
   every parse -- see `Grammars/ArithTests`. -}
open import Cubical.Foundations.Prelude
open import Theory.Instances.Monoid.Combinator.Grammars.ArithGrammar
  using (Tok ; nm ; pl ; lb ; rb ; _≟T_)
import Theory.Instances.Monoid.Combinator.Core Tok _≟T_ as C

module Theory.Instances.Monoid.Combinator.Grammars.Arith
  (𝒯 : C.AnswerFunctor)
  (div : C.DivariantAnswer 𝒯)
  (com : C.CommittingAnswer 𝒯)
  where

open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Combinator.Grammars.ArithGrammar public
open C.Combinators 𝒯 public
open C.DivCombinators 𝒯 div public
open C.RoutedCombinators 𝒯 div com public

module CE = Choice (decTag Exp) (Cb Exp)
module F = FixAll ℓG LangSet

private
  -- a literal, relabelled to the lifted `literal` the grammar's body uses
  tokL : {ℓD : Level} {D : TheoryTy ℓD tt} (c : Tok)
    → D ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ (lit↑ c)
  tokL c = mapP± liftTy lowerTy ∘⊢ tok c

  altExp : (t : Tag Exp) → ty (▷ F.Pall) ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (Cb Exp t)
  altExp enum = pmore ∘⊢ seq (LangSet Exp') (tokL nm) (F.callAt Exp')
  altExp eparen = pmore ∘⊢ seq (LangSet Exp') inner (F.callAt Exp')
    where
    inner : ty (▷ F.Pall)
      ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ ((lit↑ lb ⊗Set LangSet Exp) ⊗Set lit↑ rb)
    inner = seq (lit↑ rb)
              (seq (LangSet Exp) (tokL lb) (F.callAt Exp))
              (pless ∘⊢ tokL rb)

  expP : ty (▷ F.Pall) ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (LangSet Exp)
  expP = mapP± (rollN Exp) (unrollN Exp) ∘⊢ CE.choose gExp altExp

  exp'P : ty (▷ F.Pall) ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (LangSet Exp')
  exp'P = mapP± rollE' unrollE' ∘⊢ (addP <|> doneP)
    where
    addP : ty (▷ F.Pall) ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (Cb Exp' add)
    addP = pmore ∘⊢ seq (LangSet Exp) (tokL pl) (F.callAt Exp)

    doneP : ty (▷ F.Pall) ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (Cb Exp' done)
    doneP = mapP± liftTy lowerTy ∘⊢ nil

    rollE' : ty (Cb Exp' add) ⊕ ty (Cb Exp' done) ⊢ Lang Exp'
    rollE' = rollN Exp' ∘⊢ ⊕-elim (σ⊕ add) (σ⊕ done)

    unrollE' : Lang Exp' ⊢ ty (Cb Exp' add) ⊕ ty (Cb Exp' done)
    unrollE' = ⊕ᴰ-elim (λ where done → inr ; add → inl) ∘⊢ unrollN Exp'

step : ty (▷ F.Pall) ⊢ ty F.Pall
step = &ᴰ-intro λ where
  Exp  → expP
  Exp' → exp'P

answer : (N : NT) → ⊤Ty ⊢ ty (Ans (LangSet N))
answer = F.runAt step

arith : ⊤Ty ⊢ ty (Ans (LangSet Exp))
arith = answer Exp
