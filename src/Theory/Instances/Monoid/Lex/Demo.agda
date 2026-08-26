{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A lexicon with multi-character keywords, over real Unicode text, at `refl`.

   The alphabet is `Unicode.Base`'s internal `UChar`, so `c ≟ d` reduces;
   `String.Unicode`'s postulated oracle would leave every branch stuck.
   Keyword-before-identifier priority is `<|>`'s left bias, and skipping is
   the action's `nothing`. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Lex.Demo where

open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.Maybe as M
open import Cubical.Data.Unit using (tt)
import Agda.Builtin.String as AS

open import Theory.Instances.Monoid.Unicode.Base
open import Theory.Instances.Monoid.Lex.Base UChar _≟U_ (ℓ-suc ℓ-zero)

data Tok : Type ℓ-zero where
  KLet KIn : Tok
  Var : UChar → Tok

-- `l e t`, `i n`, a skipped space, and a catch-all -- in that order, which
-- is what makes `let` one token rather than three variables.
LetG : TheorySet ℓM tt
LetG = litSet (ch 'l') ⊗Set (litSet (ch 'e') ⊗Set litSet (ch 't'))

InG : TheorySet ℓM tt
InG = litSet (ch 'i') ⊗Set litSet (ch 'n')

TokSet : TheorySet ℓM tt
TokSet = LetG ⊕Set (InG ⊕Set (litSet (ch ' ') ⊕Set charSet))

oneTok : {ℓ' : Level} → ⊤Ty ⊢ Parser ℓ' ⟨▷⟩ ⟨□⟩ TokSet
oneTok =
  seq (litSet (ch 'e') ⊗Set litSet (ch 't')) (tok (ch 'l'))
      (seq (litSet (ch 't')) (pless ∘⊢ tok (ch 'e')) (pless ∘⊢ tok (ch 't')))
  <|> (seq (litSet (ch 'n')) (tok (ch 'i')) (pless ∘⊢ tok (ch 'n'))
  <|> (tok (ch ' ') <|> anyTok))

emit : Emit {T = Tok} {A = ty TokSet}
emit =
  semact-⊕ (semact-pure (M.just KLet))
  (semact-⊕ (semact-pure (M.just KIn))
  (semact-⊕ (semact-pure M.nothing)
            (semact-map (λ c → M.just (Var c)) semact-char)))

lexDemo : AS.String → M.Maybe (List Tok)
lexDemo s = lex {T = Tok} TokSet oneTok emit (text s)

------------------------------------------------------------------------
-- ...and it runs, on text written the way it is read.

_ : lexDemo "" ≡ M.just []
_ = refl

_ : lexDemo "x" ≡ M.just (Var (ch 'x') ∷ [])
_ = refl

-- three characters, one token
_ : lexDemo "let" ≡ M.just (KLet ∷ [])
_ = refl

-- ...but a prefix of the keyword is not the keyword: the rules fall through
_ : lexDemo "le" ≡ M.just (Var (ch 'l') ∷ Var (ch 'e') ∷ [])
_ = refl

-- whitespace is skipped by the action, not by the grammar
_ : lexDemo "let x" ≡ M.just (KLet ∷ Var (ch 'x') ∷ [])
_ = refl
