{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A lexer is a regex, and its parser.

   Nothing here has a semantic action.  A lexicon is a list of token
   regexes; the token stream is their alternation, starred; and the parse
   tree of that regex *is* the tokenisation -- which rule matched, over
   which characters, in order.  There is nothing left to compute.

   Actions belong to the next phase, carrying these parse trees into
   whatever the front end wants; they are not part of lexing.

   What is missing is that this is not yet *greedy*.  `anyOfr` is ordered
   choice, so the star finds *a* tokenisation rather than the
   maximal-munch one.  That gap is exactly `Greedy` (`Greedy/Base`), which
   needs derivative completeness -- so "the lexer is a greedy regex" is
   one theorem away from being literally the definition below. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Lex.Regex
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)

open import Theory.Instances.Monoid.Regex.Notation Alphabet _≟_ ℓ public

-- A lexicon: the token regexes, in priority order.  Each must consume,
-- which the index enforces -- a nullable rule would let the stream stand
-- still.
Lexicon : Type ℓAlph
Lexicon = List (RE notNullable)

-- one token
tokenRE : Lexicon → RE notNullable
tokenRE = anyOfr

-- ...and the stream, which is the lexer's grammar
tokensRE : Lexicon → RE nullable
tokensRE rs = tokenRE rs *r

-- the lexer: the parser for that regex.  A `yes` is the tokenisation, a
-- `no` refutes every tokenisation.
lexer : (rs : Lexicon) → Decidable (ty ⟦ tokensRE rs ⟧)
lexer rs = decide-r (tokensRE rs) ℓ

-- the tokenisation itself, when there is one
Tokenisation : (rs : Lexicon) → String → Type (lv (tokensRE rs))
Tokenisation rs w = ty ⟦ tokensRE rs ⟧ w

NoTokenisation : (rs : Lexicon) → String → Type (lv (tokensRE rs))
NoTokenisation rs w = ¬Ty (ty ⟦ tokensRE rs ⟧) w

------------------------------------------------------------------------
-- Reading the tokenisation back out.
--
-- This is the bridge to the next phase, not part of lexing: the tree
-- already *is* the answer, and these just display it.  `yield` recovers
-- the characters a regex matched, and `which` additionally reports the
-- rule, so a token is a rule index and its lexeme.

yield : ∀ {n} (r : RE n) → SemanticAction (ty ⟦ r ⟧) (List Alphabet)
yield εr = semact-pure []
yield ⊥r = ⊥Ty-elim
yield ⟨ c ⟩r = semact-pure (c ∷ [])
yield (satr P) = λ m x → (x .fst .fst ∷ []) , tt
yield (r ⊗r r') =
  semact-map (λ p → p .fst ++ p .snd) (semact-⊗₂ (yield r) (yield r'))
yield (r ⊕r r') = semact-⊕ (yield r) (yield r')
yield (r *r) = semact-map cat (semact-* (yield r))
  where
  cat : List (List Alphabet) → List Alphabet
  cat [] = []
  cat (w ∷ ws) = w ++ cat ws

-- which rule matched, and what it took
which : (rs : Lexicon) → SemanticAction (ty ⟦ tokenRE rs ⟧) (ℕ × List Alphabet)
which [] = ⊥Ty-elim
which (r ∷ []) = semact-map (λ w → 0 , w) (yield r)
which (r ∷ rs@(_ ∷ _)) =
  semact-⊕ (semact-map (λ w → 0 , w) (yield r))
           (semact-map (λ p → suc (p .fst) , p .snd) (which rs))

tokens : (rs : Lexicon)
       → SemanticAction (ty ⟦ tokensRE rs ⟧) (List (ℕ × List Alphabet))
tokens rs = semact-* (which rs)
