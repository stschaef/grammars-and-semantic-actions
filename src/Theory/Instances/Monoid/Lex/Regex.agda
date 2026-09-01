{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The token stream is the lexicon's alternation starred; its parse tree
   IS the tokenisation.  Not greedy: `anyOfr` is ordered choice,
   exponential on rejection; `Automaton/Greedy` does maximal munch in one
   pass but this path has not been rewired onto it. -}
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
open import Theory.Instances.Monoid.Regex.Decide Alphabet _≟_ ℓ public

-- token regexes in priority order; the index forces each to consume, else
-- the stream could stand still
Lexicon : Type ℓAlph
Lexicon = List (RE notNullable)

tokenRE : Lexicon → RE notNullable
tokenRE = anyOfr

tokensRE : Lexicon → RE nullable
tokensRE rs = tokenRE rs *r

-- a `yes` is the tokenisation, a `no` refutes every tokenisation
lexer : (rs : Lexicon) → Decidable (ty ⟦ tokensRE rs ⟧)
lexer rs = decide-r (tokensRE rs) ℓ

Tokenisation : (rs : Lexicon) → String → Type (lv (tokensRE rs))
Tokenisation rs w = ty ⟦ tokensRE rs ⟧ w

NoTokenisation : (rs : Lexicon) → String → Type (lv (tokensRE rs))
NoTokenisation rs w = ¬Ty (ty ⟦ tokensRE rs ⟧) w

-- display only: `yield` gives the lexeme, `which` also the rule index

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

which : (rs : Lexicon) → SemanticAction (ty ⟦ tokenRE rs ⟧) (ℕ × List Alphabet)
which [] = ⊥Ty-elim
which (r ∷ []) = semact-map (λ w → 0 , w) (yield r)
which (r ∷ rs@(_ ∷ _)) =
  semact-⊕ (semact-map (λ w → 0 , w) (yield r))
           (semact-map (λ p → suc (p .fst) , p .snd) (which rs))

tokens : (rs : Lexicon)
       → SemanticAction (ty ⟦ tokensRE rs ⟧) (List (ℕ × List Alphabet))
tokens rs = semact-* (which rs)
