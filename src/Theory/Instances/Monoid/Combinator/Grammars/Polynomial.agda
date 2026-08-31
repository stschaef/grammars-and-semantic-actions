{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Parenthesised multivariate polynomials, as one recursive-descent parser,
   for every answer.

     E ::= ( E ) K | v K | n Q | - E
     Q ::= / m K | + E | * E | ^ n K | ε
     K ::=         + E | * E | ^ n K | ε

   Three mutually recursive nonterminals tied by Löb at their `&ᴰ`, and
   three kinds of choice, all of them answer-generic:

   * `E` is *routed*: `rE` names the production from one token, because
     every `ETag` is determined by the token that starts it.
   * `K` and `Q` are routed on their *head* only -- `pow n` and `den m`
     carry a numeral from the second token, so no one-token table names
     them.  The repair is left-factoring, not a wider window: the `caret`
     and `slash` branches route *again*, over `ℕ`, on the numeral.  That
     inner sum is `PowSet`, and `natP` is the inner `choose`.
   * the ε-production of `K` and `Q` is nullable, so it cannot be
     predicted at all and is `_<|>_`d on instead -- which is always sound.

   Instantiating gives a decider, a `Maybe`-parser or an enumeration of
   every parse -- see `Grammars/PolynomialTests`. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
import Theory.Instances.Monoid.Combinator.Core as C0
import Theory.Instances.Monoid.Combinator.Grammars.PolyGrammar as PG

module Theory.Instances.Monoid.Combinator.Grammars.Polynomial
  (V : Type ℓ-zero)
  (_≟V_ : (a b : V) → (a Eq.≡ b) Sum.⊎ ((a Eq.≡ b) → Empty.⊥))
  (𝒯 : C0.AnswerFunctor (PG.Tok V _≟V_) (PG._≟_ V _≟V_))
  (div : C0.DivariantAnswer (PG.Tok V _≟V_) (PG._≟_ V _≟V_) 𝒯)
  (com : C0.CommittingAnswer (PG.Tok V _≟V_) (PG._≟_ V _≟V_) 𝒯)
  where

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (tt)

open PG V _≟V_ public
open Combinators 𝒯 public
open DivCombinators 𝒯 div public
open RoutedCombinators 𝒯 div com public

PolySet : Nt → TheorySet ℓG tt
PolySet expr = ExprSet
PolySet rest = RestSet
PolySet numTail = NumTailSet

module F = FixAll ℓG PolySet
module ChE = Choice decETag CE
module ChK = Choice decKH CK
module ChQ = Choice decQH CQ
module ChN = Choice decℕEq NatBr

private
  Hyp : TheoryTy _ tt
  Hyp = ty (▷ F.Pall)

  -- `n K`, the numeral a `^` or a `/` is followed by, routed over `ℕ`
  natP : Hyp ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ PowSet
  natP = ChN.choose gN alt
    where
    alt : (n : ℕ) → Hyp ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ (NatBr n)
    alt n = seq RestSet (tok (nat n)) (F.callAt rest)

  -- the three `K`-heads, shared with `Q`
  addP : Hyp ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ (CK hadd)
  addP = seq ExprSet (tok plus) (F.callAt expr)

  mulP : Hyp ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ (CK hmul)
  mulP = seq ExprSet (tok times) (F.callAt expr)

  powP : Hyp ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ (CK hpow)
  powP = seq PowSet (tok caret) (pless ∘⊢ natP)

  -- the ε-production, the one branch no route names
  stopP : Hyp ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (ε↑Set ℓG)
  stopP = mapP± liftTy lowerTy ∘⊢ nil

  altK : (y : KH) → Hyp ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (CK y)
  altK hadd = pmore ∘⊢ addP
  altK hmul = pmore ∘⊢ mulP
  altK hpow = pmore ∘⊢ powP

  altQ : (y : QH) → Hyp ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (CQ y)
  altQ qden = pmore ∘⊢ seq PowSet (tok slash) (pless ∘⊢ natP)
  altQ (qmore h) = altK h

  altE : (t : ETag) → Hyp ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (CE t)
  altE paren = pmore ∘⊢ seq (ExprSet ⊗Set (litSet rp ⊗Set RestSet)) (tok lp) mid
    where
    -- `) K`
    tail′ : Hyp ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ (litSet rp ⊗Set RestSet)
    tail′ = seq RestSet (tok rp) (F.callAt rest)

    -- `E ) K`
    mid : Hyp ⊢ Parser ℓG ⟨▷⟩ ⟨▷⟩ (ExprSet ⊗Set (litSet rp ⊗Set RestSet))
    mid = seq (litSet rp ⊗Set RestSet) (F.callAt expr) (pless ∘⊢ tail′)
  altE (atom v) = pmore ∘⊢ seq RestSet (tok (var v)) (F.callAt rest)
  altE (num n) = pmore ∘⊢ seq NumTailSet (tok (nat n)) (F.callAt numTail)
  altE neg = pmore ∘⊢ seq ExprSet (tok minus) (F.callAt expr)

  exprP : Hyp ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ ExprSet
  exprP = mapP± rollE unrollE ∘⊢ ChE.choose gE altE

  restP : Hyp ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ RestSet
  restP = mapP± rollK unrollK ∘⊢ (ChK.choose gK altK <|> stopP)

  numTailP : Hyp ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ NumTailSet
  numTailP = mapP± rollQ unrollQ ∘⊢ (ChQ.choose gQ altQ <|> stopP)

step : ty (▷ F.Pall) ⊢ ty F.Pall
step = &ᴰ-intro λ where
  expr → exprP
  rest → restP
  numTail → numTailP

answer : (n : Nt) → ⊤Ty ⊢ ty (Ans (PolySet n))
answer = F.runAt step

poly : ⊤Ty ⊢ ty (Ans ExprSet)
poly = answer expr
