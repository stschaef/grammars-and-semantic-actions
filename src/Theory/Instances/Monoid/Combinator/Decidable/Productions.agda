{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A predictive parser generator.  A grammar is an indexed functor; the
   index is the nonterminal, and its productions are the sum its functor
   takes, tagged by `Maybe M₁` -- a lookahead class, or the one
   ε-production a class table cannot name.

   `Prod o` is indexed by the class it predicts, so a body can only be
   given for the class its leading terminal names: a table cannot
   conflict, and the LL(1) condition is what a table *is*.  `&ᴰ` bundles
   several nonterminals so Löb is taken once; `call` answers only at
   strict suffixes and only `tok` restores an answer, which is why `led`
   demands a leading terminal.  `_<|>_` settles nullable nonterminals --
   the class picks the consuming branch, ε is tried only if it refutes. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Decidable.Productions
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.Maybe as MB
open import Cubical.Data.Maybe.Properties using (isOfHLevelMaybe)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt*)

open import Theory.Instances.Monoid.Combinator.Decidable.Lookahead
  Alphabet _≟_ (ℓ-suc ℓAlph) public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻)

isSetM₁ : isSet M₁
isSetM₁ = DiscreteEq→isSet _≟M_

-- a symbol of a production body: a terminal, or another nonterminal
data Item (X : Type ℓAlph) : Type ℓAlph where
  tm : Alphabet → Item X
  nt : X → Item X

-- A production for the class `o`: a body may only be given for the class
-- its leading terminal names, and `none` is a class with no production.
data Prod (X : Type ℓAlph) : M₁ → Type ℓAlph where
  none : {o : M₁} → Prod X o
  led  : {c : Alphabet} → List (Item X) → Prod X (tk c)

record Table (X : Type ℓAlph) : Type ℓAlph where
  field
    at  : (x : X) (o : M₁) → Prod X o    -- which production each class predicts
    nul : X → Bool                       -- ...and which nonterminals derive ε

-- A parse tree, as data.  The class names the production, so a rose tree
-- loses nothing: `node o ts` is "the production this class predicts,
-- applied to the trees its nonterminal items yielded".
data Tree : Type ℓAlph where
  node : M₁ → List Tree → Tree
  eps  : Tree

module Gen {X : Type ℓAlph} (T : Table X) where
  open Table T

  -- The table, as an indexed functor

  itemCode : Item X → Functor ℓM X (λ _ → tt) tt
  itemCode (tm c) = k (literal c)
  itemCode (nt y) = Var y

  bodyCode : List (Item X) → Functor ℓM X (λ _ → tt) tt
  bodyCode [] = k εTy
  bodyCode (i ∷ β) = ⊗e _⊙_ (two (itemCode i) (bodyCode β))

  prodCode : {o : M₁} → Prod X o → Functor ℓM X (λ _ → tt) tt
  prodCode none = k (⊥Ty↑ ℓM)
  prodCode (led {c} β) = bodyCode (tm c ∷ β)

  nulCode : Bool → Functor ℓM X (λ _ → tt) tt
  nulCode true = k εTy
  nulCode false = k (⊥Ty↑ ℓM)

  tagCode : (x : X) → MB.Maybe M₁ → Functor ℓM X (λ _ → tt) tt
  tagCode x MB.nothing = nulCode (nul x)
  tagCode x (MB.just o) = prodCode (at x o)

  F : (x : X) → Functor ℓM X (λ _ → tt) tt
  F x = ⊕e (MB.Maybe M₁) (tagCode x)

  isSetItem : (i : Item X) → isSetValued (itemCode i)
  isSetItem (tm c) = lift (isSetLiteral c)
  isSetItem (nt y) = lift tt*

  isSetBody : (β : List (Item X)) → isSetValued (bodyCode β)
  isSetBody [] = lift isSetεTy
  isSetBody (i ∷ β) zero = isSetItem i
  isSetBody (i ∷ β) (suc zero) = isSetBody β

  isSetProd : {o : M₁} (p : Prod X o) → isSetValued (prodCode p)
  isSetProd none = lift isSet⊥Ty↑
  isSetProd (led {c} β) = isSetBody (tm c ∷ β)

  isSetNul : (b : Bool) → isSetValued (nulCode b)
  isSetNul true = lift isSetεTy
  isSetNul false = lift isSet⊥Ty↑

  isSetTag : (x : X) (m : MB.Maybe M₁) → isSetValued (tagCode x m)
  isSetTag x MB.nothing = isSetNul (nul x)
  isSetTag x (MB.just o) = isSetProd (at x o)

  isSetF : (x : X) → isSetValued (F x)
  isSetF x .fst = lift (isOfHLevelMaybe 0 isSetM₁)
  isSetF x .snd = isSetTag x

  -- ...and as a family of grammars

  S : X → TheoryTy ℓG tt
  S = μ F

  Sset : X → TheorySet ℓG tt
  Sset x = S x , isSetμ F isSetF x

  setOf : (G : Functor ℓM X (λ _ → tt) tt) → isSetValued G → TheorySet ℓG tt
  setOf G sG = ⟦ G ⟧TheoryTy (μ F) , isSet⟦ G ⟧ sG (μ F) (isSetμ F isSetF)

  itemSet : Item X → TheorySet ℓG tt
  itemSet i = setOf (itemCode i) (isSetItem i)

  bodySet : List (Item X) → TheorySet ℓG tt
  bodySet β = setOf (bodyCode β) (isSetBody β)

  prodSet : {o : M₁} (p : Prod X o) → TheorySet ℓG tt
  prodSet p = setOf (prodCode p) (isSetProd p)

  nulSet : (x : X) → TheorySet ℓG tt
  nulSet x = setOf (nulCode (nul x)) (isSetNul (nul x))

  -- one summand per class, which is what `choose` decides
  C : (x : X) (o : M₁) → TheorySet ℓG tt
  C x o = prodSet (at x o)

  -- Each production claims the class its leading terminal names; a class
  -- with no production claims it vacuously.

  leadOf : {o : M₁} (p : Prod X o) → ty (prodSet p) ⊗ ⊤Ty ⊢ Λ₁ o
  leadOf none = ⊥Ty-elim ∘⊢ ⊗⊥-annihL ∘⊢ ((lowerTy ∘⊢ lowerTy) ,⊗ id⊢)
  leadOf (led {c} β) =
    (id⊢ ,⊗ ⊤Ty-intro) ∘⊢ ⊗-assoc
    ∘⊢ (((lowerTy ,⊗ id⊢) ∘⊢ ⟦⊗e⟧ (itemCode (tm c)) (bodyCode β)) ,⊗ id⊢)

  lead : (x : X) (o : M₁) → ty (C x o) ⊗ ⊤Ty ⊢ Λ₁ o
  lead x o = leadOf (at x o)

  module Pred (x : X) = Predictive _≟M_ Λ₁ Λ-cover (C x) (lead x)

  -- the class sum and the ε-production are the two halves of the unrolling
  rollAlt : (x : X) → ty (Pred.Alt x) ⊕ ty (nulSet x) ⊢ S x
  rollAlt x = roll ∘⊢ ⊕-elim (⊕ᴰ-elim λ o → σ⊕ (MB.just o)) (σ⊕ MB.nothing)

  unrollAlt : (x : X) → S x ⊢ ty (Pred.Alt x) ⊕ ty (nulSet x)
  unrollAlt x = ⊕ᴰ-elim br ∘⊢ unroll F x
    where
    br : (m : MB.Maybe M₁)
      → ⟦ tagCode x m ⟧TheoryTy (μ F) ⊢ ty (Pred.Alt x) ⊕ ty (nulSet x)
    br MB.nothing = inr
    br (MB.just o) = inl ∘⊢ σ⊕ o

  -- The parsers, mutually: `&ᴰ` bundles the family, Löb is taken there, and
  -- `call y` reads the y-th component at a strict suffix.

  Pall : TheorySet _ tt
  Pall = &ᴰSet λ x → ParserSet ℓG ⟨□⟩ ⟨□⟩ (Sset x)

  call : (y : X) → ty (▷ Pall) ⊢ Parser ℓG ⟨▷⟩ ⟨▷⟩ (Sset y)
  call y = mkP pApp ∘⊢ ▷map {t = ⟨▷⟩} (π y)

  tokP : (c : Alphabet) → ty (▷ Pall) ⊢ Parser ℓG ⟨▷⟩ ⟨□⟩ (itemSet (tm c))
  tokP c = mapP liftTy lowerTy ∘⊢ tok c

  itemP : (i : Item X) → ty (▷ Pall) ⊢ Parser ℓG ⟨▷⟩ ⟨▷⟩ (itemSet i)
  itemP (tm c) = pless ∘⊢ tokP c
  itemP (nt y) = mapP liftTy lowerTy ∘⊢ call y

  tailP : (β : List (Item X)) → ty (▷ Pall) ⊢ Parser ℓG ⟨□⟩ ⟨▷⟩ (bodySet β)
  tailP [] = pless ∘⊢ mapP liftTy lowerTy ∘⊢ nil
  tailP (i ∷ β) =
    mapP (⟦⊗e⟧⁻ (itemCode i) (bodyCode β)) (⟦⊗e⟧ (itemCode i) (bodyCode β))
    ∘⊢ seq (bodySet β) (itemP i) (tailP β)

  -- the leading terminal is where the step is paid for
  prodP : {o : M₁} (p : Prod X o) → ty (▷ Pall) ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (prodSet p)
  prodP none = mapP (liftTy ∘⊢ liftTy) (lowerTy ∘⊢ lowerTy) ∘⊢ fail
  prodP (led {c} β) =
    mapP (⟦⊗e⟧⁻ (itemCode (tm c)) (bodyCode β))
         (⟦⊗e⟧ (itemCode (tm c)) (bodyCode β))
    ∘⊢ seq (bodySet β) (tokP c) (tailP β)

  -- the ε-production, if there is one, and a refutation if there is not
  nulP : (x : X) → ty (▷ Pall) ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (nulSet x)
  nulP x = go (nul x)
    where
    go : (b : Bool)
      → ty (▷ Pall) ⊢ Parser ℓG ⟨□⟩ ⟨□⟩ (setOf (nulCode b) (isSetNul b))
    go true = mapP liftTy lowerTy ∘⊢ nil
    go false = mapP (liftTy ∘⊢ liftTy) (lowerTy ∘⊢ lowerTy) ∘⊢ fail

  step : ty (▷ Pall) ⊢ ty Pall
  step = &ᴰ-intro λ x →
    mapP (rollAlt x) (unrollAlt x)
    ∘⊢ (Pred.choose x (λ o → prodP (at x o)) <|> nulP x)

  parsers : ⊤Ty ⊢ ty Pall
  parsers = löbG {A = Pall} step

  decide : (x : X) → Decidable (S x)
  decide x = runP ℓG (π x ∘⊢ parsers)

  -- Reading the parse tree out

  private
    Kst : X → TheoryTy ℓAlph tt
    Kst _ _ = Tree

    -- the nonterminal items of a body, in order
    kids : (β : List (Item X)) → ∀ m → ⟦ bodyCode β ⟧TheoryTy Kst m → List Tree
    kids [] m z = []
    kids (tm c ∷ β) m (ms , e , g) = kids β (ms (suc zero)) (g (suc zero))
    kids (nt y ∷ β) m (ms , e , g) =
      g zero .lower ∷ kids β (ms (suc zero)) (g (suc zero))

    readProd : {o : M₁} (p : Prod X o) → ∀ m
      → ⟦ prodCode p ⟧TheoryTy Kst m → Tree
    readProd none m z = Empty.rec* (z .lower .lower)
    readProd (led {c} β) m z = node (tk c) (kids (tm c ∷ β) m z)

    readNul : (b : Bool) → ∀ m → ⟦ nulCode b ⟧TheoryTy Kst m → Tree
    readNul true m z = eps
    readNul false m z = Empty.rec* (z .lower .lower)

    alg : (x : X) → ⟦ F x ⟧TheoryTy Kst ⊢ Kst x
    alg x = ⊕ᴰ-elim br
      where
      br : (m : MB.Maybe M₁) → ⟦ tagCode x m ⟧TheoryTy Kst ⊢ Kst x
      br MB.nothing = readNul (nul x)
      br (MB.just o) = readProd (at x o)

  toTree : (x : X) → S x ⊢ Kst x
  toTree = rec F alg
