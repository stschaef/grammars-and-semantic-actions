{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A parser generator for *any* grammar whose every production begins with a
   terminal.  `Combinator.Productions` asks for an LL(1) table; this asks
   only for the guard, and takes the alternatives with `_<|>_`.

   `_<|>_` is not a committed choice: both branches are decisions at the
   same suffixes, so an ambiguous grammar is decided exactly, and only the
   *tree* returned is left-biased.  The side condition is `Guarded`: every
   production is `[]` or `term c ∷ β`, which is what makes `call`'s strict
   continuation payable and is the whole of the totality argument. -}
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Combinator.Greibach
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  where

open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (tt)
open import Cubical.Relation.Nullary using (Discrete ; yes ; no)

open import Theory.Data.Listing using (Listing ; Mem ; hd ; tl)
open import Theory.Instances.Monoid.Productions Alphabet _≟_
  using (Grammar ; module Productions ; Sym ; term ; non ; konst ; noKonst)
open import Theory.Instances.Monoid.Combinator.Base Alphabet _≟_ (ℓ-suc ℓAlph)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⟦⊗e⟧ ; ⟦⊗e⟧⁻)

module Gen (G : Grammar) where
  open Grammar G using (Nt ; K)
  open Productions G

  ------------------------------------------------------------------------
  -- The side condition: a production leads with a terminal, or is empty.

  data Lead : List (Sym K Nt) → Type ℓAlph where
    leadε : Lead []
    leadT : (c : Alphabet) (β : List (Sym K Nt)) → Lead (term c ∷ β)

  record Guarded : Type ℓAlph where
    field
      lead : (x : Nt) (t : Tag x) → Lead (prod x t)
      tags : (x : Nt) → Listing (Tag x)
      -- the combinators parse terminals and nonterminals; an opaque symbol
      -- carries its own `Parser`, which is not one of them
      noK  : K → Empty.⊥

  ------------------------------------------------------------------------
  -- The grammars: a nonterminal's trees, a symbol's, a body's.

  TreeSet : Nt → TheorySet ℓG tt
  TreeSet x = Tree x , isSetμ F isSetF x

  symSet : (s : Sym K Nt) → TheorySet ℓG tt
  symSet s =
    ⟦ symCode s ⟧TheoryTy Tree
    , isSet⟦ symCode s ⟧ (isSetSym s) Tree (isSetμ F isSetF)

  seqSet : (β : List (Sym K Nt)) → TheorySet ℓG tt
  seqSet β =
    ⟦ seqCode β ⟧TheoryTy Tree
    , isSet⟦ seqCode β ⟧ (isSetSeq β) Tree (isSetμ F isSetF)

  -- The alternatives of one nonterminal, as a right-nested binary sum over
  -- a listing of its tags: what `_<|>_` builds.
  AltsSet : (x : Nt) → List (Tag x) → TheorySet ℓG tt
  AltsSet x [] = ⊥Ty↑ ℓG , isSet⊥Ty↑
  AltsSet x (t ∷ ts) = seqSet (prod x t) ⊕Set AltsSet x ts

  module _ (x : Nt) where

    -- ...and its two halves against `μ`
    outAlts : (ts : List (Tag x)) → ty (AltsSet x ts) ⊢ Tree x
    outAlts [] = ⊥Ty-elim ∘⊢ lowerG
    outAlts (t ∷ ts) = ⊕-elim (roll ∘⊢ σ⊕ t) (outAlts ts)

    inAlts : {t : Tag x} {ts : List (Tag x)}
      → Mem t ts → ty (seqSet (prod x t)) ⊢ ty (AltsSet x ts)
    inAlts hd = inl
    inAlts (tl m) = inr ∘⊢ inAlts m

  module _ (Γ : Guarded) where
    open Guarded Γ

    ------------------------------------------------------------------------
    -- The parsers, mutually: `&ᴰ` bundles the family and Löb is taken there.

    Pall : TheorySet _ tt
    Pall = &ᴰSet λ x → ParserSet false false (TreeSet x)

    call : (y : Nt) → ty (▷ Pall) ⊢ Parser true true (TreeSet y)
    call y = mkP pApp ∘⊢ ▷map {b = true} (π y)

    tokP : (c : Alphabet) → ty (▷ Pall) ⊢ Parser true false (symSet (term c))
    tokP c = mapP liftG lowerG ∘⊢ tok c

    symbP : (s : Sym K Nt) → ty (▷ Pall) ⊢ Parser true true (symSet s)
    symbP (term c) = pless ∘⊢ tokP c
    symbP (non y) = mapP liftG lowerG ∘⊢ call y
    symbP (konst i) = Empty.rec (noK i)

    -- a body in tail position: every symbol may be a nonterminal, so the
    -- answer is only promised at strict suffixes
    tailP : (β : List (Sym K Nt)) → ty (▷ Pall) ⊢ Parser false true (seqSet β)
    tailP [] = pless ∘⊢ mapP liftG lowerG ∘⊢ nil
    tailP (s ∷ []) = pmore ∘⊢ symbP s
    tailP (s ∷ s' ∷ β) =
      mapP (⟦⊗e⟧⁻ (symCode s) (seqCode (s' ∷ β)))
           (⟦⊗e⟧ (symCode s) (seqCode (s' ∷ β)))
      ∘⊢ seq (seqSet (s' ∷ β)) (symbP s) (tailP (s' ∷ β))

    -- ...and a whole production, where the leading terminal pays for it
    bodyP : {β : List (Sym K Nt)} → Lead β
      → ty (▷ Pall) ⊢ Parser false false (seqSet β)
    bodyP leadε = mapP liftG lowerG ∘⊢ nil
    bodyP (leadT c []) = pmore ∘⊢ tokP c
    bodyP (leadT c (s' ∷ β)) =
      mapP (⟦⊗e⟧⁻ (symCode (term c)) (seqCode (s' ∷ β)))
           (⟦⊗e⟧ (symCode (term c)) (seqCode (s' ∷ β)))
      ∘⊢ seq (seqSet (s' ∷ β)) (tokP c) (tailP (s' ∷ β))

    altsP : (x : Nt) (ts : List (Tag x))
      → ty (▷ Pall) ⊢ Parser false false (AltsSet x ts)
    altsP x [] = mapP liftG lowerG ∘⊢ fail
    altsP x (t ∷ ts) = bodyP (lead x t) <|> altsP x ts

    step : ty (▷ Pall) ⊢ ty Pall
    step = &ᴰ-intro λ x →
      mapP (outAlts x (tags x .fst)) (into x) ∘⊢ altsP x (tags x .fst)
      where
      into : (x : Nt) → Tree x ⊢ ty (AltsSet x (tags x .fst))
      into x = ⊕ᴰ-elim (λ t → inAlts x (tags x .snd t)) ∘⊢ unroll F x

    parsers : ⊤Ty ⊢ ty Pall
    parsers = löbG {A = Pall} step

    decide : (x : Nt) → Decidable (Tree x)
    decide x = runP (π x ∘⊢ parsers)

------------------------------------------------------------------------
-- A surface, where the guard is not a side condition but the shape of a
-- production: one is `ε!`, or a terminal followed by anything.  A grammar
-- written this way is total by construction, and its tags are positions in
-- the list, so they are discrete and listed for free.

private variable ℓ : Level

data Pos {A : Type ℓ} : List A → Type ℓ where
  posz : {a : A} {as : List A} → Pos (a ∷ as)
  poss : {a : A} {as : List A} → Pos as → Pos (a ∷ as)

at : {A : Type ℓ} (as : List A) → Pos as → A
at (a ∷ as) posz = a
at (a ∷ as) (poss i) = at as i

posList : {A : Type ℓ} (as : List A) → List (Pos as)
posList [] = []
posList (a ∷ as) = posz ∷ map poss (posList as)

posListing : {A : Type ℓ} (as : List A) (i : Pos as) → Mem i (posList as)
posListing (a ∷ as) posz = hd
posListing (a ∷ as) (poss i) = tl (memMap (posListing as i))
  where
  memMap : {i : Pos as} {l : List (Pos as)} → Mem i l → Mem (poss i) (map poss l)
  memMap hd = hd
  memMap (tl p) = tl (memMap p)

private
  isZ : {A : Type ℓ} {a : A} {as : List A} → Pos (a ∷ as) → Bool
  isZ posz = true
  isZ (poss _) = false

  posPred : {A : Type ℓ} {a : A} {as : List A} → Pos (a ∷ as) → Pos as → Pos as
  posPred posz d = d
  posPred (poss i) d = i

discretePos : {A : Type ℓ} (as : List A) → Discrete (Pos as)
discretePos (a ∷ as) posz posz = yes refl
discretePos (a ∷ as) posz (poss j) = no λ p → true≢false (cong isZ p)
discretePos (a ∷ as) (poss i) posz = no λ p → true≢false (cong isZ (sym p))
discretePos (a ∷ as) (poss i) (poss j) with discretePos as i j
... | yes p = yes (cong poss p)
... | no ¬p = no λ p → ¬p (cong (λ z → posPred z i) p)

module FromLists
  {Nt : Type ℓ-zero} (isSetNt : isSet Nt)
  where

  -- a production, guarded: `ε!`, or one terminal and then any symbols
  infixr 5 _◂_
  data GProd : Type ℓAlph where
    ε!  : GProd
    _◂_ : Alphabet → List (Sym Empty.⊥ Nt) → GProd

  bodyOf : GProd → List (Sym Empty.⊥ Nt)
  bodyOf ε! = []
  bodyOf (c ◂ β) = term c ∷ β

  module _ (prods : Nt → List GProd) where

    theGrammar : Grammar
    theGrammar .Grammar.Nt = Nt
    theGrammar .Grammar.isSetNt = isSetNt
    theGrammar .Grammar.K = Empty.⊥
    theGrammar .Grammar.kon = noKonst
    theGrammar .Grammar.Tags x = Pos (prods x)
    theGrammar .Grammar.discreteTag x = discretePos (prods x)
    theGrammar .Grammar.bodies x t = bodyOf (at (prods x) t)

    open Gen theGrammar public

    guarded : Guarded
    guarded .Guarded.lead x t = go (at (prods x) t)
      where
      go : (p : GProd) → Lead (bodyOf p)
      go ε! = leadε
      go (c ◂ β) = leadT c β
    guarded .Guarded.tags x = posList (prods x) , posListing (prods x)
    guarded .Guarded.noK ()

    -- the parser: `Tree x ⊕ ¬Ty (Tree x)` at every word
    parse : (x : Nt) → Decidable (Tree x)
    parse = decide guarded
