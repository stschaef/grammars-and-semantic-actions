-- TODO how much of this actually used?
-- WARNING for now I have been treating this as a place to sequester the
-- semantic reasoning about guarded recursion so that importers of this
-- module can work with a clean interface
-- The implementation are subject to change per experiments w Cass
{-# OPTIONS --lossy-unification #-}
-- A memoised `▷`: the delayed hypothesis at a point is a *table* of the
-- values at the points below it, so a recursive query is a lookup rather
-- than a re-derivation.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category.Base
open import Cubical.Algebra.Theory.Finitary
open Category
open SortedSig
open SortedEqns

import Theory.Free.Base as FB
module Theory.Type.Later.Tabulated
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS}
  {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'')
  (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP)
  where

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit* ; tt* ; tt)
open import Cubical.Induction.WellFounded
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Direct.Base
open import Theory.Type.Later.Poset using (PosetDirect)
open import Cubical.Categories.Presheaf.StrictHom.Base
import Cubical.Categories.Direct.StrictDownset as SD

open import Theory.Base σeq V vs 𝒫
open import Theory.Type.Top.Base σeq V vs 𝒫
open import Theory.Type.Lift.Base σeq V vs 𝒫
open import Theory.Type.Later.Indexed σeq V vs 𝒫

open PshHomStrict

private variable ℓA ℓX ℓ< : Level

module _ {X : Type ℓX} {xs : X → S} where

  -- a family's value at a point
  At : IFam xs ℓA → IPt xs → Type ℓA
  At A p = A (p .fst) (p .snd)

  -- the position of a cell in a table
  data _∈ᴾ_ (p : IPt xs) : List (IPt xs) → Type (ℓ-max ℓX ℓM) where
    here  : ∀ {ps} → p ∈ᴾ (p ∷ ps)
    there : ∀ {q ps} → p ∈ᴾ ps → p ∈ᴾ (q ∷ ps)

  -- the memo table: one materialised cell per listed point
  Tbl : IFam xs ℓA → List (IPt xs) → Type ℓA
  Tbl {ℓA = ℓA} A [] = Unit* {ℓA}
  Tbl A (p ∷ ps) = At A p × Tbl A ps

  lookupTbl : {A : IFam xs ℓA} {p : IPt xs} {ps : List (IPt xs)}
    → p ∈ᴾ ps → Tbl A ps → At A p
  lookupTbl here t = t .fst
  lookupTbl (there i) t = lookupTbl i (t .snd)

  tabulateTbl : {A : IFam xs ℓA} → (∀ p → At A p)
    → (ps : List (IPt xs)) → Tbl A ps
  tabulateTbl f [] = tt*
  tabulateTbl f (p ∷ ps) = f p , tabulateTbl f ps

  lookup-tabulate : {A : IFam xs ℓA} (f : ∀ p → At A p)
    {p : IPt xs} {ps : List (IPt xs)} (i : p ∈ᴾ ps)
    → lookupTbl i (tabulateTbl f ps) ≡ f p
  lookup-tabulate f here = refl
  lookup-tabulate f (there i) = lookup-tabulate f i

module _ {X : Type ℓX} (xs : X → S) where

  module _ (O : IPtOrder xs ℓ<) where
    private
      module O = IPtOrder O
      module W = WFOrder (IPtOrder.toWFOrder O)
    open O using (_<_)

    -- the downset of `p` is either empty or the downset of its immediate
    -- predecessor, extended by that predecessor: the memo table grows by one
    -- cell per step, which is what makes it finite and shareable
    data ChainView (below : IPt xs → List (IPt xs)) (p : IPt xs)
      : Type (ℓ-max (ℓ-max ℓX ℓM) ℓ<) where
      minimal : [] Eq.≡ below p → ChainView below p
      extends : (q : IPt xs) → q < p → (q ∷ below q) Eq.≡ below p
        → ChainView below p

    -- an enumeration of the points below each point, presented as a chain
    record Chain : Type (ℓ-max (ℓ-max ℓX ℓM) ℓ<) where
      field
        below : IPt xs → List (IPt xs)
        find  : ∀ {p q} → q < p → q ∈ᴾ below p
        view  : ∀ p → ChainView below p

    module Tabulated (C : Chain) (A : IFam xs ℓA)
      (isSetA : ∀ x m → isSet (A x m)) where
      open Chain C public

      private
        module G = GuardedIndexed xs O
      module L = G.Fam▷ A isSetA

      -- the tabulated later modality
      ▷ᵗ : IFam xs ℓA
      ▷ᵗ x m = Tbl A (below (x , m))

      ▷ᵗapp : ∀ {x m x' m'} → (x' , m') < (x , m) → ▷ᵗ x m → A x' m'
      ▷ᵗapp lt t = lookupTbl (find lt) t

      next⊤ᵗ : L.Point → ∀ x → ⊤Ty ⊢ ▷ᵗ x
      next⊤ᵗ t x m _ = tabulateTbl (λ p → t (p .fst) (p .snd) tt) (below (x , m))

      private
        dir = PosetDirect (IPtOrder.toWFOrder O)

        Â : IPt xs → hSet (ℓ-max ℓA (ℓ-max (ℓIPt xs) ℓ<))
        Â p = LiftTheoryTy (ℓ-max (ℓIPt xs) ℓ<) (A (p .fst)) (p .snd)
            , isOfHLevelLift 2 (isSetA (p .fst) (p .snd))

      -- a table is a delayed hypothesis: read it at every point below
      tabulate : ∀ x → ▷ᵗ x ⊢ L.▷ x
      tabulate x m t .N-ob y (g , q) z h =
        lift (lookupTbl (find (W.≤-<-trans h q)) t)
      tabulate x m t .N-hom y' y g p' p e =
        funExt λ z → funExt λ h →
          cong (λ lt → lift (lookupTbl (find lt) t)) (O.isProp< _ _ _ _)

      module _ (φ : ∀ x → ▷ᵗ x ⊢ A x) where
        private
          -- the shared cell: `t` is a variable, so both its uses are one thunk
          cell : (q : IPt xs) → Tbl A (below q) → Tbl A (q ∷ below q)
          cell q t = φ (q .fst) (q .snd) t , t

          buildView : (p : IPt xs) → (∀ q → q < p → Tbl A (below q))
            → ChainView (below) p → Tbl A (below p)
          buildView p rec (minimal e) = Eq.transport (Tbl A) e tt*
          buildView p rec (extends q lt e) =
            Eq.transport (Tbl A) e (cell q (rec q lt))

        -- the table at `p`, built once from the table at its predecessor
        build : (p : IPt xs) → Acc _<_ p → Tbl A (below p)
        build p (acc r) = buildView p (λ q lt → build q (r q lt)) (view p)

        löbᵗ : L.Point
        löbᵗ x m _ = φ x m (build (x , m) (O.wf< (x , m)))

        private
          tab : (ps : List (IPt xs)) → Tbl A ps
          tab = tabulateTbl (λ p → löbᵗ (p .fst) (p .snd) tt)

          nilCase : (l : List (IPt xs)) (e : [] Eq.≡ l)
            → Eq.transport (Tbl A) e tt* ≡ tab l
          nilCase .[] Eq.refl = refl

          consCase : (l : List (IPt xs)) (q : IPt xs) (e : (q ∷ below q) Eq.≡ l)
            (t : Tbl A (below q))
            → t ≡ build q (O.wf< q) → t ≡ tab (below q)
            → Eq.transport (Tbl A) e (cell q t) ≡ tab l
          consCase .(q ∷ below q) q Eq.refl t p1 p2 i =
            φ (q .fst) (q .snd) (p1 i) , p2 i

        -- every cell of the built table holds the fixed point's value there
        build-tab : (p : IPt xs) (a : Acc _<_ p) → build p a ≡ tab (below p)
        build-tab p (acc r) = helper (view p)
          where
          helper : (v : ChainView (below) p)
            → buildView p (λ q lt → build q (r q lt)) v ≡ tab (below p)
          helper (minimal e) = nilCase (below p) e
          helper (extends q lt e) = consCase (below p) q e (build q (r q lt))
            (cong (build q) (isPropAcc q (r q lt) (O.wf< q)))
            (build-tab q (r q lt))

        -- the guarded fixed-point equation, for the tabulated hypothesis
        löbᵗ-unfold : ∀ x → löbᵗ x ≡ φ x ∘⊢ next⊤ᵗ löbᵗ x
        löbᵗ-unfold x = funExt λ m → funExt λ _ →
          cong (φ x m) (build-tab (x , m) (O.wf< (x , m)))

      -- an ordinary guarded step, solved by the memo table
      module _ (φ : ∀ x → L.▷ x ⊢ A x) where
        löbTab : L.Point
        löbTab = löbᵗ (λ x → φ x ∘⊢ tabulate x)

        private
          φᵗ : ∀ x → ▷ᵗ x ⊢ A x
          φᵗ x = φ x ∘⊢ tabulate x

          -- reading the built table anywhere gives the fixed point's value
          key : (p : IPt xs) (a : Acc _<_ p) {q : IPt xs} (lt : q < p)
            → lookupTbl (find lt) (build φᵗ p a)
              ≡ löbTab (q .fst) (q .snd) tt
          key p a lt = cong (lookupTbl (find lt)) (build-tab φᵗ p a)
                     ∙ lookup-tabulate _ (find lt)

          bridge : ∀ x m → tabulate x m (build φᵗ (x , m) (O.wf< (x , m)))
                         ≡ L.next⊤ löbTab x m tt
          bridge x m = makePshHomStrictPath
            (funExt λ y → funExt λ gq → funExt λ z → funExt λ h →
              cong lift (key (x , m) (O.wf< (x , m))
                (W.≤-<-trans h (gq .snd))))

        -- the tabulated fixed point *is* the untabulated one
        löbTab≡löb : löbTab ≡ L.löb φ
        löbTab≡löb = L.löb-uniq φ löbTab
          (λ x → funExt λ m → funExt λ _ → cong (φ x m) (bridge x m))
