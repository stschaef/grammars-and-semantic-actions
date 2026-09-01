{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `sound`: running the tree is running the matrix (Maranget.s specRun/dfltRun).
   Known gap: the converse of redundancy -- every label in the tree is
   reachable -- is NOT proved; it needs a witness-vector construction. -}
open import Cubical.Foundations.Prelude
module Theory.Instances.PatComp.Correct where

open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; _or_
  ; Bool→Type)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty

open import Theory.Instances.PatComp.Judgment public

private
  variable n : ℕ

  selCong : (b : Bool) (k : ℕ) {x y : Maybe ℕ} → x ≡ y → sel b k x ≡ sel b k y
  selCong true k _ = refl
  selCong false k e = e

  andAssoc : (a b c : Bool) → a and (b and c) ≡ (a and b) and c
  andAssoc true b c = refl
  andAssoc false b c = refl

  andSplit : (b c : Bool) → Bool→Type (b and c)
           → Bool→Type b × Bool→Type c
  andSplit true c h = tt , h

  notAnd1 : (x y : Bool) → Bool→Type (not x) → Bool→Type (not (x and y))
  notAnd1 false y _ = tt

  notAnd2 : (x y : Bool) → Bool→Type (not y) → Bool→Type (not (x and y))
  notAnd2 false y _ = tt
  notAnd2 true y h = h

  isJust : Maybe ℕ → Type ℓ-zero
  isJust nothing = Empty.⊥
  isJust (just _) = Unit

  mval : Maybe ℕ → ℕ
  mval nothing = 0
  mval (just k) = k


-- Maranget.s two lemmas.  Only pair-against-pair is not a congruence: the
-- two expanded columns must be reassociated.
specRun : (P : Mat (suc n)) (v : Val) (vs : Vals n)
  → matrixRun (spec (clsV v) P) (peel v vs) ≡ matrixRun P (v ▸ vs)
specRun [] v vs = refl
specRun ((pwild ◂ ρ) ∷ P) vtrue vs = selCong _ _ (specRun P vtrue vs)
specRun ((pvar _ ◂ ρ) ∷ P) vtrue vs = selCong _ _ (specRun P vtrue vs)
specRun ((ptrue ◂ ρ) ∷ P) vtrue vs = selCong _ _ (specRun P vtrue vs)
specRun ((pfalse ◂ ρ) ∷ P) vtrue vs = specRun P vtrue vs
specRun ((ppair _ _ ◂ ρ) ∷ P) vtrue vs = specRun P vtrue vs
specRun ((pwild ◂ ρ) ∷ P) vfalse vs = selCong _ _ (specRun P vfalse vs)
specRun ((pvar _ ◂ ρ) ∷ P) vfalse vs = selCong _ _ (specRun P vfalse vs)
specRun ((ptrue ◂ ρ) ∷ P) vfalse vs = specRun P vfalse vs
specRun ((pfalse ◂ ρ) ∷ P) vfalse vs = selCong _ _ (specRun P vfalse vs)
specRun ((ppair _ _ ◂ ρ) ∷ P) vfalse vs = specRun P vfalse vs
specRun ((pwild ◂ ρ) ∷ P) (vpair x y) vs =
  selCong _ _ (specRun P (vpair x y) vs)
specRun ((pvar _ ◂ ρ) ∷ P) (vpair x y) vs =
  selCong _ _ (specRun P (vpair x y) vs)
specRun ((ptrue ◂ ρ) ∷ P) (vpair x y) vs = specRun P (vpair x y) vs
specRun ((pfalse ◂ ρ) ∷ P) (vpair x y) vs = specRun P (vpair x y) vs
specRun ((ppair p q ◂ ρ) ∷ P) (vpair x y) vs =
    cong (λ b → sel b (rhsOf ρ) (matrixRun (spec vpairOp P) (x ▸ y ▸ vs)))
      (andAssoc (pmatch p x) (pmatch q y) (rowMatches ρ vs))
  ∙ selCong _ _ (specRun P (vpair x y) vs)

dfltRun : (P : Mat (suc n)) (v : Val) (vs : Vals n)
  → Bool→Type (not (heads P (clsV v)))
  → matrixRun (dflt P) vs ≡ matrixRun P (v ▸ vs)
dfltRun [] v vs _ = refl
dfltRun ((pwild ◂ ρ) ∷ P) vtrue vs h = selCong _ _ (dfltRun P vtrue vs h)
dfltRun ((pvar _ ◂ ρ) ∷ P) vtrue vs h = selCong _ _ (dfltRun P vtrue vs h)
dfltRun ((ptrue ◂ ρ) ∷ P) vtrue vs ()
dfltRun ((pfalse ◂ ρ) ∷ P) vtrue vs h = dfltRun P vtrue vs h
dfltRun ((ppair _ _ ◂ ρ) ∷ P) vtrue vs h = dfltRun P vtrue vs h
dfltRun ((pwild ◂ ρ) ∷ P) vfalse vs h = selCong _ _ (dfltRun P vfalse vs h)
dfltRun ((pvar _ ◂ ρ) ∷ P) vfalse vs h = selCong _ _ (dfltRun P vfalse vs h)
dfltRun ((ptrue ◂ ρ) ∷ P) vfalse vs h = dfltRun P vfalse vs h
dfltRun ((pfalse ◂ ρ) ∷ P) vfalse vs ()
dfltRun ((ppair _ _ ◂ ρ) ∷ P) vfalse vs h = dfltRun P vfalse vs h
dfltRun ((pwild ◂ ρ) ∷ P) (vpair x y) vs h =
  selCong _ _ (dfltRun P (vpair x y) vs h)
dfltRun ((pvar _ ◂ ρ) ∷ P) (vpair x y) vs h =
  selCong _ _ (dfltRun P (vpair x y) vs h)
dfltRun ((ptrue ◂ ρ) ∷ P) (vpair x y) vs h = dfltRun P (vpair x y) vs h
dfltRun ((pfalse ◂ ρ) ∷ P) (vpair x y) vs h = dfltRun P (vpair x y) vs h
dfltRun ((ppair _ _ ◂ ρ) ∷ P) (vpair x y) vs ()


-- Dispatch is on the TREE: `heads P o` is never matched on but recovered
-- from the branch shape -- the direction that reduces.
private
  skipClash : (t : Tree) → NotSkip t → Skip t → Empty.⊥
  skipClash tfail _ sk = sk
  skipClash tskip ns _ = ns
  skipClash (tleaf _) _ sk = sk
  skipClash (tswitch _ _ _ _) _ sk = sk

  pickCase : {A : Type ℓ-zero} (t : Tree)
    → (NotSkip t → A) → (Skip t → A) → A
  pickCase tfail f _ = f tt
  pickCase tskip _ g = g tt
  pickCase (tleaf _) f _ = f tt
  pickCase (tswitch _ _ _ _) f _ = f tt

  pickNot : (t : Tree) (x y : Maybe ℕ) → NotSkip t → pick t x y ≡ x
  pickNot tfail x y _ = refl
  pickNot tskip x y ns = Empty.rec ns
  pickNot (tleaf _) x y _ = refl
  pickNot (tswitch _ _ _ _) x y _ = refl

  pickIs : (t : Tree) (x y : Maybe ℕ) → Skip t → pick t x y ≡ y
  pickIs tfail x y sk = Empty.rec sk
  pickIs tskip x y _ = refl
  pickIs (tleaf _) x y sk = Empty.rec sk
  pickIs (tswitch _ _ _ _) x y sk = Empty.rec sk

  brTrue : (b : Bool) (t : Tree) (X : Type ℓ-zero)
    → NotSkip t → Br b t X → X
  brTrue true t X _ (_ , x) = x
  brTrue false t X ns sk = Empty.rec (skipClash t ns sk)

  brSkip : (b : Bool) (t : Tree) (X : Type ℓ-zero)
    → Skip t → Br b t X → Bool→Type (not b)
  brSkip true t X sk (ns , _) = Empty.rec (skipClash t ns sk)
  brSkip false t X _ _ = tt

  dfPresent : (c : Bool) (t : Tree) (X : Type ℓ-zero)
    → Bool→Type (not c) → Df c t X → X
  dfPresent false t X _ (_ , x) = x

  -- a missing head constructor makes the head column an incomplete signature
  completeFalse : (o : VOp) (P : Mat (suc n))
    → Bool→Type (not (heads P o)) → Bool→Type (not (complete P))
  completeFalse vtrueOp P h = notAnd1 (heads P vtrueOp) _ h
  completeFalse vfalseOp P h =
    notAnd2 (heads P vtrueOp) _ (notAnd1 (heads P vfalseOp) _ h)
  completeFalse vpairOp P h =
    notAnd2 (heads P vtrueOp) _ (notAnd2 (heads P vfalseOp) _ h)


-- `peel`/`clsV` make one switch lemma serve all three constructors.
private
  switchSound : (P : Mat (suc n)) (v : Val) (vs : Vals n) (bt dt : Tree)
    → Br (heads P (clsV v)) bt (Ok (VAr (clsV v) + n) bt (spec (clsV v) P))
    → Df (complete P) dt (Ok n dt (dflt P))
    → (Ok (VAr (clsV v) + n) bt (spec (clsV v) P)
       → runTree bt (peel v vs) ≡ matrixRun (spec (clsV v) P) (peel v vs))
    → (Ok n dt (dflt P) → runTree dt vs ≡ matrixRun (dflt P) vs)
    → pick bt (runTree bt (peel v vs)) (runTree dt vs) ≡ matrixRun P (v ▸ vs)
  switchSound P v vs bt dt ob od ihb ihd = pickCase bt
    (λ ns → pickNot bt _ _ ns
          ∙ ihb (brTrue _ bt _ ns ob)
          ∙ specRun P v vs)
    (λ sk → pickIs bt _ _ sk
          ∙ ihd (dfPresent _ dt _
                  (completeFalse (clsV v) P (brSkip _ bt _ sk ob)) od)
          ∙ dfltRun P v vs (brSkip _ bt _ sk ob))

sound : (n : ℕ) (t : Tree) (P : Mat n) → Ok n t P
  → (vs : Vals n) → runTree t vs ≡ matrixRun P vs
sound n tfail [] ok vs = refl
sound n tfail (r ∷ P) ok vs = Empty.rec ok
sound n tskip P ok vs = Empty.rec ok
sound zero (tleaf k) [] ok vs = Empty.rec ok
sound zero (tleaf k) ((⇒ j) ∷ P) ok ⟨⟩ = cong just (sym ok)
sound (suc n) (tleaf k) P ok vs = Empty.rec ok
sound zero (tswitch _ _ _ _) P ok vs = Empty.rec ok
sound (suc n) (tswitch a b c d) P (_ , oa , ob , oc , od) (vtrue ▸ vs) =
  switchSound P vtrue vs a d oa od
    (λ ok → sound n a (spec vtrueOp P) ok vs)
    (λ ok → sound n d (dflt P) ok vs)
sound (suc n) (tswitch a b c d) P (_ , oa , ob , oc , od) (vfalse ▸ vs) =
  switchSound P vfalse vs b d ob od
    (λ ok → sound n b (spec vfalseOp P) ok vs)
    (λ ok → sound n d (dflt P) ok vs)
sound (suc n) (tswitch a b c d) P (_ , oa , ob , oc , od) (vpair x y ▸ vs) =
  switchSound P (vpair x y) vs c d oc od
    (λ ok → sound (suc (suc n)) c (spec vpairOp P) ok (x ▸ y ▸ vs))
    (λ ok → sound n d (dflt P) ok vs)

Agrees : (n : ℕ) → Mat n → Type ℓ-zero
Agrees n P = Σ[ t ∈ Tree ] ((vs : Vals n) → runTree t vs ≡ matrixRun P vs)


noFail : Tree → Bool
noFail tfail = false
noFail tskip = true
noFail (tleaf _) = true
noFail (tswitch a b c d) = noFail a and (noFail b and (noFail c and noFail d))

NoFail : Tree → Type ℓ-zero
NoFail t = Bool→Type (noFail t)

private
  switchHits : {n : ℕ} (P : Mat (suc n)) (v : Val) (vs : Vals n) (bt dt : Tree)
    → Br (heads P (clsV v)) bt (Ok (VAr (clsV v) + n) bt (spec (clsV v) P))
    → Df (complete P) dt (Ok n dt (dflt P))
    → (Ok (VAr (clsV v) + n) bt (spec (clsV v) P)
       → Σ[ k ∈ ℕ ] (runTree bt (peel v vs) ≡ just k))
    → (Ok n dt (dflt P) → Σ[ k ∈ ℕ ] (runTree dt vs ≡ just k))
    → Σ[ k ∈ ℕ ] (pick bt (runTree bt (peel v vs)) (runTree dt vs) ≡ just k)
  switchHits {n} P v vs bt dt ob od ihb ihd = pickCase bt
    (λ ns → ihb (brTrue _ bt _ ns ob) .fst
          , pickNot bt _ _ ns ∙ ihb (brTrue _ bt _ ns ob) .snd)
    (λ sk → ihd (dd sk) .fst , pickIs bt _ _ sk ∙ ihd (dd sk) .snd)
    where
    dd : Skip bt → Ok n dt (dflt P)
    dd sk = dfPresent _ dt _
      (completeFalse (clsV v) P (brSkip _ bt _ sk ob)) od

  hits : (n : ℕ) (t : Tree) (P : Mat n) → Ok n t P → NoFail t
    → (vs : Vals n) → Σ[ k ∈ ℕ ] (runTree t vs ≡ just k)
  hits n tfail P ok ()
  hits n tskip P ok nf vs = Empty.rec ok
  hits zero (tleaf k) P ok nf vs = k , refl
  hits (suc n) (tleaf k) P ok nf vs = Empty.rec ok
  hits zero (tswitch _ _ _ _) P ok nf vs = Empty.rec ok
  hits (suc n) (tswitch a b c d) P (_ , oa , ob , oc , od) nf (vtrue ▸ vs) =
    switchHits P vtrue vs a d oa od
      (λ ok → hits n a (spec vtrueOp P) ok (andSplit _ _ nf .fst) vs)
      (λ ok → hits n d (dflt P) ok (dnf nf) vs)
    where
    dnf : Bool→Type (noFail (tswitch a b c d)) → NoFail d
    dnf h = andSplit _ _ (andSplit _ _ (andSplit _ _ h .snd) .snd) .snd
  hits (suc n) (tswitch a b c d) P (_ , oa , ob , oc , od) nf (vfalse ▸ vs) =
    switchHits P vfalse vs b d ob od
      (λ ok → hits n b (spec vfalseOp P) ok
                (andSplit _ _ (andSplit _ _ nf .snd) .fst) vs)
      (λ ok → hits n d (dflt P) ok (dnf nf) vs)
    where
    dnf : Bool→Type (noFail (tswitch a b c d)) → NoFail d
    dnf h = andSplit _ _ (andSplit _ _ (andSplit _ _ h .snd) .snd) .snd
  hits (suc n) (tswitch a b c d) P (_ , oa , ob , oc , od) nf (vpair x y ▸ vs) =
    switchHits P (vpair x y) vs c d oc od
      (λ ok → hits (suc (suc n)) c (spec vpairOp P) ok
                (andSplit _ _ (andSplit _ _ (andSplit _ _ nf .snd) .snd) .fst)
                (x ▸ y ▸ vs))
      (λ ok → hits n d (dflt P) ok (dnf nf) vs)
    where
    dnf : Bool→Type (noFail (tswitch a b c d)) → NoFail d
    dnf h = andSplit _ _ (andSplit _ _ (andSplit _ _ h .snd) .snd) .snd

exhaustive : (n : ℕ) (t : Tree) (P : Mat n) → Ok n t P → NoFail t
  → (vs : Vals n) → Σ[ k ∈ ℕ ] (matrixRun P vs ≡ just k)
exhaustive n t P ok nf vs = hits n t P ok nf vs .fst
  , sym (sound n t P ok vs) ∙ hits n t P ok nf vs .snd


labels : Tree → List ℕ
labels tfail = []
labels tskip = []
labels (tleaf k) = k ∷ []
labels (tswitch a b c d) = labels a ++ (labels b ++ (labels c ++ labels d))

Mem : ℕ → List ℕ → Type ℓ-zero
Mem k [] = Empty.⊥
Mem k (j ∷ js) = (j ≡ k) Sum.⊎ Mem k js

private
  memL : (k : ℕ) (xs ys : List ℕ) → Mem k xs → Mem k (xs ++ ys)
  memL k (x ∷ xs) ys (Sum.inl e) = Sum.inl e
  memL k (x ∷ xs) ys (Sum.inr h) = Sum.inr (memL k xs ys h)

  memR : (k : ℕ) (xs ys : List ℕ) → Mem k ys → Mem k (xs ++ ys)
  memR k [] ys h = h
  memR k (x ∷ xs) ys h = Sum.inr (memR k xs ys h)

  noJust : {k : ℕ} → nothing ≡ just k → Empty.⊥
  noJust e = subst isJust (sym e) tt

  labelled : (t : Tree) (vs : Vals n) (k : ℕ)
    → runTree t vs ≡ just k → Mem k (labels t)
  labelled tfail vs k e = Empty.rec (noJust e)
  labelled tskip vs k e = Empty.rec (noJust e)
  labelled (tleaf j) vs k e = Sum.inl (cong mval e)
  labelled (tswitch a b c d) ⟨⟩ k e = Empty.rec (noJust e)
  labelled (tswitch a b c d) (vtrue ▸ vs) k e = pickCase a
    (λ ns → memL k (labels a) _
       (labelled a vs k (sym (pickNot a _ _ ns) ∙ e)))
    (λ sk → memR k (labels a) _ (memR k (labels b) _ (memR k (labels c) _
       (labelled d vs k (sym (pickIs a _ _ sk) ∙ e)))))
  labelled (tswitch a b c d) (vfalse ▸ vs) k e = pickCase b
    (λ ns → memR k (labels a) _ (memL k (labels b) _
       (labelled b vs k (sym (pickNot b _ _ ns) ∙ e))))
    (λ sk → memR k (labels a) _ (memR k (labels b) _ (memR k (labels c) _
       (labelled d vs k (sym (pickIs b _ _ sk) ∙ e)))))
  labelled (tswitch a b c d) (vpair x y ▸ vs) k e = pickCase c
    (λ ns → memR k (labels a) _ (memR k (labels b) _ (memL k (labels c) _
       (labelled c (x ▸ y ▸ vs) k (sym (pickNot c _ _ ns) ∙ e)))))
    (λ sk → memR k (labels a) _ (memR k (labels b) _ (memR k (labels c) _
       (labelled d vs k (sym (pickIs c _ _ sk) ∙ e)))))

redundant : (n : ℕ) (t : Tree) (P : Mat n) → Ok n t P → (k : ℕ)
  → (Mem k (labels t) → Empty.⊥)
  → (vs : Vals n) → matrixRun P vs ≡ just k → Empty.⊥
redundant n t P ok k ¬mem vs e =
  ¬mem (labelled t vs k (sound n t P ok vs ∙ e))
