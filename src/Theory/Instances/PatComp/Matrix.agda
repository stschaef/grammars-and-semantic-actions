{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Clause matrices, the two matrix transformations Maranget's algorithm
   runs on, and the measure that makes it terminate.

   `Match` decides "does this value match this pattern".  This client
   compiles a whole clause MATRIX into a decision tree, so the object it
   analyses is a rectangle of patterns and not a pattern, and the recursion
   is on COLUMNS rather than on either argument of `Match`.  Nothing of the
   object language is new: `Pat` and `Val` are imported unchanged, and the
   only thing added is the width -- a row is a list of patterns terminated
   by the right-hand side it selects, and `Row n` is indexed by how many
   columns it spans.

   SPECIALISATION AND DEFAULT are the two moves.  `spec o P` keeps the rows
   whose first pattern can meet a value headed by `o`, expands `o`'s
   arguments into fresh columns, and deletes the rest; `dflt P` keeps the
   rows whose first pattern is a wildcard and drops the column.  Neither is
   a subterm of `P` under any signature -- that is exactly why this client
   is a machine, and why `Ans-re` appears where `Ans-node` would.

   THE MEASURE is the one thing that has to be got right before any of it
   can be written down, and the naive candidate does not work: total
   pattern size can GROW under specialisation, since a wildcard in the head
   column becomes `arity o` wildcards.  What does not grow is the number of
   CONSTRUCTOR NODES -- `psize` scores a wildcard zero -- and it strictly
   DROPS whenever the constructor specialised on actually occurs in the
   head column, which is the only case the algorithm ever specialises in.
   The default matrix deletes exactly the rows the wildcards do not cover,
   so it never grows the count either, but when the head column is all
   wildcards it deletes nothing and the count stands still.  That residual
   case is what the width is for: `dflt` always loses a column.  Hence the
   lexicographic pair (constructor nodes, width) in `Guard`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
module Theory.Instances.PatComp.Matrix where

open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; _or_ ; not
  ; Bool→Type ; isSetBool)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Maybe using (Maybe ; just ; nothing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ ; +-assoc
  ; +-suc)
import Cubical.Data.Nat.Order as NO
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt)

open import Theory.Instances.Match.Judgment using
  ( VOp ; vtrueOp ; vfalseOp ; vpairOp ; VAr
  ; Val ; vtrue ; vfalse ; vpair ; clsV
  ; Pat ; pwild ; pvar ; ptrue ; pfalse ; ppair ; isSetPat
  ; Env ; inst ; Match ) public

private variable n : ℕ

-- A row: one pattern per column, then the right-hand side it selects.
infixr 5 _◂_
infix 6 ⇒_

data Row : ℕ → Type ℓ-zero where
  ⇒_ : ℕ → Row 0
  _◂_ : {n : ℕ} → Pat → Row n → Row (suc n)

rhsOf : Row n → ℕ
rhsOf (⇒ k) = k
rhsOf (_ ◂ ρ) = rhsOf ρ

Mat : ℕ → Type ℓ-zero
Mat n = List (Row n)

private
  toR : Row n → List Pat × ℕ
  toR (⇒ k) = [] , k
  toR (p ◂ ρ) = (p ∷ toR ρ .fst) , toR ρ .snd

  fromR : (n : ℕ) → List Pat × ℕ → Row n
  fromR zero (_ , k) = ⇒ k
  fromR (suc n) ([] , k) = pwild ◂ fromR n ([] , k)
  fromR (suc n) (p ∷ ps , k) = p ◂ fromR n (ps , k)

  rowRet : (r : Row n) → fromR n (toR r) ≡ r
  rowRet (⇒ k) = refl
  rowRet (p ◂ ρ) = cong (p ◂_) (rowRet ρ)

isSetRow : isSet (Row n)
isSetRow {n} = isOfHLevelRetract 2 toR (fromR n) rowRet
  (isSet× (isOfHLevelList 0 isSetPat) isSetℕ)

isSetMat : isSet (Mat n)
isSetMat = isOfHLevelList 0 isSetRow


-- The scrutinee side: one value per column.
infixr 5 _▸_

data Vals : ℕ → Type ℓ-zero where
  ⟨⟩ : Vals 0
  _▸_ : {n : ℕ} → Val → Vals n → Vals (suc n)

-- ...and the head value's arguments, pushed onto the front.  The type is
-- the whole point: `VAr (clsV v) + n` is `n` at a constant and `2 + n` at
-- a pair, definitionally, so no coercion is needed anywhere downstream.
peel : (v : Val) → Vals n → Vals (VAr (clsV v) + n)
peel vtrue vs = vs
peel vfalse vs = vs
peel (vpair a b) vs = a ▸ b ▸ vs


-- Matching, as a decision, and the matrix semantics the compiler is
-- answerable to: the first row that fires.
pmatch : Pat → Val → Bool
pmatch pwild _ = true
pmatch (pvar _) _ = true
pmatch ptrue vtrue = true
pmatch ptrue vfalse = false
pmatch ptrue (vpair _ _) = false
pmatch pfalse vtrue = false
pmatch pfalse vfalse = true
pmatch pfalse (vpair _ _) = false
pmatch (ppair _ _) vtrue = false
pmatch (ppair _ _) vfalse = false
pmatch (ppair p q) (vpair a b) = pmatch p a and pmatch q b

rowMatches : Row n → Vals n → Bool
rowMatches (⇒ _) ⟨⟩ = true
rowMatches (p ◂ ρ) (v ▸ vs) = pmatch p v and rowMatches ρ vs

sel : Bool → ℕ → Maybe ℕ → Maybe ℕ
sel true k _ = just k
sel false _ m = m

matrixRun : Mat n → Vals n → Maybe ℕ
matrixRun [] vs = nothing
matrixRun (r ∷ P) vs = sel (rowMatches r vs) (rhsOf r) (matrixRun P vs)


-- `pmatch` is `Match`, decided.  Stated so that the semantics above is
-- answerable to the judgment `Match` already fixed, and not to a second
-- notion of matching invented here.
private
  andSplit : (b c : Bool) → Bool→Type (b and c)
           → Bool→Type b × Bool→Type c
  andSplit true c h = tt , h

  andJoin : (b c : Bool) → Bool→Type b → Bool→Type c → Bool→Type (b and c)
  andJoin true c _ h = h

  matchSelf : (p : Pat) (e : Env p) → Bool→Type (pmatch p (inst p e))
  matchSelf pwild _ = tt
  matchSelf (pvar _) _ = tt
  matchSelf ptrue _ = tt
  matchSelf pfalse _ = tt
  matchSelf (ppair p q) (e , f) =
    andJoin _ _ (matchSelf p e) (matchSelf q f)

matchTo : (p : Pat) (v : Val) → Match p v → Bool→Type (pmatch p v)
matchTo p v (e , q) = subst (λ w → Bool→Type (pmatch p w)) q (matchSelf p e)

matchFrom : (p : Pat) (v : Val) → Bool→Type (pmatch p v) → Match p v
matchFrom pwild v _ = v , refl
matchFrom (pvar _) v _ = v , refl
matchFrom ptrue vtrue _ = tt , refl
matchFrom pfalse vfalse _ = tt , refl
matchFrom (ppair p q) (vpair a b) h =
    ( matchFrom p a (andSplit _ _ h .fst) .fst
    , matchFrom q b (andSplit _ _ h .snd) .fst)
  , cong₂ vpair (matchFrom p a (andSplit _ _ h .fst) .snd)
                (matchFrom q b (andSplit _ _ h .snd) .snd)


-- The head column, read one row at a time and then over the matrix.  A
-- wildcard has no head, so it contributes to no constructor's cell -- and
-- that asymmetry is exactly what makes the default matrix necessary.
occAt : VOp → Row (suc n) → Bool
occAt vtrueOp (pwild ◂ _) = false
occAt vtrueOp (pvar _ ◂ _) = false
occAt vtrueOp (ptrue ◂ _) = true
occAt vtrueOp (pfalse ◂ _) = false
occAt vtrueOp (ppair _ _ ◂ _) = false
occAt vfalseOp (pwild ◂ _) = false
occAt vfalseOp (pvar _ ◂ _) = false
occAt vfalseOp (ptrue ◂ _) = false
occAt vfalseOp (pfalse ◂ _) = true
occAt vfalseOp (ppair _ _ ◂ _) = false
occAt vpairOp (pwild ◂ _) = false
occAt vpairOp (pvar _ ◂ _) = false
occAt vpairOp (ptrue ◂ _) = false
occAt vpairOp (pfalse ◂ _) = false
occAt vpairOp (ppair _ _ ◂ _) = true

heads : Mat (suc n) → VOp → Bool
heads [] _ = false
heads (r ∷ P) o = occAt o r or heads P o

-- `VOp` is finite, so "the head column is a complete signature" is a
-- conjunction one can write down.  For a signature with an open set of
-- constructors this is the place the algorithm would need a side
-- condition instead.
complete : Mat (suc n) → Bool
complete P = heads P vtrueOp and (heads P vfalseOp and heads P vpairOp)


-- Specialisation.  One clause per (constructor, head pattern) pair, so
-- that both the size lemmas and the semantic lemma in `Correct` reduce
-- without a `with`.
specStep : (o : VOp) → Row (suc n) → Mat (VAr o + n) → Mat (VAr o + n)
specStep vtrueOp (pwild ◂ ρ) Q = ρ ∷ Q
specStep vtrueOp (pvar _ ◂ ρ) Q = ρ ∷ Q
specStep vtrueOp (ptrue ◂ ρ) Q = ρ ∷ Q
specStep vtrueOp (pfalse ◂ _) Q = Q
specStep vtrueOp (ppair _ _ ◂ _) Q = Q
specStep vfalseOp (pwild ◂ ρ) Q = ρ ∷ Q
specStep vfalseOp (pvar _ ◂ ρ) Q = ρ ∷ Q
specStep vfalseOp (ptrue ◂ _) Q = Q
specStep vfalseOp (pfalse ◂ ρ) Q = ρ ∷ Q
specStep vfalseOp (ppair _ _ ◂ _) Q = Q
specStep vpairOp (pwild ◂ ρ) Q = (pwild ◂ pwild ◂ ρ) ∷ Q
specStep vpairOp (pvar _ ◂ ρ) Q = (pwild ◂ pwild ◂ ρ) ∷ Q
specStep vpairOp (ptrue ◂ _) Q = Q
specStep vpairOp (pfalse ◂ _) Q = Q
specStep vpairOp (ppair p q ◂ ρ) Q = (p ◂ q ◂ ρ) ∷ Q

spec : (o : VOp) → Mat (suc n) → Mat (VAr o + n)
spec _ [] = []
spec o (r ∷ P) = specStep o r (spec o P)

dfltStep : Row (suc n) → Mat n → Mat n
dfltStep (pwild ◂ ρ) Q = ρ ∷ Q
dfltStep (pvar _ ◂ ρ) Q = ρ ∷ Q
dfltStep (ptrue ◂ _) Q = Q
dfltStep (pfalse ◂ _) Q = Q
dfltStep (ppair _ _ ◂ _) Q = Q

dflt : Mat (suc n) → Mat n
dflt [] = []
dflt (r ∷ P) = dfltStep r (dflt P)


-- The measure: constructor nodes, wildcards free.
psize : Pat → ℕ
psize pwild = 0
psize (pvar _) = 0
psize ptrue = 1
psize pfalse = 1
psize (ppair p q) = suc (psize p + psize q)

rsize : Row n → ℕ
rsize (⇒ _) = 0
rsize (p ◂ ρ) = psize p + rsize ρ

msize : Mat n → ℕ
msize [] = 0
msize (r ∷ P) = rsize r + msize P

private
  le+ : (a b : ℕ) → b NO.≤ a + b
  le+ a b = a , refl

  <-k+ : {k m l : ℕ} → m NO.< l → k + m NO.< k + l
  <-k+ {k} {m} {l} lt =
    subst (λ z → z NO.≤ k + l) (+-suc k m) (NO.≤-k+ {k = k} lt)

  orCase : {A : Type ℓ-zero} (b c : Bool)
    → (Bool→Type b → A) → (Bool→Type c → A) → Bool→Type (b or c) → A
  orCase true _ f _ _ = f tt
  orCase false _ _ g h = g h

  specStep≤ : (o : VOp) (r : Row (suc n)) (Q : Mat (VAr o + n))
    → msize (specStep o r Q) NO.≤ rsize r + msize Q
  specStep≤ vtrueOp (pwild ◂ ρ) Q = NO.≤-refl
  specStep≤ vtrueOp (pvar _ ◂ ρ) Q = NO.≤-refl
  specStep≤ vtrueOp (ptrue ◂ ρ) Q = NO.≤-sucℕ
  specStep≤ vtrueOp (pfalse ◂ ρ) Q = NO.≤-suc (le+ (rsize ρ) (msize Q))
  specStep≤ vtrueOp (ppair p q ◂ ρ) Q = NO.≤-suc (le+ _ (msize Q))
  specStep≤ vfalseOp (pwild ◂ ρ) Q = NO.≤-refl
  specStep≤ vfalseOp (pvar _ ◂ ρ) Q = NO.≤-refl
  specStep≤ vfalseOp (ptrue ◂ ρ) Q = NO.≤-suc (le+ (rsize ρ) (msize Q))
  specStep≤ vfalseOp (pfalse ◂ ρ) Q = NO.≤-sucℕ
  specStep≤ vfalseOp (ppair p q ◂ ρ) Q = NO.≤-suc (le+ _ (msize Q))
  specStep≤ vpairOp (pwild ◂ ρ) Q = NO.≤-refl
  specStep≤ vpairOp (pvar _ ◂ ρ) Q = NO.≤-refl
  specStep≤ vpairOp (ptrue ◂ ρ) Q = NO.≤-suc (le+ (rsize ρ) (msize Q))
  specStep≤ vpairOp (pfalse ◂ ρ) Q = NO.≤-suc (le+ (rsize ρ) (msize Q))
  specStep≤ vpairOp (ppair p q ◂ ρ) Q = NO.≤-trans
    (NO.≤-reflexive
      (cong (_+ msize Q) (+-assoc (psize p) (psize q) (rsize ρ))))
    NO.≤-sucℕ

  specStep< : (o : VOp) (r : Row (suc n)) (Q : Mat (VAr o + n))
    → Bool→Type (occAt o r) → msize (specStep o r Q) NO.< rsize r + msize Q
  specStep< vtrueOp (pwild ◂ ρ) Q ()
  specStep< vtrueOp (pvar _ ◂ ρ) Q ()
  specStep< vtrueOp (ptrue ◂ ρ) Q _ = NO.≤-refl
  specStep< vtrueOp (pfalse ◂ ρ) Q ()
  specStep< vtrueOp (ppair p q ◂ ρ) Q ()
  specStep< vfalseOp (pwild ◂ ρ) Q ()
  specStep< vfalseOp (pvar _ ◂ ρ) Q ()
  specStep< vfalseOp (ptrue ◂ ρ) Q ()
  specStep< vfalseOp (pfalse ◂ ρ) Q _ = NO.≤-refl
  specStep< vfalseOp (ppair p q ◂ ρ) Q ()
  specStep< vpairOp (pwild ◂ ρ) Q ()
  specStep< vpairOp (pvar _ ◂ ρ) Q ()
  specStep< vpairOp (ptrue ◂ ρ) Q ()
  specStep< vpairOp (pfalse ◂ ρ) Q ()
  specStep< vpairOp (ppair p q ◂ ρ) Q _ = NO.≤-reflexive
    (cong suc (cong (_+ msize Q) (+-assoc (psize p) (psize q) (rsize ρ))))

  dfltStep≤ : (r : Row (suc n)) (Q : Mat n)
    → msize (dfltStep r Q) NO.≤ rsize r + msize Q
  dfltStep≤ (pwild ◂ ρ) Q = NO.≤-refl
  dfltStep≤ (pvar _ ◂ ρ) Q = NO.≤-refl
  dfltStep≤ (ptrue ◂ ρ) Q = NO.≤-suc (le+ (rsize ρ) (msize Q))
  dfltStep≤ (pfalse ◂ ρ) Q = NO.≤-suc (le+ (rsize ρ) (msize Q))
  dfltStep≤ (ppair p q ◂ ρ) Q = NO.≤-suc (le+ _ (msize Q))

spec≤ : (o : VOp) (P : Mat (suc n)) → msize (spec o P) NO.≤ msize P
spec≤ _ [] = NO.≤-refl
spec≤ o (r ∷ P) = NO.≤-trans (specStep≤ o r (spec o P)) (NO.≤-k+ (spec≤ o P))

-- The strict drop, and the only place the algorithm is allowed to
-- specialise: on a constructor that really is in the head column.
spec< : (o : VOp) (P : Mat (suc n)) → Bool→Type (heads P o)
  → msize (spec o P) NO.< msize P
spec< o (r ∷ P) h = orCase (occAt o r) (heads P o)
  (λ hr → NO.<≤-trans (specStep< o r (spec o P) hr) (NO.≤-k+ (spec≤ o P)))
  (λ hp → NO.≤<-trans (specStep≤ o r (spec o P)) (<-k+ (spec< o P hp)))
  h

dflt≤ : (P : Mat (suc n)) → msize (dflt P) NO.≤ msize P
dflt≤ [] = NO.≤-refl
dflt≤ (r ∷ P) = NO.≤-trans (dfltStep≤ r (dflt P)) (NO.≤-k+ (dflt≤ P))
