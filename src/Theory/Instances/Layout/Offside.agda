{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The offside rule as a judgment on token streams, written once, for every
   answer.

   The family is indexed by the layout state -- a mode and a stack of open
   block columns -- and the guard descends on the token list.  That is the
   whole claim being tested here: layout is not a grammar in the
   context-free sense, but it *is* syntax-directed in this framework's
   sense, because the state after a token is a function of the state before
   it and of the token's own column.  `⊗ᴰ` is what expresses that, and for
   a one-argument operation it degenerates to exactly a state machine's
   transition function.

   WHAT IS IMPLEMENTED.  Two modes.  In `scanning`, a token at column `c`
   closes every open block whose column exceeds `c` (one `}` each), and
   then, if the innermost surviving block is at column exactly `c`, starts
   a new item there (a `;`).  `klet` and `kwhere` switch to `opening`.  In
   `opening`, the next token's column is pushed and a `{` is emitted; the
   column must strictly exceed the enclosing block's, or the stream is
   rejected.  End of input in `scanning` closes every open block; end of
   input in `opening` is rejected.

   WHAT IS NOT.  Haskell's rule proper, and deliberately -- it is
   underspecified where it matters.  Specifically:

     * No line tracking.  A `;` fires on "column equals the enclosing
       block's", not on "first token of a line".  These agree exactly when
       each line's leftmost token is its first, since a continuation line
       is indented past the block column and columns increase within a
       line; they diverge for a stream that is not the output of a real
       lexer.  Tracking lines means a second ℕ in the token and a
       comparison in the state, not a change of shape.
     * No `parse-error(t)` rule.  Haskell closes an implicit block when the
       enclosing parser would otherwise fail, which makes layout depend on
       the parser it feeds -- a mutual recursion this framework has no
       reason to want.  This is the real omission, and it is visible: a
       one-line `let x = 1 in x` is *accepted*, but its `in` is indented
       past the block, so the `}` lands at the end of input rather than
       before the `in`, and the stream it renders to is one a parser would
       reject.  `OffsideTests`' `oneLine` records exactly that.  Closing on
       `in` means either a token that pops by fiat -- a two-line change,
       and a lie about every other keyword -- or the mutual recursion.
     * No empty blocks.  `let` with nothing indented past it is a rejection
       rather than `{}`.
     * No explicit braces in the input, hence no interaction between them
       and the implicit ones.

   The judgment is defined by RECURSION on the token list, not as an
   indexed `data`, for the reason `Annotated/Typing`'s `Der` is: an indexed
   family gets `UnificationStuck` on the model's constructors, and the
   recursive form additionally makes `isProp` a two-line induction rather
   than a theorem.

   `nilOp` has arity zero, so the "end of input" rule has nowhere to put
   its side condition -- there is no slot to ride along with.  That is what
   `Core`'s `Ans-&&` is for, used here at the *node* rather than at a slot:
   the cell of the cover is `⊗ᴰ o (Slots o S) &Set SideSet o S`, and the
   side condition is what distinguishes `scanning` (accept, close
   everything) from `opening` (reject) at the empty stream.  Stating every
   operation's side condition that way -- rather than only `nilOp`'s --
   keeps `Slots` a pure recursive call and puts all the arithmetic in one
   place.

   Nothing below mentions `Dec`, `Maybe` or `ND`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
module Theory.Instances.Layout.Offside where

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
import Cubical.Data.Nat.Order.Recursive as R
open import Cubical.Data.Sigma using (_×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
open import Cubical.Data.Sum using (isProp⊎)
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Theory.Instances.Layout.Guard public

-- The state.  `opening` is the one bit of memory the rule needs: a block
-- opener does not know its own block's column, because that column belongs
-- to the *next* token.  Everything else is the stack.
data Mode : Type ℓ-zero where
  scanning opening : Mode

private
  modeRep : Mode → Bool
  modeRep scanning = true
  modeRep opening = false

  modeUnrep : Bool → Mode
  modeUnrep true = scanning
  modeUnrep false = opening

  modeRet : (md : Mode) → modeUnrep (modeRep md) ≡ md
  modeRet scanning = refl
  modeRet opening = refl

isSetMode : isSet Mode
isSetMode = isOfHLevelRetract 2 modeRep modeUnrep modeRet isSetBool

Stack : Type ℓ-zero
Stack = List ℕ

LState : Type ℓ-zero
LState = Mode × Stack

isSetLState : isSet LState
isSetLState = isSetΣ isSetMode λ _ → isOfHLevelList 0 isSetℕ

-- Which keywords open a block.
modeAfter : TokKind → Mode
modeAfter klet = opening
modeAfter kwhere = opening
modeAfter kin = scanning
modeAfter keq = scanning
modeAfter (kid _) = scanning

-- The surviving stack after a token at column `c`: every block indented
-- past `c` has ended.  This is a *function* of the index and the token,
-- which is what makes the tail's index computable and the judgment
-- syntax-directed.  It is not read off the derivation, and it could not
-- be: `⊗ᴰ`'s slot indices may mention sibling slots' *model values*, never
-- their proofs.
popTo : ℕ → Stack → Stack
popOn : (c m : ℕ) (ms : Stack) → Dec (m R.≤ c) → Stack

popTo c [] = []
popTo c (m ∷ ms) = popOn c m ms (m R.≤? c)

popOn c m ms (yes _) = m ∷ ms
popOn c m ms (no _) = popTo c ms

-- ...and the proof-relevant counterpart, which *is* read off the
-- derivation.  This is `Annotated/Typing`'s `Lookup` in a different
-- costume: a chain of "this block closes" steps ending in a trichotomy at
-- the first block that survives, and `Render`'s fold turns that chain into
-- the braces and the semicolon rather than recomputing them.  The three
-- ends are mutually exclusive, so it is a proposition and the layout of a
-- stream is unique.
Close : ℕ → Stack → Type ℓ-zero
Close c [] = Unit
Close c (m ∷ ms) =
  ((c R.< m) × Close c ms) Sum.⊎ ((m ≡ c) Sum.⊎ (m R.< c))

isPropClose : (c : ℕ) (ms : Stack) → isProp (Close c ms)
isPropClose c [] = isPropUnit
isPropClose c (m ∷ ms) =
  isProp⊎ (isProp× R.isProp≤ (isPropClose c ms)) inner outer
  where
  inner : isProp ((m ≡ c) Sum.⊎ (m R.< c))
  inner = isProp⊎ (isSetℕ m c) R.isProp≤ λ p q → R.<→≢ {m} {c} q p

  outer : ((c R.< m) × Close c ms) → ((m ≡ c) Sum.⊎ (m R.< c)) → Empty.⊥
  outer (lt , _) (Sum.inl p) = R.¬m<m {c} (subst (c R.<_) p lt)
  outer (lt , _) (Sum.inr q) = R.<-asym {c} {m} lt q

decClose : (c : ℕ) (ms : Stack) → Dec (Close c ms)
decClose c [] = yes tt
decClose c (m ∷ ms) = onTri (m R.≟ c)
  where
  onTri : R.Trichotomy m c → Dec (Close c (m ∷ ms))
  onTri (R.lt q) = yes (Sum.inr (Sum.inr q))
  onTri (R.eq p) = yes (Sum.inr (Sum.inl p))
  onTri (R.gt q) = onRest (decClose c ms)
    where
    onRest : Dec (Close c ms) → Dec (Close c (m ∷ ms))
    onRest (yes w) = yes (Sum.inl (q , w))
    onRest (no ¬w) = no λ where
      (Sum.inl (_ , w)) → ¬w w
      (Sum.inr (Sum.inl p)) → R.¬m<m {c} (subst (c R.<_) p q)
      (Sum.inr (Sum.inr r)) → R.<-asym {c} {m} q r

-- The witness and the function agree: the blocks a `Close` chain steps
-- past are exactly the ones `popTo` drops.  Nothing downstream depends on
-- this -- `popTo` computes the tail's index and `Close` decorates the
-- derivation, and the two never meet -- but if they disagreed the
-- renderer's `}`s would not match the checker's state, so it is the one
-- coherence fact worth stating.
survivors : (c : ℕ) (ms : Stack) → Close c ms → Stack
survivors c [] _ = []
survivors c (m ∷ ms) (Sum.inl (_ , w)) = survivors c ms w
survivors c (m ∷ ms) (Sum.inr _) = m ∷ ms

survivors≡popTo : (c : ℕ) (ms : Stack) (w : Close c ms)
  → survivors c ms w ≡ popTo c ms
survivors≡popTo c [] w = refl
survivors≡popTo c (m ∷ ms) (Sum.inl (q , w)) =
  survivors≡popTo c ms w ∙ sym (onNo (m R.≤? c))
  where
  onNo : (d : Dec (m R.≤ c)) → popOn c m ms d ≡ popTo c ms
  onNo (yes p) = Empty.rec (R.¬m<m {c} (R.≤-trans {suc c} {m} {c} q p))
  onNo (no _) = refl
survivors≡popTo c (m ∷ ms) (Sum.inr e) = sym (onYes (m R.≤? c))
  where
  le : m R.≤ c
  le = Sum.rec (λ p → subst (m R.≤_) p (R.≤-refl m)) (R.<-weaken {m} {c}) e

  onYes : (d : Dec (m R.≤ c)) → popOn c m ms d ≡ m ∷ ms
  onYes (yes _) = refl
  onYes (no ¬p) = Empty.rec (¬p le)

-- A block must be indented strictly past its enclosing block.  At the top
-- level there is no enclosing block, so anything goes.
OpenOK : ℕ → Stack → Type ℓ-zero
OpenOK c [] = Unit
OpenOK c (m ∷ _) = m R.< c

isPropOpenOK : (c : ℕ) (ms : Stack) → isProp (OpenOK c ms)
isPropOpenOK c [] = isPropUnit
isPropOpenOK c (m ∷ _) = R.isProp≤

decOpenOK : (c : ℕ) (ms : Stack) → Dec (OpenOK c ms)
decOpenOK c [] = yes tt
decOpenOK c (m ∷ _) = suc m R.≤? c

-- Every rule's side condition, in one place, as a predicate on token
-- streams that ignores the stream.  `nilOp` in `opening` mode is the empty
-- one: a block opener at the end of input has no block.
SideT : (o : LOp) → LState → Type ℓ-zero
SideT nilOp (scanning , ms) = Unit
SideT nilOp (opening , ms) = Empty.⊥
SideT (consOp (k , c)) (scanning , ms) = Close c ms
SideT (consOp (k , c)) (opening , ms) = OpenOK c ms

isPropSideT : (o : LOp) (S : LState) → isProp (SideT o S)
isPropSideT nilOp (scanning , ms) = isPropUnit
isPropSideT nilOp (opening , ms) = Empty.isProp⊥
isPropSideT (consOp (k , c)) (scanning , ms) = isPropClose c ms
isPropSideT (consOp (k , c)) (opening , ms) = isPropOpenOK c ms

decSideT : (o : LOp) (S : LState) → Dec (SideT o S)
decSideT nilOp (scanning , ms) = yes tt
decSideT nilOp (opening , ms) = no λ ()
decSideT (consOp (k , c)) (scanning , ms) = decClose c ms
decSideT (consOp (k , c)) (opening , ms) = decOpenOK c ms

SideSet : (o : LOp) → LState → TheorySet ℓ-zero str
SideSet o S = (λ _ → SideT o S) , λ _ → isProp→isSet (isPropSideT o S)

decSide : (o : LOp) (S : LState) → Decidable (ty (SideSet o S))
decSide o S m _ = onDec (decSideT o S)
  where
  onDec : Dec (SideT o S) → DecTy (ty (SideSet o S)) m
  onDec (yes w) = Sum.inl w
  onDec (no ¬w) = Sum.inr λ w → Empty.rec (¬w w)

-- The transition.  In `scanning` the token lands in whatever block
-- survives it; in `opening` it *is* the block, so its column is pushed.
stepState : Tok → LState → LState
stepState (k , c) (scanning , ms) = modeAfter k , popTo c ms
stepState (k , c) (opening , ms) = modeAfter k , c ∷ ms

-- The judgment.  Every premise's index is determined, so this is a
-- proposition: a token stream is laid out in at most one way, and
-- unambiguity is definitional rather than a theorem.
Layout : LState → TheoryTy ℓ-zero str
Layout S tnil = SideT nilOp S
Layout S (tcons t ts) = SideT (consOp t) S × Layout (stepState t S) ts

isPropLayout : (S : LState) (ts : TokList) → isProp (Layout S ts)
isPropLayout S tnil = isPropSideT nilOp S
isPropLayout S (tcons t ts) =
  isProp× (isPropSideT (consOp t) S) (isPropLayout (stepState t S) ts)

LayoutSet : LState → TheorySet ℓ-zero str
LayoutSet S = Layout S , λ ts → isProp→isSet (isPropLayout S ts)

-- The rules, as the slots of their nodes.  `consOp`'s single slot is the
-- rest of the stream at the stepped state; `nilOp` has none.
Slots : (o : LOp) → LState → NodeArgs ℓ-zero o
Slots nilOp S ms ()
Slots (consOp t) S ms theTail = LayoutSet (stepState t S)

-- ...and the cell of the cover: the node, conjoined with the side
-- condition that no slot could carry.
Cell : (o : LOp) → LState → TheorySet ℓ-zero str
Cell o S = ⊗ᴰSet o (Slots o S) &Set SideSet o S

-- One level of unfolding, both ways, as `⊢`-terms.
rollNode : (o : LOp) (S : LState) → ty (Cell o S) ⊢ Layout S
rollNode nilOp S m ((ms , Eq.refl , ws) , sd) = sd
rollNode (consOp t) S m ((ms , Eq.refl , ws) , sd) = sd , ws theTail

unrollNode : (o : LOp) (S : LState) → Layout S & NodeAt o ⊢ ty (Cell o S)
unrollNode nilOp S m (d , (ms , Eq.refl)) = node-mk {ms = ms} (λ ()) , d
unrollNode (consOp t) S m (d , (ms , Eq.refl)) =
  node-mk {ms = ms} (λ where theTail → d .snd) , d .fst


-- The checker, for whatever answer.
module Check (𝒯 : AnswerFunctor) where

  open Subterm {X = LState} isSetLState (λ _ → 0) hiding (_<_) public
  open Combinators 𝒯 srt order public

  step : Step LayoutSet
  step S = look nodeCover branch
    where
    nodeAns : (o : LOp) → ▷ (AnsFam LayoutSet) S & NodeAt o
      ⊢ ty (Ans (⊗ᴰSet o (Slots o S)))
    nodeAns nilOp m (β , (ms , Eq.refl)) =
      Ans-node nilOp (preciseL nilOp) {As = Slots nilOp S} {ms = ms} λ ()
    nodeAns (consOp t) m (β , (ms , Eq.refl)) =
      Ans-node (consOp t) (preciseL (consOp t))
        {As = Slots (consOp t) S} {ms = ms}
        λ where
          theTail → callAt (stepState t S)
            (callTail {x = S} {x' = stepState t S} t (ms theTail)) β

    cellAns : (o : LOp) → ▷ (AnsFam LayoutSet) S & NodeAt o ⊢ ty (Ans (Cell o S))
    cellAns o = Ans-&& ∘⊢ (nodeAns o ,& side (decSide o S))

    branch : (o : LOp)
      → ▷ (AnsFam LayoutSet) S & NodeAt o ⊢ ty (Ans (LayoutSet S))
    branch o =
      Ans-map& (rollNode o S ∘⊢ π₁) (unrollNode o S) ∘⊢ (cellAns o ,& π₂)

  laidOut : Checker LayoutSet
  laidOut = fix step
