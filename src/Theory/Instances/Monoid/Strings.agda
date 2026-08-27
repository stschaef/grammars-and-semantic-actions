{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- Strings: the free monoid on an alphabet, and the Kleene-star code that
   picks a normal form for each of its elements.

   The free monoid is presented by `List Alphabet`, so `↓M tt` *is* the list
   type: `op ε· _` reduces to `[]` and `op _⊙_ ms` to `ms zero ++ ms (suc
   zero)`.  `String*` is `μ X. εTy ⊕ (char ⊗ X)`, right-nested cons lists,
   and `⊤Ty ≅ String*` says every string is uniquely such a list. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Instances.Monoid.Strings
  {ℓAlph}
  (Alphabet : Type ℓAlph) (isSetAlphabet : isSet Alphabet) where

private variable ℓA ℓB ℓC ℓD ℓY : Level

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; ++-assoc ; ++-unit-r)
import Cubical.Data.List as L
import Cubical.Data.Empty as Emp
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
open import Cubical.Data.Equality.More using (isSet→isSetEq)

open import Cubical.WildCat.LocallySmall.Base

open import Theory.Instances.Monoid.Base
open import Theory.Instances.Monoid.ListPresentation Alphabet isSetAlphabet
  using (listPresentation) public
import Theory.Type.SemanticAction.Pipeline

open import Theory.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Lift.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Sum.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Sum.Binary.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Operation.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Inductive.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Top.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Bottom.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Product.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Product.Binary.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Function.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Equalizer.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Distributivity MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Later.Derivative MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.Unambiguity.Base MonEqns Alphabet (λ _ → tt) listPresentation public
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Top.Properties MonEqns Alphabet (λ _ → tt) listPresentation

open WildCatNotation
open WildCatIso

-- the carrier: strings, as the free monoid -- here, the list type itself
String : Type ℓM
String = ↓M tt

-- a single character, as a grammar: the sum of the representables at the
-- generators
char : TheoryTy ℓM tt
char = ⊕[ c ∈ Alphabet ] ⌈ ⌈gen c ⌉ ⌉

-- the unit of ⊗, i.e. the nullary operation's convolution
-- (`I` is taken: it is the interval)
εTy : TheoryTy ℓM tt
εTy = ⊗[ ε· ][ (λ ()) ] tt*

infixr 20 _⊗_

_⊗_ : TheoryTy ℓA tt → TheoryTy ℓB tt → TheoryTy _ tt
_⊗_ {ℓA = ℓA} {ℓB = ℓB} A B =
  ⊗[ _⊙_ ][ two ℓA ℓB ] (A , B , tt*)

⊗-map : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
        {C : TheoryTy ℓC tt} {D : TheoryTy ℓD tt}
  → A ⊢ C → B ⊢ D → A ⊗ B ⊢ C ⊗ D
⊗-map {ℓA = ℓA} {ℓB = ℓB} {ℓC = ℓC} {ℓD = ℓD} f g =
  ⊗map[ _⊙_ ][ two ℓA ℓB ] (two ℓC ℓD) λ where
    zero → f
    (suc zero) → g

_,⊗_ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
      {C : TheoryTy ℓC tt} {D : TheoryTy ℓD tt}
  → A ⊢ C → B ⊢ D → A ⊗ B ⊢ C ⊗ D
_,⊗_ = ⊗-map

infixr 20 _,⊗_

-- The splitting does not depend on which summand the left factor is in,
-- so `⊗` distributes over `⊕` -- and annihilates `⊥Ty`.
⊗⊕-distL : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → (A ⊕ B) ⊗ C ⊢ (A ⊗ C) ⊕ (B ⊗ C)
⊗⊕-distL m (ms , e , (Sum.inl a , r)) = Sum.inl (ms , e , (a , r))
⊗⊕-distL m (ms , e , (Sum.inr b , r)) = Sum.inr (ms , e , (b , r))

-- The tensor distributes over a sum in its *right* factor: the mirror of
-- `⊗⊕-distL`, and a connective law at the same tier -- the splitting is
-- consumed by `⊗-elim`, never by matching the input.
⊗⊕-distR : {ℓA ℓB ℓC : Level} {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
  {C : TheoryTy ℓC tt} → A ⊗ (B ⊕ C) ⊢ (A ⊗ B) ⊕ (A ⊗ C)
⊗⊕-distR {ℓA = ℓA} {ℓB = ℓB} {ℓC = ℓC} {A = A} {B = B} {C = C} =
  ⊗-elim {ℓs = two ℓA (ℓ-max ℓB ℓC)} (A , B ⊕ C , tt*)
    {C = (A ⊗ B) ⊕ (A ⊗ C)} λ where
    {ms} (a , Sum.inl b , _) →
      Sum.inl (⊗-intro {ℓs = two ℓA ℓB} (A , B , tt*) ms (a , b , tt*))
    {ms} (a , Sum.inr c , _) →
      Sum.inr (⊗-intro {ℓs = two ℓA ℓC} (A , C , tt*) ms (a , c , tt*))

⊗⊥-annihL : {C : TheoryTy ℓC tt} → ⊥Ty ⊗ C ⊢ ⊥Ty
⊗⊥-annihL m (ms , e , (b , _)) = b

⊗⊥-annihR : {C : TheoryTy ℓC tt} → C ⊗ ⊥Ty ⊢ ⊥Ty
⊗⊥-annihR m (ms , e , (_ , (b , _))) = b

-- Tensor coherence.  The generic `eqn→Iso` lifts a monoid equation to the
-- *flat* convolution over one valuation of all three variables, which is a
-- different type from the nested `(A ⊗ B) ⊗ C`; on this presentation the
-- nested statement is just `++-assoc`, so it is proved here directly.
--
-- In `Eq`, though.  The reassociated splitting is *data* a parser carries,
-- so it must reduce to `Eq.refl` on canonical strings; a `pathToEq` is
-- stuck, and a stuck cast at `μ` blocks every recursor underneath it.
++-assocEq : (a b c : String) → ((a ++ b) ++ c) Eq.≡ (a ++ (b ++ c))
++-assocEq [] b c = Eq.refl
++-assocEq (x ∷ a) b c = Eq.ap (x ∷_) (++-assocEq a b c)

++-unit-rEq : (a : String) → (a ++ []) Eq.≡ a
++-unit-rEq [] = Eq.refl
++-unit-rEq (x ∷ a) = Eq.ap (x ∷_) (++-unit-rEq a)

⊗-assoc : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → (A ⊗ B) ⊗ C ⊢ A ⊗ (B ⊗ C)
⊗-assoc m (ms , e , ((ns , f , (a , (b , _))) , (c , _))) =
  two (ns zero) (ns (suc zero) ++ ms (suc zero))
    , split
    , (a , ((two (ns (suc zero)) (ms (suc zero)) , Eq.refl , (b , (c , tt*))) , tt*))
  where
  split : (ns zero ++ (ns (suc zero) ++ ms (suc zero))) Eq.≡ m
  split = Eq.sym (++-assocEq (ns zero) (ns (suc zero)) (ms (suc zero)))
     Eq.∙ (Eq.ap (_++ ms (suc zero)) f Eq.∙ e)

⊗-assoc⁻ : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  → A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C
⊗-assoc⁻ m (ms , e , (a , ((ns , f , (b , (c , _))) , _))) =
  two (ms zero ++ ns zero) (ns (suc zero))
    , split
    , ((two (ms zero) (ns zero) , Eq.refl , (a , (b , tt*))) , (c , tt*))
  where
  split : ((ms zero ++ ns zero) ++ ns (suc zero)) Eq.≡ m
  split = ++-assocEq (ms zero) (ns zero) (ns (suc zero))
     Eq.∙ (Eq.ap (ms zero ++_) f Eq.∙ e)

⊗-unit-r⁻ : {A : TheoryTy ℓA tt} → A ⊢ A ⊗ ⊤Ty
⊗-unit-r⁻ m a = two m [] , Eq.pathToEq (++-unit-r m) , (a , (tt , tt*))

-- the path `⊗-unit-l` transports along, named so that its coherences can
-- write the cast down instead of leaving it to unification
unit-lPath : {m : String} (ms : arities MonSig _⊙_ → String)
  → εTy (ms zero) → op _⊙_ ms Eq.≡ m → ms (suc zero) ≡ m
unit-lPath ms u e =
  cong (_++ ms (suc zero)) (Eq.eqToPath (u .snd .fst)) ∙ Eq.eqToPath e

-- the left unit law: an empty first factor is no factor
⊗-unit-l : {A : TheoryTy ℓA tt} → εTy ⊗ A ⊢ A
⊗-unit-l {A = A} m (ms , e , (u , (a , _))) =
  Eq.transport A (Eq.pathToEq (unit-lPath ms u e)) a

⊗-unit-l⁻ : {A : TheoryTy ℓA tt} → A ⊢ ⊤Ty ⊗ A
⊗-unit-l⁻ m a = two [] m , Eq.refl , (tt , (a , tt*))

εTy-pt : εTy []
εTy-pt = (λ ()) , Eq.refl , tt*

-- A fixed word as an iterated tensor of letters.  `⌈ w ⌉` is the same
-- grammar (`lits→⌈⌉`/`⌈⌉→lits` below); this shape is the one a fold over
-- `⊗` can consume letter by letter.
lits : String → TheoryTy ℓM tt
lits [] = εTy
lits (c ∷ w) = ＂ c ＂ ⊗ lits w

lits→⌈⌉ : (w : String) → lits w ⊢ ⌈ w ⌉
lits→⌈⌉ [] m (ms , e , _) = Eq.sym e
lits→⌈⌉ (c ∷ w) m (ms , e , (lc , (r , _))) =
  go (ms zero) (ms (suc zero)) m lc (lits→⌈⌉ w (ms (suc zero)) r) e
  where
  go : (x y n : String) → x Eq.≡ (c ∷ []) → y Eq.≡ w → (x ++ y) Eq.≡ n
     → n Eq.≡ (c ∷ w)
  go .(c ∷ []) .w n Eq.refl Eq.refl q = Eq.sym q

⌈⌉→lits : (w : String) → ⌈ w ⌉ ⊢ lits w
⌈⌉→lits [] m p = go p
  where
  go : m Eq.≡ [] → εTy m
  go Eq.refl = εTy-pt
⌈⌉→lits (c ∷ w) m p = go p
  where
  go : m Eq.≡ (c ∷ w) → (＂ c ＂ ⊗ lits w) m
  go Eq.refl =
    two (c ∷ []) w , Eq.refl , (Eq.refl , (⌈⌉→lits w w Eq.refl , tt*))

-- the carrier is a set, so a splitting's index equation is a proposition
isSetString : isSet String
isSetString = M .fst tt .snd

isPropEqString : {x y : String} → isProp (x Eq.≡ y)
isPropEqString = isSet→isSetEq isSetString

-- `Fin 2` has no definitional η, so a rebuilt splitting reaches an arbitrary
-- one only through this path.
two≡ : {ms : arities MonSig _⊙_ → String} {x y : String}
  → x ≡ ms zero → y ≡ ms (suc zero) → two x y ≡ ms
two≡ p q = funExt λ where
  zero → p
  (suc zero) → q

-- Two tensor elements agree as soon as their splittings and slots do: the
-- index equation is a proposition, so it never has to be computed.
⊗PathP' : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {x y : String}
  (r : x ≡ y) {ms ns : arities MonSig _⊙_ → String} (s : ms ≡ ns)
  {ex : op _⊙_ ms Eq.≡ x} {ey : op _⊙_ ns Eq.≡ y}
  {a : A (ms zero)} {a' : A (ns zero)}
  {b : B (ms (suc zero))} {b' : B (ns (suc zero))}
  → PathP (λ j → A (s j zero)) a a'
  → PathP (λ j → B (s j (suc zero))) b b'
  → PathP (λ j → (A ⊗ B) (r j))
      (ms , ex , (a , (b , tt*))) (ns , ey , (a' , (b' , tt*)))
⊗PathP' r s {ex = ex} {ey = ey} pa pb j =
  s j
  , isProp→PathP (λ i → isPropEqString {x = op _⊙_ (s i)} {y = r i}) ex ey j
  , (pa j , (pb j , tt*))

-- `Eq.transport` along a `pathToEq` is transport along the path itself.
transportEq : {A : TheoryTy ℓA tt} {x y : String} (p : x ≡ y) (a : A x)
  → PathP (λ j → A (p j)) a (Eq.transport A (Eq.pathToEq p) a)
transportEq {A = A} p a = J
  (λ _ p' → PathP (λ j → A (p' j)) a (Eq.transport A (Eq.pathToEq p') a))
  (sym (cong (λ q → Eq.transport A q a)
          (isPropEqString (Eq.pathToEq refl) Eq.refl)))
  p

-- ...so `⊗-unit-l` is the second projection, over any path of indices.
unit-l≡ : {A : TheoryTy ℓA tt} (m : String) (t : (εTy ⊗ A) m)
  (p : t .fst (suc zero) ≡ m)
  → PathP (λ j → A (p j)) (t .snd .snd .snd .fst) (⊗-unit-l {A = A} m t)
unit-l≡ {A = A} m t p =
  subst (λ r → PathP (λ j → A (r j)) a (⊗-unit-l {A = A} m t))
    (isSetString _ _ upath p) (transportEq {A = A} upath a)
  where
  a = t .snd .snd .snd .fst

  upath : t .fst (suc zero) ≡ m
  upath = unit-lPath (t .fst) (t .snd .snd .fst) (t .snd .fst)

-- Naturality of the structural maps in one slot.  `⊗-map` never touches the
-- splitting, so all but the left unitor are `refl`.

-- functoriality of `⊗-map`, slotwise
⊗-map-∘ : {A B C D E F : TheoryTy ℓM tt}
  (f : C ⊢ E) (g : D ⊢ F) (f' : A ⊢ C) (g' : B ⊢ D)
  → ⊗-map f g ∘⊢ ⊗-map f' g' ≡ ⊗-map (f ∘⊢ f') (g ∘⊢ g')
⊗-map-∘ f g f' g' = refl

-- naturality of `Eq.transport`, which is all `⊗-unit-l` does
transportEq-nat : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} (f : A ⊢ B)
  {x y : String} (q : x Eq.≡ y) (a : A x)
  → f y (Eq.transport A q a) ≡ Eq.transport B q (f x a)
transportEq-nat f Eq.refl a = refl

⊗-unit-l-nat : {K L : TheoryTy ℓM tt} (f : K ⊢ L)
  → f ∘⊢ ⊗-unit-l {A = K}
    ≡ ⊗-unit-l {A = L} ∘⊢ ⊗-map (id⊢ {A = εTy}) f
⊗-unit-l-nat f = funExt λ m → funExt λ where
  (ms , e , (u , (a , _))) →
    transportEq-nat f (Eq.pathToEq (unit-lPath ms u e)) a

⊗-assoc⁻-nat : {A B K L : TheoryTy ℓM tt} (f : K ⊢ L)
  → ⊗-assoc⁻ {A = A} {B = B} {C = L}
      ∘⊢ ⊗-map (id⊢ {A = A}) (⊗-map (id⊢ {A = B}) f)
    ≡ ⊗-map (id⊢ {A = A ⊗ B}) f ∘⊢ ⊗-assoc⁻ {A = A} {B = B} {C = K}
⊗-assoc⁻-nat f = refl

⊗-assoc-nat : {A B K L : TheoryTy ℓM tt} (f : K ⊢ L)
  → ⊗-map (id⊢ {A = A}) (⊗-map (id⊢ {A = B}) f)
      ∘⊢ ⊗-assoc {A = A} {B = B} {C = K}
    ≡ ⊗-assoc {A = A} {B = B} {C = L} ∘⊢ ⊗-map (id⊢ {A = A ⊗ B}) f
⊗-assoc-nat f = refl

-- The pentagon.  Both reassociations of a four-fold tensor keep the same
-- slots over the same splitting; they differ by `++-assoc` on its left part.
module _ {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} {C : TheoryTy ℓC tt}
  {K : TheoryTy ℓD tt} where

  private
    pentL : A ⊗ B ⊗ C ⊗ K ⊢ (A ⊗ B ⊗ C) ⊗ K
    pentL = ⊗-map (⊗-assoc {A = A} {B = B} {C = C}) (id⊢ {A = K})
      ∘⊢ ⊗-assoc⁻ {A = A ⊗ B} {B = C} {C = K}
      ∘⊢ ⊗-assoc⁻ {A = A} {B = B} {C = C ⊗ K}

    pentR : A ⊗ B ⊗ C ⊗ K ⊢ (A ⊗ B ⊗ C) ⊗ K
    pentR = ⊗-assoc⁻ {A = A} {B = B ⊗ C} {C = K}
      ∘⊢ ⊗-map (id⊢ {A = A}) (⊗-assoc⁻ {A = B} {B = C} {C = K})

    pent⁻L : (A ⊗ B ⊗ C) ⊗ K ⊢ A ⊗ B ⊗ C ⊗ K
    pent⁻L = ⊗-assoc {A = A} {B = B} {C = C ⊗ K}
      ∘⊢ ⊗-assoc {A = A ⊗ B} {B = C} {C = K}
      ∘⊢ ⊗-map (⊗-assoc⁻ {A = A} {B = B} {C = C}) (id⊢ {A = K})

    pent⁻R : (A ⊗ B ⊗ C) ⊗ K ⊢ A ⊗ B ⊗ C ⊗ K
    pent⁻R = ⊗-map (id⊢ {A = A}) (⊗-assoc {A = B} {B = C} {C = K})
      ∘⊢ ⊗-assoc {A = A} {B = B ⊗ C} {C = K}

  ⊗-pent : pentL ≡ pentR
  ⊗-pent = funExt λ m → funExt (go m)
    where
    go : (m : String) (x : (A ⊗ B ⊗ C ⊗ K) m) → pentL m x ≡ pentR m x
    go m (ms , e , (a , ((ns , f , (b , ((ps , g , (c , (k' , _))) , _))) , _))) =
      ⊗PathP' {A = A ⊗ B ⊗ C} {B = K} refl (two≡ assoc3 refl)
        (⊗PathP' {A = A} {B = B ⊗ C} assoc3 refl refl refl) refl
      where
      assoc3 : (ms zero ++ ns zero) ++ ps zero ≡ ms zero ++ (ns zero ++ ps zero)
      assoc3 = ++-assoc (ms zero) (ns zero) (ps zero)

  ⊗-pent⁻ : pent⁻L ≡ pent⁻R
  ⊗-pent⁻ = funExt λ m → funExt (go m)
    where
    go : (m : String) (x : ((A ⊗ B ⊗ C) ⊗ K) m) → pent⁻L m x ≡ pent⁻R m x
    go m (ms , e , ((ns , f , (a , ((ps , g , (b , (c , _))) , _))) , (k' , _))) =
      ⊗PathP' {A = A} {B = B ⊗ C ⊗ K} refl (two≡ refl assoc3) refl
        (⊗PathP' {A = B} {B = C ⊗ K} assoc3 refl refl refl)
      where
      assoc3 : ps zero ++ (ps (suc zero) ++ ms (suc zero))
             ≡ ns (suc zero) ++ ms (suc zero)
      assoc3 = sym (++-assoc (ps zero) (ps (suc zero)) (ms (suc zero)))
             ∙ cong (_++ ms (suc zero)) (Eq.eqToPath g)


-- ⊤ ≅ μ X. εTy ⊕ (char ⊗ X).  The branch is a named function, not a
-- `λ where`: two occurrences of the same extended lambda never compare.
kleeneBranch : Bool → Functor ℓM Unit (λ _ → tt) tt
kleeneBranch false = ⊗e ε· λ ()
kleeneBranch true = ⊗e _⊙_ (two (k char) (Var tt))

KleeneCode : Functor ℓM Unit (λ _ → tt) tt
KleeneCode = ⊕e Bool kleeneBranch

String* : TheoryTy (ℓF ℓM) tt
String* = μ {X = Unit} {xs = λ _ → tt} (λ _ → KleeneCode) tt

-- Constructors and one-step observation for the canonical presentation.
-- These live here (rather than being recovered through `Star`) so clients
-- can use `String*` without a definitional coincidence between two codes.
stringNIL-branch : LiftTheoryTy (ℓF ℓM) εTy
  ⊢ ⟦ kleeneBranch false ⟧TheoryTy (λ _ → String*)
stringNIL-branch m (lift (ms , e , u)) = ms , e , λ ()

stringNIL : LiftTheoryTy (ℓF ℓM) εTy ⊢ String*
stringNIL = roll ∘⊢ σ⊕ false ∘⊢ stringNIL-branch

stringCONS-branch : char ⊗ String*
  ⊢ ⟦ kleeneBranch true ⟧TheoryTy (λ _ → String*)
stringCONS-branch m (ms , e , c , cs , u) =
  ms , e , two (lift c) (lift cs)

stringCONS : char ⊗ String* ⊢ String*
stringCONS = roll ∘⊢ σ⊕ true ∘⊢ stringCONS-branch

StringLayer : TheoryTy _ tt
StringLayer = ⊕[ b ∈ Bool ] ⟦ kleeneBranch b ⟧TheoryTy (λ _ → String*)

unrollString : String* ⊢ StringLayer
unrollString = unroll (λ _ → KleeneCode) tt

-- Canonical input observation
--
-- The only non-formal part of `⊤Ty ≅ String*` is `read`: it has to choose a
-- cons list at each monoid element.  On this presentation the element *is*
-- the list, so `read` is a plain structural recursion -- both index
-- equations are `Eq.refl`, with no normal form and no cast.  Its section law
-- says that choice is the unique `String*` witness.
read : ⊤Ty ⊢ String*
read [] _ = stringNIL _ (lift εTy-pt)
read (c ∷ cs) _ =
  stringCONS _ (two (c ∷ []) cs , Eq.refl , ((c , Eq.refl) , read cs _ , tt*))

private
  -- Naming the slot functor with an explicit type pins its level, so the
  -- Lift levels inside `k` and `Var` are no longer free metavariables.
  ConsF : arities MonSig _⊙_ → Functor ℓM Unit (λ _ → tt) tt
  ConsF = two (k char) (Var tt)

  isPropEqS : {x y : String} → isProp (x Eq.≡ y)
  isPropEqS = isSet→isSetEq (M .fst tt .snd)

  η2 : (ns : arities MonSig _⊙_ → String) → ns ≡ two (ns zero) (ns (suc zero))
  η2 ns = funExt λ where
    zero → refl
    (suc zero) → refl

  isPropChar : (m : String) → isProp (char m)
  isPropChar m (c , q) (c' , q') =
    ΣPathP (L.cons-inj₁ (sym (Eq.eqToPath q) ∙ Eq.eqToPath q') ,
            isProp→PathP (λ _ → isPropEqS) q q')

  -- A cons layer over a list splits definitionally: `char (ms zero)` says
  -- `ms zero` is a singleton, and `(x ∷ []) ++ ms (suc zero)` reduces.
  splitCons : (c : Alphabet) (cs : List Alphabet)
    (ms : arities MonSig _⊙_ → String)
    → char (ms zero) → op _⊙_ ms ≡ c ∷ cs
    → (ms zero ≡ c ∷ []) × (ms (suc zero) ≡ cs)
  splitCons c cs ms (x , q) r =
      Eq.eqToPath q ∙ cong (_∷ []) (L.cons-inj₁ flat)
    , L.cons-inj₂ flat
    where
    flat : x ∷ ms (suc zero) ≡ c ∷ cs
    flat = cong (λ z → op _⊙_ (two z (ms (suc zero)))) (sym (Eq.eqToPath q))
         ∙ cong (op _⊙_) (sym (η2 ms)) ∙ r

  -- `op ε· ns` is `[]` on the nose, so the nullary tuple never appears.
  consNotNil : (ms : arities MonSig _⊙_ → String)
    → char (ms zero) → op _⊙_ ms ≡ [] → Emp.⊥
  consNotNil ms (c , q) r = L.¬cons≡nil
    (sym (cong (λ z → op _⊙_ (two z (ms (suc zero)))) (Eq.eqToPath q))
     ∙ cong (op _⊙_) (η2 ms) ∙ r)

  nilLayer≡ : {m : String}
    (z z' : ⟦ kleeneBranch false ⟧TheoryTy (λ _ → String*) m) → z ≡ z'
  nilLayer≡ (ms , e , u) (ms' , e' , u') =
    ΣPathP (funExt (λ ()) ,
      ΣPathP (isProp→PathP (λ _ → isPropEqS) e e' , funExt (λ ())))

  mapRead : ⟦ KleeneCode ⟧TheoryTy (λ _ → ⊤Ty)
          ⊢ ⟦ KleeneCode ⟧TheoryTy (λ _ → String*)
  mapRead = map KleeneCode (λ _ → read)

  -- The square making `read` an algebra map, by cases on the *input list*:
  -- the carrier is the list, so `Eq.refl` on `p` exposes the head that the
  -- layer's own tuple keeps behind a function application.
  readSq' : (cs : List Alphabet) (m : String) (p : cs Eq.≡ m)
    (z : ⟦ KleeneCode ⟧TheoryTy (λ _ → ⊤Ty) m)
    → read m tt ≡ roll m (mapRead m z)
  readSq' [] .[] Eq.refl (false , z) i =
    roll [] (false , nilLayer≡ (stringNIL-branch [] (lift εTy-pt))
                       (map (kleeneBranch false) (λ _ → read) [] z) i)
  readSq' [] .[] Eq.refl (true , ms , e , sl) =
    Emp.rec (consNotNil ms (sl zero .lower) (Eq.eqToPath e))
  readSq' (c ∷ cs) ._ Eq.refl (false , ms , e , u) =
    Emp.rec (L.¬nil≡cons (Eq.eqToPath e))
  readSq' (c ∷ cs) ._ Eq.refl (true , ms , e , sl) = res
    where
    sp = splitCons c cs ms (sl zero .lower) (Eq.eqToPath e)

    consL : ⟦ kleeneBranch true ⟧TheoryTy (λ _ → String*) (c ∷ cs)
    consL = stringCONS-branch (c ∷ cs)
      (two (c ∷ []) cs , Eq.refl , ((c , Eq.refl) , read cs tt , tt*))

    msP : consL .fst ≡ ms
    msP = funExt λ where
      zero → sym (sp .fst)
      (suc zero) → sym (sp .snd)

    eP : PathP (λ i → op _⊙_ (msP i) Eq.≡ (c ∷ cs)) Eq.refl e
    eP = isProp→PathP (λ i → isPropEqS) Eq.refl e

    slotP0 : (x : String) → isProp (⟦ ConsF zero ⟧TheoryTy (λ _ → String*) x)
    slotP0 x y z i = lift (isPropChar x (y .lower) (z .lower) i)

    hlp : (a : arities MonSig _⊙_)
      → PathP (λ j → ⟦ ConsF a ⟧TheoryTy (λ _ → String*) (msP j a))
          (consL .snd .snd a)
          (map (ConsF a) (λ _ → read) (ms a) (sl a))
    hlp zero = isProp→PathP (λ j → slotP0 (msP j zero)) _ _
    hlp (suc zero) j = lift (read (msP j (suc zero)) tt)

    res : read (c ∷ cs) tt
        ≡ roll (c ∷ cs) (true , ms , e ,
            λ a → map (ConsF a) (λ _ → read) (ms a) (sl a))
    res i = roll (c ∷ cs) (true , msP i , eP i , λ a → hlp a i)

  readSq : (x : Unit) → read ∘⊢ ⊤Ty-intro ≡ roll ∘⊢ mapRead
  readSq tt = funExt λ m → funExt λ z → readSq' m m Eq.refl z

-- `read` is a section of the terminal map, so `String*` is a retract of
-- `⊤Ty`.  This is the `Grammar/String/Unambiguous.agda` argument: the
-- retract of a proposition-valued type is proposition-valued.
-- `char` is a proposition at every word: a one-letter word has one letter.
unambiguous-char : (m : String) → isProp (char m)
unambiguous-char = isPropChar

read-section : read ∘⊢ ⊤Ty-intro ≡ id⊢
read-section =
  rec-section (λ _ → KleeneCode) (λ _ → ⊤Ty-intro) (λ _ → read) readSq tt

-- A string is empty, or a character followed by a string.  `unrollString`
-- lands in the raw code layer; this is the same observation as a
-- connective, which is what clients actually want to case on.
stringLayer↑ : String* ⊢ εTy ⊕ (char ⊗ String*)
stringLayer↑ = ⊕ᴰ-elim branch ∘⊢ unrollString
  where
  branch : (b : Bool)
    → ⟦ kleeneBranch b ⟧TheoryTy (λ _ → String*) ⊢ εTy ⊕ (char ⊗ String*)
  branch false m (ms , e , _) = Sum.inl (ms , e , tt*)
  branch true m (ms , e , f) =
    Sum.inr (ms , e , (f zero .lower , (f (suc zero) .lower , tt*)))

-- the unit's inverse.  `⊗-unit-l⁻` above lands in `⊤Ty`, which is weaker.
ε⊗-intro : {A : TheoryTy ℓA tt} → A ⊢ εTy ⊗ A
ε⊗-intro m a = two [] m , Eq.refl , (εTy-pt , (a , tt*))

unambiguous-String* : (m : String) → isProp (String* m)
unambiguous-String* =
  unambiguousRetract ⊤Ty-intro read read-section unambiguous⊤

-- The `Grammar/String/Terminal.agda` equivalence, recaptured.
String*≅⊤Ty : String* ≅ ⊤Ty
String*≅⊤Ty .fun = ⊤Ty-intro
String*≅⊤Ty .inv = read
String*≅⊤Ty .sec = ⊤Ty-η _ ∙ sym (⊤Ty-η id⊢)
String*≅⊤Ty .ret = read-section

observe₁ : ⊤Ty ⊢ StringLayer
observe₁ = unrollString ∘⊢ read

-- A free-monoid stage consumes a token list by choosing its canonical
-- `String*` presentation.  The source theory is arbitrary: this is the
-- concrete instance of the generic semantic-action hand-off contract.  On
-- this presentation the carrier is the token list, so the world map is the
-- identity and the inhabitation map is `read`.
module InputFrom
  {ℓ ℓ'' ℓv ℓS ℓP} {S : Type ℓS} {σ : SortedSig S ℓ}
  (σeq : SortedEqns σ ℓ'') (V : Type ℓv) (vs : V → S)
  (𝒫 : FB.FreePresentation σeq V vs ℓP) where

  module Stage = Theory.Type.SemanticAction.Pipeline
    σeq V vs 𝒫 MonEqns Alphabet (λ _ → tt) listPresentation

  stringInput : Stage.Input (List Alphabet) String*
  stringInput .Stage.world m = m
  stringInput .Stage.inhabit m = read m tt
