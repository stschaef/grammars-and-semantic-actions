{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- First/follow analysis: `RE` to `DetReg`.

   `DetReg`'s side conditions quantify over the alphabet, so over Unicode
   they cannot be enumerated -- but they can be *built*: both indices are
   complements of small sets, so `DetOfB` carries those sets as a `Supp`
   and discharges a condition by evaluating one `Bool`.  The check that
   can fail is `Disj`, finite only when at most one side is a class, so
   `[a-z]|[0-9]` is refused though deterministic.  `detOf` answers
   `nothing` there and wherever `DetReg` cannot express determinism
   (`a*b*`); none of those are holes. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Automaton.Implicit.Analysis
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Bool
  using (Bool ; true ; false ; _and_ ; _or_ ; true≢false ; false≢true)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
open import Cubical.Relation.Nullary.Base using (Discrete ; yes ; no)
import Cubical.Data.Maybe as Mb

open import Theory.Instances.Monoid.Types Alphabet _≟_ using (isSetAlphabet)
open import Theory.Instances.Monoid.Automaton.Implicit.Compile
  Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.Regex.Base Alphabet _≟_ ℓ
  using (RE ; Nullability ; nullable ; notNullable
        ; εr ; ⊥r ; ⟨_⟩r ; satr ; _⊗r_ ; _⊕r_ ; _*r)
-- not `public`: a client reaches `RE` through `Regex.Base` itself, and
-- re-exporting the constructors makes every one of them ambiguous there

private variable
  n n' : Nullability
  nn nn' : Bool

-- Decidable equality, as a `Bool` and as the two facts about it.  The
-- `_≟_` the theory is set up with is `Eq`-valued, and `with` cannot see
-- through a definition, so the elimination is a `where` on the sum.

discAlphabet : Discrete Alphabet
discAlphabet x y = Sum.rec
  (λ p → yes (Eq.eqToPath p)) (λ ¬p → no λ p → ¬p (Eq.pathToEq p)) (x ≟ y)

private
  eqbOf : {x y : Alphabet}
    → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥) → Bool
  eqbOf (Sum.inl _) = true
  eqbOf (Sum.inr _) = false

eqb : Alphabet → Alphabet → Bool
eqb x y = eqbOf (x ≟ y)

eqb-refl : (x : Alphabet) → eqb x x ≡ true
eqb-refl x = eqbAtRefl (x ≟ x)
  where
  eqbAtRefl : (s : (x Eq.≡ x) Sum.⊎ ((x Eq.≡ x) → Empty.⊥)) → eqbOf s ≡ true
  eqbAtRefl (Sum.inl _) = refl
  eqbAtRefl (Sum.inr ne) = Empty.rec (ne Eq.refl)

eqb-true : (x y : Alphabet) → eqb x y ≡ true → x ≡ y
eqb-true x y = eqbToPath (x ≟ y)
  where
  eqbToPath : (s : (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
    → eqbOf s ≡ true → x ≡ y
  eqbToPath (Sum.inl q) _ = Eq.eqToPath q
  eqbToPath (Sum.inr _) p = Empty.rec (false≢true p)

-- `Bool` scaffolding.  `notTrue` and the `(v : Bool) → x ≡ v` idiom are
-- how a stuck `Bool` gets inspected *with* its equation, which `with`
-- does not give.

private
  orFalse : (x y : Bool) → x or y ≡ false → (x ≡ false) × (y ≡ false)
  orFalse false y p = refl , p
  orFalse true y p = Empty.rec (true≢false p)

  orTrue : (x y : Bool) → x or y ≡ true → (x ≡ true) Sum.⊎ (y ≡ true)
  orTrue false y p = Sum.inr p
  orTrue true y p = Sum.inl refl

  notTrue : (x : Bool) → (x ≡ true → Empty.⊥) → x ≡ false
  notTrue false _ = refl
  notTrue true h = Empty.rec (h refl)

-- Supports.  `ℙ` is a bare predicate and its complement is not
-- decidable; a `Supp` is what makes the complement decidable outside a
-- small exception set, which is all the side conditions need.

data Cls : Type ℓAlph where
  one : Alphabet → Cls
  cls : (Alphabet → Bool) → Cls

Supp : Type ℓAlph
Supp = List Cls

holdsB : Cls → Alphabet → Bool
holdsB (one d) c = eqb d c
holdsB (cls P) c = P c

memb : Supp → Alphabet → Bool
memb [] c = false
memb (i ∷ is) c = holdsB i c or memb is c

-- union of supports is `_++_`
memb-++-l : (s t : Supp) (c : Alphabet)
  → memb (s ++ t) c ≡ false → memb s c ≡ false
memb-++-l [] t c p = refl
memb-++-l (i ∷ is) t c p =
  cong₂ _or_ (orFalse (holdsB i c) (memb (is ++ t) c) p .fst)
             (memb-++-l is t c (orFalse (holdsB i c) (memb (is ++ t) c) p .snd))

memb-++-r : (s t : Supp) (c : Alphabet)
  → memb (s ++ t) c ≡ false → memb t c ≡ false
memb-++-r [] t c p = p
memb-++-r (i ∷ is) t c p =
  memb-++-r is t c (orFalse (holdsB i c) (memb (is ++ t) c) p .snd)

-- The one check that can fail.  Everything a `DetReg` node demands
-- reduces to this.

Disj : Supp → Supp → Type ℓAlph
Disj s t = (c : Alphabet) → memb s c ≡ true → memb t c ≡ true → Empty.⊥

private
  DisjCls : Cls → Cls → Type ℓAlph
  DisjCls i j =
    (c : Alphabet) → holdsB i c ≡ true → holdsB j c ≡ true → Empty.⊥

  -- Two classes are the one pair that cannot be settled: it would take a
  -- proof that `P` and `Q` never both hold, and neither is enumerable.
  disjCls? : (i j : Cls) → Mb.Maybe (DisjCls i j)
  disjCls? (one d) (one e) with d ≟ e
  ... | Sum.inl _ = Mb.nothing
  ... | Sum.inr ne = Mb.just λ c p q →
        ne (Eq.pathToEq (eqb-true d c p ∙ sym (eqb-true e c q)))
  disjCls? (one d) (cls Q) = onMembOfD (Q d) refl
    where
    onMembOfD : (v : Bool) → Q d ≡ v → Mb.Maybe (DisjCls (one d) (cls Q))
    onMembOfD true _ = Mb.nothing
    onMembOfD false qd = Mb.just λ c p q →
      true≢false (sym q ∙ sym (cong Q (eqb-true d c p)) ∙ qd)
  disjCls? (cls P) (one e) = onMembOfE (P e) refl
    where
    onMembOfE : (v : Bool) → P e ≡ v → Mb.Maybe (DisjCls (cls P) (one e))
    onMembOfE true _ = Mb.nothing
    onMembOfE false pe = Mb.just λ c p q →
      true≢false (sym p ∙ sym (cong P (eqb-true e c q)) ∙ pe)
  disjCls? (cls P) (cls Q) = Mb.nothing

  disjClsSupp? : (i : Cls) (t : Supp)
    → Mb.Maybe ((c : Alphabet) → holdsB i c ≡ true → memb t c ≡ true → Empty.⊥)
  disjClsSupp? i [] = Mb.just λ c _ q → false≢true q
  disjClsSupp? i (j ∷ js) with disjCls? i j
  ... | Mb.nothing = Mb.nothing
  ... | Mb.just f with disjClsSupp? i js
  ...   | Mb.nothing = Mb.nothing
  ...   | Mb.just g = Mb.just λ c p q →
          Sum.rec (f c p) (g c p) (orTrue (holdsB j c) (memb js c) q)

disj? : (s t : Supp) → Mb.Maybe (Disj s t)
disj? [] t = Mb.just λ c p _ → false≢true p
disj? (i ∷ is) t with disjClsSupp? i t
... | Mb.nothing = Mb.nothing
... | Mb.just f with disj? is t
...   | Mb.nothing = Mb.nothing
...   | Mb.just g = Mb.just λ c p q →
        Sum.rec (λ h → f c h q) (λ h → g c h q)
          (orTrue (holdsB i c) (memb is c) p)

record DetOfB (nn : Bool) : Type (ℓ-suc ℓAlph) where
  constructor det
  field
    ¬FL ¬F : ℙ
    dr : DetReg ¬FL ¬F nn
    suppFL suppF : Supp
    outFL : (c : Alphabet) → memb suppFL c ≡ false → c ∈ℙ ¬FL
    outF : (c : Alphabet) → memb suppF c ≡ false → c ∈ℙ ¬F
open DetOfB public

DetOf : Type (ℓ-suc ℓAlph)
DetOf = Σ[ nn ∈ Bool ] DetOfB nn

sideCond : {P Q : ℙ} (sP sQ : Supp)
  → ((c : Alphabet) → memb sP c ≡ false → c ∈ℙ P)
  → ((c : Alphabet) → memb sQ c ≡ false → c ∈ℙ Q)
  → Disj sP sQ
  → (c : Alphabet) → (c ∈ℙ P) Sum.⊎ (c ∈ℙ Q)
sideCond {P = P} {Q = Q} sP sQ oP oQ dj c = onMembership (memb sP c) refl
  where
  onMembership : (v : Bool) → memb sP c ≡ v → (c ∈ℙ P) Sum.⊎ (c ∈ℙ Q)
  onMembership false p = Sum.inl (oP c p)
  onMembership true p = Sum.inr (oQ c (notTrue (memb sQ c) (dj c p)))

-- The leaves.  `litAut c` and `satAut P` never step once they have
-- accepted, so both follow-last supports are empty.

εDet : DetOfB false
εDet = det ⊤ℙ ⊤ℙ εdr [] [] (λ _ _ → tt*) (λ _ _ → tt*)

⊥Det : DetOfB true
⊥Det = det ⊤ℙ ⊤ℙ ⊥dr [] [] (λ _ _ → tt*) (λ _ _ → tt*)

litDet : (c : Alphabet) → DetOfB true
litDet c = det ⊤ℙ (¬ℙ ⟦ c ⟧ℙ) ＂ c ＂dr [] (one c ∷ [])
  (λ _ _ → tt*)
  (λ c' p q → Empty.rec (false≢true
    (sym (orFalse (eqb c c') false p .fst)
     ∙ sym (cong (eqb c) q) ∙ eqb-refl c)))

satDet : (P : Alphabet → Bool) → DetOfB true
satDet P = det ⊤ℙ (¬ℙ ⟦ P ⟧sat) (satdr P) [] (cls P ∷ [])
  (λ _ _ → tt*)
  (λ c p q → Empty.rec
    (false≢true (sym (orFalse (P c) false p .fst) ∙ lower q)))

-- The nodes.  Each is the `DetReg` constructor, its side condition built
-- by `sideCond`, and the support of the index the constructor announces.

seqDet : DetOfB true → DetOfB nn' → Mb.Maybe DetOf
seqDet {nn' = true} d e with disj? (d .suppFL) (e .suppF)
... | Mb.nothing = Mb.nothing
... | Mb.just dj = Mb.just (true , det
      (e .¬FL) (d .¬F)
      (d .dr ⊗DR[ sideCond (d .suppFL) (e .suppF) (d .outFL) (e .outF) dj ]
       e .dr)
      (e .suppFL) (d .suppF) (e .outFL) (d .outF))
seqDet {nn' = false} d e with disj? (d .suppFL) (e .suppF)
... | Mb.nothing = Mb.nothing
... | Mb.just dj = Mb.just (true , det
      (d .¬FL ∩ℙ e .¬F ∩ℙ e .¬FL) (d .¬F)
      (d .dr ⊗DR[ sideCond (d .suppFL) (e .suppF) (d .outFL) (e .outF) dj ]
       e .dr)
      (d .suppFL ++ e .suppF ++ e .suppFL) (d .suppF)
      (λ c p →
          d .outFL c (memb-++-l (d .suppFL) _ c p)
        , e .outF c
            (memb-++-l (e .suppF) _ c (memb-++-r (d .suppFL) _ c p))
        , e .outFL c
            (memb-++-r (e .suppF) _ c (memb-++-r (d .suppFL) _ c p)))
      (d .outF))

-- `⊕DR` wants at least one branch non-nullable, and the follow-last
-- index it announces depends on which: with both non-nullable the
-- branches cannot be re-entered, so their first sets stay out of it.
altDet : DetOfB nn → DetOfB nn' → Mb.Maybe DetOf
altDet {nn = false} {nn' = false} d e = Mb.nothing
altDet {nn = true} {nn' = true} d e with disj? (d .suppF) (e .suppF)
... | Mb.nothing = Mb.nothing
... | Mb.just dj = Mb.just (true , det
      (d .¬FL ∩ℙ e .¬FL ∩ℙ ⊤ℙ) (d .¬F ∩ℙ e .¬F)
      (_⊕DR[_]_ {notBothNull = Eq.refl} (d .dr)
        (sideCond (d .suppF) (e .suppF) (d .outF) (e .outF) dj) (e .dr))
      (d .suppFL ++ e .suppFL) (d .suppF ++ e .suppF)
      (λ c p →
          d .outFL c (memb-++-l (d .suppFL) _ c p)
        , e .outFL c (memb-++-r (d .suppFL) _ c p)
        , tt*)
      (λ c p →
          d .outF c (memb-++-l (d .suppF) _ c p)
        , e .outF c (memb-++-r (d .suppF) _ c p)))
altDet {nn = true} {nn' = false} d e with disj? (d .suppF) (e .suppF)
... | Mb.nothing = Mb.nothing
... | Mb.just dj = Mb.just (false , det
      (d .¬FL ∩ℙ e .¬FL ∩ℙ d .¬F ∩ℙ e .¬F) (d .¬F ∩ℙ e .¬F)
      (_⊕DR[_]_ {notBothNull = Eq.refl} (d .dr)
        (sideCond (d .suppF) (e .suppF) (d .outF) (e .outF) dj) (e .dr))
      (d .suppFL ++ e .suppFL ++ d .suppF ++ e .suppF)
      (d .suppF ++ e .suppF)
      (λ c p →
          d .outFL c (memb-++-l (d .suppFL) _ c p)
        , e .outFL c
            (memb-++-l (e .suppFL) _ c (memb-++-r (d .suppFL) _ c p))
        , d .outF c (memb-++-l (d .suppF) _ c
            (memb-++-r (e .suppFL) _ c (memb-++-r (d .suppFL) _ c p)))
        , e .outF c (memb-++-r (d .suppF) _ c
            (memb-++-r (e .suppFL) _ c (memb-++-r (d .suppFL) _ c p))))
      (λ c p →
          d .outF c (memb-++-l (d .suppF) _ c p)
        , e .outF c (memb-++-r (d .suppF) _ c p)))
altDet {nn = false} {nn' = true} d e with disj? (d .suppF) (e .suppF)
... | Mb.nothing = Mb.nothing
... | Mb.just dj = Mb.just (false , det
      (d .¬FL ∩ℙ e .¬FL ∩ℙ d .¬F ∩ℙ e .¬F) (d .¬F ∩ℙ e .¬F)
      (_⊕DR[_]_ {notBothNull = Eq.refl} (d .dr)
        (sideCond (d .suppF) (e .suppF) (d .outF) (e .outF) dj) (e .dr))
      (d .suppFL ++ e .suppFL ++ d .suppF ++ e .suppF)
      (d .suppF ++ e .suppF)
      (λ c p →
          d .outFL c (memb-++-l (d .suppFL) _ c p)
        , e .outFL c
            (memb-++-l (e .suppFL) _ c (memb-++-r (d .suppFL) _ c p))
        , d .outF c (memb-++-l (d .suppF) _ c
            (memb-++-r (e .suppFL) _ c (memb-++-r (d .suppFL) _ c p)))
        , e .outF c (memb-++-r (d .suppF) _ c
            (memb-++-r (e .suppFL) _ c (memb-++-r (d .suppFL) _ c p))))
      (λ c p →
          d .outF c (memb-++-l (d .suppF) _ c p)
        , e .outF c (memb-++-r (d .suppF) _ c p)))

-- The loop re-enters at the first set, so that is what joins the
-- follow-last index -- and it is the same disjointness that `⊗DR`
-- wanted, with the body against itself.
starDet : DetOfB true → Mb.Maybe DetOf
starDet d with disj? (d .suppFL) (d .suppF)
... | Mb.nothing = Mb.nothing
... | Mb.just dj = Mb.just (false , det
      (d .¬F ∩ℙ d .¬FL) (d .¬F)
      (d .dr *DR[ sideCond (d .suppFL) (d .suppF) (d .outFL) (d .outF) dj ])
      (d .suppF ++ d .suppFL) (d .suppF)
      (λ c p →
          d .outF c (memb-++-l (d .suppF) _ c p)
        , d .outFL c (memb-++-r (d .suppF) _ c p))
      (d .outF))

-- The two unit clauses are what makes `Regex.Parse`'s output usable at
-- all: it builds every concatenation as `εr ⊗r …`, and `⊗DR` refuses a
-- nullable left factor.

detOf : RE n → Mb.Maybe DetOf
detOf εr = Mb.just (false , εDet)
detOf ⊥r = Mb.just (true , ⊥Det)
detOf ⟨ c ⟩r = Mb.just (true , litDet c)
detOf (satr P) = Mb.just (true , satDet P)
detOf (εr ⊗r r') = detOf r'
detOf (r ⊗r εr) = detOf r
detOf (r ⊗r r') with detOf r | detOf r'
... | Mb.just (true , d) | Mb.just (_ , e) = seqDet d e
... | _ | _ = Mb.nothing
detOf (r ⊕r r') with detOf r | detOf r'
... | Mb.just (_ , d) | Mb.just (_ , e) = altDet d e
... | _ | _ = Mb.nothing
detOf (r *r) with detOf r
... | Mb.just (true , d) = starDet d
... | _ = Mb.nothing

-- The bridge back.  `Compile` mentions no regex syntax, so this is where
-- a `DetReg` says which regular expression it is a determinism proof
-- for.  The indices line up on the nose: `_·ν_`/`_+ν_` are left-driven
-- and match `_and_`, and `_*r` already demands what `*DR` does.  The
-- `⊕` clause splits on `b` only because `νOf b +ν νOf b'` is stuck for a
-- variable `b`.

νOf : Bool → Nullability
νOf true = notNullable
νOf false = nullable

erase : {¬FL ¬F : ℙ} {b : Bool} → DetReg ¬FL ¬F b → RE (νOf b)
erase εdr = εr
erase ⊥dr = ⊥r
erase ＂ c ＂dr = ⟨ c ⟩r
erase (satdr P) = satr P
erase (dr ⊗DR[ _ ] dr') = erase dr ⊗r erase dr'
erase (_⊕DR[_]_ {b = true} dr _ dr') = erase dr ⊕r erase dr'
erase (_⊕DR[_]_ {b = false} dr _ dr') = erase dr ⊕r erase dr'
erase (dr *DR[ _ ]) = erase dr *r

-- As with `Regex.Parse`'s `⟨|_|⟩`, a regex the analysis rejects is a type
-- error at the use site rather than a `nothing` to case on.

IsDet : {ℓ' : Level} {A : Type ℓ'} → Mb.Maybe A → Type ℓ-zero
IsDet (Mb.just _) = Unit
IsDet Mb.nothing = Empty.⊥

theDet : (m : Mb.Maybe DetOf) → IsDet m → DetOf
theDet (Mb.just d) _ = d

detOf! : (r : RE n) → {_ : IsDet (detOf r)} → DetOf
detOf! r {p} = theDet (detOf r) p
