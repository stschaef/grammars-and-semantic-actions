{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Parsers that publish their yield to their continuation.

   `Parser`'s continuation is one grammar `K`, chosen by the caller when the
   internal `&[ K ]` is instantiated -- so `seq` has to name the grammar to
   the right before the parser to the left has read anything.  A capture
   group cannot: what follows it mentions the string it is about to match.

   `ParserD` indexes the continuation by that string.  It is strictly
   stronger, and `toParser` recovers the ordinary one for free, because
   `⊗ᴰ A (λ _ _ → K)` is `A ⊗ K` on the nose (`⊗ᴰ-const`). -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (invIso)
open import Cubical.Algebra.Theory.Finitary
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open SortedSig
open SortedEqns

module Theory.Instances.Monoid.Backreference.Parser
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)
open import Cubical.Data.Unit using (Unit ; tt ; tt* ; isSetUnit*)

open import Theory.Instances.Monoid.Combinator.Decidable.Star Alphabet _≟_ ℓ
  public
open import Theory.Instances.Monoid.Backreference.Base Alphabet isSetAlphabet
  public
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-l⁻)

private variable ℓA ℓB ℓD ℓK : Level

-- `⊗ᴰ` as a `TheorySet`: the same `isSet` argument as `isSet⊗2`, with the
-- right slot's `×` a `Σ`.
isPropStrEq : {x y : String} → isProp (x Eq.≡ y)
isPropStrEq = isOfHLevelRetractFromIso 1 (invIso Eq.PathIsoEq) (isSetString _ _)

isSet⊗ᴰ : {A : TheoryTy ℓA tt} {B : String → TheoryTy ℓB tt}
  → isSetTheoryTy A → (∀ l → isSetTheoryTy (B l))
  → isSetTheoryTy (⊗ᴰ A (λ l _ → B l))
isSet⊗ᴰ {B = B} sA sB m =
  isSetΣ (isSetΠ λ _ → isSetString) λ ms →
  isSet× (isProp→isSet isPropStrEq)
    (isSetΣ (sA (ms zero)) λ _ →
      isSet× (sB (ms zero) (ms (suc zero))) isSetUnit*)

⊗ᴰSet : TheorySet ℓA tt → (String → TheorySet ℓB tt) → TheorySet _ tt
⊗ᴰSet A B = ⊗ᴰ (ty A) (λ l _ → ty (B l)) , isSet⊗ᴰ (A .snd) (λ l → B l .snd)

Cont : (ℓK : Level) → Type _
Cont ℓK = String → TheorySet ℓK tt

ParserD : (ℓK : Level) → ParserTag → ParserTag → TheorySet ℓA tt → TheoryTy _ tt
ParserD ℓK a c A =
  &[ C ∈ Cont ℓK ]
    (ty (▷? a (&ᴰSet λ l → DecSet (C l))) ⇒ ty (▷? c (DecSet (⊗ᴰSet A C))))

mkPD : {a c : ParserTag} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
  → (∀ (C : Cont ℓK)
      → D & ty (▷? a (&ᴰSet λ l → DecSet (C l)))
      ⊢ ty (▷? c (DecSet (⊗ᴰSet A C))))
  → D ⊢ ParserD ℓK a c A
mkPD f = &ᴰ-intro λ C → ⇒-intro (f C)

pDAt : {a c : ParserTag} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
  → D ⊢ ParserD ℓK a c A → (C : Cont ℓK)
  → D & ty (▷? a (&ᴰSet λ l → DecSet (C l)))
  ⊢ ty (▷? c (DecSet (⊗ᴰSet A C)))
pDAt p C = ⇒-app ∘⊢ ((π C ∘⊢ p) ,&p id⊢)

-- Forgetting the index costs nothing: a constant continuation family, and
-- `⊗ᴰ A (λ _ _ → K)` is `A ⊗ K` definitionally, so both `▷dec-map`
-- arguments are the identity.
toParser : {a c : ParserTag} {A : TheorySet ℓA tt} {D : TheoryTy ℓD tt}
  → D ⊢ ParserD ℓK a c A → D ⊢ Parser ℓK a c A
toParser p = mkP λ K →
  ▷dec-map id⊢ id⊢
  ∘⊢ pDAt p (λ _ → K)
  ∘⊢ (π₁ ,& (▷map (&ᴰ-intro λ _ → id⊢) ∘⊢ π₂))

module _ {D : TheoryTy ℓD tt} where

  -- The leaves publish nothing new: their yield is determined, so the
  -- indexed continuation is needed at one string only (`⊗ᴰ-lit`, `⊗ᴰ-ε`).
  -- These are `tok`/`nil` with a `π` in front.
  tokD : {ℓK : Level} (c : Alphabet) → D ⊢ ParserD ℓK ⟨▷⟩ ⟨□⟩ (litSet c)
  tokD c = mkPD λ C →
    ▷□ (dec-map (⊗ᴰ-lit⁻ {C = λ l → ty (C l)} c)
                (¬Ty-map (⊗ᴰ-lit {C = λ l → ty (C l)} c))
        ∘⊢ dec-lit⊗-at c {K = C ⌈gen c ⌉} ∘⊢ ▷map (π ⌈gen c ⌉))
    ∘⊢ π₂

  nilD : {ℓK : Level} → D ⊢ ParserD ℓK ⟨□⟩ ⟨□⟩ εSet
  nilD = mkPD λ C →
    ▷dec-map {K = C []} {L = ⊗ᴰSet εSet C}
             (⊗ᴰ-ε⁻ {C = λ l → ty (C l)} ∘⊢ ⊗ε-unit-l⁻)
             (⊗-unit-l ∘⊢ ⊗ᴰ-ε {C = λ l → ty (C l)})
    ∘⊢ ▷map (π []) ∘⊢ π₂

  -- Sequencing *inside* a group: both halves publish, and the group's yield
  -- is the concatenation.  `⊗ᴰ-assoc` is what re-indexes `C` at `l₁ ++ l₂`.
  seqDD : {ℓK ℓB : Level} {a b c : ParserTag}
    {A : TheorySet ℓA tt} (B : TheorySet ℓB tt)
    → D ⊢ ParserD (ℓ⊗ ℓB ℓK) b c A
    → D ⊢ ParserD ℓK a b B
    → D ⊢ ParserD ℓK a c (A ⊗Set B)
  seqDD {A = A} B p q = mkPD λ C →
    ▷dec-map
      (⊗ᴰ-assoc⁻ {A = ty A} {B = λ _ → ty B} {C = λ l → ty (C l)})
      (⊗ᴰ-assoc {A = ty A} {B = λ _ → ty B} {C = λ l → ty (C l)})
    ∘⊢ pDAt p (λ l₁ → ⊗ᴰSet B (λ l₂ → C (l₁ ++ l₂)))
    ∘⊢ (π₁ ,& (▷laxᴰ (λ l₁ → DecSet (⊗ᴰSet B (λ l₂ → C (l₁ ++ l₂))))
              ∘⊢ &ᴰ-intro λ l₁ →
                   pDAt q (λ l₂ → C (l₁ ++ l₂))
                   ∘⊢ (π₁ ,& (▷map (&ᴰ-intro λ l₂ → π (l₁ ++ l₂)) ∘⊢ π₂))))

  -- Alternation: the index sees only the string, so the two summands never
  -- have to agree on a tree (`⊗ᴰ⊕-distL`).
  infixr 15 _<|>D_
  _<|>D_ : {ℓK : Level} {a c : ParserTag}
    {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
    → D ⊢ ParserD ℓK a c A → D ⊢ ParserD ℓK a c B
    → D ⊢ ParserD ℓK a c (A ⊕Set B)
  _<|>D_ {A = A} {B = B} p q = mkPD λ C →
    ▷dec-map
      (⊗ᴰ⊕-distL⁻ {A = ty A} {B = ty B} {C = λ l → ty (C l)})
      (⊗ᴰ⊕-distL {A = ty A} {B = ty B} {C = λ l → ty (C l)})
    ∘⊢ ▷dec-⊕& ∘⊢ (pDAt p C ,& pDAt q C)

  -- `seqDD` with the second half's *grammar* also indexed: a capture group
  -- nested inside another group's body.  This is what makes `parseD` total.
  seqDᴰ : {ℓK ℓB : Level} {a b c : ParserTag} {A : TheorySet ℓA tt}
    (B : Cont ℓB)
    → D ⊢ ParserD (ℓ⊗ ℓB ℓK) b c A
    → ((l : String) → D ⊢ ParserD ℓK a b (B l))
    → D ⊢ ParserD ℓK a c (⊗ᴰSet A B)
  seqDᴰ {A = A} B p q = mkPD λ C →
    ▷dec-map
      (⊗ᴰ-assoc⁻ {A = ty A} {B = λ l → ty (B l)} {C = λ l → ty (C l)})
      (⊗ᴰ-assoc {A = ty A} {B = λ l → ty (B l)} {C = λ l → ty (C l)})
    ∘⊢ pDAt p (λ l₁ → ⊗ᴰSet (B l₁) (λ l₂ → C (l₁ ++ l₂)))
    ∘⊢ (π₁ ,& (▷laxᴰ (λ l₁ → DecSet (⊗ᴰSet (B l₁) (λ l₂ → C (l₁ ++ l₂))))
              ∘⊢ &ᴰ-intro λ l₁ →
                   pDAt (q l₁) (λ l₂ → C (l₁ ++ l₂))
                   ∘⊢ (π₁ ,& (▷map (&ᴰ-intro λ l₂ → π (l₁ ++ l₂)) ∘⊢ π₂))))

  failD : {ℓK : Level} {a c : ParserTag} → D ⊢ ParserD ℓK a c ⊥Set
  failD {c = c} = mkPD λ C →
    ▷next {t = c} (dec-no ∘⊢ ⇒-intro
      (⊗ᴰ⊥-annihL {C = λ l → ty (C l)} ∘⊢ π₂))

-- `pmore` at the publishing type: outside the `D` module, since `D` does not
-- occur in it.
pmoreD : {ℓK : Level} {c : ParserTag} {A : TheorySet ℓA tt}
  → ParserD ℓK ⟨▷⟩ c A ⊢ ParserD ℓK ⟨□⟩ c A
pmoreD = mkPD λ C → pDAt id⊢ C ∘⊢ (id& ▷wk)

-- `ParserD` as a `TheorySet`, so it can sit under `▷` and be Löb'd.
ParserSetD : (ℓK : Level) (a c : ParserTag) → TheorySet ℓA tt → TheorySet _ tt
ParserSetD ℓK a c A =
  ParserD ℓK a c A
  , isSet&ᴰ λ C → isSet⇒ (▷? c (DecSet (⊗ᴰSet A C)) .snd)

mapPD : {ℓK : Level} {a c : ParserTag}
  {A : TheorySet ℓA tt} {B : TheorySet ℓB tt}
  → ty A ⊢ ty B → ty B ⊢ ty A
  → ParserD ℓK a c A ⊢ ParserD ℓK a c B
mapPD {A = A} {B = B} f g = mkPD λ C →
  ▷dec-map (⊗ᴰ-mapL {C = λ l → ty (C l)} f) (⊗ᴰ-mapL {C = λ l → ty (C l)} g)
  ∘⊢ pDAt id⊢ C

pAppD : {ℓK : Level} {A : TheorySet ℓA tt} (C : Cont ℓK)
  → ty (▷ (ParserSetD ℓK ⟨□⟩ ⟨□⟩ A)) & ty (▷ (&ᴰSet λ l → DecSet (C l)))
  ⊢ ty (▷ (DecSet (⊗ᴰSet A C)))
pAppD C = ▷map (□here ∘⊢ pDAt id⊢ C) ∘⊢ ▷lax ∘⊢ (id⊢ ,&p ▷δ□)

boxD : {ℓK : Level} {ℓD : Level} {D : TheoryTy ℓD tt} {A : TheorySet ℓA tt}
  → ⊤Ty ⊢ ParserD ℓK ⟨□⟩ ⟨□⟩ A → D ⊢ ParserD ℓK ⟨▷⟩ ⟨▷⟩ A
boxD p = mkPD λ C → pAppD C ∘⊢ (▷next {t = ⟨▷⟩} p ,&p id⊢)

module FixD {ℓA} (ℓK : Level) (A : TheorySet ℓA tt) where
  ℓ𝒦 : Level
  ℓ𝒦 = ℓ-max ℓM ℓK

  callD : ty (▷ (ParserSetD ℓ𝒦 ⟨□⟩ ⟨□⟩ A)) ⊢ ParserD ℓ𝒦 ⟨▷⟩ ⟨▷⟩ A
  callD = mkPD pAppD

  fixD : ty (▷ (ParserSetD ℓ𝒦 ⟨□⟩ ⟨□⟩ A)) ⊢ ParserD ℓ𝒦 ⟨□⟩ ⟨□⟩ A
    → ⊤Ty ⊢ ParserD ℓ𝒦 ⟨□⟩ ⟨□⟩ A
  fixD = löbG {A = ParserSetD ℓ𝒦 ⟨□⟩ ⟨□⟩ A}

-- `many` at the publishing type: the same fixpoint, with the star's yield
-- the concatenation of the elements'.  `⊗ᴰ-mapL` carries `roll↑`/`unroll↑`
-- through the indexed continuation.
module _ (ℓK : Level) (A : TheorySet ℓA tt) where
  private
    module PD = FixD ℓK (StarSet A)

    ℓE : Level
    ℓE = ℓ⊗ (ℓF ℓA) PD.ℓ𝒦

  manyD : ⊤Ty ⊢ ParserD ℓE ⟨▷⟩ ⟨□⟩ A
        → ⊤Ty ⊢ ParserD PD.ℓ𝒦 ⟨□⟩ ⟨□⟩ (StarSet A)
  manyD p = PD.fixD
    (mapPD roll↑ unroll↑
     ∘⊢ ((pmoreD ∘⊢ seqDD (StarSet A) (p ∘⊢ ⊤Ty-intro) PD.callD) <|>D nilD))

-- The representable at a known string, as a `TheorySet` -- it is a
-- proposition, so `isSet` is free.
⌈_⌉Set : String → TheorySet ℓM tt
⌈ w ⌉Set = ⌈ w ⌉ , λ m → isProp→isSet isPropStrEq

-- Ordinary combinators throughout: by the time this is called the capture
-- is a value.
strP : {ℓK : Level} {D : TheoryTy ℓD tt} (w : String)
  → D ⊢ Parser ℓK ⟨□⟩ ⟨□⟩ ⌈ w ⌉Set
strP [] = mapP {A = εSet} {B = ⌈ [] ⌉Set} ε→⌈⌉ ⌈⌉→ε ∘⊢ nil
strP (c ∷ w) =
  mapP {A = litSet c ⊗Set ⌈ w ⌉Set} {B = ⌈ c ∷ w ⌉Set} (⊗→⌈⌉ c w) (⌈⌉→⊗ c w)
  ∘⊢ seq ⌈ w ⌉Set (pmore ∘⊢ tok c) (strP w)

strPD : {ℓK : Level} {D : TheoryTy ℓD tt} (w : String)
  → D ⊢ ParserD ℓK ⟨□⟩ ⟨□⟩ ⌈ w ⌉Set
strPD w = mkPD λ C →
  ▷dec-map (⊗ᴰ-⌈⌉⁻ {C = λ l → ty (C l)} w) (⊗ᴰ-⌈⌉ {C = λ l → ty (C l)} w)
  ∘⊢ pAt (strP w) (C w)
  ∘⊢ (π₁ ,& (▷map (π w) ∘⊢ π₂))
