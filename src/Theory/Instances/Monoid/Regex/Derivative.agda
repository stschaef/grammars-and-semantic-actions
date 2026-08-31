{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Brzozowski derivatives: matching in one left-to-right pass.

   `decide-r` builds a *decision over every parse*, so its cost tracks the
   number of parses: `(a|a)*b` on 14 letters has 2¹⁴ of them and refuting
   them all does not finish.  Enumerating parses is the wrong algorithm for
   a regular language.

   A derivative does not enumerate.  `δ r c` is another regex -- the one
   matching what may follow `c` -- so membership is a fold of `δ` along the
   input, ending in a nullability test.  That is one step per character,
   whatever the ambiguity.

   The smart constructors are what keep the *regex* from growing as it is
   differentiated; without them the derivative of a star doubles at every
   step and linear time in steps is not linear time in work. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Regex.Derivative
  {ℓAlph}
  (Alphabet : Type ℓAlph)
  (_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥))
  (ℓ : Level)
  where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (tt ; tt*)
open import Cubical.Data.FinData using (zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
import Cubical.Data.List.Properties as LP

open import Theory.Instances.Monoid.Regex.Notation Alphabet _≟_ ℓ public

RE? : Type ℓAlph
RE? = Σ[ n ∈ Nullability ] RE n

isNullable : Nullability → Bool
isNullable nullable = true
isNullable notNullable = false

∅? ε? : RE?
∅? = notNullable , ⊥r
ε? = nullable , εr

-- Smart constructors.  `⊥` annihilates, `ε` is the unit; without these
-- the derivative of a star doubles in size at every character.

infixr 20 _⊗s_
infixr 19 _⊕s_

-- Deliberately *not* smart.  `(_ , ⊥r) ⊗s x = ∅?` would collapse `⊥`
-- eagerly, but then `x ⊗s y` is stuck whenever `x` is a variable, and
-- every clause of the theorem below would have to case-split on what the
-- constructor did.  Simplification belongs in its own function with its
-- own correctness lemma, applied after the fact.
_⊗s_ : RE? → RE? → RE?
(n , r) ⊗s (n' , r') = n ·ν n' , r ⊗r r'

_⊕s_ : RE? → RE? → RE?
(n , r) ⊕s (n' , r') = n +ν n' , r ⊕r r'

-- The derivative itself

δ : ∀ {n} → RE n → Alphabet → RE?
δ εr c = ∅?
δ ⊥r c = ∅?
δ ⟨ d ⟩r c = Sum.rec (λ _ → ε?) (λ _ → ∅?) (d ≟ c)
δ (satr P) c with P c
... | true = ε?
... | false = ∅?
δ (_⊗r_ {nullable} {n'} r r') c = (δ r c ⊗s (n' , r')) ⊕s δ r' c
δ (_⊗r_ {notNullable} {n'} r r') c = δ r c ⊗s (n' , r')
δ (r ⊕r r') c = δ r c ⊕s δ r' c
δ (r *r) c = δ r c ⊗s (nullable , r *r)

δ? : RE? → Alphabet → RE?
δ? (n , r) c = δ r c

-- The residual after a prefix.  This is syntax-to-syntax, like `⟦_⟧` or
-- `anyOfr`: it computes *which regex* to try next, not whether anything
-- matched.  Nothing here decides.

residual : ∀ {n} → RE n → List Alphabet → RE?
residual r [] = _ , r
residual r (c ∷ w) = residual (δ r c .snd) w

-- The syntactic derivative computes the semantic one: `Dl c ⟦ r ⟧ ≅ ⟦ δ r c ⟧`.
-- An iso, so it transfers witnesses and refutations at once.

open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
  using (Dl)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-l⁻)

-- The smart constructors do not change the language.  Confining the
-- case analysis to these four lemmas is what keeps `δ-sound`/`δ-complete`
-- structural.

-- ...so these are all the identity, and the theorem below never has to
-- ask what a constructor did.
⊗s-out : (x y : RE?) → ty ⟦ (x ⊗s y) .snd ⟧ ⊢ ty ⟦ x .snd ⟧ ⊗ ty ⟦ y .snd ⟧
⊗s-out (n , r) (n' , r') = id⊢

⊗s-in : (x y : RE?) → ty ⟦ x .snd ⟧ ⊗ ty ⟦ y .snd ⟧ ⊢ ty ⟦ (x ⊗s y) .snd ⟧
⊗s-in (n , r) (n' , r') = id⊢

⊕s-out : (x y : RE?) → ty ⟦ (x ⊕s y) .snd ⟧ ⊢ ty ⟦ x .snd ⟧ ⊕ ty ⟦ y .snd ⟧
⊕s-out (n , r) (n' , r') = id⊢

⊕s-in : (x y : RE?) → ty ⟦ x .snd ⟧ ⊕ ty ⟦ y .snd ⟧ ⊢ ty ⟦ (x ⊕s y) .snd ⟧
⊕s-in (n , r) (n' , r') = id⊢

-- `Dl c A m` is `A (c ∷ m)`, so these are all statements about what a
-- word beginning with `c` can be.

-- The one list fact everything below rests on: a split of `c ∷ m` has
-- either an empty left factor, or a `c`-headed one.

private
  uncons++ : (u v : String) (c : Alphabet) (m : String)
    → (u ++ v) ≡ (c ∷ m)
    → ((u ≡ []) × (v ≡ c ∷ m))
      Sum.⊎ (Σ[ p ∈ String ] ((u ≡ c ∷ p) × ((p ++ v) ≡ m)))
  uncons++ [] v c m e = Sum.inl (refl , e)
  uncons++ (d ∷ u) v c m e =
    Sum.inr (u , cong (_∷ u) (LP.cons-inj₁ e) , LP.cons-inj₂ e)

-- `Dl` across the connectives.

private variable ℓA ℓB : Level

module _ (c : Alphabet) {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} where

  -- forget which side the split fell on
  Dl-⊗-out : Dl c (A ⊗ B) ⊢ (Dl c A ⊗ B) ⊕ Dl c B
  Dl-⊗-out m (ms , e , (a , (b , _))) with
    uncons++ (ms zero) (ms (suc zero)) c m (Eq.eqToPath e)
  ... | Sum.inl (u≡[] , v≡cm) =
        Sum.inr (subst B v≡cm b)
  ... | Sum.inr (p , u≡cp , pv≡m) =
        Sum.inl ( two p (ms (suc zero))
                , Eq.pathToEq pv≡m
                , (subst A u≡cp a , (b , tt*)))

  -- ...and put it back, on the left
  Dl-⊗-in-l : (Dl c A ⊗ B) ⊢ Dl c (A ⊗ B)
  Dl-⊗-in-l m (ms , e , (a , (b , _))) =
      two (c ∷ ms zero) (ms (suc zero))
    , Eq.ap (c ∷_) e
    , (a , (b , tt*))

  -- ...or on the right, which costs a witness that `A` accepts ε
  Dl-⊗-in-r : (εTy ⊢ A) → Dl c B ⊢ Dl c (A ⊗ B)
  Dl-⊗-in-r nul m b =
      two [] (c ∷ m)
    , Eq.refl
    , (nul [] εTy-pt , (b , tt*))

  -- when `A` cannot be ε the split must be `c`-headed
  Dl-⊗-out! : ¬Nullable A → Dl c (A ⊗ B) ⊢ Dl c A ⊗ B
  Dl-⊗-out! nn m (ms , e , (a , (b , _))) with
    uncons++ (ms zero) (ms (suc zero)) c m (Eq.eqToPath e)
  ... | Sum.inr (p , u≡cp , pv≡m) =
        two p (ms (suc zero)) , Eq.pathToEq pv≡m
      , (subst A u≡cp a , (b , tt*))
  ... | Sum.inl (u≡[] , _) =
        Empty.rec (lower (nn [] (subst A u≡[] a , εTy-pt)))

  -- The same two with the null parse *retained*.  `Dl-⊗-in-r` takes a
  -- section `εTy ⊢ A` and so commits to one null parse of `A`, and
  -- `Dl-⊗-out` forgets it entirely; `A & εTy` is all of them.  That is the
  -- difference between a recogniser and a parser here: with `A & εTy` the
  -- two directions are inverse, and an ambiguous `A` keeps every
  -- derivation.
  Dl-⊗-out⁺ : Dl c (A ⊗ B) ⊢ (Dl c A ⊗ B) ⊕ ((A & εTy) ⊗ Dl c B)
  Dl-⊗-out⁺ m (ms , e , (a , (b , _))) = go (ms zero) (ms (suc zero)) m a b e
    where
    -- by *matching* the equation rather than `subst`ing along a path, so
    -- the branch reduces on a canonical string and a parser built on it
    -- computes its value
    go : (u v w : String) → A u → B v → (u ++ v) Eq.≡ (c ∷ w)
       → ((Dl c A ⊗ B) ⊕ ((A & εTy) ⊗ Dl c B)) w
    go [] .(c ∷ w) w a b Eq.refl =
      Sum.inr (two [] w , Eq.refl , ((a , εTy-pt) , (b , tt*)))
    go (d ∷ u) v .(u ++ v) a b Eq.refl =
      Sum.inl (two u v , Eq.refl , (a , (b , tt*)))

  Dl-⊗-in-r⁺ : (A & εTy) ⊗ Dl c B ⊢ Dl c (A ⊗ B)
  Dl-⊗-in-r⁺ m (ms , e , ((a , u) , (b , _))) =
    go (ms zero) (ms (suc zero)) a b (u .snd .fst) e
    where
    go : (x y : String) → A x → B (c ∷ y) → [] Eq.≡ x → (x ++ y) Eq.≡ m
       → (A ⊗ B) (c ∷ m)
    go .[] y a b Eq.refl Eq.refl = two [] (c ∷ y) , Eq.refl , (a , (b , tt*))

  Dl-⊕-out : Dl c (A ⊕ B) ⊢ Dl c A ⊕ Dl c B
  Dl-⊕-out m (Sum.inl a) = Sum.inl a
  Dl-⊕-out m (Sum.inr b) = Sum.inr b

  Dl-⊕-in : Dl c A ⊕ Dl c B ⊢ Dl c (A ⊕ B)
  Dl-⊕-in m (Sum.inl a) = Sum.inl a
  Dl-⊕-in m (Sum.inr b) = Sum.inr b

-- a map of grammars acts on derivatives by applying it one letter in
Dl-map : (c : Alphabet) {C : TheoryTy ℓA tt} {D : TheoryTy ℓB tt}
  → C ⊢ D → Dl c C ⊢ Dl c D
Dl-map c f m x = f (c ∷ m) x



δ-sound : ∀ {n} (r : RE n) (c : Alphabet)
  → ty ⟦ δ r c .snd ⟧ ⊢ Dl c (ty ⟦ r ⟧)
δ-sound εr c = ⊥Ty-elim
δ-sound ⊥r c = ⊥Ty-elim
-- an `εTy` element carries `[] Eq.≡ m`, so `c ∷ m` is `c ∷ []`
δ-sound ⟨ d ⟩r c with d ≟ c
... | Sum.inl Eq.refl = λ m x → Eq.ap (d ∷_) (Eq.sym (x .snd .fst))
... | Sum.inr _ = ⊥Ty-elim
δ-sound (satr P) c with P c in eq
... | true = λ m x → (c , Eq.eqToPath eq) , Eq.ap (c ∷_) (Eq.sym (x .snd .fst))
... | false = ⊥Ty-elim
δ-sound (_⊗r_ {nullable} {n'} r r') c =
  ⊕-elim (Dl-⊗-in-l c ∘⊢ (δ-sound r c ,⊗ id⊢) ∘⊢ ⊗s-out (δ r c) (n' , r'))
         (Dl-⊗-in-r c (re-Nullable r refl) ∘⊢ δ-sound r' c)
  ∘⊢ ⊕s-out (δ r c ⊗s (n' , r')) (δ r' c)
δ-sound (_⊗r_ {notNullable} {n'} r r') c =
  Dl-⊗-in-l c ∘⊢ (δ-sound r c ,⊗ id⊢) ∘⊢ ⊗s-out (δ r c) (n' , r')
δ-sound (r ⊕r r') c =
  Dl-⊕-in c ∘⊢ (δ-sound r c ,⊕p δ-sound r' c) ∘⊢ ⊕s-out (δ r c) (δ r' c)
δ-sound (r *r) c =
  Dl-map c roll↑ ∘⊢ Dl-⊕-in c ∘⊢ inl
  ∘⊢ Dl-⊗-in-l c ∘⊢ (δ-sound r c ,⊗ id⊢) ∘⊢ ⊗s-out (δ r c) (nullable , r *r)

δ-complete : ∀ {n} (r : RE n) (c : Alphabet)
  → Dl c (ty ⟦ r ⟧) ⊢ ty ⟦ δ r c .snd ⟧
-- `εTy (c ∷ m)` would make `[]` a cons
δ-complete εr c m x = Empty.rec (LP.¬nil≡cons (Eq.eqToPath (x .snd .fst)))
δ-complete ⊥r c m x = Empty.rec (x .lower)
δ-complete ⟨ d ⟩r c with d ≟ c
... | Sum.inl Eq.refl =
      λ m x → (λ ()) , Eq.sym (Eq.pathToEq (LP.cons-inj₂ (Eq.eqToPath x))) , tt*
... | Sum.inr ne =
      λ m x → Empty.rec (ne (Eq.pathToEq (sym (LP.cons-inj₁ (Eq.eqToPath x)))))
δ-complete (satr P) c with P c in eq
... | true = λ m x → (λ ()) , Eq.sym (Eq.pathToEq (LP.cons-inj₂ (Eq.eqToPath (x .snd)))) , tt*
... | false = λ m x → Empty.rec (true≢false
      (sym (cong P (LP.cons-inj₁ (Eq.eqToPath (x .snd))) ∙ x .fst .snd)
       ∙ Eq.eqToPath eq))
  where open import Cubical.Data.Bool using (true≢false)
δ-complete (_⊗r_ {nullable} {n'} r r') c =
  ⊕s-in (δ r c ⊗s (n' , r')) (δ r' c)
  ∘⊢ ((⊗s-in (δ r c) (n' , r') ∘⊢ (δ-complete r c ,⊗ id⊢))
      ,⊕p δ-complete r' c)
  ∘⊢ Dl-⊗-out c
δ-complete (_⊗r_ {notNullable} {n'} r r') c =
  ⊗s-in (δ r c) (n' , r') ∘⊢ (δ-complete r c ,⊗ id⊢)
  ∘⊢ Dl-⊗-out! c (re-¬Nullable r refl)
δ-complete (r ⊕r r') c =
  ⊕s-in (δ r c) (δ r' c) ∘⊢ (δ-complete r c ,⊕p δ-complete r' c)
  ∘⊢ Dl-⊕-out c
δ-complete (r *r) c =
  ⊗s-in (δ r c) (nullable , r *r) ∘⊢ (δ-complete r c ,⊗ id⊢)
  ∘⊢ Dl-⊗-out! c (re-¬Nullable r refl)
  ∘⊢ ⊕-elim id⊢ (⊥Ty-elim ∘⊢ nilAbsurd) ∘⊢ Dl-⊕-out c ∘⊢ Dl-map c unroll↑
  where
  nilAbsurd : Dl c εTy ⊢ ⊥Ty
  nilAbsurd m x = Empty.rec (LP.¬nil≡cons (Eq.eqToPath (x .snd .fst)))
