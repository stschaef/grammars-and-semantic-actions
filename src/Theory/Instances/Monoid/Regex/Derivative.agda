{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Brzozowski derivatives: one δ-step per character regardless of ambiguity,
   vs `decide-r`.s cost in the number of parses (2^14 for `(a|a)*b` on 14 letters). -}
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

δ : ∀ {n} → RE n → Alphabet → RE?
δ εr c = ∅?
δ ⊥r c = ∅?
δ ⟨ d ⟩r c = Sum.rec (λ _ → ε?) (λ _ → ∅?) (d ≟ c)
δ (satr P) c with P c
... | true = ε?
... | false = ∅?
δ (_⊗r_ {nullable} {n'} r r') c = (δ r c ⊗? (n' , r')) ⊕? δ r' c
δ (_⊗r_ {notNullable} {n'} r r') c = δ r c ⊗? (n' , r')
δ (r ⊕r r') c = δ r c ⊕? δ r' c
δ (r *r) c = δ r c ⊗? (nullable , r *r)


residual : ∀ {n} → RE n → List Alphabet → RE?
residual r [] = _ , r
residual r (c ∷ w) = residual (δ r c .snd) w

-- The syntactic derivative computes the semantic one: `Dl c ⟦ r ⟧ ≅ ⟦ δ r c ⟧`.

open import Theory.Instances.Monoid.Precise Alphabet isSetAlphabet using (Dl-ε)
open import Theory.Instances.Monoid.Derivative Alphabet isSetAlphabet
  using (Dl)
open import Theory.Instances.Monoid.Residual Alphabet isSetAlphabet
  using (⊗ε-unit-l⁻)

-- Confining case analysis to these four lemmas keeps δ-sound/δ-complete structural.

⊗?-out : (x y : RE?) → ty ⟦ (x ⊗? y) .snd ⟧ ⊢ ty ⟦ x .snd ⟧ ⊗ ty ⟦ y .snd ⟧
⊗?-out (n , r) (n' , r') = id⊢

⊗?-in : (x y : RE?) → ty ⟦ x .snd ⟧ ⊗ ty ⟦ y .snd ⟧ ⊢ ty ⟦ (x ⊗? y) .snd ⟧
⊗?-in (n , r) (n' , r') = id⊢

⊕?-out : (x y : RE?) → ty ⟦ (x ⊕? y) .snd ⟧ ⊢ ty ⟦ x .snd ⟧ ⊕ ty ⟦ y .snd ⟧
⊕?-out (n , r) (n' , r') = id⊢

⊕?-in : (x y : RE?) → ty ⟦ x .snd ⟧ ⊕ ty ⟦ y .snd ⟧ ⊢ ty ⟦ (x ⊕? y) .snd ⟧
⊕?-in (n , r) (n' , r') = id⊢



private
  uncons++ : (u v : String) (c : Alphabet) (m : String)
    → (u ++ v) ≡ (c ∷ m)
    → ((u ≡ []) × (v ≡ c ∷ m))
      Sum.⊎ (Σ[ p ∈ String ] ((u ≡ c ∷ p) × ((p ++ v) ≡ m)))
  uncons++ [] v c m e = Sum.inl (refl , e)
  uncons++ (d ∷ u) v c m e =
    Sum.inr (u , cong (_∷ u) (LP.cons-inj₁ e) , LP.cons-inj₂ e)

private variable ℓA ℓB : Level

module _ (c : Alphabet) {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt} where

  Dl-⊗-out : Dl c (A ⊗ B) ⊢ (Dl c A ⊗ B) ⊕ Dl c B
  Dl-⊗-out m (ms , e , (a , (b , _))) with
    uncons++ (ms zero) (ms (suc zero)) c m (Eq.eqToPath e)
  ... | Sum.inl (u≡[] , v≡cm) =
        Sum.inr (subst B v≡cm b)
  ... | Sum.inr (p , u≡cp , pv≡m) =
        Sum.inl ( two p (ms (suc zero))
                , Eq.pathToEq pv≡m
                , (subst A u≡cp a , (b , tt*)))

  Dl-⊗-in-l : (Dl c A ⊗ B) ⊢ Dl c (A ⊗ B)
  Dl-⊗-in-l m (ms , e , (a , (b , _))) =
      two (c ∷ ms zero) (ms (suc zero))
    , Eq.ap (c ∷_) e
    , (a , (b , tt*))

  Dl-⊗-in-r : (εTy ⊢ A) → Dl c B ⊢ Dl c (A ⊗ B)
  Dl-⊗-in-r nul m b =
      two [] (c ∷ m)
    , Eq.refl
    , (nul [] εTy-pt , (b , tt*))

  Dl-⊗-out! : ¬Nullable A → Dl c (A ⊗ B) ⊢ Dl c A ⊗ B
  Dl-⊗-out! nn m (ms , e , (a , (b , _))) with
    uncons++ (ms zero) (ms (suc zero)) c m (Eq.eqToPath e)
  ... | Sum.inr (p , u≡cp , pv≡m) =
        two p (ms (suc zero)) , Eq.pathToEq pv≡m
      , (subst A u≡cp a , (b , tt*))
  ... | Sum.inl (u≡[] , _) =
        Empty.rec (lower (nn [] (subst A u≡[] a , εTy-pt)))

  -- `A & εTy` keeps every null parse (not one chosen section), so the two
  -- directions are inverse even for ambiguous `A`.
  Dl-⊗-out⁺ : Dl c (A ⊗ B) ⊢ (Dl c A ⊗ B) ⊕ ((A & εTy) ⊗ Dl c B)
  Dl-⊗-out⁺ m (ms , e , (a , (b , _))) = go (ms zero) (ms (suc zero)) m a b e
    where
    -- match the equation rather than subst so branches compute on canonical strings
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
  Dl-⊕-out = id⊢

  Dl-⊕-in : Dl c A ⊕ Dl c B ⊢ Dl c (A ⊕ B)
  Dl-⊕-in = id⊢

Dl-map : (c : Alphabet) {C : TheoryTy ℓA tt} {D : TheoryTy ℓB tt}
  → C ⊢ D → Dl c C ⊢ Dl c D
Dl-map c f m x = f (c ∷ m) x



δ-sound : ∀ {n} (r : RE n) (c : Alphabet)
  → ty ⟦ δ r c .snd ⟧ ⊢ Dl c (ty ⟦ r ⟧)
δ-sound εr c = ⊥Ty-elim
δ-sound ⊥r c = ⊥Ty-elim
δ-sound ⟨ d ⟩r c with d ≟ c
... | Sum.inl Eq.refl = λ m x → Eq.ap (d ∷_) (Eq.sym (x .snd .fst))
... | Sum.inr _ = ⊥Ty-elim
δ-sound (satr P) c with P c in eq
... | true = λ m x → (c , Eq.eqToPath eq) , Eq.ap (c ∷_) (Eq.sym (x .snd .fst))
... | false = ⊥Ty-elim
δ-sound (_⊗r_ {nullable} {n'} r r') c =
  ⊕-elim (Dl-⊗-in-l c ∘⊢ (δ-sound r c ,⊗ id⊢) ∘⊢ ⊗?-out (δ r c) (n' , r'))
         (Dl-⊗-in-r c (re-Nullable r refl) ∘⊢ δ-sound r' c)
  ∘⊢ ⊕?-out (δ r c ⊗? (n' , r')) (δ r' c)
δ-sound (_⊗r_ {notNullable} {n'} r r') c =
  Dl-⊗-in-l c ∘⊢ (δ-sound r c ,⊗ id⊢) ∘⊢ ⊗?-out (δ r c) (n' , r')
δ-sound (r ⊕r r') c =
  Dl-⊕-in c ∘⊢ (δ-sound r c ,⊕p δ-sound r' c) ∘⊢ ⊕?-out (δ r c) (δ r' c)
δ-sound (r *r) c =
  Dl-map c roll↑ ∘⊢ Dl-⊕-in c ∘⊢ inl
  ∘⊢ Dl-⊗-in-l c ∘⊢ (δ-sound r c ,⊗ id⊢) ∘⊢ ⊗?-out (δ r c) (nullable , r *r)

δ-complete : ∀ {n} (r : RE n) (c : Alphabet)
  → Dl c (ty ⟦ r ⟧) ⊢ ty ⟦ δ r c .snd ⟧
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
  ⊕?-in (δ r c ⊗? (n' , r')) (δ r' c)
  ∘⊢ ((⊗?-in (δ r c) (n' , r') ∘⊢ (δ-complete r c ,⊗ id⊢))
      ,⊕p δ-complete r' c)
  ∘⊢ Dl-⊗-out c
δ-complete (_⊗r_ {notNullable} {n'} r r') c =
  ⊗?-in (δ r c) (n' , r') ∘⊢ (δ-complete r c ,⊗ id⊢)
  ∘⊢ Dl-⊗-out! c (re-¬Nullable r refl)
δ-complete (r ⊕r r') c =
  ⊕?-in (δ r c) (δ r' c) ∘⊢ (δ-complete r c ,⊕p δ-complete r' c)
  ∘⊢ Dl-⊕-out c
δ-complete (r *r) c =
  ⊗?-in (δ r c) (nullable , r *r) ∘⊢ (δ-complete r c ,⊗ id⊢)
  ∘⊢ Dl-⊗-out! c (re-¬Nullable r refl)
  ∘⊢ ⊕-elim id⊢ (⊥Ty-elim ∘⊢ Dl-ε c) ∘⊢ Dl-⊕-out c ∘⊢ Dl-map c unroll↑
