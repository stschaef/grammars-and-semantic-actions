{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Theory.Finitary
open SortedSig
open SortedEqns
import Theory.Free.Base as FB
module Theory.Instances.Monoid.Strings.Terminal
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
open import Theory.Instances.Monoid.Strings.Base Alphabet isSetAlphabet
open import Theory.Type.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Inductive.HLevels MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Type.Top.Properties MonEqns Alphabet (λ _ → tt) listPresentation
open import Theory.Instances.Monoid.Strings.LinearProduct Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Strings.Distributivity Alphabet isSetAlphabet
open import Theory.Instances.Monoid.Strings.HLevels Alphabet isSetAlphabet

open WildCatNotation
open WildCatIso

kleeneBranch : Bool → Functor ℓM Unit (λ _ → tt) tt
kleeneBranch false = ⊗e ε· λ ()
kleeneBranch true = ⊗e _⊙_ (two (k char) (Var tt))

KleeneCode : Functor ℓM Unit (λ _ → tt) tt
KleeneCode = ⊕e Bool kleeneBranch

String* : TheoryTy (ℓF ℓM) tt
String* = μ {X = Unit} {xs = λ _ → tt} (λ _ → KleeneCode) tt

-- Here, not via `Star`: no definitional coincidence between two codes.
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

read : ⊤Ty ⊢ String*
read [] _ = stringNIL _ (lift εTy-pt)
read (c ∷ cs) _ =
  stringCONS _ (two (c ∷ []) cs , Eq.refl , ((c , Eq.refl) , read cs _ , tt*))

private
  -- explicit type pins the level, so the `Lift` levels are not free metas
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

  -- a cons layer over a list splits definitionally
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

  -- by cases on the input list: `Eq.refl` on `p` exposes the head the
  -- layer's tuple keeps behind a function application
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

unambiguous-char : (m : String) → isProp (char m)
unambiguous-char = isPropChar

read-section : read ∘⊢ ⊤Ty-intro ≡ id⊢
read-section =
  rec-section (λ _ → KleeneCode) (λ _ → ⊤Ty-intro) (λ _ → read) readSq tt

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
