{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A simply typed lambda calculus with data: three mutually recursive
   nonterminals, twenty-six productions, parsed predictively.

     A ::= bool | nat | arr A A | prod A A | list A
     v ::= f | g | n | x | xs
     t ::= true | false | if t then t else t
         | zero | suc t | natrec t t t
         | lam v : A . t | app t t
         | pair t t | fst t | snd t
         | nil : A | cons t t | foldr t t t
         | let v = t in t | v

   Every former is prefix or keyword-led, so every production is terminal-led
   and the table's type is the whole LL(1) argument.  `Src` below builds the
   token list a program is, so the tests read as programs. -}
open import Cubical.Foundations.Prelude
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

module Theory.Instances.Monoid.Combinator.Decidable.STLC where

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit using (tt)

data Tok : Type ℓ-zero where
  kbool knat karr kprod klist ktrue kfalse kif kthen kelse kzero ksuc knatrec klam kcolon kdot kapp kpair kfst ksnd knil kcons kfoldr klet kassign kin vf vg vn vx vxs : Tok

-- The 31x31 table below is 961 lines, 48% of this file, and it looks like
-- the most obvious duplication in the tree.  It is not: it is paying for
-- reduction, and the price of removing it was measured.
--
-- Replacing it with `sectionDiscrete uncode code uncode-code discreteℕ`
-- (a `code : Tok → ℕ`, a list-based `uncode`, and 31 `refl`s -- 125 lines)
-- typechecks the definition, but `sectionDiscrete`'s `yes` branch builds
-- `sym (sect x) ∙∙ cong f p ∙∙ sect y`, a path composition *per token
-- comparison*.  The parser dispatches on `_≟T_` at every step, and the
-- tests at the bottom of this file run it by normalisation, so that cost is
-- multiplied by the whole parse: the module went from checking inside the
-- ordinary build to 6 GB resident and still climbing after five minutes,
-- and was killed rather than allowed to finish.
--
-- So the table stays, and this comment is the reason.  A cheaper
-- derivation would have to reduce to `inl Eq.refl`/`inr _` in one step --
-- e.g. deciding on `code a ≡ᵇ code b` and recovering the `Eq.≡` without a
-- composite path -- not go through `Discrete`.
_≟T_ : (a b : Tok) → (a Eq.≡ b) Sum.⊎ ((a Eq.≡ b) → Empty.⊥)
kbool ≟T kbool = Sum.inl Eq.refl
kbool ≟T knat = Sum.inr λ ()
kbool ≟T karr = Sum.inr λ ()
kbool ≟T kprod = Sum.inr λ ()
kbool ≟T klist = Sum.inr λ ()
kbool ≟T ktrue = Sum.inr λ ()
kbool ≟T kfalse = Sum.inr λ ()
kbool ≟T kif = Sum.inr λ ()
kbool ≟T kthen = Sum.inr λ ()
kbool ≟T kelse = Sum.inr λ ()
kbool ≟T kzero = Sum.inr λ ()
kbool ≟T ksuc = Sum.inr λ ()
kbool ≟T knatrec = Sum.inr λ ()
kbool ≟T klam = Sum.inr λ ()
kbool ≟T kcolon = Sum.inr λ ()
kbool ≟T kdot = Sum.inr λ ()
kbool ≟T kapp = Sum.inr λ ()
kbool ≟T kpair = Sum.inr λ ()
kbool ≟T kfst = Sum.inr λ ()
kbool ≟T ksnd = Sum.inr λ ()
kbool ≟T knil = Sum.inr λ ()
kbool ≟T kcons = Sum.inr λ ()
kbool ≟T kfoldr = Sum.inr λ ()
kbool ≟T klet = Sum.inr λ ()
kbool ≟T kassign = Sum.inr λ ()
kbool ≟T kin = Sum.inr λ ()
kbool ≟T vf = Sum.inr λ ()
kbool ≟T vg = Sum.inr λ ()
kbool ≟T vn = Sum.inr λ ()
kbool ≟T vx = Sum.inr λ ()
kbool ≟T vxs = Sum.inr λ ()
knat ≟T kbool = Sum.inr λ ()
knat ≟T knat = Sum.inl Eq.refl
knat ≟T karr = Sum.inr λ ()
knat ≟T kprod = Sum.inr λ ()
knat ≟T klist = Sum.inr λ ()
knat ≟T ktrue = Sum.inr λ ()
knat ≟T kfalse = Sum.inr λ ()
knat ≟T kif = Sum.inr λ ()
knat ≟T kthen = Sum.inr λ ()
knat ≟T kelse = Sum.inr λ ()
knat ≟T kzero = Sum.inr λ ()
knat ≟T ksuc = Sum.inr λ ()
knat ≟T knatrec = Sum.inr λ ()
knat ≟T klam = Sum.inr λ ()
knat ≟T kcolon = Sum.inr λ ()
knat ≟T kdot = Sum.inr λ ()
knat ≟T kapp = Sum.inr λ ()
knat ≟T kpair = Sum.inr λ ()
knat ≟T kfst = Sum.inr λ ()
knat ≟T ksnd = Sum.inr λ ()
knat ≟T knil = Sum.inr λ ()
knat ≟T kcons = Sum.inr λ ()
knat ≟T kfoldr = Sum.inr λ ()
knat ≟T klet = Sum.inr λ ()
knat ≟T kassign = Sum.inr λ ()
knat ≟T kin = Sum.inr λ ()
knat ≟T vf = Sum.inr λ ()
knat ≟T vg = Sum.inr λ ()
knat ≟T vn = Sum.inr λ ()
knat ≟T vx = Sum.inr λ ()
knat ≟T vxs = Sum.inr λ ()
karr ≟T kbool = Sum.inr λ ()
karr ≟T knat = Sum.inr λ ()
karr ≟T karr = Sum.inl Eq.refl
karr ≟T kprod = Sum.inr λ ()
karr ≟T klist = Sum.inr λ ()
karr ≟T ktrue = Sum.inr λ ()
karr ≟T kfalse = Sum.inr λ ()
karr ≟T kif = Sum.inr λ ()
karr ≟T kthen = Sum.inr λ ()
karr ≟T kelse = Sum.inr λ ()
karr ≟T kzero = Sum.inr λ ()
karr ≟T ksuc = Sum.inr λ ()
karr ≟T knatrec = Sum.inr λ ()
karr ≟T klam = Sum.inr λ ()
karr ≟T kcolon = Sum.inr λ ()
karr ≟T kdot = Sum.inr λ ()
karr ≟T kapp = Sum.inr λ ()
karr ≟T kpair = Sum.inr λ ()
karr ≟T kfst = Sum.inr λ ()
karr ≟T ksnd = Sum.inr λ ()
karr ≟T knil = Sum.inr λ ()
karr ≟T kcons = Sum.inr λ ()
karr ≟T kfoldr = Sum.inr λ ()
karr ≟T klet = Sum.inr λ ()
karr ≟T kassign = Sum.inr λ ()
karr ≟T kin = Sum.inr λ ()
karr ≟T vf = Sum.inr λ ()
karr ≟T vg = Sum.inr λ ()
karr ≟T vn = Sum.inr λ ()
karr ≟T vx = Sum.inr λ ()
karr ≟T vxs = Sum.inr λ ()
kprod ≟T kbool = Sum.inr λ ()
kprod ≟T knat = Sum.inr λ ()
kprod ≟T karr = Sum.inr λ ()
kprod ≟T kprod = Sum.inl Eq.refl
kprod ≟T klist = Sum.inr λ ()
kprod ≟T ktrue = Sum.inr λ ()
kprod ≟T kfalse = Sum.inr λ ()
kprod ≟T kif = Sum.inr λ ()
kprod ≟T kthen = Sum.inr λ ()
kprod ≟T kelse = Sum.inr λ ()
kprod ≟T kzero = Sum.inr λ ()
kprod ≟T ksuc = Sum.inr λ ()
kprod ≟T knatrec = Sum.inr λ ()
kprod ≟T klam = Sum.inr λ ()
kprod ≟T kcolon = Sum.inr λ ()
kprod ≟T kdot = Sum.inr λ ()
kprod ≟T kapp = Sum.inr λ ()
kprod ≟T kpair = Sum.inr λ ()
kprod ≟T kfst = Sum.inr λ ()
kprod ≟T ksnd = Sum.inr λ ()
kprod ≟T knil = Sum.inr λ ()
kprod ≟T kcons = Sum.inr λ ()
kprod ≟T kfoldr = Sum.inr λ ()
kprod ≟T klet = Sum.inr λ ()
kprod ≟T kassign = Sum.inr λ ()
kprod ≟T kin = Sum.inr λ ()
kprod ≟T vf = Sum.inr λ ()
kprod ≟T vg = Sum.inr λ ()
kprod ≟T vn = Sum.inr λ ()
kprod ≟T vx = Sum.inr λ ()
kprod ≟T vxs = Sum.inr λ ()
klist ≟T kbool = Sum.inr λ ()
klist ≟T knat = Sum.inr λ ()
klist ≟T karr = Sum.inr λ ()
klist ≟T kprod = Sum.inr λ ()
klist ≟T klist = Sum.inl Eq.refl
klist ≟T ktrue = Sum.inr λ ()
klist ≟T kfalse = Sum.inr λ ()
klist ≟T kif = Sum.inr λ ()
klist ≟T kthen = Sum.inr λ ()
klist ≟T kelse = Sum.inr λ ()
klist ≟T kzero = Sum.inr λ ()
klist ≟T ksuc = Sum.inr λ ()
klist ≟T knatrec = Sum.inr λ ()
klist ≟T klam = Sum.inr λ ()
klist ≟T kcolon = Sum.inr λ ()
klist ≟T kdot = Sum.inr λ ()
klist ≟T kapp = Sum.inr λ ()
klist ≟T kpair = Sum.inr λ ()
klist ≟T kfst = Sum.inr λ ()
klist ≟T ksnd = Sum.inr λ ()
klist ≟T knil = Sum.inr λ ()
klist ≟T kcons = Sum.inr λ ()
klist ≟T kfoldr = Sum.inr λ ()
klist ≟T klet = Sum.inr λ ()
klist ≟T kassign = Sum.inr λ ()
klist ≟T kin = Sum.inr λ ()
klist ≟T vf = Sum.inr λ ()
klist ≟T vg = Sum.inr λ ()
klist ≟T vn = Sum.inr λ ()
klist ≟T vx = Sum.inr λ ()
klist ≟T vxs = Sum.inr λ ()
ktrue ≟T kbool = Sum.inr λ ()
ktrue ≟T knat = Sum.inr λ ()
ktrue ≟T karr = Sum.inr λ ()
ktrue ≟T kprod = Sum.inr λ ()
ktrue ≟T klist = Sum.inr λ ()
ktrue ≟T ktrue = Sum.inl Eq.refl
ktrue ≟T kfalse = Sum.inr λ ()
ktrue ≟T kif = Sum.inr λ ()
ktrue ≟T kthen = Sum.inr λ ()
ktrue ≟T kelse = Sum.inr λ ()
ktrue ≟T kzero = Sum.inr λ ()
ktrue ≟T ksuc = Sum.inr λ ()
ktrue ≟T knatrec = Sum.inr λ ()
ktrue ≟T klam = Sum.inr λ ()
ktrue ≟T kcolon = Sum.inr λ ()
ktrue ≟T kdot = Sum.inr λ ()
ktrue ≟T kapp = Sum.inr λ ()
ktrue ≟T kpair = Sum.inr λ ()
ktrue ≟T kfst = Sum.inr λ ()
ktrue ≟T ksnd = Sum.inr λ ()
ktrue ≟T knil = Sum.inr λ ()
ktrue ≟T kcons = Sum.inr λ ()
ktrue ≟T kfoldr = Sum.inr λ ()
ktrue ≟T klet = Sum.inr λ ()
ktrue ≟T kassign = Sum.inr λ ()
ktrue ≟T kin = Sum.inr λ ()
ktrue ≟T vf = Sum.inr λ ()
ktrue ≟T vg = Sum.inr λ ()
ktrue ≟T vn = Sum.inr λ ()
ktrue ≟T vx = Sum.inr λ ()
ktrue ≟T vxs = Sum.inr λ ()
kfalse ≟T kbool = Sum.inr λ ()
kfalse ≟T knat = Sum.inr λ ()
kfalse ≟T karr = Sum.inr λ ()
kfalse ≟T kprod = Sum.inr λ ()
kfalse ≟T klist = Sum.inr λ ()
kfalse ≟T ktrue = Sum.inr λ ()
kfalse ≟T kfalse = Sum.inl Eq.refl
kfalse ≟T kif = Sum.inr λ ()
kfalse ≟T kthen = Sum.inr λ ()
kfalse ≟T kelse = Sum.inr λ ()
kfalse ≟T kzero = Sum.inr λ ()
kfalse ≟T ksuc = Sum.inr λ ()
kfalse ≟T knatrec = Sum.inr λ ()
kfalse ≟T klam = Sum.inr λ ()
kfalse ≟T kcolon = Sum.inr λ ()
kfalse ≟T kdot = Sum.inr λ ()
kfalse ≟T kapp = Sum.inr λ ()
kfalse ≟T kpair = Sum.inr λ ()
kfalse ≟T kfst = Sum.inr λ ()
kfalse ≟T ksnd = Sum.inr λ ()
kfalse ≟T knil = Sum.inr λ ()
kfalse ≟T kcons = Sum.inr λ ()
kfalse ≟T kfoldr = Sum.inr λ ()
kfalse ≟T klet = Sum.inr λ ()
kfalse ≟T kassign = Sum.inr λ ()
kfalse ≟T kin = Sum.inr λ ()
kfalse ≟T vf = Sum.inr λ ()
kfalse ≟T vg = Sum.inr λ ()
kfalse ≟T vn = Sum.inr λ ()
kfalse ≟T vx = Sum.inr λ ()
kfalse ≟T vxs = Sum.inr λ ()
kif ≟T kbool = Sum.inr λ ()
kif ≟T knat = Sum.inr λ ()
kif ≟T karr = Sum.inr λ ()
kif ≟T kprod = Sum.inr λ ()
kif ≟T klist = Sum.inr λ ()
kif ≟T ktrue = Sum.inr λ ()
kif ≟T kfalse = Sum.inr λ ()
kif ≟T kif = Sum.inl Eq.refl
kif ≟T kthen = Sum.inr λ ()
kif ≟T kelse = Sum.inr λ ()
kif ≟T kzero = Sum.inr λ ()
kif ≟T ksuc = Sum.inr λ ()
kif ≟T knatrec = Sum.inr λ ()
kif ≟T klam = Sum.inr λ ()
kif ≟T kcolon = Sum.inr λ ()
kif ≟T kdot = Sum.inr λ ()
kif ≟T kapp = Sum.inr λ ()
kif ≟T kpair = Sum.inr λ ()
kif ≟T kfst = Sum.inr λ ()
kif ≟T ksnd = Sum.inr λ ()
kif ≟T knil = Sum.inr λ ()
kif ≟T kcons = Sum.inr λ ()
kif ≟T kfoldr = Sum.inr λ ()
kif ≟T klet = Sum.inr λ ()
kif ≟T kassign = Sum.inr λ ()
kif ≟T kin = Sum.inr λ ()
kif ≟T vf = Sum.inr λ ()
kif ≟T vg = Sum.inr λ ()
kif ≟T vn = Sum.inr λ ()
kif ≟T vx = Sum.inr λ ()
kif ≟T vxs = Sum.inr λ ()
kthen ≟T kbool = Sum.inr λ ()
kthen ≟T knat = Sum.inr λ ()
kthen ≟T karr = Sum.inr λ ()
kthen ≟T kprod = Sum.inr λ ()
kthen ≟T klist = Sum.inr λ ()
kthen ≟T ktrue = Sum.inr λ ()
kthen ≟T kfalse = Sum.inr λ ()
kthen ≟T kif = Sum.inr λ ()
kthen ≟T kthen = Sum.inl Eq.refl
kthen ≟T kelse = Sum.inr λ ()
kthen ≟T kzero = Sum.inr λ ()
kthen ≟T ksuc = Sum.inr λ ()
kthen ≟T knatrec = Sum.inr λ ()
kthen ≟T klam = Sum.inr λ ()
kthen ≟T kcolon = Sum.inr λ ()
kthen ≟T kdot = Sum.inr λ ()
kthen ≟T kapp = Sum.inr λ ()
kthen ≟T kpair = Sum.inr λ ()
kthen ≟T kfst = Sum.inr λ ()
kthen ≟T ksnd = Sum.inr λ ()
kthen ≟T knil = Sum.inr λ ()
kthen ≟T kcons = Sum.inr λ ()
kthen ≟T kfoldr = Sum.inr λ ()
kthen ≟T klet = Sum.inr λ ()
kthen ≟T kassign = Sum.inr λ ()
kthen ≟T kin = Sum.inr λ ()
kthen ≟T vf = Sum.inr λ ()
kthen ≟T vg = Sum.inr λ ()
kthen ≟T vn = Sum.inr λ ()
kthen ≟T vx = Sum.inr λ ()
kthen ≟T vxs = Sum.inr λ ()
kelse ≟T kbool = Sum.inr λ ()
kelse ≟T knat = Sum.inr λ ()
kelse ≟T karr = Sum.inr λ ()
kelse ≟T kprod = Sum.inr λ ()
kelse ≟T klist = Sum.inr λ ()
kelse ≟T ktrue = Sum.inr λ ()
kelse ≟T kfalse = Sum.inr λ ()
kelse ≟T kif = Sum.inr λ ()
kelse ≟T kthen = Sum.inr λ ()
kelse ≟T kelse = Sum.inl Eq.refl
kelse ≟T kzero = Sum.inr λ ()
kelse ≟T ksuc = Sum.inr λ ()
kelse ≟T knatrec = Sum.inr λ ()
kelse ≟T klam = Sum.inr λ ()
kelse ≟T kcolon = Sum.inr λ ()
kelse ≟T kdot = Sum.inr λ ()
kelse ≟T kapp = Sum.inr λ ()
kelse ≟T kpair = Sum.inr λ ()
kelse ≟T kfst = Sum.inr λ ()
kelse ≟T ksnd = Sum.inr λ ()
kelse ≟T knil = Sum.inr λ ()
kelse ≟T kcons = Sum.inr λ ()
kelse ≟T kfoldr = Sum.inr λ ()
kelse ≟T klet = Sum.inr λ ()
kelse ≟T kassign = Sum.inr λ ()
kelse ≟T kin = Sum.inr λ ()
kelse ≟T vf = Sum.inr λ ()
kelse ≟T vg = Sum.inr λ ()
kelse ≟T vn = Sum.inr λ ()
kelse ≟T vx = Sum.inr λ ()
kelse ≟T vxs = Sum.inr λ ()
kzero ≟T kbool = Sum.inr λ ()
kzero ≟T knat = Sum.inr λ ()
kzero ≟T karr = Sum.inr λ ()
kzero ≟T kprod = Sum.inr λ ()
kzero ≟T klist = Sum.inr λ ()
kzero ≟T ktrue = Sum.inr λ ()
kzero ≟T kfalse = Sum.inr λ ()
kzero ≟T kif = Sum.inr λ ()
kzero ≟T kthen = Sum.inr λ ()
kzero ≟T kelse = Sum.inr λ ()
kzero ≟T kzero = Sum.inl Eq.refl
kzero ≟T ksuc = Sum.inr λ ()
kzero ≟T knatrec = Sum.inr λ ()
kzero ≟T klam = Sum.inr λ ()
kzero ≟T kcolon = Sum.inr λ ()
kzero ≟T kdot = Sum.inr λ ()
kzero ≟T kapp = Sum.inr λ ()
kzero ≟T kpair = Sum.inr λ ()
kzero ≟T kfst = Sum.inr λ ()
kzero ≟T ksnd = Sum.inr λ ()
kzero ≟T knil = Sum.inr λ ()
kzero ≟T kcons = Sum.inr λ ()
kzero ≟T kfoldr = Sum.inr λ ()
kzero ≟T klet = Sum.inr λ ()
kzero ≟T kassign = Sum.inr λ ()
kzero ≟T kin = Sum.inr λ ()
kzero ≟T vf = Sum.inr λ ()
kzero ≟T vg = Sum.inr λ ()
kzero ≟T vn = Sum.inr λ ()
kzero ≟T vx = Sum.inr λ ()
kzero ≟T vxs = Sum.inr λ ()
ksuc ≟T kbool = Sum.inr λ ()
ksuc ≟T knat = Sum.inr λ ()
ksuc ≟T karr = Sum.inr λ ()
ksuc ≟T kprod = Sum.inr λ ()
ksuc ≟T klist = Sum.inr λ ()
ksuc ≟T ktrue = Sum.inr λ ()
ksuc ≟T kfalse = Sum.inr λ ()
ksuc ≟T kif = Sum.inr λ ()
ksuc ≟T kthen = Sum.inr λ ()
ksuc ≟T kelse = Sum.inr λ ()
ksuc ≟T kzero = Sum.inr λ ()
ksuc ≟T ksuc = Sum.inl Eq.refl
ksuc ≟T knatrec = Sum.inr λ ()
ksuc ≟T klam = Sum.inr λ ()
ksuc ≟T kcolon = Sum.inr λ ()
ksuc ≟T kdot = Sum.inr λ ()
ksuc ≟T kapp = Sum.inr λ ()
ksuc ≟T kpair = Sum.inr λ ()
ksuc ≟T kfst = Sum.inr λ ()
ksuc ≟T ksnd = Sum.inr λ ()
ksuc ≟T knil = Sum.inr λ ()
ksuc ≟T kcons = Sum.inr λ ()
ksuc ≟T kfoldr = Sum.inr λ ()
ksuc ≟T klet = Sum.inr λ ()
ksuc ≟T kassign = Sum.inr λ ()
ksuc ≟T kin = Sum.inr λ ()
ksuc ≟T vf = Sum.inr λ ()
ksuc ≟T vg = Sum.inr λ ()
ksuc ≟T vn = Sum.inr λ ()
ksuc ≟T vx = Sum.inr λ ()
ksuc ≟T vxs = Sum.inr λ ()
knatrec ≟T kbool = Sum.inr λ ()
knatrec ≟T knat = Sum.inr λ ()
knatrec ≟T karr = Sum.inr λ ()
knatrec ≟T kprod = Sum.inr λ ()
knatrec ≟T klist = Sum.inr λ ()
knatrec ≟T ktrue = Sum.inr λ ()
knatrec ≟T kfalse = Sum.inr λ ()
knatrec ≟T kif = Sum.inr λ ()
knatrec ≟T kthen = Sum.inr λ ()
knatrec ≟T kelse = Sum.inr λ ()
knatrec ≟T kzero = Sum.inr λ ()
knatrec ≟T ksuc = Sum.inr λ ()
knatrec ≟T knatrec = Sum.inl Eq.refl
knatrec ≟T klam = Sum.inr λ ()
knatrec ≟T kcolon = Sum.inr λ ()
knatrec ≟T kdot = Sum.inr λ ()
knatrec ≟T kapp = Sum.inr λ ()
knatrec ≟T kpair = Sum.inr λ ()
knatrec ≟T kfst = Sum.inr λ ()
knatrec ≟T ksnd = Sum.inr λ ()
knatrec ≟T knil = Sum.inr λ ()
knatrec ≟T kcons = Sum.inr λ ()
knatrec ≟T kfoldr = Sum.inr λ ()
knatrec ≟T klet = Sum.inr λ ()
knatrec ≟T kassign = Sum.inr λ ()
knatrec ≟T kin = Sum.inr λ ()
knatrec ≟T vf = Sum.inr λ ()
knatrec ≟T vg = Sum.inr λ ()
knatrec ≟T vn = Sum.inr λ ()
knatrec ≟T vx = Sum.inr λ ()
knatrec ≟T vxs = Sum.inr λ ()
klam ≟T kbool = Sum.inr λ ()
klam ≟T knat = Sum.inr λ ()
klam ≟T karr = Sum.inr λ ()
klam ≟T kprod = Sum.inr λ ()
klam ≟T klist = Sum.inr λ ()
klam ≟T ktrue = Sum.inr λ ()
klam ≟T kfalse = Sum.inr λ ()
klam ≟T kif = Sum.inr λ ()
klam ≟T kthen = Sum.inr λ ()
klam ≟T kelse = Sum.inr λ ()
klam ≟T kzero = Sum.inr λ ()
klam ≟T ksuc = Sum.inr λ ()
klam ≟T knatrec = Sum.inr λ ()
klam ≟T klam = Sum.inl Eq.refl
klam ≟T kcolon = Sum.inr λ ()
klam ≟T kdot = Sum.inr λ ()
klam ≟T kapp = Sum.inr λ ()
klam ≟T kpair = Sum.inr λ ()
klam ≟T kfst = Sum.inr λ ()
klam ≟T ksnd = Sum.inr λ ()
klam ≟T knil = Sum.inr λ ()
klam ≟T kcons = Sum.inr λ ()
klam ≟T kfoldr = Sum.inr λ ()
klam ≟T klet = Sum.inr λ ()
klam ≟T kassign = Sum.inr λ ()
klam ≟T kin = Sum.inr λ ()
klam ≟T vf = Sum.inr λ ()
klam ≟T vg = Sum.inr λ ()
klam ≟T vn = Sum.inr λ ()
klam ≟T vx = Sum.inr λ ()
klam ≟T vxs = Sum.inr λ ()
kcolon ≟T kbool = Sum.inr λ ()
kcolon ≟T knat = Sum.inr λ ()
kcolon ≟T karr = Sum.inr λ ()
kcolon ≟T kprod = Sum.inr λ ()
kcolon ≟T klist = Sum.inr λ ()
kcolon ≟T ktrue = Sum.inr λ ()
kcolon ≟T kfalse = Sum.inr λ ()
kcolon ≟T kif = Sum.inr λ ()
kcolon ≟T kthen = Sum.inr λ ()
kcolon ≟T kelse = Sum.inr λ ()
kcolon ≟T kzero = Sum.inr λ ()
kcolon ≟T ksuc = Sum.inr λ ()
kcolon ≟T knatrec = Sum.inr λ ()
kcolon ≟T klam = Sum.inr λ ()
kcolon ≟T kcolon = Sum.inl Eq.refl
kcolon ≟T kdot = Sum.inr λ ()
kcolon ≟T kapp = Sum.inr λ ()
kcolon ≟T kpair = Sum.inr λ ()
kcolon ≟T kfst = Sum.inr λ ()
kcolon ≟T ksnd = Sum.inr λ ()
kcolon ≟T knil = Sum.inr λ ()
kcolon ≟T kcons = Sum.inr λ ()
kcolon ≟T kfoldr = Sum.inr λ ()
kcolon ≟T klet = Sum.inr λ ()
kcolon ≟T kassign = Sum.inr λ ()
kcolon ≟T kin = Sum.inr λ ()
kcolon ≟T vf = Sum.inr λ ()
kcolon ≟T vg = Sum.inr λ ()
kcolon ≟T vn = Sum.inr λ ()
kcolon ≟T vx = Sum.inr λ ()
kcolon ≟T vxs = Sum.inr λ ()
kdot ≟T kbool = Sum.inr λ ()
kdot ≟T knat = Sum.inr λ ()
kdot ≟T karr = Sum.inr λ ()
kdot ≟T kprod = Sum.inr λ ()
kdot ≟T klist = Sum.inr λ ()
kdot ≟T ktrue = Sum.inr λ ()
kdot ≟T kfalse = Sum.inr λ ()
kdot ≟T kif = Sum.inr λ ()
kdot ≟T kthen = Sum.inr λ ()
kdot ≟T kelse = Sum.inr λ ()
kdot ≟T kzero = Sum.inr λ ()
kdot ≟T ksuc = Sum.inr λ ()
kdot ≟T knatrec = Sum.inr λ ()
kdot ≟T klam = Sum.inr λ ()
kdot ≟T kcolon = Sum.inr λ ()
kdot ≟T kdot = Sum.inl Eq.refl
kdot ≟T kapp = Sum.inr λ ()
kdot ≟T kpair = Sum.inr λ ()
kdot ≟T kfst = Sum.inr λ ()
kdot ≟T ksnd = Sum.inr λ ()
kdot ≟T knil = Sum.inr λ ()
kdot ≟T kcons = Sum.inr λ ()
kdot ≟T kfoldr = Sum.inr λ ()
kdot ≟T klet = Sum.inr λ ()
kdot ≟T kassign = Sum.inr λ ()
kdot ≟T kin = Sum.inr λ ()
kdot ≟T vf = Sum.inr λ ()
kdot ≟T vg = Sum.inr λ ()
kdot ≟T vn = Sum.inr λ ()
kdot ≟T vx = Sum.inr λ ()
kdot ≟T vxs = Sum.inr λ ()
kapp ≟T kbool = Sum.inr λ ()
kapp ≟T knat = Sum.inr λ ()
kapp ≟T karr = Sum.inr λ ()
kapp ≟T kprod = Sum.inr λ ()
kapp ≟T klist = Sum.inr λ ()
kapp ≟T ktrue = Sum.inr λ ()
kapp ≟T kfalse = Sum.inr λ ()
kapp ≟T kif = Sum.inr λ ()
kapp ≟T kthen = Sum.inr λ ()
kapp ≟T kelse = Sum.inr λ ()
kapp ≟T kzero = Sum.inr λ ()
kapp ≟T ksuc = Sum.inr λ ()
kapp ≟T knatrec = Sum.inr λ ()
kapp ≟T klam = Sum.inr λ ()
kapp ≟T kcolon = Sum.inr λ ()
kapp ≟T kdot = Sum.inr λ ()
kapp ≟T kapp = Sum.inl Eq.refl
kapp ≟T kpair = Sum.inr λ ()
kapp ≟T kfst = Sum.inr λ ()
kapp ≟T ksnd = Sum.inr λ ()
kapp ≟T knil = Sum.inr λ ()
kapp ≟T kcons = Sum.inr λ ()
kapp ≟T kfoldr = Sum.inr λ ()
kapp ≟T klet = Sum.inr λ ()
kapp ≟T kassign = Sum.inr λ ()
kapp ≟T kin = Sum.inr λ ()
kapp ≟T vf = Sum.inr λ ()
kapp ≟T vg = Sum.inr λ ()
kapp ≟T vn = Sum.inr λ ()
kapp ≟T vx = Sum.inr λ ()
kapp ≟T vxs = Sum.inr λ ()
kpair ≟T kbool = Sum.inr λ ()
kpair ≟T knat = Sum.inr λ ()
kpair ≟T karr = Sum.inr λ ()
kpair ≟T kprod = Sum.inr λ ()
kpair ≟T klist = Sum.inr λ ()
kpair ≟T ktrue = Sum.inr λ ()
kpair ≟T kfalse = Sum.inr λ ()
kpair ≟T kif = Sum.inr λ ()
kpair ≟T kthen = Sum.inr λ ()
kpair ≟T kelse = Sum.inr λ ()
kpair ≟T kzero = Sum.inr λ ()
kpair ≟T ksuc = Sum.inr λ ()
kpair ≟T knatrec = Sum.inr λ ()
kpair ≟T klam = Sum.inr λ ()
kpair ≟T kcolon = Sum.inr λ ()
kpair ≟T kdot = Sum.inr λ ()
kpair ≟T kapp = Sum.inr λ ()
kpair ≟T kpair = Sum.inl Eq.refl
kpair ≟T kfst = Sum.inr λ ()
kpair ≟T ksnd = Sum.inr λ ()
kpair ≟T knil = Sum.inr λ ()
kpair ≟T kcons = Sum.inr λ ()
kpair ≟T kfoldr = Sum.inr λ ()
kpair ≟T klet = Sum.inr λ ()
kpair ≟T kassign = Sum.inr λ ()
kpair ≟T kin = Sum.inr λ ()
kpair ≟T vf = Sum.inr λ ()
kpair ≟T vg = Sum.inr λ ()
kpair ≟T vn = Sum.inr λ ()
kpair ≟T vx = Sum.inr λ ()
kpair ≟T vxs = Sum.inr λ ()
kfst ≟T kbool = Sum.inr λ ()
kfst ≟T knat = Sum.inr λ ()
kfst ≟T karr = Sum.inr λ ()
kfst ≟T kprod = Sum.inr λ ()
kfst ≟T klist = Sum.inr λ ()
kfst ≟T ktrue = Sum.inr λ ()
kfst ≟T kfalse = Sum.inr λ ()
kfst ≟T kif = Sum.inr λ ()
kfst ≟T kthen = Sum.inr λ ()
kfst ≟T kelse = Sum.inr λ ()
kfst ≟T kzero = Sum.inr λ ()
kfst ≟T ksuc = Sum.inr λ ()
kfst ≟T knatrec = Sum.inr λ ()
kfst ≟T klam = Sum.inr λ ()
kfst ≟T kcolon = Sum.inr λ ()
kfst ≟T kdot = Sum.inr λ ()
kfst ≟T kapp = Sum.inr λ ()
kfst ≟T kpair = Sum.inr λ ()
kfst ≟T kfst = Sum.inl Eq.refl
kfst ≟T ksnd = Sum.inr λ ()
kfst ≟T knil = Sum.inr λ ()
kfst ≟T kcons = Sum.inr λ ()
kfst ≟T kfoldr = Sum.inr λ ()
kfst ≟T klet = Sum.inr λ ()
kfst ≟T kassign = Sum.inr λ ()
kfst ≟T kin = Sum.inr λ ()
kfst ≟T vf = Sum.inr λ ()
kfst ≟T vg = Sum.inr λ ()
kfst ≟T vn = Sum.inr λ ()
kfst ≟T vx = Sum.inr λ ()
kfst ≟T vxs = Sum.inr λ ()
ksnd ≟T kbool = Sum.inr λ ()
ksnd ≟T knat = Sum.inr λ ()
ksnd ≟T karr = Sum.inr λ ()
ksnd ≟T kprod = Sum.inr λ ()
ksnd ≟T klist = Sum.inr λ ()
ksnd ≟T ktrue = Sum.inr λ ()
ksnd ≟T kfalse = Sum.inr λ ()
ksnd ≟T kif = Sum.inr λ ()
ksnd ≟T kthen = Sum.inr λ ()
ksnd ≟T kelse = Sum.inr λ ()
ksnd ≟T kzero = Sum.inr λ ()
ksnd ≟T ksuc = Sum.inr λ ()
ksnd ≟T knatrec = Sum.inr λ ()
ksnd ≟T klam = Sum.inr λ ()
ksnd ≟T kcolon = Sum.inr λ ()
ksnd ≟T kdot = Sum.inr λ ()
ksnd ≟T kapp = Sum.inr λ ()
ksnd ≟T kpair = Sum.inr λ ()
ksnd ≟T kfst = Sum.inr λ ()
ksnd ≟T ksnd = Sum.inl Eq.refl
ksnd ≟T knil = Sum.inr λ ()
ksnd ≟T kcons = Sum.inr λ ()
ksnd ≟T kfoldr = Sum.inr λ ()
ksnd ≟T klet = Sum.inr λ ()
ksnd ≟T kassign = Sum.inr λ ()
ksnd ≟T kin = Sum.inr λ ()
ksnd ≟T vf = Sum.inr λ ()
ksnd ≟T vg = Sum.inr λ ()
ksnd ≟T vn = Sum.inr λ ()
ksnd ≟T vx = Sum.inr λ ()
ksnd ≟T vxs = Sum.inr λ ()
knil ≟T kbool = Sum.inr λ ()
knil ≟T knat = Sum.inr λ ()
knil ≟T karr = Sum.inr λ ()
knil ≟T kprod = Sum.inr λ ()
knil ≟T klist = Sum.inr λ ()
knil ≟T ktrue = Sum.inr λ ()
knil ≟T kfalse = Sum.inr λ ()
knil ≟T kif = Sum.inr λ ()
knil ≟T kthen = Sum.inr λ ()
knil ≟T kelse = Sum.inr λ ()
knil ≟T kzero = Sum.inr λ ()
knil ≟T ksuc = Sum.inr λ ()
knil ≟T knatrec = Sum.inr λ ()
knil ≟T klam = Sum.inr λ ()
knil ≟T kcolon = Sum.inr λ ()
knil ≟T kdot = Sum.inr λ ()
knil ≟T kapp = Sum.inr λ ()
knil ≟T kpair = Sum.inr λ ()
knil ≟T kfst = Sum.inr λ ()
knil ≟T ksnd = Sum.inr λ ()
knil ≟T knil = Sum.inl Eq.refl
knil ≟T kcons = Sum.inr λ ()
knil ≟T kfoldr = Sum.inr λ ()
knil ≟T klet = Sum.inr λ ()
knil ≟T kassign = Sum.inr λ ()
knil ≟T kin = Sum.inr λ ()
knil ≟T vf = Sum.inr λ ()
knil ≟T vg = Sum.inr λ ()
knil ≟T vn = Sum.inr λ ()
knil ≟T vx = Sum.inr λ ()
knil ≟T vxs = Sum.inr λ ()
kcons ≟T kbool = Sum.inr λ ()
kcons ≟T knat = Sum.inr λ ()
kcons ≟T karr = Sum.inr λ ()
kcons ≟T kprod = Sum.inr λ ()
kcons ≟T klist = Sum.inr λ ()
kcons ≟T ktrue = Sum.inr λ ()
kcons ≟T kfalse = Sum.inr λ ()
kcons ≟T kif = Sum.inr λ ()
kcons ≟T kthen = Sum.inr λ ()
kcons ≟T kelse = Sum.inr λ ()
kcons ≟T kzero = Sum.inr λ ()
kcons ≟T ksuc = Sum.inr λ ()
kcons ≟T knatrec = Sum.inr λ ()
kcons ≟T klam = Sum.inr λ ()
kcons ≟T kcolon = Sum.inr λ ()
kcons ≟T kdot = Sum.inr λ ()
kcons ≟T kapp = Sum.inr λ ()
kcons ≟T kpair = Sum.inr λ ()
kcons ≟T kfst = Sum.inr λ ()
kcons ≟T ksnd = Sum.inr λ ()
kcons ≟T knil = Sum.inr λ ()
kcons ≟T kcons = Sum.inl Eq.refl
kcons ≟T kfoldr = Sum.inr λ ()
kcons ≟T klet = Sum.inr λ ()
kcons ≟T kassign = Sum.inr λ ()
kcons ≟T kin = Sum.inr λ ()
kcons ≟T vf = Sum.inr λ ()
kcons ≟T vg = Sum.inr λ ()
kcons ≟T vn = Sum.inr λ ()
kcons ≟T vx = Sum.inr λ ()
kcons ≟T vxs = Sum.inr λ ()
kfoldr ≟T kbool = Sum.inr λ ()
kfoldr ≟T knat = Sum.inr λ ()
kfoldr ≟T karr = Sum.inr λ ()
kfoldr ≟T kprod = Sum.inr λ ()
kfoldr ≟T klist = Sum.inr λ ()
kfoldr ≟T ktrue = Sum.inr λ ()
kfoldr ≟T kfalse = Sum.inr λ ()
kfoldr ≟T kif = Sum.inr λ ()
kfoldr ≟T kthen = Sum.inr λ ()
kfoldr ≟T kelse = Sum.inr λ ()
kfoldr ≟T kzero = Sum.inr λ ()
kfoldr ≟T ksuc = Sum.inr λ ()
kfoldr ≟T knatrec = Sum.inr λ ()
kfoldr ≟T klam = Sum.inr λ ()
kfoldr ≟T kcolon = Sum.inr λ ()
kfoldr ≟T kdot = Sum.inr λ ()
kfoldr ≟T kapp = Sum.inr λ ()
kfoldr ≟T kpair = Sum.inr λ ()
kfoldr ≟T kfst = Sum.inr λ ()
kfoldr ≟T ksnd = Sum.inr λ ()
kfoldr ≟T knil = Sum.inr λ ()
kfoldr ≟T kcons = Sum.inr λ ()
kfoldr ≟T kfoldr = Sum.inl Eq.refl
kfoldr ≟T klet = Sum.inr λ ()
kfoldr ≟T kassign = Sum.inr λ ()
kfoldr ≟T kin = Sum.inr λ ()
kfoldr ≟T vf = Sum.inr λ ()
kfoldr ≟T vg = Sum.inr λ ()
kfoldr ≟T vn = Sum.inr λ ()
kfoldr ≟T vx = Sum.inr λ ()
kfoldr ≟T vxs = Sum.inr λ ()
klet ≟T kbool = Sum.inr λ ()
klet ≟T knat = Sum.inr λ ()
klet ≟T karr = Sum.inr λ ()
klet ≟T kprod = Sum.inr λ ()
klet ≟T klist = Sum.inr λ ()
klet ≟T ktrue = Sum.inr λ ()
klet ≟T kfalse = Sum.inr λ ()
klet ≟T kif = Sum.inr λ ()
klet ≟T kthen = Sum.inr λ ()
klet ≟T kelse = Sum.inr λ ()
klet ≟T kzero = Sum.inr λ ()
klet ≟T ksuc = Sum.inr λ ()
klet ≟T knatrec = Sum.inr λ ()
klet ≟T klam = Sum.inr λ ()
klet ≟T kcolon = Sum.inr λ ()
klet ≟T kdot = Sum.inr λ ()
klet ≟T kapp = Sum.inr λ ()
klet ≟T kpair = Sum.inr λ ()
klet ≟T kfst = Sum.inr λ ()
klet ≟T ksnd = Sum.inr λ ()
klet ≟T knil = Sum.inr λ ()
klet ≟T kcons = Sum.inr λ ()
klet ≟T kfoldr = Sum.inr λ ()
klet ≟T klet = Sum.inl Eq.refl
klet ≟T kassign = Sum.inr λ ()
klet ≟T kin = Sum.inr λ ()
klet ≟T vf = Sum.inr λ ()
klet ≟T vg = Sum.inr λ ()
klet ≟T vn = Sum.inr λ ()
klet ≟T vx = Sum.inr λ ()
klet ≟T vxs = Sum.inr λ ()
kassign ≟T kbool = Sum.inr λ ()
kassign ≟T knat = Sum.inr λ ()
kassign ≟T karr = Sum.inr λ ()
kassign ≟T kprod = Sum.inr λ ()
kassign ≟T klist = Sum.inr λ ()
kassign ≟T ktrue = Sum.inr λ ()
kassign ≟T kfalse = Sum.inr λ ()
kassign ≟T kif = Sum.inr λ ()
kassign ≟T kthen = Sum.inr λ ()
kassign ≟T kelse = Sum.inr λ ()
kassign ≟T kzero = Sum.inr λ ()
kassign ≟T ksuc = Sum.inr λ ()
kassign ≟T knatrec = Sum.inr λ ()
kassign ≟T klam = Sum.inr λ ()
kassign ≟T kcolon = Sum.inr λ ()
kassign ≟T kdot = Sum.inr λ ()
kassign ≟T kapp = Sum.inr λ ()
kassign ≟T kpair = Sum.inr λ ()
kassign ≟T kfst = Sum.inr λ ()
kassign ≟T ksnd = Sum.inr λ ()
kassign ≟T knil = Sum.inr λ ()
kassign ≟T kcons = Sum.inr λ ()
kassign ≟T kfoldr = Sum.inr λ ()
kassign ≟T klet = Sum.inr λ ()
kassign ≟T kassign = Sum.inl Eq.refl
kassign ≟T kin = Sum.inr λ ()
kassign ≟T vf = Sum.inr λ ()
kassign ≟T vg = Sum.inr λ ()
kassign ≟T vn = Sum.inr λ ()
kassign ≟T vx = Sum.inr λ ()
kassign ≟T vxs = Sum.inr λ ()
kin ≟T kbool = Sum.inr λ ()
kin ≟T knat = Sum.inr λ ()
kin ≟T karr = Sum.inr λ ()
kin ≟T kprod = Sum.inr λ ()
kin ≟T klist = Sum.inr λ ()
kin ≟T ktrue = Sum.inr λ ()
kin ≟T kfalse = Sum.inr λ ()
kin ≟T kif = Sum.inr λ ()
kin ≟T kthen = Sum.inr λ ()
kin ≟T kelse = Sum.inr λ ()
kin ≟T kzero = Sum.inr λ ()
kin ≟T ksuc = Sum.inr λ ()
kin ≟T knatrec = Sum.inr λ ()
kin ≟T klam = Sum.inr λ ()
kin ≟T kcolon = Sum.inr λ ()
kin ≟T kdot = Sum.inr λ ()
kin ≟T kapp = Sum.inr λ ()
kin ≟T kpair = Sum.inr λ ()
kin ≟T kfst = Sum.inr λ ()
kin ≟T ksnd = Sum.inr λ ()
kin ≟T knil = Sum.inr λ ()
kin ≟T kcons = Sum.inr λ ()
kin ≟T kfoldr = Sum.inr λ ()
kin ≟T klet = Sum.inr λ ()
kin ≟T kassign = Sum.inr λ ()
kin ≟T kin = Sum.inl Eq.refl
kin ≟T vf = Sum.inr λ ()
kin ≟T vg = Sum.inr λ ()
kin ≟T vn = Sum.inr λ ()
kin ≟T vx = Sum.inr λ ()
kin ≟T vxs = Sum.inr λ ()
vf ≟T kbool = Sum.inr λ ()
vf ≟T knat = Sum.inr λ ()
vf ≟T karr = Sum.inr λ ()
vf ≟T kprod = Sum.inr λ ()
vf ≟T klist = Sum.inr λ ()
vf ≟T ktrue = Sum.inr λ ()
vf ≟T kfalse = Sum.inr λ ()
vf ≟T kif = Sum.inr λ ()
vf ≟T kthen = Sum.inr λ ()
vf ≟T kelse = Sum.inr λ ()
vf ≟T kzero = Sum.inr λ ()
vf ≟T ksuc = Sum.inr λ ()
vf ≟T knatrec = Sum.inr λ ()
vf ≟T klam = Sum.inr λ ()
vf ≟T kcolon = Sum.inr λ ()
vf ≟T kdot = Sum.inr λ ()
vf ≟T kapp = Sum.inr λ ()
vf ≟T kpair = Sum.inr λ ()
vf ≟T kfst = Sum.inr λ ()
vf ≟T ksnd = Sum.inr λ ()
vf ≟T knil = Sum.inr λ ()
vf ≟T kcons = Sum.inr λ ()
vf ≟T kfoldr = Sum.inr λ ()
vf ≟T klet = Sum.inr λ ()
vf ≟T kassign = Sum.inr λ ()
vf ≟T kin = Sum.inr λ ()
vf ≟T vf = Sum.inl Eq.refl
vf ≟T vg = Sum.inr λ ()
vf ≟T vn = Sum.inr λ ()
vf ≟T vx = Sum.inr λ ()
vf ≟T vxs = Sum.inr λ ()
vg ≟T kbool = Sum.inr λ ()
vg ≟T knat = Sum.inr λ ()
vg ≟T karr = Sum.inr λ ()
vg ≟T kprod = Sum.inr λ ()
vg ≟T klist = Sum.inr λ ()
vg ≟T ktrue = Sum.inr λ ()
vg ≟T kfalse = Sum.inr λ ()
vg ≟T kif = Sum.inr λ ()
vg ≟T kthen = Sum.inr λ ()
vg ≟T kelse = Sum.inr λ ()
vg ≟T kzero = Sum.inr λ ()
vg ≟T ksuc = Sum.inr λ ()
vg ≟T knatrec = Sum.inr λ ()
vg ≟T klam = Sum.inr λ ()
vg ≟T kcolon = Sum.inr λ ()
vg ≟T kdot = Sum.inr λ ()
vg ≟T kapp = Sum.inr λ ()
vg ≟T kpair = Sum.inr λ ()
vg ≟T kfst = Sum.inr λ ()
vg ≟T ksnd = Sum.inr λ ()
vg ≟T knil = Sum.inr λ ()
vg ≟T kcons = Sum.inr λ ()
vg ≟T kfoldr = Sum.inr λ ()
vg ≟T klet = Sum.inr λ ()
vg ≟T kassign = Sum.inr λ ()
vg ≟T kin = Sum.inr λ ()
vg ≟T vf = Sum.inr λ ()
vg ≟T vg = Sum.inl Eq.refl
vg ≟T vn = Sum.inr λ ()
vg ≟T vx = Sum.inr λ ()
vg ≟T vxs = Sum.inr λ ()
vn ≟T kbool = Sum.inr λ ()
vn ≟T knat = Sum.inr λ ()
vn ≟T karr = Sum.inr λ ()
vn ≟T kprod = Sum.inr λ ()
vn ≟T klist = Sum.inr λ ()
vn ≟T ktrue = Sum.inr λ ()
vn ≟T kfalse = Sum.inr λ ()
vn ≟T kif = Sum.inr λ ()
vn ≟T kthen = Sum.inr λ ()
vn ≟T kelse = Sum.inr λ ()
vn ≟T kzero = Sum.inr λ ()
vn ≟T ksuc = Sum.inr λ ()
vn ≟T knatrec = Sum.inr λ ()
vn ≟T klam = Sum.inr λ ()
vn ≟T kcolon = Sum.inr λ ()
vn ≟T kdot = Sum.inr λ ()
vn ≟T kapp = Sum.inr λ ()
vn ≟T kpair = Sum.inr λ ()
vn ≟T kfst = Sum.inr λ ()
vn ≟T ksnd = Sum.inr λ ()
vn ≟T knil = Sum.inr λ ()
vn ≟T kcons = Sum.inr λ ()
vn ≟T kfoldr = Sum.inr λ ()
vn ≟T klet = Sum.inr λ ()
vn ≟T kassign = Sum.inr λ ()
vn ≟T kin = Sum.inr λ ()
vn ≟T vf = Sum.inr λ ()
vn ≟T vg = Sum.inr λ ()
vn ≟T vn = Sum.inl Eq.refl
vn ≟T vx = Sum.inr λ ()
vn ≟T vxs = Sum.inr λ ()
vx ≟T kbool = Sum.inr λ ()
vx ≟T knat = Sum.inr λ ()
vx ≟T karr = Sum.inr λ ()
vx ≟T kprod = Sum.inr λ ()
vx ≟T klist = Sum.inr λ ()
vx ≟T ktrue = Sum.inr λ ()
vx ≟T kfalse = Sum.inr λ ()
vx ≟T kif = Sum.inr λ ()
vx ≟T kthen = Sum.inr λ ()
vx ≟T kelse = Sum.inr λ ()
vx ≟T kzero = Sum.inr λ ()
vx ≟T ksuc = Sum.inr λ ()
vx ≟T knatrec = Sum.inr λ ()
vx ≟T klam = Sum.inr λ ()
vx ≟T kcolon = Sum.inr λ ()
vx ≟T kdot = Sum.inr λ ()
vx ≟T kapp = Sum.inr λ ()
vx ≟T kpair = Sum.inr λ ()
vx ≟T kfst = Sum.inr λ ()
vx ≟T ksnd = Sum.inr λ ()
vx ≟T knil = Sum.inr λ ()
vx ≟T kcons = Sum.inr λ ()
vx ≟T kfoldr = Sum.inr λ ()
vx ≟T klet = Sum.inr λ ()
vx ≟T kassign = Sum.inr λ ()
vx ≟T kin = Sum.inr λ ()
vx ≟T vf = Sum.inr λ ()
vx ≟T vg = Sum.inr λ ()
vx ≟T vn = Sum.inr λ ()
vx ≟T vx = Sum.inl Eq.refl
vx ≟T vxs = Sum.inr λ ()
vxs ≟T kbool = Sum.inr λ ()
vxs ≟T knat = Sum.inr λ ()
vxs ≟T karr = Sum.inr λ ()
vxs ≟T kprod = Sum.inr λ ()
vxs ≟T klist = Sum.inr λ ()
vxs ≟T ktrue = Sum.inr λ ()
vxs ≟T kfalse = Sum.inr λ ()
vxs ≟T kif = Sum.inr λ ()
vxs ≟T kthen = Sum.inr λ ()
vxs ≟T kelse = Sum.inr λ ()
vxs ≟T kzero = Sum.inr λ ()
vxs ≟T ksuc = Sum.inr λ ()
vxs ≟T knatrec = Sum.inr λ ()
vxs ≟T klam = Sum.inr λ ()
vxs ≟T kcolon = Sum.inr λ ()
vxs ≟T kdot = Sum.inr λ ()
vxs ≟T kapp = Sum.inr λ ()
vxs ≟T kpair = Sum.inr λ ()
vxs ≟T kfst = Sum.inr λ ()
vxs ≟T ksnd = Sum.inr λ ()
vxs ≟T knil = Sum.inr λ ()
vxs ≟T kcons = Sum.inr λ ()
vxs ≟T kfoldr = Sum.inr λ ()
vxs ≟T klet = Sum.inr λ ()
vxs ≟T kassign = Sum.inr λ ()
vxs ≟T kin = Sum.inr λ ()
vxs ≟T vf = Sum.inr λ ()
vxs ≟T vg = Sum.inr λ ()
vxs ≟T vn = Sum.inr λ ()
vxs ≟T vx = Sum.inr λ ()
vxs ≟T vxs = Sum.inl Eq.refl

open import Theory.Instances.Monoid.Combinator.Decidable.Synthesis Tok _≟T_

-- the three nonterminals
data NT : Type ℓ-zero where
  Ty Tm Var : NT

-- The grammar, as rules.  Every production is led by its keyword, so the
-- classes with no production need not be mentioned at all -- the `_ = none`
-- catch-alls below were the table saying nothing, three times over.
stlcRules : Rules NT
stlcRules .Rules.nullable _ = false

-- A ::= bool | nat | arr A A | prod A A | list A
stlcRules .Rules.of Ty =
    (kbool  , [])
  ∷ (knat   , [])
  ∷ (karr   , nt Ty ∷ nt Ty ∷ [])
  ∷ (kprod  , nt Ty ∷ nt Ty ∷ [])
  ∷ (klist  , nt Ty ∷ [])
  ∷ []

stlcRules .Rules.of Var =
    (vf , []) ∷ (vg , []) ∷ (vn , []) ∷ (vx , []) ∷ (vxs , []) ∷ []

stlcRules .Rules.of Tm =
    (ktrue   , [])
  ∷ (kfalse  , [])
  ∷ (kif     , nt Tm ∷ tm kthen ∷ nt Tm ∷ tm kelse ∷ nt Tm ∷ [])
  ∷ (kzero   , [])
  ∷ (ksuc    , nt Tm ∷ [])
  ∷ (knatrec , nt Tm ∷ nt Tm ∷ nt Tm ∷ [])
  ∷ (klam    , nt Var ∷ tm kcolon ∷ nt Ty ∷ tm kdot ∷ nt Tm ∷ [])
  ∷ (kapp    , nt Tm ∷ nt Tm ∷ [])
  ∷ (kpair   , nt Tm ∷ nt Tm ∷ [])
  ∷ (kfst    , nt Tm ∷ [])
  ∷ (ksnd    , nt Tm ∷ [])
  ∷ (knil    , tm kcolon ∷ nt Ty ∷ [])
  ∷ (kcons   , nt Tm ∷ nt Tm ∷ [])
  ∷ (kfoldr  , nt Tm ∷ nt Tm ∷ nt Tm ∷ [])
  ∷ (klet    , nt Var ∷ tm kassign ∷ nt Tm ∷ tm kin ∷ nt Tm ∷ [])
  ∷ (vf , []) ∷ (vg , []) ∷ (vn , []) ∷ (vx , []) ∷ (vxs , [])
  ∷ []

module SS = Synth (Ty ∷ Tm ∷ Var ∷ []) stlcRules

-- twenty-five productions across three nonterminals, and no two of them
-- share a leading keyword -- computed, not asserted
stlcLL1 : SS.clashes Eq.≡ []
stlcLL1 = Eq.refl

stlc : Table NT
stlc = SS.table

open Gen stlc

Type′ Term Name : TheoryTy ℓG tt
Type′ = S Ty
Term = S Tm
Name = S Var

parseTy : Decidable Type′
parseTy = decide Ty

parseTm : Decidable Term
parseTm = decide Tm

-- Raw syntax: a program is the token list these build.

Src : Type ℓ-zero
Src = List Tok

infixl 8 _`$_
infixr 2 `λ_∶_∙_
infixr 2 `let_≔_`in_
infixr 3 `if_`then_`else_

`bool `nat : Src
`bool = kbool ∷ []
`nat = knat ∷ []

_`⇒_ _`×_ : Src → Src → Src
A `⇒ B = karr ∷ A ++ B
A `× B = kprod ∷ A ++ B

`list : Src → Src
`list A = klist ∷ A

`true `false `zero : Src
`true = ktrue ∷ []
`false = kfalse ∷ []
`zero = kzero ∷ []

`suc `fst `snd : Src → Src
`suc t = ksuc ∷ t
`fst t = kfst ∷ t
`snd t = ksnd ∷ t

`var : Tok → Src
`var x = x ∷ []

`if_`then_`else_ : Src → Src → Src → Src
`if c `then a `else b = kif ∷ c ++ kthen ∷ a ++ kelse ∷ b

`natrec : Src → Src → Src → Src
`natrec z s n = knatrec ∷ z ++ s ++ n

`λ_∶_∙_ : Tok → Src → Src → Src
`λ x ∶ A ∙ t = klam ∷ x ∷ kcolon ∷ A ++ kdot ∷ t

_`$_ : Src → Src → Src
t `$ u = kapp ∷ t ++ u

`pair : Src → Src → Src
`pair a b = kpair ∷ a ++ b

`nil : Src → Src
`nil A = knil ∷ kcolon ∷ A

`cons : Src → Src → Src
`cons h t = kcons ∷ h ++ t

`foldr : Src → Src → Src → Src
`foldr f z xs = kfoldr ∷ f ++ z ++ xs

`let_≔_`in_ : Tok → Src → Src → Src
`let x ≔ t `in u = klet ∷ x ∷ kassign ∷ t ++ kin ∷ u

-- numerals, so the programs can mention numbers
`num : ℕ → Src
`num zero = `zero
`num (suc m) = `suc (`num m)

-- Parsing.  Every `Eq.refl` is the parser running on the token list.

-- types
yes-nat : Type′ `nat
yes-nat = theYes (parseTy `nat tt) Eq.refl

yes-arr : Type′ (`nat `⇒ `bool)
yes-arr = theYes (parseTy (`nat `⇒ `bool) tt) Eq.refl

yes-listprod : Type′ (`list (`nat `× (`nat `⇒ `bool)))
yes-listprod = theYes (parseTy (`list (`nat `× (`nat `⇒ `bool))) tt) Eq.refl

-- terms
idSrc : Src
idSrc = `λ vx ∶ `nat ∙ `var vx

yes-id : Term idSrc
yes-id = theYes (parseTm idSrc tt) Eq.refl

yes-ite : Term (`if `true `then `zero `else (`suc `zero))
yes-ite = theYes (parseTm (`if `true `then `zero `else (`suc `zero)) tt) Eq.refl

yes-proj : Term (`fst (`pair `zero `true))
yes-proj = theYes (parseTm (`fst (`pair `zero `true)) tt) Eq.refl

yes-list : Term (`cons (`num 1) (`cons (`num 2) (`nil `nat)))
yes-list = theYes (parseTm (`cons (`num 1) (`cons (`num 2) (`nil `nat))) tt) Eq.refl

-- addition, by the recursor:  λ n : nat . λ x : nat . natrec x (λ g : nat . suc g) n
addSrc : Src
addSrc = `λ vn ∶ `nat ∙ `λ vx ∶ `nat ∙
           `natrec (`var vx) (`λ vg ∶ `nat ∙ `suc (`var vg)) (`var vn)

yes-add : Term addSrc
yes-add = theYes (parseTm addSrc tt) Eq.refl

-- Two real programs.

-- fib, by the pair trick:
--   let g = add in
--   let f = λ n : nat . fst (natrec ⟨0,1⟩ (λ x : nat × nat . ⟨snd x, g (fst x) (snd x)⟩) n)
--   in f 5
fibSrc : Src
fibSrc =
  `let vg ≔ addSrc `in
  `let vf ≔ (`λ vn ∶ `nat ∙
               `fst (`natrec (`pair `zero (`suc `zero))
                             (`λ vx ∶ (`nat `× `nat) ∙
                                `pair (`snd (`var vx))
                                      (`var vg `$ `fst (`var vx) `$ `snd (`var vx)))
                             (`var vn)))
  `in (`var vf `$ `num 5)

yes-fib : Term fibSrc
yes-fib = theYes (parseTm fibSrc tt) Eq.refl

-- summing a list with the fold former:
--   let f = add in let xs = 1 ∷ 2 ∷ 3 ∷ nil : nat in foldr f 0 xs
sumSrc : Src
sumSrc =
  `let vf ≔ addSrc `in
  `let vxs ≔ `cons (`num 1) (`cons (`num 2) (`cons (`num 3) (`nil `nat))) `in
  `foldr (`var vf) `zero (`var vxs)

yes-sum : Term sumSrc
yes-sum = theYes (parseTm sumSrc tt) Eq.refl

-- how big those really are, as token lists
fib-size : length fibSrc ≡ 65
fib-size = refl

sum-size : length sumSrc ≡ 47
sum-size = refl

-- ...and the rejections, which are refutations.

-- the two languages do not accept each other
no-type-as-term : ¬Ty Term `nat
no-type-as-term = theNo (parseTm `nat tt) Eq.refl

no-term-as-type : ¬Ty Type′ (`var vx)
no-term-as-type = theNo (parseTy (`var vx) tt) Eq.refl

-- a binder with no annotation
no-bare-lam : ¬Ty Term (klam ∷ vx ∷ kdot ∷ vx ∷ [])
no-bare-lam = theNo (parseTm (klam ∷ vx ∷ kdot ∷ vx ∷ []) tt) Eq.refl

-- an `if` with no `else` branch
no-half-if : ¬Ty Term (kif ∷ ktrue ∷ kthen ∷ kzero ∷ [])
no-half-if = theNo (parseTm (kif ∷ ktrue ∷ kthen ∷ kzero ∷ []) tt) Eq.refl

-- a recursor short one argument
no-short-natrec : ¬Ty Term (knatrec ∷ kzero ∷ kzero ∷ [])
no-short-natrec = theNo (parseTm (knatrec ∷ kzero ∷ kzero ∷ []) tt) Eq.refl

-- a keyword in a type position
no-kw-type : ¬Ty Type′ (karr ∷ knat ∷ ktrue ∷ [])
no-kw-type = theNo (parseTy (karr ∷ knat ∷ ktrue ∷ []) tt) Eq.refl

-- and a whole program with one token too many
no-trailing : ¬Ty Term (sumSrc ++ (kzero ∷ []))
no-trailing = theNo (parseTm (sumSrc ++ (kzero ∷ [])) tt) Eq.refl

-- The parse tree, as data.

open import Cubical.Data.Nat using (_+_)

nodes : Tree → ℕ
nodes (node _ ts) = suc (go ts)
  where
  go : List Tree → ℕ
  go [] = 0
  go (t ∷ ts) = nodes t + go ts
nodes eps = 1

fibTree sumTree : Tree
fibTree = toTree Tm fibSrc yes-fib
sumTree = toTree Tm sumSrc yes-sum

fib-nodes : nodes fibTree ≡ 51
fib-nodes = refl

sum-nodes : nodes sumTree ≡ 36
sum-nodes = refl

-- Pass 1: the concrete tree becomes an abstract one.

import Cubical.Data.Maybe as M

private
  _>>=_ : {A B : Type ℓ-zero} → M.Maybe A → (A → M.Maybe B) → M.Maybe B
  M.just a >>= f = f a
  M.nothing >>= f = M.nothing

data ATy : Type ℓ-zero where
  Bo Na : ATy
  Ar Pr : ATy → ATy → ATy
  Li : ATy → ATy

data ATm : Type ℓ-zero where
  Tru Fls Zer : ATm
  Ite Rec Foldr : ATm → ATm → ATm → ATm
  Suc Fst Snd : ATm → ATm
  App Pair Cons : ATm → ATm → ATm
  Nil : ATy → ATm
  Lam : Tok → ATy → ATm → ATm
  Let : Tok → ATm → ATm → ATm
  Nm : Tok → ATm

toTy : Tree → M.Maybe ATy
toTy (node (tk kbool) []) = M.just Bo
toTy (node (tk knat) []) = M.just Na
toTy (node (tk karr) (a ∷ b ∷ [])) = toTy a >>= λ A → toTy b >>= λ B → M.just (Ar A B)
toTy (node (tk kprod) (a ∷ b ∷ [])) = toTy a >>= λ A → toTy b >>= λ B → M.just (Pr A B)
toTy (node (tk klist) (a ∷ [])) = toTy a >>= λ A → M.just (Li A)
toTy _ = M.nothing

toName : Tree → M.Maybe Tok
toName (node (tk c) []) = M.just c
toName _ = M.nothing

toTm : Tree → M.Maybe ATm
toTm (node (tk ktrue) []) = M.just Tru
toTm (node (tk kfalse) []) = M.just Fls
toTm (node (tk kzero) []) = M.just Zer
toTm (node (tk kif) (c ∷ a ∷ b ∷ [])) =
  toTm c >>= λ C → toTm a >>= λ A → toTm b >>= λ B → M.just (Ite C A B)
toTm (node (tk ksuc) (t ∷ [])) = toTm t >>= λ T → M.just (Suc T)
toTm (node (tk knatrec) (z ∷ s ∷ n ∷ [])) =
  toTm z >>= λ Z → toTm s >>= λ Sx → toTm n >>= λ N → M.just (Rec Z Sx N)
toTm (node (tk klam) (v ∷ a ∷ t ∷ [])) =
  toName v >>= λ x → toTy a >>= λ A → toTm t >>= λ T → M.just (Lam x A T)
toTm (node (tk kapp) (f ∷ a ∷ [])) =
  toTm f >>= λ Fn → toTm a >>= λ A → M.just (App Fn A)
toTm (node (tk kpair) (a ∷ b ∷ [])) =
  toTm a >>= λ A → toTm b >>= λ B → M.just (Pair A B)
toTm (node (tk kfst) (t ∷ [])) = toTm t >>= λ T → M.just (Fst T)
toTm (node (tk ksnd) (t ∷ [])) = toTm t >>= λ T → M.just (Snd T)
toTm (node (tk knil) (a ∷ [])) = toTy a >>= λ A → M.just (Nil A)
toTm (node (tk kcons) (h ∷ t ∷ [])) =
  toTm h >>= λ H → toTm t >>= λ T → M.just (Cons H T)
toTm (node (tk kfoldr) (f ∷ z ∷ xs ∷ [])) =
  toTm f >>= λ Fn → toTm z >>= λ Z → toTm xs >>= λ Xs → M.just (Foldr Fn Z Xs)
toTm (node (tk klet) (v ∷ t ∷ u ∷ [])) =
  toName v >>= λ x → toTm t >>= λ T → toTm u >>= λ U → M.just (Let x T U)
toTm (node (tk vf) []) = M.just (Nm vf)
toTm (node (tk vg) []) = M.just (Nm vg)
toTm (node (tk vn) []) = M.just (Nm vn)
toTm (node (tk vx) []) = M.just (Nm vx)
toTm (node (tk vxs) []) = M.just (Nm vxs)
toTm _ = M.nothing

-- Pass 2: scope checking.  Names become de Bruijn indices, and an unbound
-- name is `nothing`.

data BTm : Type ℓ-zero where
  BTru BFls BZer : BTm
  BIte BRec BFoldr : BTm → BTm → BTm → BTm
  BSuc BFst BSnd : BTm → BTm
  BApp BPair BCons : BTm → BTm → BTm
  BNil : ATy → BTm
  BLam : ATy → BTm → BTm
  BLet : BTm → BTm → BTm
  BVar : ℕ → BTm

eqTok : Tok → Tok → Bool
eqTok a b = Sum.rec (λ _ → true) (λ _ → false) (a ≟T b)

idx : List Tok → Tok → M.Maybe ℕ
idx [] y = M.nothing
idx (x ∷ Γ) y with eqTok x y
... | true = M.just 0
... | false = idx Γ y >>= λ i → M.just (suc i)

scope : List Tok → ATm → M.Maybe BTm
scope Γ Tru = M.just BTru
scope Γ Fls = M.just BFls
scope Γ Zer = M.just BZer
scope Γ (Ite c a b) =
  scope Γ c >>= λ C → scope Γ a >>= λ A → scope Γ b >>= λ B → M.just (BIte C A B)
scope Γ (Rec z s n) =
  scope Γ z >>= λ Z → scope Γ s >>= λ Sx → scope Γ n >>= λ N → M.just (BRec Z Sx N)
scope Γ (Foldr f z xs) =
  scope Γ f >>= λ Fn → scope Γ z >>= λ Z → scope Γ xs >>= λ Xs →
  M.just (BFoldr Fn Z Xs)
scope Γ (Suc t) = scope Γ t >>= λ T → M.just (BSuc T)
scope Γ (Fst t) = scope Γ t >>= λ T → M.just (BFst T)
scope Γ (Snd t) = scope Γ t >>= λ T → M.just (BSnd T)
scope Γ (App f a) = scope Γ f >>= λ Fn → scope Γ a >>= λ A → M.just (BApp Fn A)
scope Γ (Pair a b) = scope Γ a >>= λ A → scope Γ b >>= λ B → M.just (BPair A B)
scope Γ (Cons h t) = scope Γ h >>= λ H → scope Γ t >>= λ T → M.just (BCons H T)
scope Γ (Nil A) = M.just (BNil A)
scope Γ (Lam x A t) = scope (x ∷ Γ) t >>= λ T → M.just (BLam A T)
scope Γ (Let x t u) =
  scope Γ t >>= λ T → scope (x ∷ Γ) u >>= λ U → M.just (BLet T U)
scope Γ (Nm x) = idx Γ x >>= λ i → M.just (BVar i)

-- Pass 3: type inference.  Every binder is annotated, so nothing is
-- checked against an expected type -- inference alone suffices.

eqTy : ATy → ATy → Bool
eqTy Bo Bo = true
eqTy Na Na = true
eqTy (Ar a b) (Ar a' b') = eqTy a a' and eqTy b b'
  where open import Cubical.Data.Bool using (_and_)
eqTy (Pr a b) (Pr a' b') = eqTy a a' and eqTy b b'
  where open import Cubical.Data.Bool using (_and_)
eqTy (Li a) (Li a') = eqTy a a'
eqTy _ _ = false

private
  guard : Bool → ATy → M.Maybe ATy
  guard true A = M.just A
  guard false A = M.nothing

  lookΓ : List ATy → ℕ → M.Maybe ATy
  lookΓ [] i = M.nothing
  lookΓ (A ∷ Γ) zero = M.just A
  lookΓ (A ∷ Γ) (suc i) = lookΓ Γ i

infer : List ATy → BTm → M.Maybe ATy
infer Γ BTru = M.just Bo
infer Γ BFls = M.just Bo
infer Γ BZer = M.just Na
infer Γ (BVar i) = lookΓ Γ i
infer Γ (BSuc t) = infer Γ t >>= λ A → guard (eqTy A Na) Na
infer Γ (BIte c a b) =
  infer Γ c >>= λ C → infer Γ a >>= λ A → infer Γ b >>= λ B →
  guard (eqTy C Bo and eqTy A B) A
  where open import Cubical.Data.Bool using (_and_)
infer Γ (BLam A t) = infer (A ∷ Γ) t >>= λ B → M.just (Ar A B)
infer Γ (BApp f a) = infer Γ f >>= λ Fn → infer Γ a >>= λ A → app Fn A
  where
  app : ATy → ATy → M.Maybe ATy
  app (Ar A B) A' = guard (eqTy A A') B
  app _ _ = M.nothing
infer Γ (BPair a b) = infer Γ a >>= λ A → infer Γ b >>= λ B → M.just (Pr A B)
infer Γ (BFst t) = infer Γ t >>= fst'
  where
  fst' : ATy → M.Maybe ATy
  fst' (Pr A B) = M.just A
  fst' _ = M.nothing
infer Γ (BSnd t) = infer Γ t >>= snd'
  where
  snd' : ATy → M.Maybe ATy
  snd' (Pr A B) = M.just B
  snd' _ = M.nothing
infer Γ (BRec z s n) =
  infer Γ z >>= λ A → infer Γ s >>= λ Sx → infer Γ n >>= λ N →
  guard (eqTy Sx (Ar A A) and eqTy N Na) A
  where open import Cubical.Data.Bool using (_and_)
infer Γ (BNil A) = M.just (Li A)
infer Γ (BCons h t) =
  infer Γ h >>= λ A → infer Γ t >>= λ L → guard (eqTy L (Li A)) (Li A)
infer Γ (BFoldr f z xs) =
  infer Γ f >>= λ Fn → infer Γ z >>= λ B → infer Γ xs >>= λ L → go Fn B L
  where
  go : ATy → ATy → ATy → M.Maybe ATy
  go (Ar A (Ar B' B'')) B (Li A') =
    guard (eqTy A A' and (eqTy B B' and eqTy B B'')) B
    where open import Cubical.Data.Bool using (_and_)
  go _ _ _ = M.nothing
infer Γ (BLet t u) = infer Γ t >>= λ A → infer (A ∷ Γ) u

-- The whole front end: token list → parse tree → AST → scoped → typed.

astOf : (w : Src) → M.Maybe ATm
astOf w = go (parseTm w tt)
  where
  go : DecTy Term w → M.Maybe ATm
  go (Sum.inl t) = toTm (toTree Tm w t)
  go (Sum.inr _) = M.nothing

scopeOf : (w : Src) → M.Maybe BTm
scopeOf w = astOf w >>= scope []

tyOf : (w : Src) → M.Maybe ATy
tyOf w = scopeOf w >>= infer []

-- ...run on the two programs.

add-type : tyOf addSrc ≡ M.just (Ar Na (Ar Na Na))
add-type = refl

fib-type : tyOf fibSrc ≡ M.just Na
fib-type = refl

sum-type : tyOf sumSrc ≡ M.just Na
sum-type = refl

list-type : tyOf (`cons (`num 1) (`cons (`num 2) (`nil `nat))) ≡ M.just (Li Na)
list-type = refl

id-type : tyOf idSrc ≡ M.just (Ar Na Na)
id-type = refl

pair-type : tyOf (`pair `zero `true) ≡ M.just (Pr Na Bo)
pair-type = refl

-- ...and each pass rejects what is its business to reject.

-- the parser rejects: a type is not a term
parse-rejects : astOf `nat ≡ M.nothing
parse-rejects = refl

-- the scope checker rejects: `x` is free, though it parsed fine
unbound-parses : astOf (`var vx) ≡ M.just (Nm vx)
unbound-parses = refl

unbound-unscoped : scopeOf (`var vx) ≡ M.nothing
unbound-unscoped = refl

-- the typechecker rejects: `if` on a number, though it scoped fine
badIf : Src
badIf = `if `zero `then `zero `else `zero

isJust : {A : Type ℓ-zero} → M.Maybe A → Bool
isJust (M.just _) = true
isJust M.nothing = false

badIf-scopes : isJust (scopeOf badIf) ≡ true
badIf-scopes = refl

badIf-untyped : tyOf badIf ≡ M.nothing
badIf-untyped = refl

-- ...and a few more type errors
badSuc : tyOf (`suc `true) ≡ M.nothing
badSuc = refl

badApp : tyOf (idSrc `$ `true) ≡ M.nothing
badApp = refl

badCons : tyOf (`cons `true (`nil `nat)) ≡ M.nothing
badCons = refl

badFold : tyOf (`foldr idSrc `zero (`cons (`num 1) (`nil `nat))) ≡ M.nothing
badFold = refl

-- Pass 2, completed.  A `Maybe` says nothing when it says nothing, so the
-- pass is made to answer with a decision: a derivation, or a refutation of
-- every derivation.  The refutations come from inversion -- one line per
-- former, since `Scoped` is an inductive family.

open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)

infix 4 _∈_

data _∈_ (x : Tok) : List Tok → Type ℓ-zero where
  here  : {Γ : List Tok} → x ∈ (x ∷ Γ)
  there : {y : Tok} {Γ : List Tok} → x ∈ Γ → x ∈ (y ∷ Γ)

_∈?_ : (x : Tok) (Γ : List Tok) → Dec (x ∈ Γ)
x ∈? [] = no λ ()
x ∈? (y ∷ Γ) = hd (y ≟T x)
  where
  rest : Dec (x ∈ Γ) → ((x Eq.≡ y) → Empty.⊥) → Dec (x ∈ (y ∷ Γ))
  rest (yes i) ne = yes (there i)
  rest (no ¬i) ne = no λ where
    here → ne Eq.refl
    (there i) → ¬i i

  hd : (y Eq.≡ x) Sum.⊎ ((y Eq.≡ x) → Empty.⊥) → Dec (x ∈ (y ∷ Γ))
  hd (Sum.inl Eq.refl) = yes here
  hd (Sum.inr ne) = rest (x ∈? Γ) λ where Eq.refl → ne Eq.refl

data Scoped : List Tok → ATm → Type ℓ-zero where
  sTru : {Γ : List Tok} → Scoped Γ Tru
  sFls : {Γ : List Tok} → Scoped Γ Fls
  sZer : {Γ : List Tok} → Scoped Γ Zer
  sNil : {Γ : List Tok} {A : ATy} → Scoped Γ (Nil A)
  sNm  : {Γ : List Tok} {x : Tok} → x ∈ Γ → Scoped Γ (Nm x)
  sSuc : {Γ : List Tok} {t : ATm} → Scoped Γ t → Scoped Γ (Suc t)
  sFst : {Γ : List Tok} {t : ATm} → Scoped Γ t → Scoped Γ (Fst t)
  sSnd : {Γ : List Tok} {t : ATm} → Scoped Γ t → Scoped Γ (Snd t)
  sApp : {Γ : List Tok} {f a : ATm} → Scoped Γ f → Scoped Γ a → Scoped Γ (App f a)
  sPair : {Γ : List Tok} {a b : ATm} → Scoped Γ a → Scoped Γ b → Scoped Γ (Pair a b)
  sCons : {Γ : List Tok} {h t : ATm} → Scoped Γ h → Scoped Γ t → Scoped Γ (Cons h t)
  sIte : {Γ : List Tok} {c a b : ATm}
    → Scoped Γ c → Scoped Γ a → Scoped Γ b → Scoped Γ (Ite c a b)
  sRec : {Γ : List Tok} {z s n : ATm}
    → Scoped Γ z → Scoped Γ s → Scoped Γ n → Scoped Γ (Rec z s n)
  sFoldr : {Γ : List Tok} {f z xs : ATm}
    → Scoped Γ f → Scoped Γ z → Scoped Γ xs → Scoped Γ (Foldr f z xs)
  sLam : {Γ : List Tok} {x : Tok} {A : ATy} {t : ATm}
    → Scoped (x ∷ Γ) t → Scoped Γ (Lam x A t)
  sLet : {Γ : List Tok} {x : Tok} {t u : ATm}
    → Scoped Γ t → Scoped (x ∷ Γ) u → Scoped Γ (Let x t u)

-- ...and the decision, one clause per former
private
  d1 : {A C : Type ℓ-zero} → Dec A → (A → C) → (C → A) → Dec C
  d1 (yes a) f g = yes (f a)
  d1 (no ¬a) f g = no λ c → ¬a (g c)

  d2 : {A B C : Type ℓ-zero} → Dec A → Dec B → (A → B → C)
     → (C → A) → (C → B) → Dec C
  d2 (yes a) (yes b) f g h = yes (f a b)
  d2 (no ¬a) _ f g h = no λ c → ¬a (g c)
  d2 _ (no ¬b) f g h = no λ c → ¬b (h c)

  d3 : {A B C D : Type ℓ-zero} → Dec A → Dec B → Dec C → (A → B → C → D)
     → (D → A) → (D → B) → (D → C) → Dec D
  d3 (yes a) (yes b) (yes c) f g h i = yes (f a b c)
  d3 (no ¬a) _ _ f g h i = no λ d → ¬a (g d)
  d3 _ (no ¬b) _ f g h i = no λ d → ¬b (h d)
  d3 _ _ (no ¬c) f g h i = no λ d → ¬c (i d)

scoped? : (Γ : List Tok) (t : ATm) → Dec (Scoped Γ t)
scoped? Γ Tru = yes sTru
scoped? Γ Fls = yes sFls
scoped? Γ Zer = yes sZer
scoped? Γ (Nil A) = yes sNil
scoped? Γ (Nm x) = d1 (x ∈? Γ) sNm λ where (sNm i) → i
scoped? Γ (Suc t) = d1 (scoped? Γ t) sSuc λ where (sSuc p) → p
scoped? Γ (Fst t) = d1 (scoped? Γ t) sFst λ where (sFst p) → p
scoped? Γ (Snd t) = d1 (scoped? Γ t) sSnd λ where (sSnd p) → p
scoped? Γ (App f a) = d2 (scoped? Γ f) (scoped? Γ a) sApp
  (λ where (sApp p q) → p) (λ where (sApp p q) → q)
scoped? Γ (Pair a b) = d2 (scoped? Γ a) (scoped? Γ b) sPair
  (λ where (sPair p q) → p) (λ where (sPair p q) → q)
scoped? Γ (Cons h t) = d2 (scoped? Γ h) (scoped? Γ t) sCons
  (λ where (sCons p q) → p) (λ where (sCons p q) → q)
scoped? Γ (Ite c a b) = d3 (scoped? Γ c) (scoped? Γ a) (scoped? Γ b) sIte
  (λ where (sIte p q r) → p) (λ where (sIte p q r) → q) (λ where (sIte p q r) → r)
scoped? Γ (Rec z s n) = d3 (scoped? Γ z) (scoped? Γ s) (scoped? Γ n) sRec
  (λ where (sRec p q r) → p) (λ where (sRec p q r) → q) (λ where (sRec p q r) → r)
scoped? Γ (Foldr f z xs) = d3 (scoped? Γ f) (scoped? Γ z) (scoped? Γ xs) sFoldr
  (λ where (sFoldr p q r) → p) (λ where (sFoldr p q r) → q)
  (λ where (sFoldr p q r) → r)
scoped? Γ (Lam x A t) = d1 (scoped? (x ∷ Γ) t) sLam λ where (sLam p) → p
scoped? Γ (Let x t u) = d2 (scoped? Γ t) (scoped? (x ∷ Γ) u) sLet
  (λ where (sLet p q) → p) (λ where (sLet p q) → q)

-- Pass 3, completed.  Same move: `Typed` is an inductive family, and the
-- decision answers with a derivation or a refutation of all of them.  What
-- makes the refutations available is that this calculus is fully annotated,
-- hence *uniquely* typed: a mismatch with the inferred type really does
-- refute, by `unique`.

open import Cubical.Data.Sigma using (Σ-syntax ; _×_)

_≟ty_ : (A B : ATy) → (A Eq.≡ B) Sum.⊎ ((A Eq.≡ B) → Empty.⊥)
Bo ≟ty Bo = Sum.inl Eq.refl
Na ≟ty Na = Sum.inl Eq.refl
Ar a b ≟ty Ar a' b' = go (a ≟ty a') (b ≟ty b')
  where
  go : (a Eq.≡ a') Sum.⊎ ((a Eq.≡ a') → Empty.⊥)
     → (b Eq.≡ b') Sum.⊎ ((b Eq.≡ b') → Empty.⊥)
     → (Ar a b Eq.≡ Ar a' b') Sum.⊎ ((Ar a b Eq.≡ Ar a' b') → Empty.⊥)
  go (Sum.inl Eq.refl) (Sum.inl Eq.refl) = Sum.inl Eq.refl
  go (Sum.inr ne) _ = Sum.inr λ where Eq.refl → ne Eq.refl
  go _ (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl
Pr a b ≟ty Pr a' b' = go (a ≟ty a') (b ≟ty b')
  where
  go : (a Eq.≡ a') Sum.⊎ ((a Eq.≡ a') → Empty.⊥)
     → (b Eq.≡ b') Sum.⊎ ((b Eq.≡ b') → Empty.⊥)
     → (Pr a b Eq.≡ Pr a' b') Sum.⊎ ((Pr a b Eq.≡ Pr a' b') → Empty.⊥)
  go (Sum.inl Eq.refl) (Sum.inl Eq.refl) = Sum.inl Eq.refl
  go (Sum.inr ne) _ = Sum.inr λ where Eq.refl → ne Eq.refl
  go _ (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl
Li a ≟ty Li a' = go (a ≟ty a')
  where
  go : (a Eq.≡ a') Sum.⊎ ((a Eq.≡ a') → Empty.⊥)
     → (Li a Eq.≡ Li a') Sum.⊎ ((Li a Eq.≡ Li a') → Empty.⊥)
  go (Sum.inl Eq.refl) = Sum.inl Eq.refl
  go (Sum.inr ne) = Sum.inr λ where Eq.refl → ne Eq.refl
Bo ≟ty Na = Sum.inr λ ()
Bo ≟ty Ar _ _ = Sum.inr λ ()
Bo ≟ty Pr _ _ = Sum.inr λ ()
Bo ≟ty Li _ = Sum.inr λ ()
Na ≟ty Bo = Sum.inr λ ()
Na ≟ty Ar _ _ = Sum.inr λ ()
Na ≟ty Pr _ _ = Sum.inr λ ()
Na ≟ty Li _ = Sum.inr λ ()
Ar _ _ ≟ty Bo = Sum.inr λ ()
Ar _ _ ≟ty Na = Sum.inr λ ()
Ar _ _ ≟ty Pr _ _ = Sum.inr λ ()
Ar _ _ ≟ty Li _ = Sum.inr λ ()
Pr _ _ ≟ty Bo = Sum.inr λ ()
Pr _ _ ≟ty Na = Sum.inr λ ()
Pr _ _ ≟ty Ar _ _ = Sum.inr λ ()
Pr _ _ ≟ty Li _ = Sum.inr λ ()
Li _ ≟ty Bo = Sum.inr λ ()
Li _ ≟ty Na = Sum.inr λ ()
Li _ ≟ty Ar _ _ = Sum.inr λ ()
Li _ ≟ty Pr _ _ = Sum.inr λ ()

Ctx : Type ℓ-zero
Ctx = List (Tok × ATy)

-- a context lookup, as a function: shadowing is then automatic and the
-- lookup is deterministic by construction
lookupC : Ctx → Tok → M.Maybe ATy
lookupC [] x = M.nothing
lookupC ((y , B) ∷ Γ) x = go (y ≟T x)
  where
  go : (y Eq.≡ x) Sum.⊎ ((y Eq.≡ x) → Empty.⊥) → M.Maybe ATy
  go (Sum.inl Eq.refl) = M.just B
  go (Sum.inr _) = lookupC Γ x

data Typed : Ctx → ATm → ATy → Type ℓ-zero where
  tTru : {Γ : Ctx} → Typed Γ Tru Bo
  tFls : {Γ : Ctx} → Typed Γ Fls Bo
  tZer : {Γ : Ctx} → Typed Γ Zer Na
  tNil : {Γ : Ctx} {A : ATy} → Typed Γ (Nil A) (Li A)
  tNm  : {Γ : Ctx} {x : Tok} {A : ATy}
    → lookupC Γ x Eq.≡ M.just A → Typed Γ (Nm x) A
  tSuc : {Γ : Ctx} {t : ATm} → Typed Γ t Na → Typed Γ (Suc t) Na
  tFst : {Γ : Ctx} {t : ATm} {A B : ATy}
    → Typed Γ t (Pr A B) → Typed Γ (Fst t) A
  tSnd : {Γ : Ctx} {t : ATm} {A B : ATy}
    → Typed Γ t (Pr A B) → Typed Γ (Snd t) B
  tApp : {Γ : Ctx} {f a : ATm} {A B : ATy}
    → Typed Γ f (Ar A B) → Typed Γ a A → Typed Γ (App f a) B
  tPair : {Γ : Ctx} {a b : ATm} {A B : ATy}
    → Typed Γ a A → Typed Γ b B → Typed Γ (Pair a b) (Pr A B)
  tCons : {Γ : Ctx} {h t : ATm} {A : ATy}
    → Typed Γ h A → Typed Γ t (Li A) → Typed Γ (Cons h t) (Li A)
  tIte : {Γ : Ctx} {c a b : ATm} {A : ATy}
    → Typed Γ c Bo → Typed Γ a A → Typed Γ b A → Typed Γ (Ite c a b) A
  tRec : {Γ : Ctx} {z s n : ATm} {A : ATy}
    → Typed Γ z A → Typed Γ s (Ar A A) → Typed Γ n Na → Typed Γ (Rec z s n) A
  tFoldr : {Γ : Ctx} {f z xs : ATm} {A B : ATy}
    → Typed Γ f (Ar A (Ar B B)) → Typed Γ z B → Typed Γ xs (Li A)
    → Typed Γ (Foldr f z xs) B
  tLam : {Γ : Ctx} {x : Tok} {A : ATy} {t : ATm} {B : ATy}
    → Typed ((x , A) ∷ Γ) t B → Typed Γ (Lam x A t) (Ar A B)
  tLet : {Γ : Ctx} {x : Tok} {t u : ATm} {A B : ATy}
    → Typed Γ t A → Typed ((x , A) ∷ Γ) u B → Typed Γ (Let x t u) B

-- the context is deterministic...
justInj : {A B : ATy} → M.just A Eq.≡ M.just B → A Eq.≡ B
justInj Eq.refl = Eq.refl

uniqueᶜ : {x : Tok} {A B : ATy} {Γ : Ctx}
  → lookupC Γ x Eq.≡ M.just A → lookupC Γ x Eq.≡ M.just B → A Eq.≡ B
uniqueᶜ p q = justInj (Eq.sym p Eq.∙ q)

-- ...and so, every binder being annotated, is the typing
unique : {Γ : Ctx} {t : ATm} {A B : ATy} → Typed Γ t A → Typed Γ t B → A Eq.≡ B
unique tTru tTru = Eq.refl
unique tFls tFls = Eq.refl
unique tZer tZer = Eq.refl
unique tNil tNil = Eq.refl
unique (tNm p) (tNm q) = uniqueᶜ p q
unique (tSuc _) (tSuc _) = Eq.refl
unique (tFst p) (tFst q) = go (unique p q)
  where
  go : {A B A' B' : ATy} → Pr A B Eq.≡ Pr A' B' → A Eq.≡ A'
  go Eq.refl = Eq.refl
unique (tSnd p) (tSnd q) = go (unique p q)
  where
  go : {A B A' B' : ATy} → Pr A B Eq.≡ Pr A' B' → B Eq.≡ B'
  go Eq.refl = Eq.refl
unique (tApp p _) (tApp q _) = go (unique p q)
  where
  go : {A B A' B' : ATy} → Ar A B Eq.≡ Ar A' B' → B Eq.≡ B'
  go Eq.refl = Eq.refl
unique (tPair p p') (tPair q q') = go (unique p q) (unique p' q')
  where
  go : {A A' B B' : ATy} → A Eq.≡ A' → B Eq.≡ B' → Pr A B Eq.≡ Pr A' B'
  go Eq.refl Eq.refl = Eq.refl
unique (tCons p _) (tCons q _) = go (unique p q)
  where
  go : {A A' : ATy} → A Eq.≡ A' → Li A Eq.≡ Li A'
  go Eq.refl = Eq.refl
unique (tIte _ p _) (tIte _ q _) = unique p q
unique (tRec p _ _) (tRec q _ _) = unique p q
unique (tFoldr _ p _) (tFoldr _ q _) = unique p q
unique (tLam p) (tLam q) = go (unique p q)
  where
  go : {A B B' : ATy} → B Eq.≡ B' → Ar A B Eq.≡ Ar A B'
  go Eq.refl = Eq.refl
unique (tLet p p') (tLet q q') = go (unique p q) p' q'
  where
  go : {Γ : Ctx} {x : Tok} {u : ATm} {A A' B B' : ATy} → A Eq.≡ A'
     → Typed ((x , A) ∷ Γ) u B → Typed ((x , A') ∷ Γ) u B' → B Eq.≡ B'
  go Eq.refl p' q' = unique p' q'

-- views, so a former that needs a shaped type says so once
data ArV : ATy → Type ℓ-zero where
  isAr : (A B : ATy) → ArV (Ar A B)
  noAr : {C : ATy} → ((A B : ATy) → C Eq.≡ Ar A B → Empty.⊥) → ArV C

arV : (C : ATy) → ArV C
arV Bo = noAr λ A B ()
arV Na = noAr λ A B ()
arV (Ar A B) = isAr A B
arV (Pr _ _) = noAr λ A B ()
arV (Li _) = noAr λ A B ()

data PrV : ATy → Type ℓ-zero where
  isPr : (A B : ATy) → PrV (Pr A B)
  noPr : {C : ATy} → ((A B : ATy) → C Eq.≡ Pr A B → Empty.⊥) → PrV C

prV : (C : ATy) → PrV C
prV Bo = noPr λ A B ()
prV Na = noPr λ A B ()
prV (Ar _ _) = noPr λ A B ()
prV (Pr A B) = isPr A B
prV (Li _) = noPr λ A B ()

private
  arDom : {A B A' B' : ATy} → Ar A B Eq.≡ Ar A' B' → A Eq.≡ A'
  arDom Eq.refl = Eq.refl

  arCod : {A B A' B' : ATy} → Ar A B Eq.≡ Ar A' B' → B Eq.≡ B'
  arCod Eq.refl = Eq.refl

  liC : {A A' : ATy} → A Eq.≡ A' → Li A Eq.≡ Li A'
  liC Eq.refl = Eq.refl

  arC : {A B B' : ATy} → B Eq.≡ B' → Ar A B Eq.≡ Ar A B'
  arC Eq.refl = Eq.refl

  arBoth : {B₀ B : ATy} → B₀ Eq.≡ B → Ar B₀ B₀ Eq.≡ Ar B B
  arBoth Eq.refl = Eq.refl

Ty? : Ctx → ATm → Type ℓ-zero
Ty? Γ t = Σ[ A ∈ ATy ] Typed Γ t A

typed? : (Γ : Ctx) (t : ATm) → Dec (Ty? Γ t)
typed? Γ Tru = yes (Bo , tTru)
typed? Γ Fls = yes (Bo , tFls)
typed? Γ Zer = yes (Na , tZer)
typed? Γ (Nil A) = yes (Li A , tNil)
typed? Γ (Nm x) = go (lookupC Γ x) Eq.refl
  where
  bad : {A : ATy} → M.nothing Eq.≡ M.just A → Empty.⊥
  bad ()

  go : (r : M.Maybe ATy) → lookupC Γ x Eq.≡ r → Dec (Ty? Γ (Nm x))
  go (M.just A) e = yes (A , tNm e)
  go M.nothing e = no λ where (A , tNm p) → bad (Eq.sym e Eq.∙ p)
typed? Γ (Suc t) = go (typed? Γ t)
  where
  go : Dec (Ty? Γ t) → Dec (Ty? Γ (Suc t))
  go (no ¬p) = no λ where (_ , tSuc d) → ¬p (Na , d)
  go (yes (A , d)) = chk (A ≟ty Na)
    where
    chk : (A Eq.≡ Na) Sum.⊎ ((A Eq.≡ Na) → Empty.⊥) → Dec (Ty? Γ (Suc t))
    chk (Sum.inl Eq.refl) = yes (Na , tSuc d)
    chk (Sum.inr ne) = no λ where (_ , tSuc d') → ne (unique d d')
typed? Γ (Fst t) = go (typed? Γ t)
  where
  go : Dec (Ty? Γ t) → Dec (Ty? Γ (Fst t))
  go (no ¬p) = no λ where (_ , tFst d) → ¬p (_ , d)
  go (yes (C , d)) = chk (prV C)
    where
    chk : PrV C → Dec (Ty? Γ (Fst t))
    chk (isPr A B) = yes (A , tFst d)
    chk (noPr ne) = no λ where
      (_ , tFst {A = A} {B = B} d') → ne A B (unique d d')
typed? Γ (Snd t) = go (typed? Γ t)
  where
  go : Dec (Ty? Γ t) → Dec (Ty? Γ (Snd t))
  go (no ¬p) = no λ where (_ , tSnd d) → ¬p (_ , d)
  go (yes (C , d)) = chk (prV C)
    where
    chk : PrV C → Dec (Ty? Γ (Snd t))
    chk (isPr A B) = yes (B , tSnd d)
    chk (noPr ne) = no λ where
      (_ , tSnd {A = A} {B = B} d') → ne A B (unique d d')
typed? Γ (Pair a b) = go (typed? Γ a) (typed? Γ b)
  where
  go : Dec (Ty? Γ a) → Dec (Ty? Γ b) → Dec (Ty? Γ (Pair a b))
  go (no ¬p) _ = no λ where (_ , tPair d _) → ¬p (_ , d)
  go _ (no ¬q) = no λ where (_ , tPair _ d) → ¬q (_ , d)
  go (yes (A , da)) (yes (B , db)) = yes (Pr A B , tPair da db)
typed? Γ (App f a) = go (typed? Γ f) (typed? Γ a)
  where
  go : Dec (Ty? Γ f) → Dec (Ty? Γ a) → Dec (Ty? Γ (App f a))
  go (no ¬p) _ = no λ where (_ , tApp d _) → ¬p (_ , d)
  go _ (no ¬q) = no λ where (_ , tApp _ d) → ¬q (_ , d)
  go (yes (C , df)) (yes (A' , da)) = chk (arV C)
    where
    chk : ArV C → Dec (Ty? Γ (App f a))
    chk (noAr ne) = no λ where
      (_ , tApp {A = A''} {B = B''} d' _) → ne A'' B'' (unique df d')
    chk (isAr A B) = chk2 (A ≟ty A')
      where
      chk2 : (A Eq.≡ A') Sum.⊎ ((A Eq.≡ A') → Empty.⊥) → Dec (Ty? Γ (App f a))
      chk2 (Sum.inl Eq.refl) = yes (B , tApp df da)
      chk2 (Sum.inr ne) = no λ where
        (_ , tApp d' e') →
          ne (arDom (unique df d') Eq.∙ Eq.sym (unique da e'))
typed? Γ (Cons h t) = go (typed? Γ h) (typed? Γ t)
  where
  go : Dec (Ty? Γ h) → Dec (Ty? Γ t) → Dec (Ty? Γ (Cons h t))
  go (no ¬p) _ = no λ where (_ , tCons d _) → ¬p (_ , d)
  go _ (no ¬q) = no λ where (_ , tCons _ d) → ¬q (_ , d)
  go (yes (A , dh)) (yes (L , dt)) = chk (L ≟ty Li A)
    where
    chk : (L Eq.≡ Li A) Sum.⊎ ((L Eq.≡ Li A) → Empty.⊥) → Dec (Ty? Γ (Cons h t))
    chk (Sum.inl Eq.refl) = yes (Li A , tCons dh dt)
    chk (Sum.inr ne) = no λ where
      (_ , tCons dh' dt') →
        ne (unique dt dt' Eq.∙ liC (Eq.sym (unique dh dh')))
typed? Γ (Ite c a b) = go (typed? Γ c) (typed? Γ a) (typed? Γ b)
  where
  go : Dec (Ty? Γ c) → Dec (Ty? Γ a) → Dec (Ty? Γ b) → Dec (Ty? Γ (Ite c a b))
  go (no ¬p) _ _ = no λ where (_ , tIte d _ _) → ¬p (_ , d)
  go _ (no ¬q) _ = no λ where (_ , tIte _ d _) → ¬q (_ , d)
  go _ _ (no ¬r) = no λ where (_ , tIte _ _ d) → ¬r (_ , d)
  go (yes (C , dc)) (yes (A , da)) (yes (B , db)) = chk (C ≟ty Bo) (A ≟ty B)
    where
    chk : (C Eq.≡ Bo) Sum.⊎ ((C Eq.≡ Bo) → Empty.⊥)
        → (A Eq.≡ B) Sum.⊎ ((A Eq.≡ B) → Empty.⊥) → Dec (Ty? Γ (Ite c a b))
    chk (Sum.inr ne) _ = no λ where (_ , tIte d' _ _) → ne (unique dc d')
    chk _ (Sum.inr ne) = no λ where
      (_ , tIte _ d' e') → ne (unique da d' Eq.∙ Eq.sym (unique db e'))
    chk (Sum.inl Eq.refl) (Sum.inl Eq.refl) = yes (A , tIte dc da db)
typed? Γ (Rec z s n) = go (typed? Γ z) (typed? Γ s) (typed? Γ n)
  where
  go : Dec (Ty? Γ z) → Dec (Ty? Γ s) → Dec (Ty? Γ n) → Dec (Ty? Γ (Rec z s n))
  go (no ¬p) _ _ = no λ where (_ , tRec d _ _) → ¬p (_ , d)
  go _ (no ¬q) _ = no λ where (_ , tRec _ d _) → ¬q (_ , d)
  go _ _ (no ¬r) = no λ where (_ , tRec _ _ d) → ¬r (_ , d)
  go (yes (A , dz)) (yes (Sy , ds)) (yes (N , dn)) =
    chk (Sy ≟ty Ar A A) (N ≟ty Na)
    where
    chk : (Sy Eq.≡ Ar A A) Sum.⊎ ((Sy Eq.≡ Ar A A) → Empty.⊥)
        → (N Eq.≡ Na) Sum.⊎ ((N Eq.≡ Na) → Empty.⊥) → Dec (Ty? Γ (Rec z s n))
    chk (Sum.inr ne) _ = no λ where
      (_ , tRec d' e' _) →
        ne (unique ds e' Eq.∙ arBoth (Eq.sym (unique dz d')))
    chk _ (Sum.inr ne) = no λ where (_ , tRec _ _ d') → ne (unique dn d')
    chk (Sum.inl Eq.refl) (Sum.inl Eq.refl) = yes (A , tRec dz ds dn)
typed? Γ (Lam x A t) = go (typed? ((x , A) ∷ Γ) t)
  where
  go : Dec (Ty? ((x , A) ∷ Γ) t) → Dec (Ty? Γ (Lam x A t))
  go (no ¬p) = no λ where (_ , tLam d) → ¬p (_ , d)
  go (yes (B , d)) = yes (Ar A B , tLam d)
typed? Γ (Foldr f z xs) = go (typed? Γ f) (typed? Γ z) (typed? Γ xs)
  where
  go : Dec (Ty? Γ f) → Dec (Ty? Γ z) → Dec (Ty? Γ xs)
     → Dec (Ty? Γ (Foldr f z xs))
  go (no ¬p) _ _ = no λ where (_ , tFoldr d _ _) → ¬p (_ , d)
  go _ (no ¬q) _ = no λ where (_ , tFoldr _ d _) → ¬q (_ , d)
  go _ _ (no ¬r) = no λ where (_ , tFoldr _ _ d) → ¬r (_ , d)
  go (yes (C , df)) (yes (B , dz)) (yes (L , dxs)) = chk (arV C)
    where
    chk : ArV C → Dec (Ty? Γ (Foldr f z xs))
    chk (noAr ne) = no λ where
      (_ , tFoldr {A = A₀} {B = B₀} d' _ _) → ne A₀ (Ar B₀ B₀) (unique df d')
    chk (isAr A rest) = chk2 (rest ≟ty Ar B B) (L ≟ty Li A)
      where
      chk2 : (rest Eq.≡ Ar B B) Sum.⊎ ((rest Eq.≡ Ar B B) → Empty.⊥)
           → (L Eq.≡ Li A) Sum.⊎ ((L Eq.≡ Li A) → Empty.⊥)
           → Dec (Ty? Γ (Foldr f z xs))
      chk2 (Sum.inr ne) _ = no λ where
        (_ , tFoldr d' e' _) →
          ne (arCod (unique df d') Eq.∙ arBoth (Eq.sym (unique dz e')))
      chk2 _ (Sum.inr ne) = no λ where
        (_ , tFoldr d' _ e') →
          ne (unique dxs e' Eq.∙ liC (Eq.sym (arDom (unique df d'))))
      chk2 (Sum.inl Eq.refl) (Sum.inl Eq.refl) = yes (B , tFoldr df dz dxs)
typed? Γ (Let x t u) = go (typed? Γ t)
  where
  go : Dec (Ty? Γ t) → Dec (Ty? Γ (Let x t u))
  go (no ¬p) = no λ where (_ , tLet d _) → ¬p (_ , d)
  go (yes (A , dt)) = go2 (typed? ((x , A) ∷ Γ) u)
    where
    shift : {A' B' : ATy} → A Eq.≡ A' → Typed ((x , A') ∷ Γ) u B'
          → Ty? ((x , A) ∷ Γ) u
    shift Eq.refl d = _ , d

    go2 : Dec (Ty? ((x , A) ∷ Γ) u) → Dec (Ty? Γ (Let x t u))
    go2 (no ¬q) = no λ where
      (_ , tLet d' e') → ¬q (shift (unique dt d') e')
    go2 (yes (B , du)) = yes (B , tLet dt du)

-- Running the two complete passes.  `theD` extracts a derivation and
-- `theNotD` a refutation, exactly as `theYes`/`theNo` do for the parser.

isYesD : {A : Type ℓ-zero} → Dec A → Bool
isYesD (yes _) = true
isYesD (no _) = false

theD : {A : Type ℓ-zero} (d : Dec A) → isYesD d Eq.≡ true → A
theD (yes a) _ = a
theD (no _) ()

theNotD : {A : Type ℓ-zero} (d : Dec A) → isYesD d Eq.≡ false → A → Empty.⊥
theNotD (no ¬a) _ = ¬a
theNotD (yes _) ()

private
  orTru : M.Maybe ATm → ATm
  orTru (M.just t) = t
  orTru M.nothing = Tru

fibAST sumAST addAST badIfAST : ATm
fibAST = orTru (astOf fibSrc)
sumAST = orTru (astOf sumSrc)
addAST = orTru (astOf addSrc)
badIfAST = orTru (astOf badIf)

-- scope checking: a derivation, and for a free variable a refutation
fib-scoped : Scoped [] fibAST
fib-scoped = theD (scoped? [] fibAST) Eq.refl

sum-scoped : Scoped [] sumAST
sum-scoped = theD (scoped? [] sumAST) Eq.refl

unbound-refuted : Scoped [] (Nm vx) → Empty.⊥
unbound-refuted = theNotD (scoped? [] (Nm vx)) Eq.refl

-- ...but bound under a binder that binds it
bound-scoped : Scoped [] (Lam vx Na (Nm vx))
bound-scoped = theD (scoped? [] (Lam vx Na (Nm vx))) Eq.refl

-- type checking: a derivation carrying its type
fib-typed : Ty? [] fibAST
fib-typed = theD (typed? [] fibAST) Eq.refl

fib-typed-nat : fst fib-typed ≡ Na
fib-typed-nat = refl

sum-typed : Ty? [] sumAST
sum-typed = theD (typed? [] sumAST) Eq.refl

sum-typed-nat : fst sum-typed ≡ Na
sum-typed-nat = refl

add-typed : Ty? [] addAST
add-typed = theD (typed? [] addAST) Eq.refl

add-typed-arr : fst add-typed ≡ Ar Na (Ar Na Na)
add-typed-arr = refl

-- ...and refutations of *every* derivation, which is what completeness buys
badIf-refuted : Ty? [] badIfAST → Empty.⊥
badIf-refuted = theNotD (typed? [] badIfAST) Eq.refl

badSuc-refuted : Ty? [] (Suc Tru) → Empty.⊥
badSuc-refuted = theNotD (typed? [] (Suc Tru)) Eq.refl

badApp-refuted : Ty? [] (App (Lam vx Na (Nm vx)) Tru) → Empty.⊥
badApp-refuted = theNotD (typed? [] (App (Lam vx Na (Nm vx)) Tru)) Eq.refl

badCons-refuted : Ty? [] (Cons Tru (Nil Na)) → Empty.⊥
badCons-refuted = theNotD (typed? [] (Cons Tru (Nil Na))) Eq.refl

badFst-refuted : Ty? [] (Fst Zer) → Empty.⊥
badFst-refuted = theNotD (typed? [] (Fst Zer)) Eq.refl
