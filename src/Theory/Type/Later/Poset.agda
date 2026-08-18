-- TODO how much of this actually used?
-- WARNING for now I have been treating this as a place to sequester the
-- semantic reasoning about guarded recursion so that importers of this
-- module can work with a clean interface
-- The implementation are subject to change per experiments w Cass
{- A well-ordered poset is a (thin) direct category.

   `Cubical.Categories.Direct.Base` gives the thin category `WFOrder→Cat`
   on the reflexive closure of a well-founded order; the degree functor on
   it is the identity, which is the direct structure `StrictDownset` --
   and hence `▷` -- is indexed by. -}
open import Cubical.Categories.Direct.Base
  using (WFOrder ; WFOrder→Cat ; DirectStr ; mkDirectStr)
module Theory.Type.Later.Poset where

open import Cubical.Foundations.Prelude using (Level)

private variable ℓD ℓ< : Level

PosetDirect : (Wo : WFOrder ℓD ℓ<) → DirectStr (WFOrder→Cat Wo) Wo
PosetDirect Wo = mkDirectStr (WFOrder→Cat Wo) Wo (λ x → x) (λ f → f)
