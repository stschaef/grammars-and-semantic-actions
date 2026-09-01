-- A well-ordered poset is a (thin) direct category.
open import Cubical.Categories.Direct.Base
  using (WFOrder ; WFOrder→Cat ; DirectStr ; mkDirectStr)
module Theory.Type.Later.Poset where

open import Cubical.Foundations.Prelude using (Level)

private variable ℓD ℓ< : Level

PosetDirect : (Wo : WFOrder ℓD ℓ<) → DirectStr (WFOrder→Cat Wo) Wo
PosetDirect Wo = mkDirectStr (WFOrder→Cat Wo) Wo (λ x → x) (λ f → f)
