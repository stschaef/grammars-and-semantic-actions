-- ⟨▷⟩: later (smaller resources); ⟨□⟩: now and later
open import Cubical.Foundations.Prelude

module Theory.Type.Later.Tag where

data ParserTag : Type where
  ⟨▷⟩ ⟨□⟩ : ParserTag
