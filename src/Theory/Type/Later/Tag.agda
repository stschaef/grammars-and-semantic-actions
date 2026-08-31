{- Which guarded modality a term is available under.  `⟨▷⟩` is "at every
   proper suffix", `⟨□⟩` is that and here as well, so `⟨□⟩` is the stronger
   assumption and the weaker conclusion.  A parser is indexed by one of these
   for its hypothesis and one for its conclusion. -}
open import Cubical.Foundations.Prelude

module Theory.Type.Later.Tag where

data ParserTag : Type where
  ⟨▷⟩ ⟨□⟩ : ParserTag
