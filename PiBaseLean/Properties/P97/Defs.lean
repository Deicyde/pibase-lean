module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

namespace PiBase

/- 97. Embeddable in ℝ -/
class EmbeddableInR (X : Type*) [TopologicalSpace X] : Prop where
  embeddable : ∃ f : X → ℝ, IsEmbedding f

end PiBase

namespace PiBase.Formal

def P97 : Property where
  toPred := EmbeddableInR
  well_defined φ h := by
    obtain ⟨f, hf⟩ := h.embeddable
    exact ⟨⟨f ∘ φ.symm, hf.comp φ.symm.isEmbedding⟩⟩

end PiBase.Formal
