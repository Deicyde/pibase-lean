module

public import Mathlib.Topology.Homeomorph.Lemmas
public import PiBaseLean.AdditionalDefs.Constructions
public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u

namespace PiBase

/- 77. Corson compact -/
class CorsonCompactSpace (X : Type u) [TopologicalSpace X] : Prop extends CompactSpace X where
  isHomoeo_subset : ∃ α : Type u, ∃ f : X → (SigmaProduct (fun (_ : α) ↦ (0 : ℝ))),
    Topology.IsEmbedding f

end PiBase

namespace PiBase.Formal

def P77 : Property where
  toPred := CorsonCompactSpace
  well_defined φ h := by
    obtain ⟨α, f, hf⟩ := h.isHomoeo_subset
    -- preserve compact via φ.compactSpace: need CompactSpace X instance from h
    exact {
      toCompactSpace := @Homeomorph.compactSpace _ _ _ _ h.toCompactSpace φ
      isHomoeo_subset := ⟨α, f ∘ φ.symm, hf.comp φ.symm.isEmbedding⟩
    }

end PiBase.Formal
