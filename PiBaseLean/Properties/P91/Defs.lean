module

public import Mathlib.Topology.Homeomorph.Lemmas
public import PiBaseLean.AdditionalDefs.Constructions
public import PiBaseLean.Properties.Bundled.Defs
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

@[expose] public section

universe u

namespace PiBase

open Topology

/- 91. Eberlein compact -/
class EberleinCompactSpace (X : Type u) [TopologicalSpace X] : Prop extends CompactSpace X where
  eberlein_compact : ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E)
    (f : X → WeakSpace ℝ E), CompleteSpace E ∧ IsEmbedding f

end PiBase

namespace PiBase.Formal

def P91 : Property where
  toPred := EberleinCompactSpace
  well_defined φ h := by
    obtain ⟨E, hNAG, hNS, f, hComp, hEmb⟩ := h.eberlein_compact
    exact {
      toCompactSpace := @Homeomorph.compactSpace _ _ _ _ h.toCompactSpace φ
      eberlein_compact := ⟨E, hNAG, hNS, f ∘ φ.symm, hComp, hEmb.comp φ.symm.isEmbedding⟩
    }

end PiBase.Formal
