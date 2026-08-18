module

public import Mathlib.Order.Filter.Map
public import Mathlib.Topology.Defs.Filter
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Set Topology Filter

namespace PiBase

/- 202. Has a point with a unique neighborhood -/
class HasPointWithUniqueNeighborhood (X : Type*) [TopologicalSpace X] : Prop where
  ex_point_unique_nbhd : ∃ p : X, 𝓝 p = ⊤

end PiBase

namespace PiBase.Formal

def P202 : Property where
  toPred := HasPointWithUniqueNeighborhood
  well_defined φ h := by
    obtain ⟨p, hp⟩ := h.ex_point_unique_nbhd
    refine ⟨⟨φ p, ?_⟩⟩
    have h_map : Filter.map φ (𝓝 p) = 𝓝 (φ p) := φ.map_nhds_eq p
    have h_top : Filter.map φ ⊤ = ⊤ :=
      Function.Surjective.filter_map_top φ.surjective
    calc 𝓝 (φ p) = Filter.map φ (𝓝 p) := h_map.symm
      _ = Filter.map φ ⊤ := by rw [hp]
      _ = ⊤ := h_top

end PiBase.Formal
