module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Topology.Defs.Filter
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Filter

namespace PiBase

/- 21. Weakly countably compact -/
class WeaklyCountablyCompact (X : Type*) [TopologicalSpace X] : Prop where
  weakly_countably_compact : ∀ s : Set X, s.Infinite → ∃ x : X, AccPt x (𝓟 s)

end PiBase

namespace PiBase.Formal

def P21 : Property where
  toPred := WeaklyCountablyCompact
  well_defined := fun {X Y} _ _ φ h => by
    constructor
    intro s hsInf
    have hSub : s ⊆ range φ := by
      rw [φ.range_coe]
      exact subset_univ _
    have hInfPre : (φ ⁻¹' s).Infinite := hsInf.preimage hSub
    obtain ⟨x, hx⟩ := h.weakly_countably_compact _ hInfPre
    refine ⟨φ x, ?_⟩
    have hcomap : Filter.comap (φ : X → Y) (𝓟 s) = 𝓟 (φ ⁻¹' s) := Filter.comap_principal
    have hx_comap : AccPt x (Filter.comap (φ : X → Y) (𝓟 s)) := by
      rw [hcomap]
      exact hx
    exact φ.isOpenEmbedding.accPt_comap_iff.mp hx_comap

end PiBase.Formal
