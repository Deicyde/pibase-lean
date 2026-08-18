module

public import Mathlib.Topology.Bases
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

namespace PiBase

/- 50. Zero dimensional -/
class ZeroDimensionalSpace (X : Type*) [TopologicalSpace X] : Prop where
  zero_dimensional : ∃ B : Set (Set X), IsTopologicalBasis B ∧ ∀ s ∈ B, IsClopen s

end PiBase

namespace PiBase.Formal

def P50 : Property where
  toPred := ZeroDimensionalSpace
  well_defined φ h := by
    rcases h.zero_dimensional with ⟨B, Bβ, Bc⟩
    refine ⟨Set.image φ '' B, Bβ.isQuotientMap φ.isQuotientMap φ.isOpenMap, ?_⟩
    rintro _ ⟨s, sB, rfl⟩
    have hc : IsClopen s := Bc s sB
    -- IsClopen = IsClosed ∧ IsOpen, so order is ⟨closed, open⟩
    exact ⟨φ.isClosedMap _ hc.1, φ.isOpenMap _ hc.2⟩

end PiBase.Formal
