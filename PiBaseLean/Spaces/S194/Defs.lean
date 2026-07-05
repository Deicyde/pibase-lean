module

public import Mathlib.Topology.Order
public import Mathlib.Data.Real.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S194

/- Space 194: Indiscrete topology on ℝ.
See https://topology.pi-base.org/spaces/S000194.
The carrier is the real numbers, topologized with only ∅ and the whole space open. -/

/-- Indiscrete topology on ℝ (pi-Base S194). -/
def S194 : Type := ℝ

instance S194_top : TopologicalSpace S194 := ⊤

end S194
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S194 as a bundled `Space` (carrier + topology). -/
noncomputable def S194 : Space := ⟨PiBase.Spaces.S194.S194, PiBase.Spaces.S194.S194_top⟩

end PiBase.Formal
