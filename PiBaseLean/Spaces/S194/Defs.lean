module

public import Mathlib.Topology.Order
public import Mathlib.Data.Real.Basic

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S194

/- Space 194: Indiscrete topology on ℝ.
See https://topology.pi-base.org/spaces/S000194.
The carrier is the real numbers, topologized with only ∅ and the whole space open. -/

/-- Indiscrete topology on ℝ (pi-Base S194). -/
def S194 : Type := ℝ

instance : TopologicalSpace S194 := ⊤

end S194
end PiBase.Spaces
