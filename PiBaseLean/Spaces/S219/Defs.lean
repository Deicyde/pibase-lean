module

public import Mathlib.Topology.Order
public import Mathlib.Data.Real.Basic

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S219

/- Space 219: Discrete space of size $2^{\mathfrak c}$.
See https://topology.pi-base.org/spaces/S000219.
Carrier is `Set ℝ` (the power set of ℝ, of cardinality `2 ^ 𝔠`); all subsets are open. -/

/-- Discrete space of size `2 ^ 𝔠` (pi-Base S219), realized as the power set of ℝ. -/
def S219 : Type := Set ℝ

instance : TopologicalSpace S219 := ⊥

end S219
end PiBase.Spaces
