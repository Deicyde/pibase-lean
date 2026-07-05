module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S54

/- Space 54: Double pointed reals.
See https://topology.pi-base.org/spaces/S000054.
The product of ℝ (S25) with the indiscrete two-point space `Fin 2` (S4): the basic
open sets are `A × {0, 1}` for `A` a basic open set of ℝ, i.e. two parallel copies
of the standard topology on ℝ. -/

/-- The double pointed reals (pi-Base S54): `ℝ × Fin 2`. -/
def S54 : Type := ℝ × Fin 2

instance : TopologicalSpace S54 :=
  @instTopologicalSpaceProd ℝ (Fin 2) inferInstance ⊤

end S54
end PiBase.Spaces
