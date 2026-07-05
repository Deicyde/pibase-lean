module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S16

/- Space 16: Cofinite topology on ℝ.
See https://topology.pi-base.org/spaces/S000016.
A subset U ⊆ ℝ is open iff U = ∅ or ℝ \ U is finite; this is Mathlib's
`CofiniteTopology` construction specialized to the carrier ℝ. -/

/-- Cofinite topology on ℝ (pi-Base S16). -/
def S16 : Type := CofiniteTopology ℝ

instance : TopologicalSpace S16 := inferInstanceAs (TopologicalSpace (CofiniteTopology ℝ))

end S16
end PiBase.Spaces
