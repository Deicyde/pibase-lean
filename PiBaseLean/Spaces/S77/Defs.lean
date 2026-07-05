module

public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S77

/- Space 77: Product of Michael line and irrational numbers.
See https://topology.pi-base.org/spaces/S000077.
The carrier is `ℝ × {x : ℝ // Irrational x}`; the topology is the product of the
Michael line topology (Euclidean opens together with all irrational singletons,
π-Base S63) on the first factor and the subspace topology from ℝ (π-Base S28) on
the second factor. -/

/-- Michael line, as the first factor of `S77` (pi-Base S63, carrier ℝ). -/
def S77.Michael : Type := ℝ

instance : TopologicalSpace S77.Michael :=
  TopologicalSpace.generateFrom
    ({U : Set ℝ | IsOpen U} ∪ {V : Set ℝ | ∃ x : ℝ, Irrational x ∧ V = {x}})

/-- The irrational numbers, as the second factor of `S77` (pi-Base S28). -/
def S77.Irrationals : Type := {x : ℝ // Irrational x}

instance : TopologicalSpace S77.Irrationals := instTopologicalSpaceSubtype

/-- Product of Michael line and irrational numbers (pi-Base S77). -/
def S77 : Type := S77.Michael × S77.Irrationals

instance : TopologicalSpace S77 := instTopologicalSpaceProd

end S77
end PiBase.Spaces
