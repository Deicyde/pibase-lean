module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S66

/- Space 66: Double origin plane.
See https://topology.pi-base.org/spaces/S000066.
Carrier `X = ℝ² ⊕ Unit`: all of the plane `ℝ × ℝ` (via `Sum.inl`, including the ordinary
origin `(0,0)`), together with one extra point `0* = Sum.inr ()`. The topology is generated
by: the usual Euclidean open subsets of the plane minus the origin, together with the
half-disk neighbourhood bases `Vₙ(0) = {(x,y) : x²+y² < 1/n², y > 0} ∪ {0}` at the origin
and `Vₙ(0*) = {(x,y) : x²+y² < 1/n², y < 0} ∪ {0*}` at the extra point. -/

/-- Double origin plane (pi-Base S66): the plane `ℝ × ℝ` with one extra point `0*`
adjoined, represented as `Sum.inr ()`. -/
def S66 : Type := (ℝ × ℝ) ⊕ Unit

/-- The generating subbasis for the topology on `S66`:
* the Euclidean-open subsets of the plane minus the origin (lifted through `Sum.inl`),
  giving every point other than the origin and `0*` its usual Euclidean neighbourhoods;
* the half-disk neighbourhood bases `Vₙ(0)` at the origin `(0,0)`;
* the half-disk neighbourhood bases `Vₙ(0*)` at the extra point `0* = Sum.inr ()`. -/
def S66.Generators : Set (Set S66) :=
  (Set.range fun U : {U : Set (ℝ × ℝ) // IsOpen U ∧ (0, 0) ∉ U} => Sum.inl '' U.1) ∪
  (Set.range fun n : ℕ =>
    (Sum.inl '' {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1 / (n + 1 : ℝ) ^ 2 ∧ 0 < p.2}) ∪
      {Sum.inl (0, 0)}) ∪
  (Set.range fun n : ℕ =>
    (Sum.inl '' {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1 / (n + 1 : ℝ) ^ 2 ∧ p.2 < 0}) ∪
      {Sum.inr ()})

instance : TopologicalSpace S66 := TopologicalSpace.generateFrom S66.Generators

end S66
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S66 as a bundled `Space` (carrier + topology). -/
noncomputable def S66 : Space := ⟨PiBase.Spaces.S66.S66, inferInstance⟩

end PiBase.Formal
