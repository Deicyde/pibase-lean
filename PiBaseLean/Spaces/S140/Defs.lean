module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Set.Countable

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S140

/- Space 140: ℝ extended by a point with co-countable open neighborhoods.
See https://topology.pi-base.org/spaces/S000140.
The carrier is `ℝ ∪ {∞}` (modeled as `Option ℝ`, with `none` playing the role of `∞`);
the topology is generated from the Euclidean-open subsets of ℝ together with the sets
`{∞} ∪ U` for `U` open and co-countable in ℝ. -/

/-- ℝ extended by a point with co-countable open neighborhoods (pi-Base S140). -/
def S140 : Type := Option ℝ

instance : TopologicalSpace S140 :=
  TopologicalSpace.generateFrom
    ({s | ∃ U : Set ℝ, IsOpen U ∧ s = Option.some '' U} ∪
      {s | ∃ U : Set ℝ, IsOpen U ∧ Uᶜ.Countable ∧ s = insert none (Option.some '' U)})

end S140
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S140 as a bundled `Space` (carrier + topology). -/
noncomputable def S140 : Space := ⟨PiBase.Spaces.S140.S140, inferInstance⟩

end PiBase.Formal
