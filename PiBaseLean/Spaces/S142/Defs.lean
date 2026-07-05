module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Defs.Induced

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S142

/- Space 142: Erdős space.
See https://topology.pi-base.org/spaces/S000142.
The subspace of `ℓ²` (real square-summable sequences, π-Base S30's ambient Banach
space) consisting of those sequences all of whose coordinates are rational, with
the subspace topology inherited from the `ℓ²`-norm topology. -/

/-- The rational-coordinate points of `ℓ²`: the carrier predicate for Erdős space. -/
def S142.IsRatSeq (x : lp (fun _ : ℕ => ℝ) 2) : Prop := ∀ i, ∃ q : ℚ, x i = (q : ℝ)

/-- Erdős space (pi-Base S142): the subspace of `ℓ²` of sequences with all
coordinates rational. -/
noncomputable def S142 : Type := {x : lp (fun _ : ℕ => ℝ) 2 // S142.IsRatSeq x}

noncomputable instance : TopologicalSpace S142 := instTopologicalSpaceSubtype

end S142
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S142 as a bundled `Space` (carrier + topology). -/
noncomputable def S142 : Space := ⟨PiBase.Spaces.S142.S142, inferInstance⟩

end PiBase.Formal
