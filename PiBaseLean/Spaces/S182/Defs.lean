module

public import Mathlib.Topology.Instances.Rat
public import Mathlib.Analysis.Real.Cardinality

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S182

/- Space 182: Disjoint union of continuum many copies of ℚ.
See https://topology.pi-base.org/spaces/S000182.
The disjoint union (topological sum) of 𝔠-many copies of ℚ, indexed by ℝ
(which has cardinality continuum, `Cardinal.mk_real`), each copy carrying
the usual (subspace-of-ℝ) topology on ℚ; the disjoint union carries the
sigma/coproduct topology (a set is open iff its restriction to each
summand is open). -/

/-- Disjoint union of continuum many copies of `ℚ` (pi-Base S182), indexed by `ℝ`
since `#ℝ = 𝔠` (`Cardinal.mk_real`). -/
def S182 : Type := Σ _ : ℝ, ℚ

instance S182_top : TopologicalSpace S182 := instTopologicalSpaceSigma

end S182
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S182 as a bundled `Space` (carrier + topology). -/
noncomputable def S182 : Space := ⟨PiBase.Spaces.S182.S182, PiBase.Spaces.S182.S182_top⟩

end PiBase.Formal
