module

public import Mathlib.Topology.Compactification.StoneCech

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S111

/- Space 111: Single ultrafilter subspace of βω.
See https://topology.pi-base.org/spaces/S000111.
The carrier is ω ∪ {F} for a fixed non-principal ultrafilter F on ω = ℕ, i.e. the
principal ultrafilters `pure n` together with `hyperfilter ℕ`, carrying the subspace
topology induced from βω (the space of all ultrafilters on ℕ, pi-Base S108). -/

/-- Single ultrafilter subspace of βω (pi-Base S111): the points of `ω` (as principal
ultrafilters) together with one fixed non-principal ultrafilter on `ω = ℕ`. -/
def S111 : Type := {u : Ultrafilter ℕ // (∃ n : ℕ, u = pure n) ∨ u = Filter.hyperfilter ℕ}

instance : TopologicalSpace S111 := instTopologicalSpaceSubtype

end S111
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S111 as a bundled `Space` (carrier + topology). -/
noncomputable def S111 : Space := ⟨PiBase.Spaces.S111.S111, inferInstance⟩

end PiBase.Formal
