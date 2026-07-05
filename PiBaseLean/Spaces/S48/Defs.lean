module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S48

/- Space 48: Cofinite topology on $\omega$ extended by a non-open generic point.
See https://topology.pi-base.org/spaces/S000048.
Carrier $X = \omega \sqcup \{p\}$ (using `Option ℕ`, with `p := none`); a nonempty
set is open iff it contains `p` and has finite complement. -/

/-- Cofinite topology on `ω` extended by a non-open generic point `p`
(pi-Base S48). The point `p` is represented as `none`. -/
def S48 : Type := Option ℕ

instance : TopologicalSpace S48 :=
  TopologicalSpace.generateFrom
    {s : Set (Option ℕ) | (none : Option ℕ) ∈ s ∧ sᶜ.Finite}

end S48
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S48 as a bundled `Space` (carrier + topology). -/
noncomputable def S48 : Space := ⟨PiBase.Spaces.S48.S48, inferInstance⟩

end PiBase.Formal
