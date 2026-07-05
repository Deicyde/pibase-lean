module

public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Constructions

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S222

/- Space 222: Product topology on $\omega^{2^\mathfrak{c}}$.
See https://topology.pi-base.org/spaces/S000222.
The carrier is `Set ℝ → ℕ`, i.e. the `2^𝔠`-indexed power of `ω` (π-Base S2, discrete
topology on a countably infinite set), the index set `Set ℝ` having cardinality `2^𝔠`
(as in π-Base S219); topologized with the product topology built from the discrete
topology `⊥` on each factor `ℕ`. -/

/-- Product topology on `ω^(2^𝔠)` (pi-Base S222), the carrier `Set ℝ → ℕ`. -/
def S222 : Type := Set ℝ → ℕ

instance S222_top : TopologicalSpace S222 :=
  @Pi.topologicalSpace (Set ℝ) (fun _ => ℕ) (fun _ => (⊥ : TopologicalSpace ℕ))

end S222
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S222 as a bundled `Space` (carrier + topology). -/
noncomputable def S222 : Space := ⟨PiBase.Spaces.S222.S222, PiBase.Spaces.S222.S222_top⟩

end PiBase.Formal
