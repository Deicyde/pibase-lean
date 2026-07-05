module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S101

/- Space 101: Continuum power of a countable discrete space.
See https://topology.pi-base.org/spaces/S000101.
Carrier `ℝ → ℕ` (a continuum-indexed product of the countable discrete space `ℕ`);
topology is the product (Tychonoff) topology `Pi.topologicalSpace`, built from the
discrete topology `⊥` on each factor `ℕ`. -/

/-- Continuum power of a countable discrete space (pi-Base S101). -/
def S101 : Type := ℝ → ℕ

instance S101_top : TopologicalSpace S101 :=
  @Pi.topologicalSpace ℝ (fun _ => ℕ) (fun _ => ⊥)

end S101
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S101 as a bundled `Space` (carrier + topology). -/
noncomputable def S101 : Space := ⟨PiBase.Spaces.S101.S101, PiBase.Spaces.S101.S101_top⟩

end PiBase.Formal
