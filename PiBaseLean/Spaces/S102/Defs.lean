module

public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Constructions

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S102

/- Space 102: Baire space of weight continuum B(𝔠).
See https://topology.pi-base.org/spaces/S000102.
The carrier is ℕ → ℝ, i.e. the countable power of ℝ (π-Base S3, discrete topology);
topologized with the product topology built from the discrete topology `⊥` on each factor. -/

/-- Baire space of weight continuum `B(𝔠)` (pi-Base S102), the carrier `ℕ → ℝ`. -/
def S102 : Type := ℕ → ℝ

instance : TopologicalSpace S102 :=
  @Pi.topologicalSpace ℕ (fun _ => ℝ) (fun _ => (⊥ : TopologicalSpace ℝ))

end S102
end PiBase.Spaces
