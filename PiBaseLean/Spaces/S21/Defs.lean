module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.Module.WeakBilin

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S21

/- Space 21: Weak topology on separable Hilbert space.
See https://topology.pi-base.org/spaces/S000021.
Carrier: `H := ℓ²(ℕ, ℝ)`, the separable infinite-dimensional real Hilbert space of
square-summable real sequences. Topology: the weak topology on `H`, i.e. the coarsest
topology making every continuous linear functional continuous; by the Riesz
representation theorem every such functional is `⟨·, y⟩` for some `y : H`, so this is
exactly the topology induced on `H` by the bilinear form
`innerₗ H : H →ₗ[ℝ] H →ₗ[ℝ] ℝ` (`WeakBilin`), whose subbasic open sets at `x` are
`{y | |⟪y - x, xᵢ⟫| < ε, i = 1, …, n}`. -/

/-- Weak topology on separable Hilbert space (pi-Base S21).
The carrier is `ℓ²(ℕ, ℝ)`, the separable infinite-dimensional real Hilbert space of
square-summable real sequences. -/
def S21 : Type := WeakBilin (innerₗ ℓ²(ℕ, ℝ))

noncomputable instance S21_top : TopologicalSpace S21 :=
  WeakBilin.instTopologicalSpace (innerₗ ℓ²(ℕ, ℝ))

end S21
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S21 as a bundled `Space` (carrier + topology). -/
noncomputable def S21 : Space := ⟨PiBase.Spaces.S21.S21, PiBase.Spaces.S21.S21_top⟩

end PiBase.Formal
