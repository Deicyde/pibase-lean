module

public import Mathlib.Topology.Separation.Basic
public import PiBaseLean.Properties.Bundled.Basic
public import PiBaseLean.Properties.P1.Defs
public import PiBaseLean.Properties.P16.Defs

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces

/- Space 4: the indiscrete topology on a two-point set {0, 1}.
See https://topology.pi-base.org/spaces/S000004.
The single most-separating space in π-Base: it is compact (P16) but not T₀ (P1). -/

/-- The indiscrete topology on `Fin 2`. -/
def Indiscrete2 : Type := Fin 2

namespace Indiscrete2

instance : TopologicalSpace Indiscrete2 := ⊤
instance : Finite Indiscrete2 := inferInstanceAs (Finite (Fin 2))
instance : DecidableEq Indiscrete2 := inferInstanceAs (DecidableEq (Fin 2))
instance : CompactSpace Indiscrete2 := Finite.compactSpace

/-- The two points are topologically inseparable, so the space is not T₀. -/
theorem not_t0 : ¬ T0Space Indiscrete2 := by
  rw [t0Space_iff_inseparable]
  intro h
  have e01 : ((0 : Fin 2) : Indiscrete2) = ((1 : Fin 2) : Indiscrete2) := by
    apply h
    rw [inseparable_iff_forall_isOpen]
    intro s hs
    rcases (TopologicalSpace.isOpen_top_iff s).mp hs with rfl | rfl <;> simp
  exact absurd e01 (by decide)

end Indiscrete2

theorem indiscrete2_compact : CompactSpace Indiscrete2 := inferInstance

end PiBase.Spaces

namespace PiBase.Formal

/-- Compact does not imply T₀ — witnessed by the indiscrete two-point space
(π-Base S4), the topological analog of a finite counterexample magma.
Stated for `Type` (universe 0), where the witness lives. -/
theorem not_P16_le_P1 : ¬ ((P16 : Property.{0}) ≤ P1) := fun h =>
  Spaces.Indiscrete2.not_t0 (h Spaces.Indiscrete2 inferInstance Spaces.indiscrete2_compact)

end PiBase.Formal

namespace PiBase.Formal

/-- π-Base S4 as a bundled `Space` (carrier + topology). -/
noncomputable def S4 : Space := ⟨PiBase.Spaces.Indiscrete2, inferInstance⟩

end PiBase.Formal
