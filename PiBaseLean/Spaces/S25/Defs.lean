module

public import Mathlib.Topology.Instances.Real.Lemmas
public import PiBaseLean.Properties.Bundled.Basic
public import PiBaseLean.Properties.P3.Defs
public import PiBaseLean.Properties.P16.Defs
public import PiBaseLean.Properties.P36.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces

/- Space 25: Euclidean real numbers ℝ.
See https://topology.pi-base.org/spaces/S000025.
The traits we need: ℝ is T₂ (P3) and connected (P36) but not compact (P16). -/

theorem reals_t2 : T2Space ℝ := inferInstance

theorem reals_preconnected : PreconnectedSpace ℝ := inferInstance

theorem reals_not_compact : ¬ CompactSpace ℝ := not_compactSpace_iff.mpr inferInstance

end PiBase.Spaces

namespace PiBase.Formal

/-- T₂ does not imply compact — witnessed by ℝ (π-Base S25).
Stated for `Type` (universe 0), where the witness lives. -/
theorem not_P3_le_P16 : ¬ ((P3 : Property.{0}) ≤ P16) := fun h =>
  Spaces.reals_not_compact (h ℝ inferInstance Spaces.reals_t2)

/-- Connected does not imply compact — witnessed by ℝ (π-Base S25). -/
theorem not_P36_le_P16 : ¬ ((P36 : Property.{0}) ≤ P16) := fun h =>
  Spaces.reals_not_compact (h ℝ inferInstance Spaces.reals_preconnected)

end PiBase.Formal
