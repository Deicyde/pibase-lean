module

public import PiBaseLean.Prototype.S4.Defs
public import PiBaseLean.Properties.P175.Defs
import Mathlib.Tactic.NormNum

@[expose] public section

open Cardinal

namespace PiBase.Formal

open PiBase.Spaces

/-- **S4 does *not* have cardinality ≥ 3** (π-Base trait `P175`, asserted `false`).
`#S4 = #(Fin 2) = 2 < 3`. -/
theorem S4_not_P175 : ¬ P175 S4 := by
  intro h
  have h3 : (3 : Cardinal) ≤ #(Fin 2) := h.card_ge
  norm_num [Cardinal.mk_fin] at h3

end PiBase.Formal
