module

public import PiBaseLean.Prototype.S4.Defs
public import PiBaseLean.Properties.P125.Defs

@[expose] public section

namespace PiBase.Formal

open PiBase.Spaces

/-- **S4 has multiple points** (π-Base trait `P125`, asserted).
`S4` is `Fin 2`, which is nontrivial. -/
theorem S4_P125 : P125 S4 := inferInstanceAs (Nontrivial (Fin 2))

end PiBase.Formal
