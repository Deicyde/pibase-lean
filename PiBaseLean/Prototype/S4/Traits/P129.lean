module

public import PiBaseLean.Prototype.S4.Defs
public import PiBaseLean.Properties.P129.Defs

@[expose] public section

namespace PiBase.Formal

open PiBase.Spaces

/-- **S4 is indiscrete** (π-Base trait `P129`, asserted).
The topology on `S4` is `⊤` by definition, so `S4_top = ⊤` holds by `rfl`. -/
theorem S4_P129 : P129 S4 := ⟨rfl⟩

end PiBase.Formal
