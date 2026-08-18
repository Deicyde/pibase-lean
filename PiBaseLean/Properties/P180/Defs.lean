module

public import Mathlib.Topology.Bases
public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.Properties.P26.Lemmas

@[expose] public section

open TopologicalSpace

namespace PiBase

/- 180. Hereditarily separable -/
class HereditarilySeparableSpace (X : Type*) [TopologicalSpace X] : Prop where
  subset_separable : Hereditarily SeparableSpace X

end PiBase

namespace PiBase.Formal

def P180 : Property where
  toPred := HereditarilySeparableSpace
  well_defined φ h :=
    ⟨Hereditarily.wellDefined WellDefined.separableSpace ⟨φ⟩ h.subset_separable⟩

end PiBase.Formal
