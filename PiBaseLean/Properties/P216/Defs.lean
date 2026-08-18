module

public import Mathlib.Topology.Compactness.Paracompact
public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.Properties.P30.Lemmas

@[expose] public section

open Topology Set Filter Function

namespace PiBase

/- 216. Hereditarily paracompact space -/
class HereditarilyParacompact (X : Type*) [TopologicalSpace X] : Prop where
  subset_paracompact : Hereditarily ParacompactSpace X

end PiBase

namespace PiBase.Formal

def P216 : Property where
  toPred := HereditarilyParacompact
  well_defined φ h :=
    ⟨Hereditarily.wellDefined WellDefined.paracompactSpace ⟨φ⟩ h.subset_paracompact⟩

end PiBase.Formal
