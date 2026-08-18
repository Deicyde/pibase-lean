module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.Properties.P18.Lemmas

@[expose] public section

open Topology Set Filter TopologicalSpace

universe u

namespace PiBase

/- 149. ω-Lindelöf -/
class OmegaLindelof (X : Type u) [TopologicalSpace X] : Prop where
  omega_lindelof : Omega LindelofSpace X

end PiBase

namespace PiBase.Formal

def P149 : Property where
  toPred := OmegaLindelof
  well_defined φ h :=
    ⟨Omega.wellDefined WellDefined.lindelofSpace ⟨φ⟩ h.omega_lindelof⟩

end PiBase.Formal
