module

public import PiBaseLean.AdditionalDefs.Games
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.Properties.P151.Defs

@[expose] public section

universe u

namespace PiBase

/- 152. Markov Rothberger -/
class MarkovRothbergerSpace (X : Type u) [TopologicalSpace X] : Prop where
  markov_rothberger : Nonempty X → HasMarkovKWinningStrategyB (rothbergerGame X) 1

end PiBase

namespace PiBase.Formal

open PiBase

def P152 : Property where
  toPred := MarkovRothbergerSpace
  well_defined φ h :=
    ⟨fun hY ↦ (h.markov_rothberger ⟨φ.symm hY.some⟩).rothbergerGame_of_homeomorph φ⟩

end PiBase.Formal
