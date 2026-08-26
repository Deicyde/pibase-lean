module

public import PiBaseLean.AdditionalDefs.Games
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.Properties.P69.Defs

@[expose] public section

universe u

namespace PiBase

/- 70. Markov Menger -/
class MarkovMengerSpace (X : Type u) [TopologicalSpace X] : Prop where
  markov_menger : HasMarkovKWinningStrategyB (mengerGame X) 1

end PiBase

namespace PiBase.Formal

def P70 : Property where
  toPred := MarkovMengerSpace
  well_defined φ h :=
    ⟨h.markov_menger.mengerGame_of_homeomorph φ⟩

end PiBase.Formal
