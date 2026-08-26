module

public import PiBaseLean.AdditionalDefs.Games
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.Properties.P69.Defs

@[expose] public section

universe u

namespace PiBase

/- 72. 2-Markov Menger -/
class TwoMarkovMengerSpace (X : Type u) [TopologicalSpace X] : Prop where
  two_markov_menger : HasMarkovKWinningStrategyB (mengerGame X) 2

end PiBase

namespace PiBase.Formal

def P72 : Property where
  toPred := TwoMarkovMengerSpace
  well_defined φ h :=
    ⟨h.two_markov_menger.mengerGame_of_homeomorph φ⟩

end PiBase.Formal
