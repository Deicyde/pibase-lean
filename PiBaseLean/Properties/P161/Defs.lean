module

public import PiBaseLean.AdditionalDefs.Games
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.Properties.P160.Defs

@[expose] public section

universe u

namespace PiBase

/- 161. Markov k-Menger -/
class MarkovKMengerSpace (X : Type u) [TopologicalSpace X] : Prop where
  markov_k_menger : HasMarkovKWinningStrategyB (kMengerGame X) 1

end PiBase

namespace PiBase.Formal

open PiBase

def P161 : Property where
  toPred := MarkovKMengerSpace
  well_defined φ h :=
    ⟨h.markov_k_menger.kMengerGame_of_homeomorph φ⟩

end PiBase.Formal
