module

public import PiBaseLean.AdditionalDefs.Games
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u v

namespace PiBase

/- 151. Strategically Rothberger -/
class StrategicallyRothbergerSpace (X : Type u) [TopologicalSpace X] : Prop where
  strategically_rothberger : Nonempty X → HasWinningStrategyB (rothbergerGame X)

open Set

section Rothberger

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem rothbergerGame_isPayoff_iff (φ : X ≃ₜ Y) (b : ℕ → Set (Set Y)) :
    (rothbergerGame Y).IsPayoff b ↔
      (rothbergerGame X).IsPayoff fun n ↦ preimageFamilyEquiv φ (b n) :=
  g1Game_isPayoff_iff (preimageSetEquiv φ) (preimageFamilyEquiv_mem_openCovers' φ)
    (preimageFamilyEquiv_mem_openCovers' φ) b

theorem HasWinningStrategyB.rothbergerGame_of_homeomorph (φ : X ≃ₜ Y)
    (h : HasWinningStrategyB (rothbergerGame X)) : HasWinningStrategyB (rothbergerGame Y) :=
  h.of_equiv (preimageFamilyEquiv φ) fun b hb ↦ (rothbergerGame_isPayoff_iff φ b).mp hb

theorem HasMarkovKWinningStrategyB.rothbergerGame_of_homeomorph {k : ℕ} (φ : X ≃ₜ Y)
    (h : HasMarkovKWinningStrategyB (rothbergerGame X) k) :
    HasMarkovKWinningStrategyB (rothbergerGame Y) k :=
  h.of_equiv (preimageFamilyEquiv φ) fun b hb ↦ (rothbergerGame_isPayoff_iff φ b).mp hb

end Rothberger

end PiBase

namespace PiBase.Formal

open PiBase

def P151 : Property where
  toPred := StrategicallyRothbergerSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h :=
    ⟨fun hY ↦ (h.strategically_rothberger ⟨φ.symm hY.some⟩).rothbergerGame_of_homeomorph φ⟩

end PiBase.Formal
