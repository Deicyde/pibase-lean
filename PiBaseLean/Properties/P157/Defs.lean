module

public import PiBaseLean.AdditionalDefs.Games
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.Properties.P151.Defs

@[expose] public section

universe u v

namespace PiBase

/- 157. Strategically k-Rothberger -/
class StrategicallyKRothbergerSpace (X : Type u) [TopologicalSpace X] : Prop where
  strategically_k_rothberger : HasWinningStrategyB (kRothbergerGame X)

end PiBase

namespace PiBase

open Set

/-! ### Transporting the k-Rothberger game along a homeomorphism

The k-Rothberger game is the `g1Game` played with k-covers, so the transport machinery of
`PiBaseLean.Properties.P151.Defs` applies verbatim once we know that being a k-cover is
invariant under a homeomorphism (`preimageFamilyEquiv_isKCover'`). -/

section KRothberger

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem preimageFamilyEquiv_mem_kCovers (φ : X ≃ₜ Y) (S : Set (Set Y)) :
    preimageFamilyEquiv φ S ∈ {A : Set (Set X) | IsKCover' A} ↔
      S ∈ {A : Set (Set Y) | IsKCover' A} :=
  preimageFamilyEquiv_isKCover' φ S

theorem kRothbergerGame_isPayoff_iff (φ : X ≃ₜ Y) (b : ℕ → Set (Set Y)) :
    (kRothbergerGame Y).IsPayoff b ↔
      (kRothbergerGame X).IsPayoff fun n ↦ preimageFamilyEquiv φ (b n) :=
  g1Game_isPayoff_iff (preimageSetEquiv φ) (preimageFamilyEquiv_mem_kCovers φ)
    (preimageFamilyEquiv_mem_kCovers φ) b

theorem HasWinningStrategyB.kRothbergerGame_of_homeomorph (φ : X ≃ₜ Y)
    (h : HasWinningStrategyB (kRothbergerGame X)) : HasWinningStrategyB (kRothbergerGame Y) :=
  h.of_equiv (preimageFamilyEquiv φ) fun b hb ↦ (kRothbergerGame_isPayoff_iff φ b).mp hb

theorem HasMarkovKWinningStrategyB.kRothbergerGame_of_homeomorph {k : ℕ} (φ : X ≃ₜ Y)
    (h : HasMarkovKWinningStrategyB (kRothbergerGame X) k) :
    HasMarkovKWinningStrategyB (kRothbergerGame Y) k :=
  h.of_equiv (preimageFamilyEquiv φ) fun b hb ↦ (kRothbergerGame_isPayoff_iff φ b).mp hb

end KRothberger

end PiBase

namespace PiBase.Formal

open PiBase

def P157 : Property where
  toPred := StrategicallyKRothbergerSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h :=
    ⟨h.strategically_k_rothberger.kRothbergerGame_of_homeomorph φ⟩

end PiBase.Formal
