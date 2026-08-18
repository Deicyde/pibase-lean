module

public import PiBaseLean.AdditionalDefs.Games
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.Properties.P151.Defs

@[expose] public section

universe u

namespace PiBase

/- 160. Strategically k-Menger -/
class StrategicallyKMengerSpace (X : Type u) [TopologicalSpace X] : Prop where
  strategically_k_menger : HasWinningStrategyB (kMengerGame X)

end PiBase

namespace PiBase

open Set

/-! ### Transporting the k-Menger game along a homeomorphism

The k-Menger game is the `gFinGame` played with k-covers, so the transport machinery of
`PiBaseLean.Properties.P151.Defs` applies verbatim once we know that being a k-cover is
invariant under a homeomorphism (`preimageFamilyEquiv_isKCover'`). -/

section KMenger

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem preimageFamilyEquiv_mem_kCovers' (φ : X ≃ₜ Y) (S : Set (Set Y)) :
    preimageFamilyEquiv φ S ∈ {A : Set (Set X) | IsKCover' A} ↔
      S ∈ {A : Set (Set Y) | IsKCover' A} :=
  preimageFamilyEquiv_isKCover' φ S

theorem kMengerGame_isPayoff_iff (φ : X ≃ₜ Y) (b : ℕ → Set (Set Y)) :
    (kMengerGame Y).IsPayoff b ↔
      (kMengerGame X).IsPayoff fun n ↦ preimageFamilyEquiv φ (b n) :=
  gFinGame_isPayoff_iff (preimageSetEquiv φ) (preimageFamilyEquiv_mem_kCovers' φ)
    (preimageFamilyEquiv_mem_kCovers' φ) b

theorem HasWinningStrategyB.kMengerGame_of_homeomorph (φ : X ≃ₜ Y)
    (h : HasWinningStrategyB (kMengerGame X)) : HasWinningStrategyB (kMengerGame Y) :=
  h.of_equiv (preimageFamilyEquiv φ) fun b hb ↦ (kMengerGame_isPayoff_iff φ b).mp hb

theorem HasMarkovKWinningStrategyB.kMengerGame_of_homeomorph {k : ℕ} (φ : X ≃ₜ Y)
    (h : HasMarkovKWinningStrategyB (kMengerGame X) k) :
    HasMarkovKWinningStrategyB (kMengerGame Y) k :=
  h.of_equiv (preimageFamilyEquiv φ) fun b hb ↦ (kMengerGame_isPayoff_iff φ b).mp hb

end KMenger

end PiBase

namespace PiBase.Formal

open PiBase

def P160 : Property where
  toPred := StrategicallyKMengerSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h :=
    ⟨h.strategically_k_menger.kMengerGame_of_homeomorph φ⟩

end PiBase.Formal
