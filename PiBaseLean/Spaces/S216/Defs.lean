module

public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Rat.Denumerable

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Filter

namespace PiBase.Spaces
namespace S216

/- Space 216: Katětov's non-normal subspace of βℕ.
See https://topology.pi-base.org/spaces/S000216.
Fix a bijection φ : ℕ ≃ ℚ. For each real `r` pick (via `Real.exists_seq_rat_strictMono_tendsto`)
a sequence of rationals `katetovRatSeq r : ℕ → ℚ` tending to `r`, transport it into `Ultrafilter ℕ`
(the carrier of βℕ, pi-Base S108) along `φ.symm` and `pure`, and pick a cluster point
`katetovPt r` of that sequence (which exists since `Ultrafilter ℕ` is compact). The carrier
`S216` is `ℕ` (as principal ultrafilters) together with `D = katetovPt '' {irrationals}`,
topologized as a subspace of βℕ. -/

/-- A fixed bijection `ℕ ≃ ℚ`, used to move sequences of rationals into `Ultrafilter ℕ`. -/
noncomputable def katetovEquiv : ℕ ≃ ℚ := (Denumerable.eqv ℚ).symm

/-- For each real `r`, a sequence of rationals tending to `r`
(only the irrational case is used in the construction of `S216`). -/
noncomputable def katetovRatSeq (r : ℝ) : ℕ → ℚ :=
  (Real.exists_seq_rat_strictMono_tendsto r).choose

/-- The corresponding sequence of principal ultrafilters `E_r`, living in βℕ. -/
noncomputable def katetovSeq (r : ℝ) : ℕ → Ultrafilter ℕ :=
  fun n => pure (katetovEquiv.symm (katetovRatSeq r n))

/-- A cluster point `p_{E_r}` of `E_r` in the compact space βℕ (a limit point of `E_r`,
since `E_r` is the range of a sequence). -/
noncomputable def katetovPt (r : ℝ) : Ultrafilter ℕ :=
  (exists_clusterPt_of_compactSpace (map (katetovSeq r) atTop)).choose

/-- `D`: one chosen limit point `katetovPt r` for each irrational `r`. -/
noncomputable def katetovD : Set (Ultrafilter ℕ) :=
  katetovPt '' {r : ℝ | Irrational r}

/-- The carrier of Katětov's space: `ℕ` (as principal ultrafilters) together with `D`,
sitting inside βℕ. -/
noncomputable def katetovCarrier : Set (Ultrafilter ℕ) :=
  Set.range (pure : ℕ → Ultrafilter ℕ) ∪ katetovD

/-- Katětov's non-normal subspace of βℕ (pi-Base S216), realized as the subspace
`ℕ ∪ D ⊆ βℕ` of the Stone-Čech compactification of the naturals. -/
def S216 : Type := katetovCarrier

instance S216_top : TopologicalSpace S216 := inferInstanceAs (TopologicalSpace katetovCarrier)

end S216
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S216 as a bundled `Space` (carrier + topology). -/
noncomputable def S216 : Space := ⟨PiBase.Spaces.S216.S216, PiBase.Spaces.S216.S216_top⟩

end PiBase.Formal
