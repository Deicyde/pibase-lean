module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u

namespace PiBase

/- 240. CW complex -/
class CWComplexSpace (X : Type u) [TopologicalSpace X] : Prop where
  cell_structure : Nonempty (Topology.CWComplex (@Set.univ X))

end PiBase

namespace PiBase.Formal

open Topology Set

/-- Images under a partial equivalence postcomposed with an equivalence. -/
theorem image_transEquiv {α β γ : Type*} (e : PartialEquiv α β) (g : β ≃ γ) (s : Set α) :
    e.transEquiv g '' s = g '' (e '' s) := by
  rw [PartialEquiv.coe_transEquiv, Set.image_comp]

/-- A homeomorphism transports a CW structure on the whole space to a CW structure on the whole
target space: postcompose every characteristic map with the homeomorphism. -/
@[instance_reducible]
def cwComplexUnivOfHomeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (hX : CWComplex (univ : Set X)) : CWComplex (univ : Set Y) where
  cell n := hX.cell n
  map n i := (hX.map n i).transEquiv φ.toEquiv
  source_eq n i := hX.source_eq n i
  continuousOn n i := by
    simpa only [PartialEquiv.coe_transEquiv, Homeomorph.coe_toEquiv] using
      φ.continuous.comp_continuousOn (hX.continuousOn n i)
  continuousOn_symm n i := by
    simp only [PartialEquiv.coe_transEquiv_symm, PartialEquiv.transEquiv_target]
    exact (hX.continuousOn_symm n i).comp φ.symm.continuous.continuousOn
      (mapsTo_preimage _ _)
  pairwiseDisjoint' := by
    intro a _ b _ hab
    simp only [Function.onFun, image_transEquiv]
    exact (Set.disjoint_image_iff φ.injective).mpr
      (hX.pairwiseDisjoint' (mem_univ a) (mem_univ b) hab)
  mapsTo' n i := by
    obtain ⟨I, hI⟩ := hX.mapsTo' n i
    refine ⟨I, fun x hx => ?_⟩
    have hmem := hI hx
    simp only [mem_iUnion] at hmem ⊢
    obtain ⟨m, hm, j, hj, hmem⟩ := hmem
    refine ⟨m, hm, j, hj, ?_⟩
    rw [image_transEquiv]
    exact ⟨_, hmem, rfl⟩
  closed' A _ hA := by
    rw [← φ.isClosed_preimage]
    refine hX.closed' _ (subset_univ _) fun n j => ?_
    have h1 := hA n j
    rw [image_transEquiv] at h1
    have h2 : φ ⁻¹' (A ∩ φ '' (hX.map n j '' Metric.closedBall 0 1))
        = φ ⁻¹' A ∩ hX.map n j '' Metric.closedBall 0 1 := by
      rw [Set.preimage_inter, Set.preimage_image_eq _ φ.injective]
    exact h2 ▸ h1.preimage φ.continuous
  union' := by
    calc ⋃ (n : ℕ) (j : hX.cell n), (hX.map n j).transEquiv φ.toEquiv '' Metric.closedBall 0 1
        = φ '' ⋃ (n : ℕ) (j : hX.cell n), hX.map n j '' Metric.closedBall 0 1 := by
          simp only [image_transEquiv, Homeomorph.coe_toEquiv, Set.image_iUnion]
      _ = φ '' (univ : Set X) := by rw [hX.union']
      _ = univ := by rw [Set.image_univ, φ.surjective.range_eq]

def P240 : Property where
  toPred := CWComplexSpace
  well_defined φ h := ⟨h.cell_structure.map (cwComplexUnivOfHomeomorph φ)⟩

end PiBase.Formal
