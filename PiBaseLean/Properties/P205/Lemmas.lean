module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P205.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.cutPointSpace : WellDefined CutPointSpace :=
  fun {X Y} _ _ hφ hX => by
    let φ := hφ.some
    haveI hcX : ConnectedSpace X := hX.toConnectedSpace
    haveI hcY : ConnectedSpace Y := (Homeomorph.connectedSpace_iff φ).mp hcX
    constructor
    intro q
    intro hpc
    have hq : IsCutPoint (φ.symm q) := hX.all_cut (φ.symm q)
    have h_eq : φ.symm '' ({q}ᶜ : Set Y) = ({φ.symm q}ᶜ : Set X) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [mem_compl_iff, mem_singleton_iff] at hy ⊢
        intro heq
        apply hy
        rw [← φ.apply_symm_apply (y := y), heq, φ.apply_symm_apply]
      · intro hx
        simp only [mem_compl_iff, mem_singleton_iff] at hx
        refine ⟨φ x, ?_, by simp [Homeomorph.symm_apply_apply]⟩
        simp only [mem_compl_iff, mem_singleton_iff]
        intro heq
        apply hx
        have : φ.symm (φ x) = φ.symm q := by rw [heq]
        simpa [Homeomorph.symm_apply_apply] using this
    have : IsPreconnected ({φ.symm q}ᶜ : Set X) := by
      rw [← h_eq]
      exact hpc.image _ φ.symm.continuous.continuousOn
    exact hq this

end Meta

end PiBase
