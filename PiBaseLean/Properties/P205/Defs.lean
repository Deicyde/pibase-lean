module

public import PiBaseLean.AdditionalDefs.Constructions
public import PiBaseLean.Properties.Bundled.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

open Topology Set Function

namespace PiBase

/- 205. Cut point space -/
class CutPointSpace (X : Type*)
    [TopologicalSpace X] extends ConnectedSpace X where
  all_cut (p : X) : IsCutPoint p

end PiBase

namespace PiBase.Formal

def P205 : Property where
  toPred := CutPointSpace
  well_defined {X Y} _ _ φ h := by
    haveI hcX : ConnectedSpace X := h.toConnectedSpace
    haveI hcY : ConnectedSpace Y := (Homeomorph.connectedSpace_iff φ).mp hcX
    constructor
    intro q
    intro hpc
    have hq : IsCutPoint (φ.symm q) := h.all_cut (φ.symm q)
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

end PiBase.Formal
