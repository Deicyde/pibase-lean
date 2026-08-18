module

public import Mathlib.Topology.Algebra.Module.Basic
public import PiBaseLean.Properties.Bundled.Defs
public import Mathlib.Data.Real.Basic
public import PiBaseLean.AdditionalDefs.Meta
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance

@[expose] public section

universe u

namespace PiBase

/- 238. Has a real TVS topology -/
class HasRealTVSTopology (X : Type u) [t : TopologicalSpace X] : Prop where
  homeomorphic_to_tvs : ∃ a : (AddCommMonoid X), ∃ (_ : @Module ℝ X _ a),
    (Continuous fun ((r , x) : ℝ × X) ↦ r • x) ∧
      Continuous fun ((x, y) : X × X) ↦ x + y

end PiBase

namespace PiBase.Formal

def P238 : Property where
  toPred := HasRealTVSTopology
  well_defined {X Y} _ _ φ h := by
    obtain ⟨aX, mX, hCont⟩ := h.homeomorphic_to_tvs
    obtain ⟨hSmulCont, hAddCont⟩ := hCont
    letI : AddCommMonoid X := aX
    letI : Module ℝ X := mX
    let e : Y ≃ X := φ.symm.toEquiv
    let aY : AddCommMonoid Y := e.addCommMonoid
    letI : AddCommMonoid Y := aY
    let mY : Module ℝ Y := e.module ℝ
    refine ⟨aY, mY, ?_, ?_⟩
    · -- scalar multiplication continuity by conjugation with φ / φ.symm
      -- Y smul is φ (r • φ.symm y) by Equiv.smul / module transport
      have h_eq : (fun p : ℝ × Y => p.1 • p.2) =
          (fun p : ℝ × Y => φ (p.1 • φ.symm p.2)) := by
        funext p
        rfl
      rw [h_eq]
      have h_fst : Continuous (fun p : ℝ × Y => p.1) := continuous_fst
      have h_snd_symm : Continuous (fun p : ℝ × Y => φ.symm p.2) :=
        φ.symm.continuous.comp continuous_snd
      have h_pair : Continuous (fun p : ℝ × Y => (p.1, φ.symm p.2)) :=
        Continuous.prodMk h_fst h_snd_symm
      have h_comp : Continuous (fun p : ℝ × Y => p.1 • φ.symm p.2) :=
        hSmulCont.comp h_pair
      exact φ.continuous.comp h_comp
    · -- addition continuity by conjugation with φ / φ.symm
      -- Y addition is φ (φ.symm y₁ + φ.symm y₂) by Equiv.add transport
      have h_eq : (fun p : Y × Y => p.1 + p.2) =
          (fun p : Y × Y => φ (φ.symm p.1 + φ.symm p.2)) := by
        funext p
        rfl
      rw [h_eq]
      have h_fst_symm : Continuous (fun p : Y × Y => φ.symm p.1) :=
        φ.symm.continuous.comp continuous_fst
      have h_snd_symm : Continuous (fun p : Y × Y => φ.symm p.2) :=
        φ.symm.continuous.comp continuous_snd
      have h_pair : Continuous (fun p : Y × Y => (φ.symm p.1, φ.symm p.2)) :=
        Continuous.prodMk h_fst_symm h_snd_symm
      have h_comp : Continuous (fun p : Y × Y => φ.symm p.1 + φ.symm p.2) :=
        hAddCont.comp h_pair
      exact φ.continuous.comp h_comp

end PiBase.Formal
