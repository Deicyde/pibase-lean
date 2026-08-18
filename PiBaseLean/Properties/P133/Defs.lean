module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

namespace PiBase

/- 133. Lots -/
class Lots (X : Type*) [TopologicalSpace X] : Prop where
  from_linear_order : ∃ (_ : LinearOrder X), OrderTopology X

/-- The order topology transported along a homeomorphism is again an order topology. -/
theorem Homeomorph.lots {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [h : Lots X] (f : X ≃ₜ Y) : Lots Y where
  from_linear_order := by
    classical
    obtain ⟨l, hl⟩ := h.from_linear_order
    let I : LinearOrder Y := Equiv.linearOrder f.toEquiv.symm
    refine ⟨I, ?_⟩
    refine { topology_eq_generate_intervals := ?_ }
    rw [← f.symm.induced_eq]
    refine StrictMono.induced_topology_eq_preorder (fun ⦃a b⦄ a_1 ↦ a_1) ?_
    rw [f.symm.range_coe]
    exact Set.ordConnected_univ

end PiBase

namespace PiBase.Formal

def P133 : Property where
  toPred := Lots
  well_defined φ h := Homeomorph.lots (h := h) φ

end PiBase.Formal
