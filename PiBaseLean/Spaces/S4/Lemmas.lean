module

public import PiBaseLean.Properties.P129.Defs
public import PiBaseLean.Spaces.Constructions.Finite.Lemmas
public import PiBaseLean.Spaces.S4.Defs

-- BEGIN PIBASE TRAIT IMPORTS
public meta import PiBaseLean.Audit.Spaces.Registry
public import PiBaseLean.Properties.P176.Defs
public import PiBaseLean.Properties.P185.Defs
public import PiBaseLean.Properties.P204.Defs
public import PiBaseLean.Properties.P205.Defs
public import PiBaseLean.Theorems.T430.Theorem
public import PiBaseLean.Theorems.T448.Theorem
public import PiBaseLean.Theorems.T558.Theorem
public import PiBaseLean.Theorems.T635.Theorem
-- END PIBASE TRAIT IMPORTS

@[expose] public section

namespace PiBase.Formal

/-! ## Direct catalog traits -/

theorem S4_P125 : P125 PiBase.S4 :=
  P125.well_defined PiBase.S4_canonicalHomeomorph.symm
    (show Nontrivial (PiBase.SpaceConstructions.FiniteIndiscrete 2) from inferInstance)

register_certificate S000004 P000125 true
  proof PiBase.Formal.S4_P125
  provenance direct
  assumptions []

theorem S4_P129 : P129 PiBase.S4 := by
  change IndiscreteTopology PiBase.S4
  infer_instance

register_certificate S000004 P000129 true
  proof PiBase.Formal.S4_P129
  provenance direct
  assumptions []

theorem S4_P175_not : ¬P175 PiBase.S4 := by
  intro h
  exact PiBase.SpaceConstructions.finiteIndiscreteTwo_not_cardGeThree
    (P175.well_defined PiBase.S4_canonicalHomeomorph h)

register_certificate S000004 P000175 false
  proof PiBase.Formal.S4_P175_not
  provenance direct
  assumptions []

end PiBase.Formal

/- BEGIN PIBASE TRAIT DERIVATIONS -/
/- Traits for S4 (Indiscrete topology on $\{0,1\}$).
Direct obligations are handwritten outside this generated region:
  S4_P125 : P125 PiBase.S4  (Has multiple points)
  S4_P129 : P129 PiBase.S4  (Indiscrete)
  S4_P175_not : ¬ P175 PiBase.S4  (Cardinality $\geq 3$)

Generated derived declarations:
-/

namespace PiBase.Formal

theorem S4_P176_not : ¬ P176 PiBase.S4 := by
  intro h
  exact S4_P175_not (T430 PiBase.S4 inferInstance h)

register_certificate S000004 P000176 false
  proof PiBase.Formal.S4_P176_not
  provenance derived
  assumptions []

theorem S4_P185 : P185 PiBase.S4 :=
  T448 PiBase.S4 inferInstance S4_P129

register_certificate S000004 P000185 true
  proof PiBase.Formal.S4_P185
  provenance derived
  assumptions []

theorem S4_P204_not : ¬ P204 PiBase.S4 := by
  intro h
  exact S4_P175_not (T558 PiBase.S4 inferInstance h)

register_certificate S000004 P000204 false
  proof PiBase.Formal.S4_P204_not
  provenance derived
  assumptions []

theorem S4_P205_not : ¬ P205 PiBase.S4 := by
  intro h
  exact S4_P204_not (T635 PiBase.S4 inferInstance h)

register_certificate S000004 P000205 false
  proof PiBase.Formal.S4_P205_not
  provenance derived
  assumptions []

end PiBase.Formal
/- END PIBASE TRAIT DERIVATIONS -/
