module

public import PiBaseLean.Audit.Spaces.Registry
public import PiBaseLean.Properties.P52.Defs

open Lean

open PiBase.Audit.Spaces

namespace PiBase.Audit.Spaces.Tests

def RegistrySmokeCarrier := Bool

instance : TopologicalSpace RegistrySmokeCarrier := ⊥

instance : DiscreteTopology RegistrySmokeCarrier := ⟨rfl⟩

def registrySmokeCanonical :
    RegistrySmokeCarrier ≃ₜ RegistrySmokeCarrier :=
  Homeomorph.refl RegistrySmokeCarrier

theorem registrySmokeP52 :
    DiscreteTopology RegistrySmokeCarrier :=
  inferInstance

end PiBase.Audit.Spaces.Tests

register_space S000001
  carrier PiBase.Audit.Spaces.Tests.RegistrySmokeCarrier
  canonical PiBase.Audit.Spaces.Tests.registrySmokeCanonical
  assumptions []

register_certificate S000001 P000052 true
  proof PiBase.Audit.Spaces.Tests.registrySmokeP52
  provenance direct
  assumptions []

run_cmd do
  let env ← getEnv
  let space ← match getSpaceById env "S000001" with
    | .ok entry => pure entry
    | .error message => throwError message
  unless space.carrier == ``PiBase.Audit.Spaces.Tests.RegistrySmokeCarrier &&
      space.canonicalHomeomorph == ``PiBase.Audit.Spaces.Tests.registrySmokeCanonical &&
      space.assumptionIds.isEmpty do
    throwError "unexpected S000001 space registration: {repr space}"
  let certificate ← match getCertificate env "S000001" "P000052" with
    | .ok entry => pure entry
    | .error message => throwError message
  unless certificate.property == ``PiBase.Formal.P52 &&
      certificate.proof == ``PiBase.Audit.Spaces.Tests.registrySmokeP52 &&
      certificate.polarity &&
      certificate.provenance == .direct &&
      certificate.assumptionIds.isEmpty do
    throwError "unexpected S000001/P000052 certificate registration: {repr certificate}"
