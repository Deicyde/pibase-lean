module

public import PiBaseLean.Audit.Spaces.Registry
public import PiBaseLean.Properties.P52.Bundled

@[expose] public section

open Lean

open PiBase.Audit.Spaces

namespace PiBase.Audit.Spaces.Tests

/- These ordinary declarations ensure the registry's field labels and assumption names remain
usable as identifiers outside the two registration commands. -/
def carrier : Nat := 0
def canonical : Nat := 0
def assumptions : Nat := 0
def proof : Nat := 0
def provenance : Nat := 0
def continuumHypothesis : Nat := 0
def notContinuumHypothesis : Nat := 0
def martinsAxiom : Nat := 0
def generalizedContinuumHypothesis : Nat := 0

def RegistrySmokeCarrier := Bool

instance registrySmokeTopology : TopologicalSpace RegistrySmokeCarrier := ⊥

instance registrySmokeDiscrete : DiscreteTopology RegistrySmokeCarrier := ⟨rfl⟩

def registrySmokeCanonical :
    RegistrySmokeCarrier ≃ₜ RegistrySmokeCarrier :=
  Homeomorph.refl RegistrySmokeCarrier

theorem registrySmokeP52 :
    DiscreteTopology RegistrySmokeCarrier :=
  inferInstance

inductive TopologyCarrier where
  | first
  | second

instance topologyCarrierTopology : TopologicalSpace TopologyCarrier := ⊥

@[instance_reducible]
def alternateTopology : TopologicalSpace TopologyCarrier := ⊤

def mismatchedCanonical :
    @Homeomorph TopologyCarrier TopologyCarrier alternateTopology alternateTopology :=
  @Homeomorph.refl TopologyCarrier alternateTopology

end PiBase.Audit.Spaces.Tests

register_space S000001
  carrier PiBase.Audit.Spaces.Tests.RegistrySmokeCarrier
  canonical PiBase.Audit.Spaces.Tests.registrySmokeCanonical
  assumptions []

namespace PiBase.Audit.Spaces.Tests

/- This later, higher-priority instance must not change which topology certificate validation uses.
The canonical homeomorphism remains the source of truth for the registered presentation. -/
instance (priority := 2000) registrySmokeLaterTopology :
    TopologicalSpace RegistrySmokeCarrier := ⊤

end PiBase.Audit.Spaces.Tests

register_certificate S000001 P000052 true
  proof PiBase.Audit.Spaces.Tests.registrySmokeP52
  provenance direct
  assumptions []

run_cmd do
  let rejected ← try
    Lean.Elab.Command.liftTermElabM <|
      validateSpaceDecls
        ``PiBase.Audit.Spaces.Tests.TopologyCarrier
        ``PiBase.Audit.Spaces.Tests.mismatchedCanonical
    pure false
  catch _ =>
    pure true
  unless rejected do
    throwError "accepted a canonical homeomorphism with the wrong source topology"
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
