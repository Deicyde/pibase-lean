module

public meta import PiBaseLean.Audit.Spaces.Registry

open Lean
open PiBase.Audit.Spaces

run_cmd do
  let space : SpaceRegistration := {
    spaceId := "TEST-CROSS-MODULE-DUPLICATE"
    catalogName := "synthetic duplicate fixture"
    «carrier» := `PiBase.Audit.Spaces.Tests.SyntheticCarrier
    canonicalHomeomorph := `PiBase.Audit.Spaces.Tests.syntheticCanonical
    assumptionIds := #[]
  }
  let certificate : CertificateRegistration := {
    spaceId := "TEST-CROSS-MODULE-DUPLICATE"
    propertyId := "P000001"
    property := `PiBase.Formal.P1
    «proof» := `PiBase.Audit.Spaces.Tests.syntheticProof
    polarity := true
    «provenance» := .derived
    assumptionIds := #[]
  }
  let env ← getEnv
  let env := spaceRegistryExt.addEntry env space
  setEnv <| certificateRegistryExt.addEntry env certificate
