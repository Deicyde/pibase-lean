module

public meta import PiBaseLean.Audit.Spaces.Audit
public meta import PiBaseLean.Audit.Spaces.Tests.DuplicateDiamondLeft
public meta import PiBaseLean.Audit.Spaces.Tests.DuplicateDiamondRight
public meta import PiBaseLean.Audit.Spaces.Tests.DuplicateIndependent

@[expose] public meta section

open Lean
open PiBase.Audit.Spaces

def duplicateSpaceId := "TEST-CROSS-MODULE-DUPLICATE"

run_cmd do
  let env ← getEnv
  let spaces := (getSpaceRegistrations env).filter (·.spaceId == duplicateSpaceId)
  unless spaces.size == 2 do
    throwError
      "expected one diamond-imported and one independent space registration; found {spaces.size}"
  let certificates := (getCertificateRegistrations env).filter fun entry =>
    entry.spaceId == duplicateSpaceId && entry.propertyId == "P000001"
  unless certificates.size == 2 do
    throwError
      "expected one diamond-imported and one independent certificate registration; found \
        {certificates.size}"
  let report ← Lean.Elab.Command.liftTermElabM buildAuditReport
  unless report.failures.any (·.code == "duplicate-space-registration") do
    throwError "audit did not report the cross-module space duplicate"
  unless report.failures.any (·.code == "duplicate-certificate-registration") do
    throwError "audit did not report the cross-module certificate duplicate"
  unless report.failures.any (·.code == "duplicate-proof-registration") do
    throwError "audit did not report the cross-module proof duplicate"
  unless report.failures.any (·.code == "duplicate-space-carrier") do
    throwError "audit did not report a carrier shared by distinct space IDs"
  unless report.failures.any (·.code == "duplicate-canonical-homeomorph") do
    throwError "audit did not report a canonical homeomorphism shared by distinct space IDs"
