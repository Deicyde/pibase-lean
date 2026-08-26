from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from build_dashboard_data import space_audit_projection
from run_space_audit import (
    AuditOutputError,
    AuditReportValidationError,
    AuditUnsuccessfulError,
    load_audit_artifact,
    parse_report,
    run_space_audit,
)

HASH_A = "a" * 64
HASH_B = "0" * 63 + "b"


def failure(code: str = "audit-failure") -> dict:
    return {"code": code, "message": "audit failed"}


def assumptions() -> dict:
    return {"expected": [], "declared": [], "used": [], "valid": True}


def axioms() -> dict:
    return {"axioms": [], "trusted": [], "conditional": [], "forbidden": []}


def presentation(status: str = "implemented", failures: list[dict] | None = None) -> dict:
    failures = [] if failures is None else failures
    implemented = status == "implemented"
    return {
        "carrier": "PiBase.S1" if implemented else None,
        "canonicalHomeomorph": "PiBase.S1_canonicalHomeomorph" if implemented else None,
        "typeValid": implemented,
        "assumptions": assumptions(),
        "axioms": axioms(),
        "failures": failures,
        "status": status,
    }


def trait(status: str = "implemented", failures: list[dict] | None = None) -> dict:
    failures = [] if failures is None else failures
    implemented = status == "implemented"
    return {
        "propertyId": "P000001",
        "name": "Compact",
        "expected": True,
        "polarity": True,
        "certificate": "PiBase.S1_P1" if implemented else None,
        "provenance": "direct" if implemented else None,
        "typeValid": implemented,
        "assumptions": assumptions(),
        "axioms": axioms(),
        "failures": failures,
        "status": status,
    }


def valid_report() -> dict:
    return {
        "schemaVersion": 1,
        "scope": ["S000001"],
        "catalogSchemaVersion": 1,
        "sourceHashes": {"pibase": HASH_A, "independence": HASH_B},
        "summary": {
            "spaces": 1,
            "implemented": 1,
            "notImplemented": 0,
            "invalid": 0,
            "traits": 1,
            "failures": 0,
        },
        "spaces": [
            {
                "spaceId": "S000001",
                "catalogName": "A space",
                "presentation": presentation(),
                "traits": [trait()],
                "failures": [],
                "status": "implemented",
            }
        ],
        "failures": [],
    }


def load_result(report: dict):
    with mock.patch("run_space_audit.subprocess.run") as run:
        run.return_value = subprocess.CompletedProcess(
            ["lake", "exe", "spaceAudit"], 0, json.dumps(report), ""
        )
        return run_space_audit(Path("/tmp/audit-root"))


class DashboardSpaceAuditProjectionTest(unittest.TestCase):
    def test_audit_owns_targeted_semantics_and_traits(self) -> None:
        report = valid_report()
        catalog = {
            "properties": [{"uid": "P000001", "name": "Compact"}],
            "spaces": [
                {"uid": "S000001", "name": "A space"},
                {"uid": "S000002", "name": "Another space"},
            ],
            "traits": [
                {"space": "S000001", "property": "P000001", "value": False},
                {"space": "S000002", "property": "P000001", "value": True},
            ],
        }

        statuses, traits = space_audit_projection(report, catalog)

        targeted = statuses["S000001"]
        self.assertTrue(targeted["declarationPresent"])
        self.assertTrue(targeted["dependencyClean"])
        self.assertEqual(targeted["status"], "dependency-clean")
        self.assertTrue(targeted["spaceAudit"]["targeted"])
        self.assertEqual(traits["S000001"]["traits"], [{
            "property": "P000001",
            "name": "Compact",
            "value": True,
            "status": "asserted",
            "via": "PiBase.S1_P1",
        }])

        untargeted = statuses["S000002"]
        self.assertFalse(untargeted["declarationPresent"])
        self.assertFalse(untargeted["dependencyClean"])
        self.assertEqual(untargeted["status"], "missing-declaration")
        self.assertEqual(
            untargeted["spaceAudit"],
            {"status": "not-targeted", "targeted": False},
        )
        self.assertEqual(traits["S000002"]["traits"][0]["status"], "asserted")

    def test_failed_target_uses_compatibility_debt_status(self) -> None:
        report = valid_report()
        report["spaces"][0]["presentation"] = presentation(
            "not-implemented", [failure("missing-homeomorph")]
        )
        report["spaces"][0]["presentation"]["carrier"] = "PiBase.S1"
        report["spaces"][0]["presentation"]["canonicalHomeomorph"] = (
            "PiBase.S1_canonicalHomeomorph"
        )
        report["spaces"][0]["status"] = "not-implemented"
        report["summary"].update({"implemented": 0, "notImplemented": 1, "failures": 1})
        catalog = {
            "properties": [{"uid": "P000001", "name": "Compact"}],
            "spaces": [{"uid": "S000001", "name": "A space"}],
            "traits": [],
        }

        statuses, _ = space_audit_projection(report, catalog)

        self.assertFalse(statuses["S000001"]["dependencyClean"])
        self.assertEqual(statuses["S000001"]["status"], "local-debt")


class SpaceAuditAdapterTest(unittest.TestCase):
    def assert_invalid(self, report: dict, message: str) -> None:
        with self.assertRaisesRegex(AuditReportValidationError, message):
            parse_report(json.dumps(report))

    def test_valid_success_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            artifact = Path(temporary) / "space-audit.json"
            artifact.write_text(json.dumps(valid_report()), encoding="utf-8")

            result = load_audit_artifact(artifact)

        self.assertIsNone(result.process_succeeded)
        self.assertTrue(result.report_succeeded)
        self.assertTrue(result.succeeded)
        self.assertIs(result.require_success(), result)

    @mock.patch("run_space_audit.subprocess.run")
    def test_subprocess_success(self, run: mock.Mock) -> None:
        root = Path("/tmp/configurable-audit-root")
        run.return_value = subprocess.CompletedProcess(
            ["lake", "exe", "spaceAudit"], 0, json.dumps(valid_report()), ""
        )

        result = run_space_audit(root)

        self.assertTrue(result.process_succeeded)
        self.assertTrue(result.report_succeeded)
        run.assert_called_once_with(
            ["lake", "exe", "spaceAudit"],
            cwd=root.resolve(),
            capture_output=True,
            text=True,
            check=False,
        )

    @mock.patch("run_space_audit.subprocess.run")
    def test_nonzero_json_is_parsed_then_require_success_rejects_it(
        self, run: mock.Mock
    ) -> None:
        report = valid_report()
        item_failure = failure("missing-certificate")
        report["spaces"][0]["traits"][0] = trait("not-implemented", [item_failure])
        report["spaces"][0]["status"] = "not-implemented"
        report["summary"].update(
            {"implemented": 0, "notImplemented": 1, "failures": 1}
        )
        run.return_value = subprocess.CompletedProcess(
            ["lake", "exe", "spaceAudit"], 1, json.dumps(report), "diagnostic"
        )

        result = run_space_audit(Path("/tmp/audit-root"))

        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.report["spaces"][0]["status"], "not-implemented")
        self.assertFalse(result.process_succeeded)
        self.assertFalse(result.report_succeeded)
        with self.assertRaises(AuditUnsuccessfulError) as raised:
            result.require_success()
        self.assertIs(raised.exception.result, result)

    @mock.patch("run_space_audit.subprocess.run")
    def test_nonzero_process_cannot_be_accepted_with_successful_report(
        self, run: mock.Mock
    ) -> None:
        run.return_value = subprocess.CompletedProcess(
            ["lake", "exe", "spaceAudit"], 7, json.dumps(valid_report()), "failed"
        )

        result = run_space_audit(Path("/tmp/audit-root"))

        self.assertTrue(result.report_succeeded)
        self.assertFalse(result.succeeded)
        with self.assertRaises(AuditUnsuccessfulError):
            result.require_success()

    def test_malformed_json(self) -> None:
        with self.assertRaises(AuditOutputError):
            parse_report("not json")

    def test_schema_mismatch(self) -> None:
        report = valid_report()
        report["schemaVersion"] = 2
        self.assert_invalid(report, r"schemaVersion")

    def test_duplicate_space_ids(self) -> None:
        report = valid_report()
        duplicate = copy.deepcopy(report["spaces"][0])
        report["spaces"].append(duplicate)
        report["scope"].append("S000002")
        report["summary"].update({"spaces": 2, "implemented": 2, "traits": 2})
        self.assert_invalid(report, r"spaceId values must be unique")

    def test_duplicate_scope(self) -> None:
        report = valid_report()
        report["scope"].append("S000001")
        self.assert_invalid(report, r"strings must be unique")

    def test_bad_hashes(self) -> None:
        for bad_hash in ("", "A" * 64, "a" * 63, "g" * 64):
            with self.subTest(hash=bad_hash):
                report = valid_report()
                report["sourceHashes"]["pibase"] = bad_hash
                self.assert_invalid(report, r"64-character lowercase hexadecimal")

        report = valid_report()
        report["sourceHashes"]["extra"] = HASH_A
        self.assert_invalid(report, r"expected exactly")

    def test_inconsistent_summary(self) -> None:
        report = valid_report()
        report["summary"]["implemented"] = 0
        self.assert_invalid(report, r"summary\.implemented")

    def test_summary_cannot_hide_nested_failures(self) -> None:
        report = valid_report()
        report["spaces"][0]["traits"][0] = trait(
            "not-implemented", [failure()]
        )
        report["spaces"][0]["status"] = "not-implemented"
        report["summary"].update({"implemented": 0, "notImplemented": 1})
        self.assert_invalid(report, r"summary\.failures")

    def test_report_failure_rejects_zero_exit_result(self) -> None:
        report = valid_report()
        report_failure = failure("registry-failure")
        report["failures"] = [report_failure]
        report["summary"]["failures"] = 1
        result = load_result(report)

        self.assertTrue(result.process_succeeded)
        self.assertFalse(result.report_succeeded)
        with self.assertRaises(AuditUnsuccessfulError) as raised:
            result.require_success()
        self.assertIs(raised.exception.result, result)

    def test_assumption_validity_must_match_arrays(self) -> None:
        report = valid_report()
        report["spaces"][0]["presentation"]["assumptions"]["expected"] = [
            "continuum-hypothesis"
        ]
        self.assert_invalid(report, r"assumptions\.valid")

    def test_axiom_cannot_be_omitted_from_classification(self) -> None:
        report = valid_report()
        report["spaces"][0]["presentation"]["axioms"] = {
            "axioms": ["Classical.choice"],
            "trusted": [],
            "conditional": [],
            "forbidden": [],
        }
        self.assert_invalid(report, r"axioms\.trusted.*exactly classify")

    def test_axiom_cannot_appear_in_multiple_classifications(self) -> None:
        report = valid_report()
        report["spaces"][0]["traits"][0]["axioms"] = {
            "axioms": ["Classical.choice"],
            "trusted": ["Classical.choice"],
            "conditional": ["Classical.choice"],
            "forbidden": [],
        }
        self.assert_invalid(report, r"axioms\.conditional.*exactly classify")

    def test_unknown_axiom_cannot_be_reclassified_as_trusted(self) -> None:
        report = valid_report()
        report["spaces"][0]["presentation"]["axioms"] = {
            "axioms": ["Unsafe.axiom"],
            "trusted": ["Unsafe.axiom"],
            "conditional": [],
            "forbidden": [],
        }
        self.assert_invalid(report, r"axioms\.trusted.*exactly classify")

    def test_conditional_assumptions_must_be_induced_by_axioms(self) -> None:
        report = valid_report()
        report["spaces"][0]["traits"][0]["assumptions"] = {
            "expected": ["continuum-hypothesis"],
            "declared": ["continuum-hypothesis"],
            "used": ["continuum-hypothesis"],
            "valid": True,
        }
        self.assert_invalid(report, r"assumptions\.used.*conditional axioms")

    def test_invalid_status(self) -> None:
        report = valid_report()
        report["spaces"][0]["status"] = "failed"
        self.assert_invalid(report, r"unsupported status")

    @mock.patch("run_space_audit.Path.read_text", autospec=True)
    @mock.patch("run_space_audit.subprocess.run")
    def test_subprocess_path_never_reads_lean_files(
        self, run: mock.Mock, read_text: mock.Mock
    ) -> None:
        run.return_value = subprocess.CompletedProcess(
            ["lake", "exe", "spaceAudit"], 0, json.dumps(valid_report()), ""
        )

        result = run_space_audit(Path("/tmp/audit-root"))

        self.assertTrue(result.succeeded)
        read_text.assert_not_called()

    def test_artifact_path_reads_only_explicit_json(self) -> None:
        report = valid_report()
        with tempfile.TemporaryDirectory() as temporary:
            artifact = Path(temporary) / "report.json"
            artifact.write_text(json.dumps(report), encoding="utf-8")
            original = Path.read_text
            reads: list[Path] = []

            def guarded_read_text(path: Path, *args, **kwargs) -> str:
                reads.append(path)
                if path.suffix == ".lean":
                    raise AssertionError("adapter attempted to read a Lean source file")
                return original(path, *args, **kwargs)

            with mock.patch.object(Path, "read_text", autospec=True, side_effect=guarded_read_text):
                result = load_audit_artifact(artifact)

        self.assertTrue(result.succeeded)
        self.assertEqual(reads, [artifact])


if __name__ == "__main__":
    unittest.main()
