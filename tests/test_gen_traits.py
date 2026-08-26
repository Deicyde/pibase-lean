import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "gen_traits.py"
SPEC = importlib.util.spec_from_file_location("gen_traits", SCRIPT)
assert SPEC and SPEC.loader
GEN_TRAITS = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN_TRAITS
SPEC.loader.exec_module(GEN_TRAITS)


def atom(prop, value=True):
    return {"kind": "atom", "property": prop, "value": value}


def implication(uid, antecedents, conclusion):
    when = antecedents[0] if len(antecedents) == 1 else {
        "kind": "and",
        "subs": antecedents,
    }
    return {"uid": uid, "when": when, "then": conclusion}


class CloseTests(unittest.TestCase):
    def test_generates_positive_forward_and_constructive_contrapositive(self):
        theorem = implication(
            "T000007",
            [atom("P000001"), atom("P000002")],
            atom("P000003"),
        )

        known, derivations, _ = GEN_TRAITS.close(
            {"P000001": True, "P000002": True},
            [theorem],
            {"P000001", "P000002", "P000003"},
        )
        self.assertIs(known["P000003"], True)
        self.assertEqual(derivations["P000003"][0], "implication")

        known, derivations, _ = GEN_TRAITS.close(
            {"P000002": True, "P000003": False},
            [theorem],
            {"P000001", "P000002", "P000003"},
        )
        self.assertIs(known["P000001"], False)
        self.assertEqual(derivations["P000001"][0], "contrapositive")

    def test_rejects_negative_antecedent_and_negative_conclusion(self):
        negative_antecedent = implication(
            "T000008", [atom("P000001", False)], atom("P000002")
        )
        negative_conclusion = implication(
            "T000009", [atom("P000001")], atom("P000002", False)
        )

        known, derivations, _ = GEN_TRAITS.close(
            {"P000002": False},
            [negative_antecedent, negative_conclusion],
            {"P000001", "P000002"},
        )

        self.assertNotIn("P000001", known)
        self.assertEqual(derivations, {"P000002": ("direct", None, ())})

    def test_does_not_overwrite_conflicting_direct_data(self):
        theorem = implication(
            "T000010", [atom("P000001")], atom("P000002")
        )
        known, derivations, _ = GEN_TRAITS.close(
            {"P000001": True, "P000002": False},
            [theorem],
            {"P000001", "P000002"},
        )
        self.assertIs(known["P000002"], False)
        self.assertEqual(derivations["P000002"][0], "direct")


class AvailabilityTests(unittest.TestCase):
    def test_requires_expected_declaration_not_only_numbered_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            theorem_root = Path(directory) / "PiBaseLean" / "Theorems"
            declared = theorem_root / "T1" / "Theorem.lean"
            declared.parent.mkdir(parents=True)
            declared.write_text("theorem T1 : True := trivial\n", encoding="utf-8")
            missing = theorem_root / "T500" / "Theorem.lean"
            missing.parent.mkdir(parents=True)
            missing.write_text("theorem differentlyNamed : True := trivial\n", encoding="utf-8")

            self.assertEqual(GEN_TRAITS.available("T", directory), {"T000001"})


class RenderingTests(unittest.TestCase):
    def setUp(self):
        self.theorem = implication(
            "T000007",
            [atom("P000001"), atom("P000002")],
            atom("P000003"),
        )
        self.names = {
            "P000001": "first",
            "P000002": "second",
            "P000003": "third",
        }

    def render(self, seed, independence=None):
        return GEN_TRAITS.render_generated_region(
            "S000147",
            seed,
            [self.theorem],
            {"P000001", "P000002", "P000003"},
            self.names,
            {"S000147": "Conditional space"},
            independence or {},
        )

    def test_uses_stable_namespace_carrier_and_separates_direct_obligations(self):
        output = self.render({"P000001": True, "P000002": True})

        self.assertIn("S147_P1 : P1 PiBase.S147", output)
        self.assertIn("S147_P2 : P2 PiBase.S147", output)
        self.assertIn("namespace PiBase.Formal", output)
        self.assertIn("theorem S147_P3 : P3 PiBase.S147 :=", output)
        self.assertIn("end PiBase.Formal", output)
        self.assertIn(
            "T7 PiBase.S147 inferInstance ⟨S147_P1, S147_P2⟩", output
        )
        certificate = (
            "register_certificate S000147 P000003 true\n"
            "  proof PiBase.Formal.S147_P3\n"
            "  provenance derived\n"
            "  assumptions []"
        )
        self.assertIn(certificate, output)
        self.assertLess(output.index("theorem S147_P3"), output.index(certificate))
        self.assertLess(output.index(certificate), output.index("end PiBase.Formal"))
        self.assertNotIn("theorem S147_P1", output)
        self.assertEqual(output.count(GEN_TRAITS.GENERATED_BEGIN), 1)
        self.assertEqual(output.count(GEN_TRAITS.GENERATED_END), 1)
        imports = GEN_TRAITS.render_generated_imports(
            {"P000001": True, "P000002": True},
            [self.theorem],
            {"P000001", "P000002", "P000003"},
        )
        self.assertIn(
            "public meta import PiBaseLean.Audit.Spaces.Registry", imports
        )
        self.assertIn("public import PiBaseLean.Properties.P3.Defs", imports)
        self.assertIn("public import PiBaseLean.Theorems.T7.Theorem", imports)

    def test_renders_sound_contrapositive(self):
        output = self.render({"P000002": True, "P000003": False})

        self.assertIn("theorem S147_P1_not : ¬ P1 PiBase.S147 := by", output)
        self.assertIn("intro h", output)
        proof = (
            "theorem S147_P1_not : ¬ P1 PiBase.S147 := by\n"
            "  intro h\n"
            "  exact S147_P3_not (T7 PiBase.S147 inferInstance ⟨h, S147_P2⟩)"
        )
        certificate = (
            "register_certificate S000147 P000001 false\n"
            "  proof PiBase.Formal.S147_P1_not\n"
            "  provenance derived\n"
            "  assumptions []"
        )
        self.assertIn(f"{proof}\n\n{certificate}", output)

    def test_adds_conditional_binders_to_obligations_and_references(self):
        independence = {
            "conditionalSpaces": [
                {"space": "S000147", "assumptions": ["CH", "not CH", "MA"]},
                {"space": "S000147", "assumptions": ["CH", "GCH"]},
            ]
        }
        output = self.render(
            {"P000001": True, "P000002": True}, independence
        )

        self.assertIn(
            "S147_P1 [PiBase.ContinuumHypothesis] [PiBase.NotContinuumHypothesis] "
            "[PiBase.MartinsAxiom] [PiBase.GeneralizedContinuumHypothesis] : "
            "P1 PiBase.S147",
            output,
        )
        self.assertIn(
            "theorem S147_P3 [PiBase.ContinuumHypothesis] "
            "[PiBase.NotContinuumHypothesis] [PiBase.MartinsAxiom] "
            "[PiBase.GeneralizedContinuumHypothesis] : P3 PiBase.S147 :=",
            output,
        )
        self.assertIn("⟨S147_P1, S147_P2⟩", output)
        self.assertIn(
            "assumptions [continuumHypothesis, notContinuumHypothesis, "
            "martinsAxiom, generalizedContinuumHypothesis]",
            output,
        )
        self.assertEqual(output.count("continuumHypothesis"), 1)

    def test_never_emits_proof_placeholders(self):
        output = self.render({"P000001": True, "P000002": True})
        lowered = output.lower()
        for forbidden in ("sorry", "admit", "axiom", "placeholder"):
            self.assertNotIn(forbidden, lowered)


class RegionTests(unittest.TestCase):
    def test_replacement_preserves_handwritten_content_and_is_idempotent(self):
        old_region = (
            f"{GEN_TRAITS.GENERATED_BEGIN}\nold\n"
            f"{GEN_TRAITS.GENERATED_END}"
        )
        new_region = (
            f"{GEN_TRAITS.GENERATED_BEGIN}\nnew\n"
            f"{GEN_TRAITS.GENERATED_END}"
        )
        source = f"namespace Handwritten\n\n{old_region}\n\nend Handwritten\n"

        updated = GEN_TRAITS.replace_generated_region(source, new_region)
        self.assertIn("namespace Handwritten", updated)
        self.assertIn("end Handwritten", updated)
        self.assertNotIn("old", updated)
        self.assertEqual(
            GEN_TRAITS.replace_generated_region(updated, new_region), updated
        )

    def test_rejects_malformed_delimiters(self):
        with self.assertRaisesRegex(ValueError, "complete generated trait region"):
            GEN_TRAITS.replace_generated_region(
                f"handwritten\n{GEN_TRAITS.GENERATED_BEGIN}\n", "region"
            )


class CliTests(unittest.TestCase):
    def make_fixture(self, directory):
        root = Path(directory)
        catalog = {
            "properties": [
                {"uid": "P000001", "name": "first"},
                {"uid": "P000002", "name": "second"},
            ],
            "spaces": [{"uid": "S000003", "name": "fixture"}],
            "traits": [
                {"space": "S000003", "property": "P000001", "value": True}
            ],
            "theorems": [
                implication("T000001", [atom("P000001")], atom("P000002"))
            ],
        }
        catalog_path = root / "catalog.json"
        catalog_path.write_text(json.dumps(catalog), encoding="utf-8")
        independence_path = root / "independence.json"
        independence_path.write_text("{}", encoding="utf-8")
        declarations = {
            "Properties/P1/Defs.lean": "def P1\n",
            "Properties/P2/Defs.lean": "def P2\n",
            "Theorems/T1/Theorem.lean": "theorem T1 : P1 ≤ P2 := by sorry\n",
        }
        for relative_path, content in declarations.items():
            source = root / "lean" / "PiBaseLean" / relative_path
            source.parent.mkdir(parents=True)
            source.write_text(content, encoding="utf-8")
        lemmas = root / "spaces" / "S3" / "Lemmas.lean"
        lemmas.parent.mkdir(parents=True)
        lemmas.write_text(
            "module\n\npublic import PiBaseLean.Spaces.S3.Defs\n\n"
            "@[expose] public section\n\nnamespace PiBase.Formal\n\nend PiBase.Formal\n",
            encoding="utf-8",
        )
        return catalog_path, independence_path, root / "lean", root / "spaces", lemmas

    def run_cli(self, *args):
        return subprocess.run(
            [sys.executable, str(SCRIPT), *map(str, args)],
            text=True,
            capture_output=True,
            check=False,
        )

    def test_write_is_idempotent_and_check_detects_stale_region(self):
        with tempfile.TemporaryDirectory() as directory:
            catalog, independence, lean_root, lemmas_root, lemmas = self.make_fixture(directory)
            common = (
                "--catalog", catalog,
                "--independence", independence,
                "--lean-root", lean_root,
                "--lemmas-root", lemmas_root,
            )

            first = self.run_cli("--write", *common, "S3")
            self.assertEqual(first.returncode, 0, first.stderr)
            first_content = lemmas.read_text(encoding="utf-8")
            self.assertIn("namespace PiBase.Formal", first_content)
            self.assertIn("theorem S3_P2", first_content)
            self.assertIn(
                "register_certificate S000003 P000002 true\n"
                "  proof PiBase.Formal.S3_P2\n"
                "  provenance derived\n"
                "  assumptions []",
                first_content,
            )

            second = self.run_cli("--write", *common, "S3")
            self.assertEqual(second.returncode, 0, second.stderr)
            self.assertIn("unchanged:", second.stdout)
            self.assertEqual(lemmas.read_text(encoding="utf-8"), first_content)

            current = self.run_cli("--check", *common, "S3")
            self.assertEqual(current.returncode, 0, current.stderr)
            self.assertIn("current:", current.stdout)

            lemmas.write_text(first_content.replace("theorem S3_P2", "theorem stale"), encoding="utf-8")
            stale = self.run_cli("--check", *common, "S3")
            self.assertEqual(stale.returncode, 1)
            self.assertIn("stale:", stale.stdout)
            self.assertIn("theorem stale", lemmas.read_text(encoding="utf-8"))

    def test_write_refuses_to_create_missing_numbered_lemmas_file(self):
        with tempfile.TemporaryDirectory() as directory:
            catalog, independence, lean_root, lemmas_root, lemmas = self.make_fixture(directory)
            lemmas.unlink()
            result = self.run_cli(
                "--write",
                "--catalog", catalog,
                "--independence", independence,
                "--lean-root", lean_root,
                "--lemmas-root", lemmas_root,
                "S3",
            )
            self.assertEqual(result.returncode, 1)
            self.assertIn("does not exist", result.stderr)
            self.assertFalse(lemmas.exists())


if __name__ == "__main__":
    unittest.main()
