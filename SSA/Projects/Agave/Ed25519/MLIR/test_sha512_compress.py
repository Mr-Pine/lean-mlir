"""Reject incomplete provenance inventories and misidentified compiler regions."""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import extract_sha512_compress as extract
from import_sha512_compress import extract_region


class CompressionIntegrityTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.out = Path(self.temp.name)
        self.manifest_path = self.out / "sha512-compress-manifest.json"
        self.manifest = json.loads(
            (extract.HERE / "generated/sha512-compress-manifest.json").read_text())
        for entry in self.manifest["kernels"].values():
            for name in entry["files_sha256"]:
                shutil.copyfile(extract.HERE / "generated" / name, self.out / name)
        self.dispatch = "agave_sha512_compress_dispatch"

    def check_manifest(self, manifest):
        self.manifest_path.write_text(json.dumps(manifest))
        return extract.check_artifacts(self.out)

    def test_complete_inventory(self):
        self.check_manifest(self.manifest)

    def test_incomplete_or_inconsistent_inventory(self):
        def mutate(field, value):
            changed = copy.deepcopy(self.manifest)
            target = changed
            for key in field[:-1]:
                target = target[key]
            target[field[-1]] = value
            return changed

        kernel = ["kernels", self.dispatch]
        mutations = [
            (["kernels"], {}),
            (kernel + ["files_sha256"], {}),
            (kernel + ["original_global_definitions"], {}),
            (kernel + ["mlir_operations"], {}),
            (kernel + ["original_definition_sha256"], "0" * 64),
            (kernel + ["llvm_inlining_applied_after_rustc"], True),
            (["dependency_features"], ["force-soft"]),
            (["dependency_rustflags"], ["--cfg=sha2_backend=soft"]),
            (["caller_external_symbol"], "wrong_dispatcher"),
        ]
        for field, value in mutations:
            with self.subTest(field=field):
                with self.assertRaises(AssertionError):
                    self.check_manifest(mutate(field, value))
        missing_kernel = copy.deepcopy(self.manifest)
        del missing_kernel["kernels"][self.dispatch]
        with self.assertRaises(AssertionError):
            self.check_manifest(missing_kernel)

    def test_changed_global_definition(self):
        changed = copy.deepcopy(self.manifest)
        globals_ = changed["kernels"][self.dispatch]["original_global_definitions"]
        next(iter(globals_.values()))["definition"] += " "
        with self.assertRaises(AssertionError):
            self.check_manifest(changed)

    def test_containing_function_and_signature(self):
        text = (self.out / f"{self.dispatch}.mlir").read_text()
        expected = self.manifest["kernels"][self.dispatch]["target_symbol"]
        symbol, signature, body = extract_region(text, expected)
        self.assertEqual(symbol, expected)
        self.assertEqual(signature, "!llvm.func<void (ptr, ptr, i64)>")
        self.assertTrue(body.startswith("  ^bb0("))
        mutations = [
            text.replace(f'sym_name = "{expected}"', 'sym_name = "wrong"'),
            text.replace("!llvm.func<void (ptr, ptr, i64)>",
                         "!llvm.func<void (ptr, ptr, i32)>", 1),
            text.replace("%arg2: i64):", "%arg2: i32):", 1),
            text + "\n" + text,
        ]
        for i, changed in enumerate(mutations):
            with self.subTest(mutation=i):
                with self.assertRaises(AssertionError):
                    extract_region(changed, expected)


if __name__ == "__main__":
    unittest.main()
