# Author: Fangzhu Shen
"""Pure public CLI construction; no native executable or verifier is started."""
import contextlib
import io
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from agent_houdini.launcher import (
    CampaignOptions, build_verifier_command, native_options, parse_campaign_arguments,
)


class LauncherCommandTests(unittest.TestCase):
    def test_pass_through_choices_are_c_owned_without_probe_or_default_model(self):
        with patch("subprocess.Popen", side_effect=AssertionError("unexpected process")), \
             patch.object(Path, "mkdir", side_effect=AssertionError("unexpected output")):
            minimal = native_options(model="model-a")
            self.assertEqual(json.loads(minimal.selection_json), {
                "provider": "codex", "model": "model-a",
                "reasoning_effort": None, "executable": None})
            self.assertEqual(minimal.isolation, "local")
            explicit = native_options("claude", model="model-b", reasoning_effort="max",
                                      executable="/uninstalled/claude", scratch_parent=Path("scratch"))
            self.assertEqual(json.loads(explicit.selection_json), {
                "provider": "claude", "model": "model-b",
                "reasoning_effort": "max", "executable": "/uninstalled/claude"})
            self.assertEqual(explicit.scratch_parent, Path("scratch").resolve())
            with self.assertRaisesRegex(ValueError, "--model is required"):
                native_options("claude")

    def test_delimiter_preserves_opaque_future_verifier_options(self):
        options = parse_campaign_arguments([
            "--verifier", "/public/whiel-symbolic", "--model", "model-a", "--",
            "--input", "1,2", "--future-verifier-choice", "uninterpreted value", "--help"])
        self.assertEqual(options.verifier_arguments, (
            "--input", "1,2", "--future-verifier-choice", "uninterpreted value", "--help"))
        self.assertEqual(json.loads(options.native.selection_json)["model"], "model-a")

    def test_endpoint_argv_has_no_shell_splitting_and_is_not_a_launcher(self):
        options = CampaignOptions(Path("/public/whiel-symbolic"), ("--input", "1"), native_options(model="model-a"))
        endpoint = ("/python", "/C/__main__.py", "endpoint", "--help", "", "a b;$(false)")
        command = build_verifier_command(options, endpoint)
        self.assertEqual(command, (
            "/public/whiel-symbolic", "campaign", "run", "--input", "1",
            "--proposer-executable", "/python", "--proposer-arg", "/C/__main__.py",
            "--proposer-arg", "endpoint", "--proposer-arg", "--help",
            "--proposer-arg", "", "--proposer-arg", "a b;$(false)"))

    def test_no_proposer_skips_selection_and_requires_no_endpoint(self):
        with patch("agent_houdini.launcher.validate_selection", side_effect=AssertionError("selection")):
            options = parse_campaign_arguments([
                "--verifier", "/public/whiel-symbolic", "--no-proposer", "--", "--input", "1"])
        self.assertIsNone(options.native)
        self.assertEqual(build_verifier_command(options, ()), (
            "/public/whiel-symbolic", "campaign", "run", "--input", "1", "--no-proposer"))
        with self.assertRaises(ValueError):
            build_verifier_command(options, ("/unexpected/endpoint",))
        self.assertIsNone(native_options("none"))

    def test_help_and_invalid_configuration_finish_before_external_work(self):
        with patch("subprocess.Popen", side_effect=AssertionError("process")), \
             patch.object(Path, "mkdir", side_effect=AssertionError("output")):
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit) as help_exit:
                parse_campaign_arguments(["--help"])
            self.assertEqual(help_exit.exception.code, 0)
            for args in ([], ["--model", ""], ["--no-proposer", "--model", "model-a"],
                         ["--provider", "claude", "--model", "model-a", "--isolation", "container"],
                         ["--model", "model-a", "--reasoning-effort", ""],
                         ["--model", "model-a", "--provider-cli", ""]):
                with self.subTest(args=args), contextlib.redirect_stderr(io.StringIO()), \
                     self.assertRaises(SystemExit) as error:
                    parse_campaign_arguments(["--verifier", "/public/whiel-symbolic", *args])
                self.assertEqual(error.exception.code, 2)

    def test_only_conflicting_endpoint_flags_are_reserved(self):
        for flag in ("--proposer-executable", "--proposer-arg", "--no-proposer",
                     "--proposer-executable=/other", "--proposer-arg=x", "--no-proposer=true"):
            with self.subTest(flag=flag), self.assertRaisesRegex(ValueError, "conflicting"):
                build_verifier_command(CampaignOptions(Path("/public"), (flag,), native_options(model="model-a")),
                                       ("/python",))
        # Native option interpretation stays in B during migration, not a copied registry here.
        value = build_verifier_command(CampaignOptions(Path("/public"), ("--unrecognized",),
                                                       native_options(model="model-a")), ("/python",))
        self.assertIn("--unrecognized", value)

    def test_relative_endpoint_invalid_text_and_missing_argv_are_rejected(self):
        options = CampaignOptions(Path("/public"), (), native_options(model="model-a"))
        for endpoint in ((), ("relative/python",), ("/python", "\0"), ("/python", "\ud800")):
            with self.subTest(endpoint=endpoint), self.assertRaises(ValueError):
                build_verifier_command(options, endpoint)
        with self.assertRaises(ValueError):
            build_verifier_command(CampaignOptions(Path("relative"), (), None), ())


if __name__ == "__main__":
    unittest.main()
