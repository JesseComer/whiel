# Author: Fangzhu Shen
"""Pass-through provider selection support, without probing or installing."""

import unittest

from agent_houdini.provider_config import (
    MAX_ARGUMENT_CHARACTERS, validate_configuration, validate_selection,
)


class ProviderConfigTests(unittest.TestCase):
    def test_any_model_and_effort_string_passes_through_unchanged(self):
        for provider in ("codex", "claude"):
            for model in ("model-a", "model-b", "vendor/model.2-preview", "モデル", "x" * MAX_ARGUMENT_CHARACTERS):
                with self.subTest(provider=provider, model=model):
                    self.assertEqual(validate_selection(provider, model), {
                        "provider": provider, "model": model,
                        "reasoning_effort": None, "executable": None})
            for effort in ("low", "medium", "high", "xhigh", "max", "unheard-of"):
                self.assertEqual(validate_selection(provider, "model-a", effort)["reasoning_effort"], effort)

    def test_model_is_required_and_no_default_model_exists(self):
        for provider in ("codex", "claude"):
            with self.subTest(provider=provider), self.assertRaisesRegex(ValueError, "--model is required"):
                validate_selection(provider)

    def test_rejections_cover_provider_empty_and_control_characters(self):
        with self.assertRaisesRegex(ValueError, "unsupported provider"):
            validate_selection("gemini", "model-a")
        for model in ("", "model\na", "model\0a", "model\x7f", "x" * (MAX_ARGUMENT_CHARACTERS + 1), 3):
            with self.subTest(model=model), self.assertRaises(ValueError):
                validate_selection("claude", model)
        for effort in ("", "high\nlow", 3):
            with self.subTest(effort=effort), self.assertRaises(ValueError):
                validate_selection("claude", "model-a", effort)

    def test_explicit_cli_path_is_accepted_for_either_provider_without_probing(self):
        for provider in ("codex", "claude"):
            with self.subTest(provider=provider):
                selection = validate_selection(provider, "model-a", executable="/does/not/exist")
                self.assertEqual(selection["executable"], "/does/not/exist")
        with self.assertRaises(ValueError):
            validate_selection("codex", "model-a", executable="")

    def test_helper_input_fields_are_strict(self):
        for value in [[], {}, {"provider": True}, {"provider": "codex"},
                      {"provider": "codex", "model": None},
                      {"provider": "codex", "model": 3},
                      {"provider": "claude", "model": "model-a", "executable": 3},
                      {"provider": "codex", "model": "model-a", "verified": True}]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                validate_configuration(value)
        self.assertEqual(validate_configuration({"provider": "codex", "model": "model-a",
                                                 "reasoning_effort": None, "executable": None}),
                         validate_selection("codex", "model-a"))


if __name__ == "__main__":
    unittest.main()
