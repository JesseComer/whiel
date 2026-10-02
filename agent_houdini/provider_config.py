# Author: Fangzhu Shen
"""Pure C-owned native-provider selection; the Python runtime resolves the CLI.

Model and reasoning-effort strings are passed through to the provider CLI
verbatim. C keeps no model table and no default model: the caller names the
model, and the provider decides whether it accepts it.
"""


MAX_CONFIGURATION_BYTES = 16 * 1024
MAX_ARGUMENT_CHARACTERS = 256
MAX_PATH_CHARACTERS = 4096


def validate_argument(name, value, maximum=MAX_ARGUMENT_CHARACTERS) -> str:
    """Accept any nonempty printable one-line string; enumerate nothing."""
    if not isinstance(value, str):
        raise ValueError(name + " must be a string")
    if not value or len(value) > maximum:
        raise ValueError(name + " must be nonempty and at most " + str(maximum) + " characters")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise ValueError(name + " must not contain control characters")
    return value


def validate_selection(provider, model=None, reasoning_effort=None, executable=None) -> dict:
    if provider not in ("codex", "claude"):
        raise ValueError("unsupported provider; expected codex or claude")
    if model is None:
        raise ValueError("--model is required; C has no default model")
    validate_argument("model", model)
    if reasoning_effort is not None:
        validate_argument("reasoning_effort", reasoning_effort)
    if executable is not None:
        validate_argument("executable", executable, MAX_PATH_CHARACTERS)
    return {"provider": provider, "model": model, "reasoning_effort": reasoning_effort,
            "executable": executable}


def validate_configuration(value) -> dict:
    if (not isinstance(value, dict) or "provider" not in value
            or set(value) - {"provider", "model", "reasoning_effort", "executable"}):
        raise ValueError("invalid provider selection fields")
    for name in ("provider", "model", "reasoning_effort"):
        if name in value and value[name] is not None and not isinstance(value[name], str):
            raise ValueError(name + " must be a string")
    return validate_selection(**value)
