# Author: Fangzhu Shen
"""Bounded, strict JSON for the editable Python proposer client."""

import json
import math


MAX_JSON_BYTES = 64 * 1024 * 1024


class JsonWireError(ValueError):
    """Malformed or oversized JSON, without copying the rejected payload."""


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise JsonWireError("duplicate JSON key")
        result[key] = value
    return result


def _nonfinite(_):
    raise JsonWireError("nonfinite JSON number")


def _finite_float(value):
    number = float(value)
    if not math.isfinite(number):
        raise JsonWireError("nonfinite JSON number")
    return number


def _validate(value, depth=0):
    # Match the bounded nesting accepted by serde_json. In particular, Python's
    # JSON decoder otherwise permits lone surrogate escapes and coerces keys.
    if depth > 128:
        raise JsonWireError("JSON nesting exceeds bound")
    if value is None or type(value) in (bool, int):
        return
    if type(value) is float:
        if not math.isfinite(value):
            raise JsonWireError("nonfinite JSON number")
        return
    if type(value) is str:
        try:
            value.encode("utf-8")
        except UnicodeError as error:
            raise JsonWireError("invalid JSON string") from error
        return
    if type(value) is list:
        for item in value:
            _validate(item, depth + 1)
        return
    if type(value) is dict:
        for key, item in value.items():
            if type(key) is not str:
                raise JsonWireError("JSON object key must be a string")
            _validate(key, depth + 1)
            _validate(item, depth + 1)
        return
    raise JsonWireError("unsupported JSON value")


def _limit(maximum):
    if type(maximum) is not int or maximum <= 0:
        raise JsonWireError("JSON byte limit must be positive")


def decode(data, maximum=MAX_JSON_BYTES):
    """Decode one UTF-8 value, rejecting duplicates, nonfinite numbers and tails."""
    _limit(maximum)
    if type(data) is not bytes or not data or len(data) > maximum:
        raise JsonWireError("empty, oversized or invalid JSON input")
    try:
        value = json.loads(data.decode("utf-8"), object_pairs_hook=_unique_object,
                           parse_constant=_nonfinite, parse_float=_finite_float)
        _validate(value)
        return value
    except (ValueError, UnicodeError, RecursionError) as error:
        raise JsonWireError("invalid JSON input") from error


def encode(value, *, sort_keys=False, maximum=MAX_JSON_BYTES):
    """Encode compact UTF-8; preserve typed field order unless explicitly sorted."""
    _limit(maximum)
    try:
        _validate(value)
        encoder = json.JSONEncoder(ensure_ascii=False, allow_nan=False,
                                   separators=(",", ":"), sort_keys=sort_keys)
        output = bytearray()
        for text in encoder.iterencode(value):
            chunk = text.encode("utf-8")
            if len(chunk) > maximum - len(output):
                raise JsonWireError("encoded JSON exceeds byte limit")
            output.extend(chunk)
        return bytes(output)
    except (ValueError, UnicodeError, RecursionError, TypeError) as error:
        raise JsonWireError("invalid or oversized JSON output") from error
