#!/usr/bin/env python3
"""Independent finite diagnostic; universal claims are proved in Lean.

The scanner uses explicit left-to-right string matching and keeps unmatched
letters.  It neither uses the count equations to construct words nor truncates
an odd final letter.  The reference recurrence is evaluated separately.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

RULES = {
    "A289001": {"00": "0010", "01": "001", "10": "010"},
    "A289035": {"00": "0010", "01": "010", "10": "010"},
    "A289239": {"00": "0010", "01": "100", "10": "010"},
}
SOURCE_BLOBS = {
    "A289001": "6f944cdb050a6b7d5f4177e51d930a0a7b8ab567",
    "A289004": "6f5f23da2ff5a9e1c5f1a93658ff14a4f28b81ba",
    "A289035": "eb669752b0c3adaf6f2efcc02427ff5fea938a80",
    "A289037": "0ffbc6fe8245432a4da043d40052947ce7e42388",
    "A289239": "e2f4db2f1a8934180c28657ea538a6bc3c02a428",
    "A293077": "8655774d9d9d19d2fbc387e90063ce9ae811bf26",
}


def scan(word: str, rules: dict[str, str]) -> str:
    pieces = []
    i = 0
    while i < len(word):
        pair = word[i : i + 2]
        if pair in rules:
            pieces.append(rules[pair])
            i += 2
        else:
            pieces.append(word[i])
            i += 1
    return "".join(pieces)


def reference(last: int) -> list[int]:
    values = [2, 4, 7, 11, 18, 31, 52, 89, 151, 257]
    for n in range(10, last + 1):
        values.append(
            2 * values[n - 1] - values[n - 2] + 2 * values[n - 4]
            - values[n - 5] + values[n - 7] - values[n - 8] - values[n - 10]
        )
    return values[: last + 1]


def main() -> None:
    base = Path(__file__).resolve().parent
    for name, expected in SOURCE_BLOBS.items():
        data = (base / "sources" / f"{name}.seq").read_bytes()
        blob = b"blob " + str(len(data)).encode() + b"\0" + data
        assert hashlib.sha1(blob).hexdigest() == expected, name

    last = 23
    claimed = reference(last)
    observed = {}
    for name, rules in RULES.items():
        word = "00"
        counts = []
        for n in range(last + 1):
            length, ones = len(word), word.count("1")
            assert "11" not in word and word.endswith("0"), (name, n)
            assert 2 * ones <= length, (name, n)
            counts.append((length, ones))
            if n < last:
                new_word = scan(word, rules)
                assert new_word.count("1") == length // 2, (name, n)
                assert len(new_word) == 2 * length - ones - length % 2, (name, n)
                word = new_word
        failures = [n for n, (length, _) in enumerate(counts) if length != claimed[n]]
        assert failures[0] == 22, (name, failures)
        assert counts[22][0] == 268184 and claimed[22] == 268182
        for n in range(last - 1):
            assert counts[n + 2][0] + counts[n][0] // 2 + counts[n + 1][0] % 2 == 2 * counts[n + 1][0]
        observed[name] = counts

    assert observed["A289001"] == observed["A289035"] == observed["A289239"]
    summary = {
        "source_blobs_checked": len(SOURCE_BLOBS),
        "direct_scanner_variants": len(RULES),
        "iterations_checked": [0, last],
        "first_failure": 22,
        "actual_at_22": 268184,
        "claimed_at_22": 268182,
        "all_counts_equal": True,
        "tail": [
            {"n": n, "actual": observed["A289001"][n][0], "claimed": claimed[n]}
            for n in range(19, last + 1)
        ],
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
