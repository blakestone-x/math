"""Emit the standalone files for Left to Solve's statement and proof checkers."""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def export(sequence, output):
    target = ROOT / f"{sequence}.lean"
    if not (len(sequence) == 7 and sequence.startswith("A") and sequence[1:].isdigit() and target.is_file()):
        raise ValueError(f"Unknown sequence {sequence!r}")
    source = target.read_text()
    namespace = f"OMA.S_oeis_a{sequence[1:]}"
    board = (ROOT / "Boards.lean").read_text().split("namespace MonotoneGrids\n", 1)[1].split("end MonotoneGrids", 1)[0]
    header = source.split("/-!", 1)[1].split("-/", 1)[0]
    sequence_def = source.split("open MonotoneGrids\n", 1)[1].split("private def rowTypes", 1)[0].strip()
    theorem = source.split("theorem main :", 1)[1].split(" := by", 1)[0]
    statement = (f"import Mathlib.RingTheory.PowerSeries.Basic\n\n/-!{header}\n"
                 f"R. H. Hardin defined the sequence. Colin Barker conjectured these formulas in 2018.\n"
                 f"Formalization: @blakestone-x.\n-/\n\nnamespace {namespace}\n"
                 f"{board}\n{sequence_def}\n\ntheorem main :{theorem} := by\n  sorry\n\nend {namespace}\n")
    core = (ROOT / "Certificate.lean").read_text().split("namespace MonotoneGrids\n", 1)[1].split("end MonotoneGrids", 1)[0]
    body = source.split("private def rowTypes", 1)[1].split(f"end {namespace}", 1)[0].replace("theorem main :", "theorem barker :")
    proof = (f"import OMAStatements.S_oeis_a{sequence[1:]}\n"
             "import Mathlib.Tactic.Ring\nimport Mathlib.Tactic.LinearCombination\n\n"
             f"namespace {namespace}\n{core}\nprivate def rowTypes{body}end {namespace}\n\n"
             f"theorem OMA.solution : type_of% @{namespace}.main := {namespace}.barker\n")
    for directory, content in [("statements", statement), ("proofs", proof)]:
        dest = output / directory / f"oeis-a{sequence[1:]}.lean"
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(content)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sequence", help="OEIS identifier, e.g. A207449")
    parser.add_argument("output", type=Path, help="directory for statements/ and proofs/")
    args = parser.parse_args()
    export(args.sequence, args.output)
