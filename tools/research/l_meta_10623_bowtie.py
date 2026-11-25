"""Reproduce or check the seven-slot bowtie decoder certificate.

Run with the pinned Lean toolchain's cadical on PATH. With --proof FILE the
independent checker verifies a previously generated text LRAT certificate.
The CNF covers five inputs, all 32 rows, two backward operands per binary
gate, unary NOT with duplicated operand, and at most one NOT. The final
wire is the output. This certificate pertains to the bowtie decoder.
"""
import argparse
import hashlib
import subprocess
import tempfile
from itertools import combinations
from pathlib import Path

CNF_SHA256 = "14be3e73bcbfbab76e9f2ed0c984da7b8fb57d5d88043318b6924272dea1975e"
EDGE_MASKS = (3, 5, 6, 9, 17, 24)


def generate_cnf(path):
    clauses = []
    variable_count = 0

    def variable():
        nonlocal variable_count
        variable_count += 1
        return variable_count

    def select_one(count):
        selectors = [variable() for _ in range(count)]
        clauses.append(selectors)
        clauses.extend([-a, -b] for a, b in combinations(selectors, 2))
        return selectors

    wires = [[variable() for _ in range(32)] for _ in range(12)]
    for wire in range(5):
        for row, literal in enumerate(wires[wire]):
            clauses.append([literal if row & (1 << wire) else -literal])

    inverters = []
    for output in range(5, 12):
        conj, disj, invert = select_one(3)
        inverters.append(invert)
        left, right = select_one(output), select_one(output)
        for first in range(output):
            for second in range(first):
                clauses.append([invert, -left[first], -right[second]])
            clauses.append([-invert, -left[first], right[first]])

        operands = [[variable() for _ in range(32)] for _ in range(2)]
        for selectors, values in zip((left, right), operands):
            for source, select in enumerate(selectors):
                for actual, chosen in zip(wires[source], values):
                    clauses.extend(([-select, -actual, chosen], [-select, actual, -chosen]))

        for a, b, out in zip(*operands, wires[output]):
            clauses.extend((
                [-conj, -a, -b, out], [-conj, a, -out], [-conj, b, -out],
                [-disj, a, b, -out], [-disj, -a, out], [-disj, -b, out],
                [-invert, a, out], [-invert, -a, -out],
            ))

    clauses.extend([-a, -b] for a, b in combinations(inverters, 2))
    for row, literal in enumerate(wires[-1]):
        target = any((row & edge) == edge for edge in EDGE_MASKS)
        clauses.append([literal if target else -literal])

    with path.open("w", encoding="ascii", newline="\n") as output_file:
        print("p cnf", variable_count, len(clauses), file=output_file)
        for clause in clauses:
            print(*clause, 0, file=output_file)

    if hashlib.sha256(path.read_bytes()).hexdigest() != CNF_SHA256:
        raise ValueError("CNF differs from the checked instance")


def check_rup(cnf, proof):
    """Validate each ordered unit-propagation chain through the empty clause."""
    clauses = {}
    for line in cnf.read_text().splitlines():
        if line.startswith("p "):
            continue
        literals = list(map(int, line.split()))
        if literals[-1] != 0:
            raise ValueError("unterminated CNF clause")
        clauses[len(clauses) + 1] = frozenset(literals[:-1])

    last_id = len(clauses)
    additions = 0
    with proof.open(encoding="ascii") as stream:
        for line in stream:
            fields = line.split()
            if not fields or fields[0] == "c":
                continue
            if fields[1] == "d":
                if fields[-1] != "0":
                    raise ValueError("unterminated deletion")
                for key in map(int, fields[2:-1]):
                    clauses.pop(key, None)
                continue

            row = list(map(int, fields))
            key = row[0]
            if key <= last_id or row[-1] != 0:
                raise ValueError("invalid proof clause")
            cut = row.index(0, 1)
            clause = frozenset(row[1:cut])
            truth = {-literal for literal in clause}
            conflict = any(-literal in truth for literal in truth)
            for hint in row[cut + 1:-1]:
                if conflict:
                    break
                if hint <= 0 or hint not in clauses:
                    raise ValueError("missing or unsupported proof hint")
                cited = clauses[hint]
                if any(literal in truth for literal in cited):
                    raise ValueError("satisfied clause in propagation chain")
                unset = [literal for literal in cited if -literal not in truth]
                if len(unset) > 1:
                    raise ValueError("nonunit proof hint")
                if not unset:
                    conflict = True
                else:
                    truth.add(unset[0])
            if not conflict:
                raise ValueError(f"no conflict for clause {key}")
            additions += 1
            if not clause:
                return additions
            clauses[key] = clause
            last_id = key
    raise ValueError("no verified empty clause")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cadical", default="cadical")
    parser.add_argument("--proof", type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp)
        cnf = root / "bowtie.cnf"
        generate_cnf(cnf)
        proof = args.proof
        if proof is None:
            proof = root / "bowtie.lrat"
            run = subprocess.run([args.cadical, "-q", "--no-binary", "--lrat", str(cnf), str(proof)])
            if run.returncode != 20:
                raise SystemExit(f"solver exit {run.returncode}")
        additions = check_rup(cnf, proof)
        print(f"Verified the empty clause after {additions} additions.")


if __name__ == "__main__":
    main()
