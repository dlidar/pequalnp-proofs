"""Split a one-a-side lower-bound proof with one spare reader into Lean modules.

The kernel verifies coverage of the first step and each listed branch separately.
Run with the generated single-file Lower.lean, an output directory, and the
directory containing the assembly-template and join-template from L-meta-20496.
"""
from itertools import combinations
from pathlib import Path
import re
import sys


def numbers(text):
    return tuple(int(x, 16) for x in re.findall(r"0x[0-9a-f]+", text))


def read_instance(source):
    raw = numbers(source.split("def rawInputs : List W :=", 1)[1].split("]", 1)[0])
    width = int(re.search(r"def sep .*?BitVec (\d+)", source)[1])
    budget = int(re.search(r"theorem exact_negation : [^\n]+\) (\d+) := by", source)[1])
    namespace = re.search(r"^namespace (PEqualNP\.Outside\.Mask\d+)$", source, re.M)[1]
    return raw, width, budget, namespace


def children(raw, width, budget):
    mask = (1 << width) - 1

    def separates(wires):
        covered = 0
        for value in wires:
            covered |= (value >> width) & ~value
        return covered & mask == mask

    # Separation is monotone under adjoining more wires.
    if (budget != len(raw) or not separates(raw)
            or any(separates(raw[:i] + raw[i+1:]) for i in range(len(raw)))):
        raise ValueError("the unique full-input, one-spare split does not apply")

    states = {}
    for i, j in combinations(range(len(raw)), 2):
        a, b = raw[i], raw[j]
        rest = tuple(w for index, w in enumerate(raw) if index not in (i, j))
        for value in (a & b, a | b):
            for kept in ((), (a,), (b,)):
                state = (value,) + kept + rest
                if separates(state):
                    states[1 - len(kept), state] = None
    return list(states)


def split(src, out, templates):
    source = src.read_text()
    raw, width, budget, namespace = read_instance(source)
    states = children(raw, width, budget)
    if not states:
        raise ValueError("no first-step branches")
    out.mkdir(exist_ok=True)
    core = source[:source.index("\n", source.index("theorem inputs_nodup"))]
    (out / "Core.lean").write_text(core + "\nend " + namespace + "\n")

    denied = []
    for i, (spare, wires) in enumerate(states):
        wire_list = "[" + ", ".join(map(hex, wires)) + "]"
        denied.append(f"({spare}, {wire_list})")
        (out / f"Branch{i}.lean").write_text(
            f"import Core\nnamespace {namespace}\nset_option maxRecDepth 32000 in\n"
            f"set_option maxHeartbeats 100000000 in\ntheorem br{i} : "
            f"optimized {budget-1} {spare} {wire_list} = false := by decide +kernel\nend {namespace}\n"
        )
    template = (templates / "assembly-template").read_text().replace("PEqualNP.Outside.Mask1534", namespace)
    header, logic = template.split("section Assembly")
    logic = re.sub(r"\b[789]\b", lambda m: str(budget + int(m[0]) - 8), logic)
    (out / "Logic.lean").write_text(header[:header.index(":=")+2] + "\n  ["
                                   + ",\n   ".join(denied) + "]\n\nsection Assembly" + logic)

    join = (templates / "join-template").read_text()
    join = join[join.index("namespace "):join.index("  rcases h with")]
    join = join.replace("PEqualNP.Outside.Mask1534", namespace).replace("optimized 7", f"optimized {budget-1}")
    end = source[source.index("theorem exact_negation"):].replace("no_small C", f"no_small {namespace}.denied_false C")
    (out / "Lower.lean").write_text(
        "import Logic\n" + "".join(f"import Branch{i}\n" for i in range(len(states))) + join
        + "  rcases h with " + " | ".join(["rfl"] * len(states)) + "\n"
        + "".join(f"  · exact br{i}\n" for i in range(len(states))) + "end " + namespace + "\n" + end
    )
    return len(states)


if __name__ == "__main__":
    print(split(*(Path(arg) for arg in sys.argv[1:])))
