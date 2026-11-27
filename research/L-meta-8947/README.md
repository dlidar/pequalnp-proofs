# L-meta-8947 — read-two flags in a projective plane

A flag is an incident point–line pair. Call it hard for a circuit if no accepting proof tree on those two inputs uses each input at most twice. Write N = q² + q + 1 and s for the circuit size.

Under the posted acceptance and rejection tests, the number of flags that do have such a tree is at most 34(s + 2N + 4). Density.lean localizes the proof from upstream L-meta-8945 to individual flags. Residual.lean uses the independently rebuilt upstream 349N ≤ 100s theorem, L-meta-5351, to cover all orders 200 through 349.

Any counterexample must have q ≥ 350. More than 46.7% of all flags must be hard. Some perfect matching of points to incident lines contains more than 46.7% hard flags. For q ≥ 422, more than half of the same matching must be hard. The matching theorem applies Hall's theorem to the regular incidence graph, removes a perfect matching, and inducts on the degree to find a matching attaining at least the average weight.

Hardness can be created at low cost. Append two self-AND gates followed by a self-OR. This preserves the Boolean function and makes every nonempty prime implicant fail the read-two test. In particular, every flag becomes hard. Consequence.lean checks that the posted statement would imply Nq ≤ 100(s + 3) for any valid-output binary monotone circuit on the same tests. The open step is a size lower bound for circuits with a dense matching of hard flags, taking account of shared subcircuits.

The sources use upstream commit 624acb3fb2189a78719c262c1af407bd73fb3b5c and Lean 4.36.0. Density.lean and the background lemmas in Amplify.lean adapt the Apache-2.0 licensed L_meta_8945.lean from that commit. Run `bash verify.sh` inside this directory of the fork checkout to build the research results and print their axioms. This branch contains research for a proof-only assignment.
