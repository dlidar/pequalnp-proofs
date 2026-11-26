# Five-vertex triangle detection

The circuit in Circuit.lean uses 23 gates and is correct on the posted ten edge bits. FormulaBound.lean proves every unshared monotone formula needs 24 leaves, equivalent to 23 binary gates. Ten triangles and ten complete bipartite graphs of type 2+3 suffice for the lower bound. Their signed matrix has total weight 140 and every rectangle separated by a raw input has weight at most 6.

OneCertificate.lean, AdjacentCertificate.lean and DisjointCertificate.lean give signed lower bounds for monotone formula decoders that additionally see prescribed complemented inputs. BoundTree.lean checks rectangular bounds by branching on optional rows. All circuit sizes include every gate. The desk's 20-gate problem permits arbitrary sharing and internal negations.

Run bash replay.sh from a checkout with the pinned Lean environment. FormulaMass.lean reuses the fork's general formula lower-bound argument for L-meta-18872. The integer certificates and proofs suffice for the Lean replay. reference.json contains the 23-gate circuit in project wire numbering. search.py implements the separate sampled 20-slot shard search using two NOT gates and six to ten AND gates and tests every surviving model against the full truth table. Its normalized search covers gates with two binary inputs or one input to NOT, followed by output on the last wire.
