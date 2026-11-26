# Exact circuit bounds on promised inputs

For the six shared input wires of L-meta-22815, the promise includes each singleton and each unordered pair. Upper.lean and Lower.lean give the explicit circuit and the lower bound. Compile each from the project's lean directory using the pinned toolchain and lake env lean.

To regenerate the Lean files in a separate directory, run replay.sh from this directory with the two cited fork commits available in the checkout. Then run python3 general.py example.json regenerated. The minimal JSON example contains only the public statement and unit name. For split monotone promise statements use generate.py with the same arguments. The witness is evaluated independently on each promised input. For a negative result the generated Lean file verifies the live-wire search and its connection to the exact requested statement. A search timeout alone gives no lower bound.
