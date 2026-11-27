# A lower bound for the prescribed 3-by-3 permanent prefix

L-meta-27300 proposes a circuit of at most 12 gates for the Boolean permanent, with its first two gates fixed to AND(0,1) and AND(5,8). Result.lean proves the exact negation. Sharp.lean proves that at least 13 binary gates are needed even if unary NOT gates are free. Reference.lean gives a 19-gate circuit satisfying every normal-form condition on all 512 inputs.

For each of the nine inputs there is a pair of assignments differing there on which both prefix signals agree and the permanent changes. Every original input must therefore be used after the prefix. Each computed wire must also be used or named as output. With at most ten later binary gates the use list, including the output port, has at most as many entries as there are distinct wires. A unary NOT adds one input port and one wire, leaving this count unchanged. Every wire must therefore appear once in the list.

Set inputs 0 and 8 false and inputs 3, 4 and 5 true. Both prefix outputs become false. With the remaining inputs named a, b, c, d in the order 1, 2, 6, 7, the function is ac OR bc OR bd. On eight selected assignments its output has formula cost five. All initial signals together have cost four. The potential in Certificate.lean is invariant under NOT and subadditive under AND and OR. Summing the gate inequalities cancels the cost of every intermediate signal in a circuit where each wire is used once.

The integer script check_bounds.py independently checks all 65,536 pairs of wire signatures and all 256 complements. It also checks 32 restrictions of the same kind and their two minimum hitting pairs. These extra counts are independent computations. Run bash verify.sh for the pinned Lean replay.
