import PEqualNP.Research.Cached3803.Core
namespace PEqualNP.Research.CachedFlagTerms
namespace Mode0
def selected : Array Mask := #[8193,131073,8388609,33554433,8194,16386,262146,16777218,16388,32772,524292,33554436,8200,32776,65544,1048584,16400,65552,131088,2097168,32800,131104,262176,4194336,65600,262208,524352,8388672,131200,524416,1048704,16777344,262400,1048832,2097408,33554688,8704,524800,2097664,4194816,17408,1049600,4195328,8389632,34816,2099200,8390656,16779264,69632,4198400,16781312,33558528]
def separators : List Mask := [3211303,42205848,177472,4737289,21233693]
def terms : List Mask := [8193,131073,8388609,33554433,8194,16386,262146,16777218,16388,32772,524292,33554436,8200,32776,65544,1048584,16400,65552,131088,2097168,32800,131104,262176,4194336,65600,262208,524352,8388672,131200,524416,1048704,16777344,262400,1048832,2097408,33554688,8704,524800,2097664,4194816,17408,1049600,4195328,8389632,34816,2099200,8390656,16779264,69632,4198400,16781312,33558528]
def positive : List Mask := [8193,131073,8388609,33554433,8194,16386,262146,16777218,16388,32772,524292,33554436,8200,32776,65544,1048584,16400,65552,131088,2097168,32800,131104,262176,4194336,65600,262208,524352,8388672,131200,524416,1048704,16777344,262400,1048832,2097408,33554688,8704,524800,2097664,4194816,17408,1049600,4195328,8389632,34816,2099200,8390656,16779264,69632,4198400,16781312,33558528]
def negative : List Mask := [3211303,7340103,6357127,5310471,5275731,4751635,5769235,1609747,2688035,1640483,3674147,6324419,3182659,4292995,2196611,623875,4786435,2659331,21233693,23068749,6553741,19137549,22020181,18088469,5507093,19923045,17891877,18940965,2425989,4524165,17106437,1378821,21496089,17564697,4982809,18890857,17318185,19399721,2641961,6308041,20988233,4475017,2379913,4737289,2888713,808969,21004625,17859153,17335569,17073681,1348113,824337,1841169,17842785,3166305,16859937,17368353,608545,1133089,1595425,4243905,2150593,16827201,1102401,115585,4278657,362113,346753,316033,2397313,16877313,1333761,6422606,14680206,12714254,10620942,10551462,9503270,11538470,5376070,3280966,12648838,8585990,4393222,1247750,9572870,42467386,46137498,13107482,38275098,44040362,36176938,11014186,39846090,35783754,37881930,4851978,9048330,34212874,2757642,42992178,35129394,9965618,37781714,34636370,38799442,12616082,41976466,8950034,9474578,42009250,35718306,34671138,34147362,35685570,33719874,34736706,1217090,2266178,8487810,33654402,231170,8557314,724226,693506,33754626,12845212,29360412,25428508,21102924,19006540,10752140,25297676,17171980,8786444,2495500,17834100,25174324,26214964,9449524,20980052,5253204,12591508,4466836,8663188,9703956,1325076,18883684,3158116,8462756,2172068,10498212,25232164,16852260,16917828,4335940,2241604,1194052,4270468,339076,2372740,16975620,208132,462340,1448452,408580,25690424,58720824,50857016,42205848,38013080,50595352,34343960,35668200,50348648,52429928,41960104,10506408,25183016,8933672,37767368,16925512,4344136,50464328,33704520,33835656,8671880,8540936,678152,33951240,416264,924680,51380848,50340976,34613360,17311024,8925488,34090032,1587248,4235728,33596624,37759184,16819536,50366032,8434064,33851024,8688272,33827984,308368,570640,801808,35661024,33581280,2126048,34622048,1079392,8471456,92576,8417696,33639072,33631392,601376,555296,4221376,61888,2143424,16942912,185152,177472,162112,1202752,8442752,33885824,670976]
def row (i : Fin 52) : Mask := selected[i.val]!
theorem separator_valid : ∀ z ∈ separators, z ∈ negative := by
  have cert : separators.all (fun z => negative.contains z) = true := by decide +kernel
  simpa [List.all_eq_true,List.any_eq_true, Bool.or_eq_true, or_iff_not_imp_left, List.mem_finRange] using cert
theorem selection_valid : ∀ i, row i ∈ positive := by
  have cert : (List.finRange 52).all (fun i => positive.contains (row i)) = true := by decide +kernel
  simpa [List.all_eq_true,List.any_eq_true, Bool.or_eq_true, or_iff_not_imp_left, List.mem_finRange] using cert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem separates : ∀ i j : Fin 52, i < j → ∃ z ∈ separators, on (row i &&& row j) z := by
  have cert : (List.finRange 52).all (fun i => (List.finRange 52).all (fun j => decide (i < j) == false || separators.any (fun z => decide (on (row i &&& row j) z)))) = true := by decide +kernel
  simpa [List.all_eq_true,List.any_eq_true, Bool.or_eq_true, or_iff_not_imp_left, List.mem_finRange] using cert
theorem lower {m : ℕ} (ts : Fin m → Mask)
    (pos : ∀ x ∈ positive, ∃ j, on (ts j) x)
    (neg : ∀ j z, z ∈ negative → ¬on (ts j) z) : 52 ≤ m :=
  packing row separators ts separates (fun i => pos _ (selection_valid i))
    (fun j z hz => neg j z (separator_valid z hz))
theorem upper_positive : ∀ x ∈ positive, ∃ t ∈ terms, on t x := by
  have cert : positive.all (fun x => terms.any (fun t => decide (on t x))) = true := by decide +kernel
  simpa [List.all_eq_true,List.any_eq_true, Bool.or_eq_true, or_iff_not_imp_left, List.mem_finRange] using cert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem upper_negative : ∀ x ∈ negative, ∀ t ∈ terms, ¬on t x := by
  have cert : negative.all (fun x => terms.all (fun t => !decide (on t x))) = true := by decide +kernel
  simpa [List.all_eq_true,List.any_eq_true, Bool.or_eq_true, or_iff_not_imp_left, List.mem_finRange] using cert
theorem upper_count : terms.length = 52 := by decide
end Mode0

end PEqualNP.Research.CachedFlagTerms

#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.selected
#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.separators
#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.terms
#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.positive
#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.negative
#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.row
#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.separator_valid
#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.selection_valid
#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.separates
#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.lower
#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.upper_positive
#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.upper_negative
#print axioms PEqualNP.Research.CachedFlagTerms.Mode0.upper_count
