import Assemble
import Orbit0
import Orbit1
import Orbit2
import Orbit3
import Orbit4
import Orbit5
import Orbit6
import Orbit7
import Orbit8
import Orbit9
import Orbit10
import Orbit11
import Orbit12
import Orbit13
import Orbit14
import Orbit15
import Batch0
import Batch1
import Batch2
import Batch3
import Batch4
import Batch5
import Batch6
import Batch7
import Batch8
import Batch9
import Batch10
import Batch11
import Batch12
import Batch13
import Batch14
import Batch15
import Batch16
import Batch17
import Batch18
import Batch19
import Batch20
import Batch21
namespace PHPOverlap
theorem routes (m : Fin 4096) : rightEntry m.val = true := by
  let b : Fin 16 := ⟨m.val/256, by omega⟩
  let k : Fin 256 := ⟨m.val%256, Nat.mod_lt _ (by decide)⟩
  have eq : m.val = 256*b.val+k.val := by dsimp [b,k]; omega
  rw [eq]
  clear eq
  generalize b = j
  fin_cases j
  · exact orb0 k
  · exact orb1 k
  · exact orb2 k
  · exact orb3 k
  · exact orb4 k
  · exact orb5 k
  · exact orb6 k
  · exact orb7 k
  · exact orb8 k
  · exact orb9 k
  · exact orb10 k
  · exact orb11 k
  · exact orb12 k
  · exact orb13 k
  · exact orb14 k
  · exact orb15 k
theorem rich1 : Rich (form 1) := ⟨19, 12, by decide, from_pack checked1_0, from_pack checked1_1⟩
theorem rich3 : Rich (form 3) := ⟨17, 18, by decide, from_pack checked3_0, from_pack checked3_1⟩
theorem rich7 : Rich (form 7) := ⟨11, 21, by decide, from_pack checked7_0, from_pack checked7_1⟩
theorem rich9 : Rich (form 9) := ⟨16, 18, by decide, from_pack checked9_0, from_pack checked9_1⟩
theorem rich10 : Rich (form 10) := ⟨20, 16, by decide, from_pack checked10_0, from_pack checked10_1⟩
theorem rich11 : Rich (form 11) := ⟨18, 20, by decide, from_pack checked11_0, from_pack checked11_1⟩
theorem rich14 : Rich (form 14) := ⟨19, 16, by decide, from_pack checked14_0, from_pack checked14_1⟩
theorem rich15 : Rich (form 15) := ⟨15, 19, by decide, from_pack checked15_0, from_pack checked15_1⟩
theorem rich27 : Rich (form 27) := ⟨16, 19, by decide, from_pack checked27_0, from_pack checked27_1⟩
theorem rich29 : Rich (form 29) := ⟨20, 18, by decide, from_pack checked29_0, from_pack checked29_1⟩
theorem rich31 : Rich (form 31) := ⟨18, 17, by decide, from_pack checked31_0, from_pack checked31_1⟩
theorem rich63 : Rich (form 63) := ⟨21, 12, by decide, from_pack checked63_0, from_pack checked63_1⟩
theorem rich73 : Rich (form 73) := ⟨12, 20, by decide, from_pack checked73_0, from_pack checked73_1⟩
theorem rich74 : Rich (form 74) := ⟨19, 17, by decide, from_pack checked74_0, from_pack checked74_1⟩
theorem rich75 : Rich (form 75) := ⟨18, 20, by decide, from_pack checked75_0, from_pack checked75_1⟩
theorem rich78 : Rich (form 78) := ⟨20, 12, by decide, from_pack checked78_0, from_pack checked78_1⟩
theorem rich79 : Rich (form 79) := ⟨19, 18, by decide, from_pack checked79_0, from_pack checked79_1⟩
theorem rich83 : Rich (form 83) := ⟨20, 19, by decide, from_pack checked83_0, from_pack checked83_1⟩
theorem rich84 : Rich (form 84) := ⟨19, 19, by decide, from_pack checked84_0, from_pack checked84_1⟩
theorem rich85 : Rich (form 85) := ⟨18, 19, by decide, from_pack checked85_0, from_pack checked85_1⟩
theorem rich87 : Rich (form 87) := ⟨18, 20, by decide, from_pack checked87_0, from_pack checked87_1⟩
theorem rich91 : Rich (form 91) := ⟨19, 18, by decide, from_pack checked91_0, from_pack checked91_1⟩
theorem rich93 : Rich (form 93) := ⟨19, 20, by decide, from_pack checked93_0, from_pack checked93_1⟩
theorem rich94 : Rich (form 94) := ⟨20, 18, by decide, from_pack checked94_0, from_pack checked94_1⟩
theorem rich95 : Rich (form 95) := ⟨20, 19, by decide, from_pack checked95_0, from_pack checked95_1⟩
theorem rich118 : Rich (form 118) := ⟨12, 20, by decide, from_pack checked118_0, from_pack checked118_1⟩
theorem rich119 : Rich (form 119) := ⟨18, 19, by decide, from_pack checked119_0, from_pack checked119_1⟩
theorem rich127 : Rich (form 127) := ⟨19, 15, by decide, from_pack checked127_0, from_pack checked127_1⟩
theorem rich219 : Rich (form 219) := ⟨20, 12, by decide, from_pack checked219_0, from_pack checked219_1⟩
theorem rich221 : Rich (form 221) := ⟨18, 20, by decide, from_pack checked221_0, from_pack checked221_1⟩
theorem rich223 : Rich (form 223) := ⟨19, 18, by decide, from_pack checked223_0, from_pack checked223_1⟩
theorem rich238 : Rich (form 238) := ⟨20, 19, by decide, from_pack checked238_0, from_pack checked238_1⟩
theorem rich239 : Rich (form 239) := ⟨19, 20, by decide, from_pack checked239_0, from_pack checked239_1⟩
theorem rich255 : Rich (form 255) := ⟨17, 18, by decide, from_pack checked255_0, from_pack checked255_1⟩
theorem rich511 : Rich (form 511) := ⟨12, 20, by decide, from_pack checked511_0, from_pack checked511_1⟩
theorem rich585 : Rich (form 585) := ⟨14, 17, by decide, from_pack checked585_0, from_pack checked585_1⟩
theorem rich586 : Rich (form 586) := ⟨15, 19, by decide, from_pack checked586_0, from_pack checked586_1⟩
theorem rich587 : Rich (form 587) := ⟨18, 19, by decide, from_pack checked587_0, from_pack checked587_1⟩
theorem rich590 : Rich (form 590) := ⟨17, 14, by decide, from_pack checked590_0, from_pack checked590_1⟩
theorem rich591 : Rich (form 591) := ⟨19, 17, by decide, from_pack checked591_0, from_pack checked591_1⟩
theorem rich594 : Rich (form 594) := ⟨20, 16, by decide, from_pack checked594_0, from_pack checked594_1⟩
theorem rich595 : Rich (form 595) := ⟨19, 20, by decide, from_pack checked595_0, from_pack checked595_1⟩
theorem rich596 : Rich (form 596) := ⟨20, 19, by decide, from_pack checked596_0, from_pack checked596_1⟩
theorem rich597 : Rich (form 597) := ⟨17, 20, by decide, from_pack checked597_0, from_pack checked597_1⟩
theorem rich598 : Rich (form 598) := ⟨19, 15, by decide, from_pack checked598_0, from_pack checked598_1⟩
theorem rich599 : Rich (form 599) := ⟨19, 19, by decide, from_pack checked599_0, from_pack checked599_1⟩
theorem rich603 : Rich (form 603) := ⟨20, 17, by decide, from_pack checked603_0, from_pack checked603_1⟩
theorem rich605 : Rich (form 605) := ⟨20, 19, by decide, from_pack checked605_0, from_pack checked605_1⟩
theorem rich606 : Rich (form 606) := ⟨19, 18, by decide, from_pack checked606_0, from_pack checked606_1⟩
theorem rich607 : Rich (form 607) := ⟨20, 19, by decide, from_pack checked607_0, from_pack checked607_1⟩
theorem rich630 : Rich (form 630) := ⟨15, 17, by decide, from_pack checked630_0, from_pack checked630_1⟩
theorem rich631 : Rich (form 631) := ⟨17, 19, by decide, from_pack checked631_0, from_pack checked631_1⟩
theorem rich639 : Rich (form 639) := ⟨18, 19, by decide, from_pack checked639_0, from_pack checked639_1⟩
theorem rich667 : Rich (form 667) := ⟨20, 19, by decide, from_pack checked667_0, from_pack checked667_1⟩
theorem rich668 : Rich (form 668) := ⟨19, 20, by decide, from_pack checked668_0, from_pack checked668_1⟩
theorem rich669 : Rich (form 669) := ⟨20, 19, by decide, from_pack checked669_0, from_pack checked669_1⟩
theorem rich671 : Rich (form 671) := ⟨20, 20, by decide, from_pack checked671_0, from_pack checked671_1⟩
theorem rich679 : Rich (form 679) := ⟨19, 20, by decide, from_pack checked679_0, from_pack checked679_1⟩
theorem rich685 : Rich (form 685) := ⟨15, 19, by decide, from_pack checked685_0, from_pack checked685_1⟩
theorem rich686 : Rich (form 686) := ⟨20, 18, by decide, from_pack checked686_0, from_pack checked686_1⟩
theorem rich687 : Rich (form 687) := ⟨19, 19, by decide, from_pack checked687_0, from_pack checked687_1⟩
theorem rich703 : Rich (form 703) := ⟨20, 18, by decide, from_pack checked703_0, from_pack checked703_1⟩
theorem rich731 : Rich (form 731) := ⟨19, 15, by decide, from_pack checked731_0, from_pack checked731_1⟩
theorem rich733 : Rich (form 733) := ⟨19, 20, by decide, from_pack checked733_0, from_pack checked733_1⟩
theorem rich734 : Rich (form 734) := ⟨18, 20, by decide, from_pack checked734_0, from_pack checked734_1⟩
theorem rich735 : Rich (form 735) := ⟨19, 19, by decide, from_pack checked735_0, from_pack checked735_1⟩
theorem rich750 : Rich (form 750) := ⟨19, 20, by decide, from_pack checked750_0, from_pack checked750_1⟩
theorem rich751 : Rich (form 751) := ⟨20, 20, by decide, from_pack checked751_0, from_pack checked751_1⟩
theorem rich758 : Rich (form 758) := ⟨18, 19, by decide, from_pack checked758_0, from_pack checked758_1⟩
theorem rich759 : Rich (form 759) := ⟨19, 20, by decide, from_pack checked759_0, from_pack checked759_1⟩
theorem rich767 : Rich (form 767) := ⟨19, 20, by decide, from_pack checked767_0, from_pack checked767_1⟩
theorem rich950 : Rich (form 950) := ⟨17, 15, by decide, from_pack checked950_0, from_pack checked950_1⟩
theorem rich951 : Rich (form 951) := ⟨19, 17, by decide, from_pack checked951_0, from_pack checked951_1⟩
theorem rich959 : Rich (form 959) := ⟨19, 18, by decide, from_pack checked959_0, from_pack checked959_1⟩
theorem rich1023 : Rich (form 1023) := ⟨15, 19, by decide, from_pack checked1023_0, from_pack checked1023_1⟩
theorem rich1755 : Rich (form 1755) := ⟨16, 16, by decide, from_pack checked1755_0, from_pack checked1755_1⟩
theorem rich1757 : Rich (form 1757) := ⟨19, 18, by decide, from_pack checked1757_0, from_pack checked1757_1⟩
theorem rich1759 : Rich (form 1759) := ⟨17, 19, by decide, from_pack checked1759_0, from_pack checked1759_1⟩
theorem rich1773 : Rich (form 1773) := ⟨20, 18, by decide, from_pack checked1773_0, from_pack checked1773_1⟩
theorem rich1774 : Rich (form 1774) := ⟨20, 19, by decide, from_pack checked1774_0, from_pack checked1774_1⟩
theorem rich1775 : Rich (form 1775) := ⟨20, 19, by decide, from_pack checked1775_0, from_pack checked1775_1⟩
theorem rich1791 : Rich (form 1791) := ⟨18, 19, by decide, from_pack checked1791_0, from_pack checked1791_1⟩
theorem rich1911 : Rich (form 1911) := ⟨20, 20, by decide, from_pack checked1911_0, from_pack checked1911_1⟩
theorem rich1919 : Rich (form 1919) := ⟨20, 19, by decide, from_pack checked1919_0, from_pack checked1919_1⟩
theorem rich2047 : Rich (form 2047) := ⟨18, 17, by decide, from_pack checked2047_0, from_pack checked2047_1⟩
theorem rich4095 : Rich (form 4095) := ⟨20, 13, by decide, from_pack checked4095_0, from_pack checked4095_1⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem rich_key (k : Nat) (h : k ∈ keylist.toList) (nz : k ≠ 0) : Rich (form k) := by
  change k ∈ [0, 1, 3, 7, 9, 10, 11, 14, 15, 27, 29, 31, 63, 73, 74, 75, 78, 79, 83, 84, 85, 87, 91, 93, 94, 95, 118, 119, 127, 219, 221, 223, 238, 239, 255, 511, 585, 586, 587, 590, 591, 594, 595, 596, 597, 598, 599, 603, 605, 606, 607, 630, 631, 639, 667, 668, 669, 671, 679, 685, 686, 687, 703, 731, 733, 734, 735, 750, 751, 758, 759, 767, 950, 951, 959, 1023, 1755, 1757, 1759, 1773, 1774, 1775, 1791, 1911, 1919, 2047, 4095] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (nz rfl).elim
  · exact rich1
  · exact rich3
  · exact rich7
  · exact rich9
  · exact rich10
  · exact rich11
  · exact rich14
  · exact rich15
  · exact rich27
  · exact rich29
  · exact rich31
  · exact rich63
  · exact rich73
  · exact rich74
  · exact rich75
  · exact rich78
  · exact rich79
  · exact rich83
  · exact rich84
  · exact rich85
  · exact rich87
  · exact rich91
  · exact rich93
  · exact rich94
  · exact rich95
  · exact rich118
  · exact rich119
  · exact rich127
  · exact rich219
  · exact rich221
  · exact rich223
  · exact rich238
  · exact rich239
  · exact rich255
  · exact rich511
  · exact rich585
  · exact rich586
  · exact rich587
  · exact rich590
  · exact rich591
  · exact rich594
  · exact rich595
  · exact rich596
  · exact rich597
  · exact rich598
  · exact rich599
  · exact rich603
  · exact rich605
  · exact rich606
  · exact rich607
  · exact rich630
  · exact rich631
  · exact rich639
  · exact rich667
  · exact rich668
  · exact rich669
  · exact rich671
  · exact rich679
  · exact rich685
  · exact rich686
  · exact rich687
  · exact rich703
  · exact rich731
  · exact rich733
  · exact rich734
  · exact rich735
  · exact rich750
  · exact rich751
  · exact rich758
  · exact rich759
  · exact rich767
  · exact rich950
  · exact rich951
  · exact rich959
  · exact rich1023
  · exact rich1755
  · exact rich1757
  · exact rich1759
  · exact rich1773
  · exact rich1774
  · exact rich1775
  · exact rich1791
  · exact rich1911
  · exact rich1919
  · exact rich2047
  · exact rich4095
theorem every_root (f : Finset Grid) (ne : f ≠ ∅) : Rich f := allRich routes rich_key f ne
open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_118.Graph
theorem shared_ten (π : List (LinClause Grid)) (hr : IsLinRefutation (PHP 4 3) π) (short : π.length ≤ 51) :
    ∃ C P r c d, Encoded F C P π ∧ r < π.length ∧ P r = [c,d] ∧ c ≠ d ∧
      (∀ a, FalseAt C a r) ∧ 10 ≤ (Live P c ∩ Live P d).card :=
  common_lines every_root π hr short
#print axioms shared_ten
end PHPOverlap
