import OptimalBase
namespace PEqualNP.Research.Cached9815
open TripleFormulaMass
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
private def wit92 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.var none) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp92 : Sharp 92 := by
  refine ⟨wit92,rfl,?_⟩
  intro x
  change (wit92).eval (fill false 0 2 x)=target x
  simp only [wit92, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit94 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.var none) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp94 : Sharp 94 := by
  refine ⟨wit94,rfl,?_⟩
  intro x
  change (wit94).eval (fill false 0 4 x)=target x
  simp only [wit94, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit95 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.var none) (.var (some 4))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp95 : Sharp 95 := by
  refine ⟨wit95,rfl,?_⟩
  intro x
  change (wit95).eval (fill false 0 5 x)=target x
  simp only [wit95, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit96 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.var none) (.var (some 2))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp96 : Sharp 96 := by
  refine ⟨wit96,rfl,?_⟩
  intro x
  change (wit96).eval (fill false 0 6 x)=target x
  simp only [wit96, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit104 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.var none) (.var (some 4)))))
theorem sharp104 : Sharp 104 := by
  refine ⟨wit104,rfl,?_⟩
  intro x
  change (wit104).eval (fill false 1 2 x)=target x
  simp only [wit104, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit105 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.var none)) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp105 : Sharp 105 := by
  refine ⟨wit105,rfl,?_⟩
  intro x
  change (wit105).eval (fill false 1 3 x)=target x
  simp only [wit105, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit106 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.var none) (.var (some 2)))))
theorem sharp106 : Sharp 106 := by
  refine ⟨wit106,rfl,?_⟩
  intro x
  change (wit106).eval (fill false 1 4 x)=target x
  simp only [wit106, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit107 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.var none) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp107 : Sharp 107 := by
  refine ⟨wit107,rfl,?_⟩
  intro x
  change (wit107).eval (fill false 1 5 x)=target x
  simp only [wit107, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit108 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.var none) (.var (some 5))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp108 : Sharp 108 := by
  refine ⟨wit108,rfl,?_⟩
  intro x
  change (wit108).eval (fill false 1 6 x)=target x
  simp only [wit108, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit117 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.var none) (.var (some 1)))))
theorem sharp117 : Sharp 117 := by
  refine ⟨wit117,rfl,?_⟩
  intro x
  change (wit117).eval (fill false 2 4 x)=target x
  simp only [wit117, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit119 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.var none) (.var (some 0))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp119 : Sharp 119 := by
  refine ⟨wit119,rfl,?_⟩
  intro x
  change (wit119).eval (fill false 2 6 x)=target x
  simp only [wit119, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit127 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.var none) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp127 : Sharp 127 := by
  refine ⟨wit127,rfl,?_⟩
  intro x
  change (wit127).eval (fill false 3 4 x)=target x
  simp only [wit127, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit128 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.var none))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp128 : Sharp 128 := by
  refine ⟨wit128,rfl,?_⟩
  intro x
  change (wit128).eval (fill false 3 5 x)=target x
  simp only [wit128, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit129 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.var none) (.var (some 4))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp129 : Sharp 129 := by
  refine ⟨wit129,rfl,?_⟩
  intro x
  change (wit129).eval (fill false 3 6 x)=target x
  simp only [wit129, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit137 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.var none) (.var (some 0))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp137 : Sharp 137 := by
  refine ⟨wit137,rfl,?_⟩
  intro x
  change (wit137).eval (fill false 4 5 x)=target x
  simp only [wit137, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit138 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.disj (.var (some 1)) (.var (some 5))) (.var (some 6))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.var none) (.var (some 3))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp138 : Sharp 138 := by
  refine ⟨wit138,rfl,?_⟩
  intro x
  change (wit138).eval (fill false 4 6 x)=target x
  simp only [wit138, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit146 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 7)) (.disj (.var (some 1)) (.var (some 3)))) (.conj (.var (some 8)) (.disj (.disj (.var (some 0)) (.var (some 2))) (.var (some 6))))) (.conj (.var (some 9)) (.disj (.var none) (.var (some 1))))) (.conj (.var (some 10)) (.disj (.disj (.var (some 0)) (.var (some 4))) (.var (some 5))))) (.conj (.var (some 11)) (.disj (.disj (.var (some 3)) (.var (some 4))) (.var (some 6))))) (.conj (.var (some 12)) (.disj (.var (some 3)) (.var (some 5))))) (.conj (.var (some 13)) (.disj (.disj (.var (some 1)) (.var (some 2))) (.var (some 4)))))
theorem sharp146 : Sharp 146 := by
  refine ⟨wit146,rfl,?_⟩
  intro x
  change (wit146).eval (fill false 5 6 x)=target x
  simp only [wit146, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit162 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.var none) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp162 : Sharp 162 := by
  refine ⟨wit162,rfl,?_⟩
  intro x
  change (wit162).eval (fill false 7 9 x)=target x
  simp only [wit162, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit164 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.var none) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp164 : Sharp 164 := by
  refine ⟨wit164,rfl,?_⟩
  intro x
  change (wit164).eval (fill false 7 11 x)=target x
  simp only [wit164, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit165 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.var none) (.var (some 11))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp165 : Sharp 165 := by
  refine ⟨wit165,rfl,?_⟩
  intro x
  change (wit165).eval (fill false 7 12 x)=target x
  simp only [wit165, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit166 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.var none) (.var (some 9))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp166 : Sharp 166 := by
  refine ⟨wit166,rfl,?_⟩
  intro x
  change (wit166).eval (fill false 7 13 x)=target x
  simp only [wit166, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit167 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.var none) (.var (some 11)))))
theorem sharp167 : Sharp 167 := by
  refine ⟨wit167,rfl,?_⟩
  intro x
  change (wit167).eval (fill false 8 9 x)=target x
  simp only [wit167, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit168 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.var none)) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp168 : Sharp 168 := by
  refine ⟨wit168,rfl,?_⟩
  intro x
  change (wit168).eval (fill false 8 10 x)=target x
  simp only [wit168, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit169 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.var none) (.var (some 9)))))
theorem sharp169 : Sharp 169 := by
  refine ⟨wit169,rfl,?_⟩
  intro x
  change (wit169).eval (fill false 8 11 x)=target x
  simp only [wit169, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit171 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.var none))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp171 : Sharp 171 := by
  refine ⟨wit171,rfl,?_⟩
  intro x
  change (wit171).eval (fill false 8 13 x)=target x
  simp only [wit171, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit172 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.var none) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp172 : Sharp 172 := by
  refine ⟨wit172,rfl,?_⟩
  intro x
  change (wit172).eval (fill false 9 10 x)=target x
  simp only [wit172, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit173 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.var none) (.var (some 8)))))
theorem sharp173 : Sharp 173 := by
  refine ⟨wit173,rfl,?_⟩
  intro x
  change (wit173).eval (fill false 9 11 x)=target x
  simp only [wit173, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit174 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.var none) (.var (some 10))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp174 : Sharp 174 := by
  refine ⟨wit174,rfl,?_⟩
  intro x
  change (wit174).eval (fill false 9 12 x)=target x
  simp only [wit174, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit175 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.var none) (.var (some 7))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp175 : Sharp 175 := by
  refine ⟨wit175,rfl,?_⟩
  intro x
  change (wit175).eval (fill false 9 13 x)=target x
  simp only [wit175, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit176 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.var none) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp176 : Sharp 176 := by
  refine ⟨wit176,rfl,?_⟩
  intro x
  change (wit176).eval (fill false 10 11 x)=target x
  simp only [wit176, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit177 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.var none) (.var (some 9))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp177 : Sharp 177 := by
  refine ⟨wit177,rfl,?_⟩
  intro x
  change (wit177).eval (fill false 10 12 x)=target x
  simp only [wit177, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit178 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.var none) (.var (some 11))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp178 : Sharp 178 := by
  refine ⟨wit178,rfl,?_⟩
  intro x
  change (wit178).eval (fill false 10 13 x)=target x
  simp only [wit178, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit179 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.var none) (.var (some 7))))) (.conj (.var (some 4)) (.disj (.disj (.var (some 10)) (.var (some 11))) (.var (some 13))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp179 : Sharp 179 := by
  refine ⟨wit179,rfl,?_⟩
  intro x
  change (wit179).eval (fill false 11 12 x)=target x
  simp only [wit179, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
private def wit180 : Formula (Option EdgeInput) := (.disj (.disj (.disj (.disj (.disj (.disj (.conj (.var (some 0)) (.disj (.var (some 8)) (.var (some 10)))) (.conj (.var (some 1)) (.disj (.disj (.var (some 7)) (.var (some 9))) (.var (some 13))))) (.conj (.var (some 2)) (.disj (.var (some 8)) (.var (some 13))))) (.conj (.var (some 3)) (.disj (.disj (.var (some 7)) (.var (some 11))) (.var (some 12))))) (.conj (.var (some 4)) (.disj (.var none) (.var (some 10))))) (.conj (.var (some 5)) (.disj (.disj (.var (some 9)) (.var (some 10))) (.var (some 12))))) (.conj (.var (some 6)) (.disj (.disj (.var (some 8)) (.var (some 9))) (.var (some 11)))))
theorem sharp180 : Sharp 180 := by
  refine ⟨wit180,rfl,?_⟩
  intro x
  change (wit180).eval (fill false 11 13 x)=target x
  simp only [wit180, Formula.eval, fill, Bool.false_eq_true, ite_false, target, Bool.and_or_distrib_left]
  generalize h0 : x 0=b0, h1 : x 1=b1, h2 : x 2=b2, h3 : x 3=b3, h4 : x 4=b4, h5 : x 5=b5, h6 : x 6=b6, h7 : x 7=b7, h8 : x 8=b8, h9 : x 9=b9, h10 : x 10=b10, h11 : x 11=b11, h12 : x 12=b12, h13 : x 13=b13
  first | ac_rfl | (clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13; revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13; decide +kernel)
end PEqualNP.Research.Cached9815
