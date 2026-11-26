import FormulaBound
namespace PEqualNP.Research.Triangle17393
open Finset PEqualNP.Research.TripleFormulaMass
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
def rename {I J} (g : I → J) : Formula I → Formula J
  | .var i => .var (g i)
  | .conj f h => .conj (rename g f) (rename g h)
  | .disj f h => .disj (rename g f) (rename g h)
theorem renamed_leaves {I J} (g : I → J) (f : Formula I) : (rename g f).leaves=f.leaves := by
  induction f <;> simp_all [rename,Formula.leaves]
theorem renamed_eval {I J} (g : I → J) (f : Formula I) (x : J → Bool) :
    (rename g f).eval x=f.eval (fun i => x (g i)) := by
  induction f <;> simp_all [rename,Formula.eval]
def term (t : Fin 10) : Finset (Fin 10) :=
  (#[{0,1,4},{0,2,5},{0,3,6},{1,2,7},{1,3,8},{2,3,9},{4,5,7},{4,6,8},{5,6,9},{7,8,9}] : Array (Finset (Fin 10)))[t.val]!
theorem terms (x : Fin 10 → Bool) : triangle x=true ↔ ∃ t,∀ i ∈ term t,x i=true := by
  simp only [triangle,Bool.or_eq_true,Bool.and_eq_true]
  constructor
  · intro h
    rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h
    · exact ⟨0,by change ∀ i ∈ ({0,1,4} : Finset (Fin 10)), x i = true; simp [h.1.1,h.1.2,h.2]⟩
    · exact ⟨1,by change ∀ i ∈ ({0,2,5} : Finset (Fin 10)), x i = true; simp [h.1.1,h.1.2,h.2]⟩
    · exact ⟨2,by change ∀ i ∈ ({0,3,6} : Finset (Fin 10)), x i = true; simp [h.1.1,h.1.2,h.2]⟩
    · exact ⟨3,by change ∀ i ∈ ({1,2,7} : Finset (Fin 10)), x i = true; simp [h.1.1,h.1.2,h.2]⟩
    · exact ⟨4,by change ∀ i ∈ ({1,3,8} : Finset (Fin 10)), x i = true; simp [h.1.1,h.1.2,h.2]⟩
    · exact ⟨5,by change ∀ i ∈ ({2,3,9} : Finset (Fin 10)), x i = true; simp [h.1.1,h.1.2,h.2]⟩
    · exact ⟨6,by change ∀ i ∈ ({4,5,7} : Finset (Fin 10)), x i = true; simp [h.1.1,h.1.2,h.2]⟩
    · exact ⟨7,by change ∀ i ∈ ({4,6,8} : Finset (Fin 10)), x i = true; simp [h.1.1,h.1.2,h.2]⟩
    · exact ⟨8,by change ∀ i ∈ ({5,6,9} : Finset (Fin 10)), x i = true; simp [h.1.1,h.1.2,h.2]⟩
    · exact ⟨9,by change ∀ i ∈ ({7,8,9} : Finset (Fin 10)), x i = true; simp [h.1.1,h.1.2,h.2]⟩
  · rintro ⟨t,h⟩
    fin_cases t
    · change ∀ i ∈ ({0,1,4} : Finset (Fin 10)), x i = true at h
      simp at h
      exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨h.1,h.2.1⟩,h.2.2⟩)))))))))
    · change ∀ i ∈ ({0,2,5} : Finset (Fin 10)), x i = true at h
      simp at h
      exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨h.1,h.2.1⟩,h.2.2⟩)))))))))
    · change ∀ i ∈ ({0,3,6} : Finset (Fin 10)), x i = true at h
      simp at h
      exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨h.1,h.2.1⟩,h.2.2⟩))))))))
    · change ∀ i ∈ ({1,2,7} : Finset (Fin 10)), x i = true at h
      simp at h
      exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨h.1,h.2.1⟩,h.2.2⟩)))))))
    · change ∀ i ∈ ({1,3,8} : Finset (Fin 10)), x i = true at h
      simp at h
      exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨h.1,h.2.1⟩,h.2.2⟩))))))
    · change ∀ i ∈ ({2,3,9} : Finset (Fin 10)), x i = true at h
      simp at h
      exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨h.1,h.2.1⟩,h.2.2⟩)))))
    · change ∀ i ∈ ({4,5,7} : Finset (Fin 10)), x i = true at h
      simp at h
      exact (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨h.1,h.2.1⟩,h.2.2⟩))))
    · change ∀ i ∈ ({4,6,8} : Finset (Fin 10)), x i = true at h
      simp at h
      exact (Or.inl (Or.inl (Or.inr ⟨⟨h.1,h.2.1⟩,h.2.2⟩)))
    · change ∀ i ∈ ({5,6,9} : Finset (Fin 10)), x i = true at h
      simp at h
      exact (Or.inl (Or.inr ⟨⟨h.1,h.2.1⟩,h.2.2⟩))
    · change ∀ i ∈ ({7,8,9} : Finset (Fin 10)), x i = true at h
      simp at h
      exact (Or.inr ⟨⟨h.1,h.2.1⟩,h.2.2⟩)
def permTable : Array Nat := #[654820258320,654820258320,590394765600,582310236960,654766597440,590341104720,582256576080,654820258320,650777994000,521927008560,645729104385,645729104385,576758034690,568673506050,632038712580,645729104385,641686840065,563067642885,554983114245,503744700675,452452626465,447907049490,452452626465,310971535410,452452626465,245485756500,383984869425,240940179525,374893715475,104004665445,436283573025,431737996050,302887010610,436283573025,436283573025,371858080305,217189910100,362766926355,212644333125,83793347685,645639735105,632003004180,645639735105,641597470785,645639735105,576650778450,568566249810,563014047525,554929518885,503619557475,452364239985,452364239985,245451030900,383896482945,447800776050,452364239985,310865261970,240887566965,374769555075,103952052885,436210911345,436210911345,371785418625,217170909300,431647447410,302796461970,436210911345,362658490755,212607445365,83756459925,425358165015,425358165015,232081686855,352344831000,425340278055,232063799895,352309057080,425358165015,279313610025,86037131865,413215639575,413215639575,344244569880,207812368455,413197752615,344208795960,207794481495,275255613225,413215639575,69852342105,26661699975,22116123000,26661699975,14534907015,22080349080,26643813015,14517020055,17552659065,5425866105,26661699975]
def perm (a b i : Fin 10) : Fin 10 := Fin.ofNat 10 (((permTable[a.val*10+b.val]! >>> (4*i.val)) % 16))
def rep (a b : Fin 10) : Fin 10 := (#[0,1,1,1,1,1,1,7,7,7,1,0,1,1,1,7,7,1,1,7,1,1,0,1,7,1,7,1,7,1,1,1,1,0,7,7,1,7,1,1,1,1,7,7,0,1,1,1,1,7,1,7,1,7,1,0,1,1,7,1,1,7,7,1,1,1,0,7,1,1,7,1,1,7,1,1,7,0,1,1,7,1,7,1,1,7,1,1,0,1,7,7,1,1,7,1,1,1,1,0] : Array (Fin 10))[a.val*10+b.val]!
theorem coordinates : ∀ a b,perm a b a=0 ∧ perm a b b=rep a b ∧ (rep a b=0 ∨ rep a b=1 ∨ rep a b=7) := by decide +kernel
def termImageTable : Array Nat := #[654820258320,654820258320,650792743425,650289303585,641083073040,637055558145,636552118305,654820258320,654568538400,646513508610,590395610160,590395610160,521943516465,521440076625,383384688480,590395610160,590143890240,314932594785,314429154945,453239702850,582339597315,517915018515,582339597315,509356548885,582339597315,363246130950,578060362500,298821552150,449211204900,290263082520,581584375875,517159797075,509104767285,581584375875,581584375875,577556860980,361735749750,448707703380,297311170950,289256141160,571794220080,378520483680,571794220080,571542500160,571794220080,498763064625,498259624785,305489328225,304985888385,425480189250,559712658435,559712658435,354356377350,555433423620,490709017875,559712658435,482150548245,285352736790,417426142500,276794267160,558705840195,558705840195,554678325300,352594399350,489702199635,481647169845,558705840195,416671044180,283590758790,275535729000,173165250915,173165250915,161082706230,104461437300,168586189155,156503644470,95303313780,173165250915,31178561925,19096017240,172158371475,172158371475,103706277780,159320667030,167579309715,94548154260,154741605270,30675122325,172158371475,17837417880,143965767225,79541188425,143965767225,143210607465,70383064905,139386705465,138631545705,10537547865,9782388105,143965767225]
def termImage (a b i : Fin 10) : Fin 10 := Fin.ofNat 10 (((termImageTable[a.val*10+b.val]! >>> (4*i.val)) % 16))
def termPreTable : Array Nat := #[654820258320,654820258320,650792743425,646513508610,641083073040,637055558145,632776323330,654820258320,654568538400,650289303585,590395610160,590395610160,582339597315,578060362500,571794220080,590395610160,590143890240,559712658435,555433423620,581584375875,521943516465,517915018515,521943516465,509356548885,521943516465,498763064625,521440076625,490709017875,517159797075,482150548245,453239702850,449211204900,444931970085,453239702850,453239702850,452987982930,425480189250,448707703380,417426142500,413146907685,383384688480,378520483680,383384688480,383132968560,383384688480,363246130950,358966896135,354356377350,350077142535,361735749750,314932594785,314932594785,305489328225,314429154945,298821552150,314932594785,290263082520,285352736790,297311170950,276794267160,246228781170,246228781170,245977061250,232206452850,230117738535,225838503720,246228781170,228859077255,212069861415,207790626600,173165250915,173165250915,168586189155,172158371475,161082706230,156503644470,159320667030,173165250915,143965767225,139386705465,104461437300,104461437300,103706277780,95303313780,92378892615,90868573335,83220769095,79541188425,104461437300,70383064905,31178561925,30675122325,31178561925,26599500165,17837417880,19096017240,14516955480,10537547865,5958486105,31178561925]
def termPre (a b i : Fin 10) : Fin 10 := Fin.ofNat 10 (((termPreTable[a.val*10+b.val]! >>> (4*i.val)) % 16))
theorem images : ∀ a b t,∃ u,(term t).image (perm a b)=term u := by
  have h : ∀ a b t,(term t).image (perm a b)=term (termImage a b t) := by decide +kernel
  exact fun a b t => ⟨_,h a b t⟩
theorem preimages : ∀ a b u,∃ t,(term t).image (perm a b)=term u := by
  have h : ∀ a b u,(term (termPre a b u)).image (perm a b)=term u := by decide +kernel
  exact fun a b u => ⟨_,h a b u⟩
theorem perm_ok (a b : Fin 10) (x : Fin 10 → Bool) : triangle (fun i => x (perm a b i))=triangle x := by
  apply Bool.eq_iff_iff.mpr
  rw [terms,terms]
  constructor
  · rintro ⟨t,h⟩
    obtain ⟨u,e⟩ := images a b t
    refine ⟨u,?_⟩
    intro i hi
    rw [←e] at hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact h j hj
  · rintro ⟨u,h⟩
    obtain ⟨t,e⟩ := preimages a b u
    exact ⟨t,fun j hj => h _ (e ▸ mem_image_of_mem _ hj)⟩
end PEqualNP.Research.Triangle17393
