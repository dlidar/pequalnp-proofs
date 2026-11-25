import PEqualNP.Research.L_meta_1980_cap_boundary
import Mathlib.Data.List.Sublists

namespace PEqualNP.Research.PlaneFactorSupport
open PEqualNP.Research.CapBoundary
abbrev Vertex := Fin 26
abbrev Column := BitVec 468

def neighbours (v : Vertex) : Word := #[42082304, 17063936, 34127872, 1155072, 2310144, 4620288, 9240576, 18481152, 36962304, 6823936, 13647872, 27295744, 54591488, 523, 1046, 2092, 4184, 177, 354, 708, 1416, 2832, 5664, 3137, 6274, 4357][v.val]!

def adj (u v : Vertex) := (neighbours u).getLsbD v.val

theorem incidence_index : ∀ p l : Fin 13,
    (adj (Fin.castAdd 13 p) (Fin.natAdd 13 l) = decide (inc p l)) ∧
    (adj (Fin.natAdd 13 l) (Fin.castAdd 13 p) = decide (inc p l)) ∧
    adj (Fin.castAdd 13 p) (Fin.castAdd 13 l) = false ∧
    adj (Fin.natAdd 13 p) (Fin.natAdd 13 l) = false := by decide +kernel

theorem symmetric : ∀ i j, adj i j = adj j i := by decide +kernel

def selected (x : Word) (v : Vertex) := x.getLsbD v.val = true
def HasEdge (x : Word) := ∃ i j : Vertex, adj i j = true ∧ selected x i ∧ selected x j
def Touch (i : Vertex) (x : Word) := x &&& neighbours i ≠ 0
instance (i x) : Decidable (Touch i x) := by unfold Touch; infer_instance
def pin (v : Vertex) (x : Word) : Word := x ||| ((1 : Word) <<< v.val)
def ignores (f : Word → Prop) (i : Vertex) := ∀ x, f (pin i x) ↔ f x
def projected (i : Vertex) (x : Word) := HasEdge x ∨ Touch i x

theorem touch_iff (i : Vertex) (x : Word) :
    Touch i x ↔ ∃ j, adj i j = true ∧ selected x j := by
  unfold Touch adj selected
  constructor
  · contrapose!
    intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    specialize h ⟨k,hk⟩
    simp_all; grind
  · rintro ⟨j,h₁,h₂⟩ he
    have ht := congrArg (fun y : Word => y.getLsbD j.val) he
    simp only [BitVec.getLsbD_and, h₁, h₂] at ht
    have hz : ∀ k : Vertex, (0 : Word).getLsbD k.val = false := by decide +kernel
    rw [hz j] at ht
    contradiction

theorem selected_pin (i j : Vertex) (x : Word) :
    selected (pin i x) j ↔ selected x j ∨ j = i := by
  have unit : ∀ a b : Vertex, ((1 : Word) <<< a.val).getLsbD b.val = decide (b = a) := by decide +kernel
  simp only [selected, pin, BitVec.getLsbD_or, unit, Bool.or_eq_true, decide_eq_true_eq]

theorem edge_pin (i : Vertex) (x : Word) :
    HasEdge (pin i x) ↔ HasEdge x ∨ Touch i x := by
  have irrefl : ∀ j : Vertex, adj j j = false := by decide +kernel
  simp only [HasEdge, selected_pin, touch_iff]
  constructor
  · rintro ⟨a,b,h,(ha|rfl),(hb|rfl)⟩
    · exact Or.inl ⟨_,_,h,ha,hb⟩
    · exact Or.inr ⟨a,(symmetric _ _).trans h,ha⟩
    · exact Or.inr ⟨b,h,hb⟩
    · simp_all
  · rintro (⟨a,b,h,ha,hb⟩|⟨b,h,hb⟩)
    · exact ⟨a,b,h,Or.inl ha,Or.inl hb⟩
    · exact ⟨i,b,h,Or.inr rfl,Or.inl hb⟩

theorem projection_ignores (i) : ignores (projected i) i := by
  intro x
  change (HasEdge _ ∨ _) ↔ (HasEdge _ ∨ _)
  rw [←edge_pin, ←edge_pin]
  simp [pin, BitVec.or_assoc]

theorem projection_minimal (f : Word → Prop) (i : Vertex) (hi : ignores f i)
    (hf : ∀ x, HasEdge x → f x) (x : Word) (h : projected i x) : f x :=
  (hi x).mp (hf _ ((edge_pin i x).mpr h))

def sample (k : Fin 468) : Word := boundary.toArray[k.val]!

theorem sample_mem (k : Fin 468) : sample k ∈ boundary := by
  have hk : k.val < boundary.length := by rw [sample_count.1]; exact k.isLt
  simp [sample, getElem!_pos, hk]

def column (i : Vertex) : Column := #[666850634718150829742524603844685763704564498713531865570875577886835539598883468487693929895306840518400018407787118101382098667932403892224, 351673631349928528518246969579174266739459641198554705605646443150953001119855869356247761650993915469004908301170291068671016808611328032768, 666787253874075934036718159235734733229535864898373306708647646013601946406053765732309279017134027026889605629629895587504446602290804293616, 288418421205207403615182466347005911790636340967519983475820582084967921696281464229191341247476098763686061543509244780016702113687342940159, 485679722848640499970850650644114530383790217516376092922409178559082309417447532816259954864835648126387847422634090084831745654782334598927, 513183027611336165732027152872026616390382172993293337620612575368197301280341691639734363756874017540729827866621920813581885582283877906686, 666877395372615165352133889028145045232152696950027924924646256332261838357184774975558956476399812589553732256829594440416047711032872265709, 380968156307066598569340519068278021871267472956660559151025840602235338541713740420442846718101997547561244670954550076679253530428193085435, 750237070991985366878749869218070640342159431406207078447355909393804110854385955763055234853102354701050559857636399645083489049377146560479, 571417346184666992993235548298572216150861381969831607389961346852493103788678527297439481454170665165504879420115249639788545524843639996415, 756189721177973904127294961129206897531285205948756329738860845293876326183715587632767573198120010906534017650803678062657182964973427310335, 761400540022342172347857807061915063172081801413540544165987909302911966933961015383591233394349584232208746725528750025627496118674121489847, 761773500005913346762315015472792719605861707307978888055388560119159489942454627600293965666465023518807959000464966920553653394248027728767, 762145642166990290864647761179972242614403843423934852075238459986516854051285913368716079090054116087482992234247418337298695817282952626175, 762145642166990290864647761179969894071821069590967703199612484861294842740390809583131381565690028840894963886640910197800940613827054010367, 762145642166990290862065511301887682567330695949433434365566156790872856871153060579979957304138905800392042826219898224171140140714094823247, 762145642166816999011347460090859327183964924975396794687404928762267181556797301220974105866135058293137739075355913979573184413042233711858, 762145551312323043128027363273504939265978351315489362177504390292411942450225846800068415504945420870622940026664046830410859899108638851071, 761773591572983371709029356039270205363679777592082538698648980967167164905994111440016969711839911484839791193025116186204262706846041374719, 667246761489657659298646075340100964045027561674851523022329847807534831532126973914652775379738774880798171783101662647334283569002362730527, 473727220961913905316619498499016283393857387999960985011641465744293629661205085688921568438232607159232442601010668277249788076618556631332, 276465966449261759337486647236563712559027246037389208481640813610728100173921627292057866654444623483134787643092862787761011879929631318776, 249156158878063573075879191479258976972989751934620126253162706769637161397584977810722664666662383619460991172600301703915095106098714302337, 101995775407819646413236763385680009458842893702359373003016472270923700347075549011646920807727334586918928781816120470267380698812155691007, 410577493289524553368660863130650639485752392239281422035164673757756532710563438304128678777473417102963982185870270322939799277312792592383, 107639691473577234531535598483015306546958694380819678388583422242937428763809759794394730711058967591201133097100172852125584387437840302079][i.val]!

private theorem col0 : ∀ k : Fin 468, (column 0).getLsbD k.val = decide (Touch 0 (sample k)) := by unfold Touch; decide +kernel
private theorem col1 : ∀ k : Fin 468, (column 1).getLsbD k.val = decide (Touch 1 (sample k)) := by unfold Touch; decide +kernel
private theorem col2 : ∀ k : Fin 468, (column 2).getLsbD k.val = decide (Touch 2 (sample k)) := by unfold Touch; decide +kernel
private theorem col3 : ∀ k : Fin 468, (column 3).getLsbD k.val = decide (Touch 3 (sample k)) := by unfold Touch; decide +kernel
private theorem col4 : ∀ k : Fin 468, (column 4).getLsbD k.val = decide (Touch 4 (sample k)) := by unfold Touch; decide +kernel
private theorem col5 : ∀ k : Fin 468, (column 5).getLsbD k.val = decide (Touch 5 (sample k)) := by unfold Touch; decide +kernel
private theorem col6 : ∀ k : Fin 468, (column 6).getLsbD k.val = decide (Touch 6 (sample k)) := by unfold Touch; decide +kernel
private theorem col7 : ∀ k : Fin 468, (column 7).getLsbD k.val = decide (Touch 7 (sample k)) := by unfold Touch; decide +kernel
private theorem col8 : ∀ k : Fin 468, (column 8).getLsbD k.val = decide (Touch 8 (sample k)) := by unfold Touch; decide +kernel
private theorem col9 : ∀ k : Fin 468, (column 9).getLsbD k.val = decide (Touch 9 (sample k)) := by unfold Touch; decide +kernel
private theorem col10 : ∀ k : Fin 468, (column 10).getLsbD k.val = decide (Touch 10 (sample k)) := by unfold Touch; decide +kernel
private theorem col11 : ∀ k : Fin 468, (column 11).getLsbD k.val = decide (Touch 11 (sample k)) := by unfold Touch; decide +kernel
private theorem col12 : ∀ k : Fin 468, (column 12).getLsbD k.val = decide (Touch 12 (sample k)) := by unfold Touch; decide +kernel
private theorem col13 : ∀ k : Fin 468, (column 13).getLsbD k.val = decide (Touch 13 (sample k)) := by unfold Touch; decide +kernel
private theorem col14 : ∀ k : Fin 468, (column 14).getLsbD k.val = decide (Touch 14 (sample k)) := by unfold Touch; decide +kernel
private theorem col15 : ∀ k : Fin 468, (column 15).getLsbD k.val = decide (Touch 15 (sample k)) := by unfold Touch; decide +kernel
private theorem col16 : ∀ k : Fin 468, (column 16).getLsbD k.val = decide (Touch 16 (sample k)) := by unfold Touch; decide +kernel
private theorem col17 : ∀ k : Fin 468, (column 17).getLsbD k.val = decide (Touch 17 (sample k)) := by unfold Touch; decide +kernel
private theorem col18 : ∀ k : Fin 468, (column 18).getLsbD k.val = decide (Touch 18 (sample k)) := by unfold Touch; decide +kernel
private theorem col19 : ∀ k : Fin 468, (column 19).getLsbD k.val = decide (Touch 19 (sample k)) := by unfold Touch; decide +kernel
private theorem col20 : ∀ k : Fin 468, (column 20).getLsbD k.val = decide (Touch 20 (sample k)) := by unfold Touch; decide +kernel
private theorem col21 : ∀ k : Fin 468, (column 21).getLsbD k.val = decide (Touch 21 (sample k)) := by unfold Touch; decide +kernel
private theorem col22 : ∀ k : Fin 468, (column 22).getLsbD k.val = decide (Touch 22 (sample k)) := by unfold Touch; decide +kernel
private theorem col23 : ∀ k : Fin 468, (column 23).getLsbD k.val = decide (Touch 23 (sample k)) := by unfold Touch; decide +kernel
private theorem col24 : ∀ k : Fin 468, (column 24).getLsbD k.val = decide (Touch 24 (sample k)) := by unfold Touch; decide +kernel
private theorem col25 : ∀ k : Fin 468, (column 25).getLsbD k.val = decide (Touch 25 (sample k)) := by unfold Touch; decide +kernel
theorem column_spec (i : Vertex) (k : Fin 468) : (column i).getLsbD k.val = decide (Touch i (sample k)) := by
  fin_cases i <;> first | exact col0 k | exact col1 k | exact col2 k | exact col3 k | exact col4 k | exact col5 k | exact col6 k | exact col7 k | exact col8 k | exact col9 k | exact col10 k | exact col11 k | exact col12 k | exact col13 k | exact col14 k | exact col15 k | exact col16 k | exact col17 k | exact col18 k | exact col19 k | exact col20 k | exact col21 k | exact col22 k | exact col23 k | exact col24 k | exact col25 k

def common : List Vertex → Column
  | [] => BitVec.allOnes 468
  | i :: rest => column i &&& common rest

theorem common_spec (vs : List Vertex) (k : Fin 468) :
    (common vs).getLsbD k.val = true ↔ ∀ i ∈ vs, Touch i (sample k) := by
  induction vs with
  | nil => simp only [common, BitVec.getLsbD_allOnes, k.isLt, decide_true, List.not_mem_nil, false_implies, implies_true]
  | cons i vs ih => simp only [common, BitVec.getLsbD_and, Bool.and_eq_true, column_spec, decide_eq_true_eq, ih, List.forall_mem_cons]

theorem common_error (vs : List Vertex) (hn : common vs ≠ 0)
    (F : Vertex → Word → Prop) (hi : ∀ i ∈ vs, ignores (F i) i)
    (hp : ∀ i ∈ vs, ∀ x, HasEdge x → F i x) :
    ∃ x, Generic x ∧ ∀ i ∈ vs, F i x := by
  have ex : ∃ k : Fin 468, (common vs).getLsbD k.val = true := by
    by_contra! h
    apply hn
    apply BitVec.eq_of_getLsbD_eq
    intro n hn'
    simpa using h ⟨n,hn'⟩
  obtain ⟨k,hk⟩ := ex
  exact ⟨_,boundary_checked _ (sample_mem k),fun i hm =>
    projection_minimal _ i (hi i hm) (hp i hm) _ (Or.inr ((common_spec vs k).mp hk i hm))⟩

def combinations (n : Nat) := (List.finRange 26).sublistsLen n
def exceptions (n : Nat) := (combinations n).filter (fun vs => common vs == 0)

def star (i : Vertex) : List Vertex := (List.finRange 26).filter (fun j => i == j || adj i j)

theorem star_exact (i : Vertex) (x : Word) :
    (∀ j ∈ star i, projected j x) ↔ HasEdge x := by
  constructor
  · intro h
    by_contra hn
    have ht : Touch i x := (h i (by simp [star])).resolve_left hn
    obtain ⟨j,ha,hj⟩ := (touch_iff i x).mp ht
    have ht' := (h j (by simp [star,ha])).resolve_left hn
    obtain ⟨k,hk,hs⟩ := (touch_iff j x).mp ht'
    exact hn ⟨j,k,hk,hj,hs⟩
  · exact fun he _ _ => Or.inl he

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
theorem no_small : ∀ n : Fin 5, exceptions n.val = [] := by decide +kernel

def minimalStars : List (List Vertex) := [[12, 16, 22, 24, 25], [11, 15, 21, 23, 24], [10, 14, 20, 22, 23], [9, 13, 19, 21, 22], [8, 18, 20, 21, 25], [7, 17, 19, 20, 24], [6, 16, 18, 19, 23], [5, 15, 17, 18, 22], [5, 9, 10, 12, 22], [4, 14, 16, 17, 21], [4, 8, 9, 11, 21], [3, 13, 15, 16, 20], [3, 7, 8, 10, 20], [3, 4, 6, 12, 16], [2, 14, 15, 19, 25], [2, 6, 7, 9, 19], [2, 3, 5, 11, 15], [1, 13, 14, 18, 24], [1, 7, 11, 12, 24], [1, 5, 6, 8, 18], [1, 2, 4, 10, 14], [0, 13, 17, 23, 25], [0, 6, 10, 11, 23], [0, 4, 5, 7, 17], [0, 2, 8, 12, 25], [0, 1, 3, 9, 13]]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
theorem five_cases : exceptions 5 = minimalStars := by decide +kernel

theorem stars_listed : ∀ s ∈ minimalStars, ∃ v : Vertex, s = star v := by decide +kernel

theorem small_error (n : Fin 5) (vs : List Vertex) (hv : vs ∈ combinations n.val)
    (F : Vertex → Word → Prop) (hi : ∀ i ∈ vs, ignores (F i) i)
    (hp : ∀ i ∈ vs, ∀ x, HasEdge x → F i x) :
    ∃ x, Generic x ∧ ∀ i ∈ vs, F i x := by
  apply common_error vs _ F hi hp
  intro hz
  have hm : vs ∈ exceptions n.val := List.mem_filter.mpr ⟨hv, by simp [hz]⟩
  simp [no_small n] at hm

theorem five_omissions (vs : List Vertex) (hv : vs ∈ combinations 5)
    (F : Vertex → Word → Prop) (hi : ∀ i ∈ vs, ignores (F i) i)
    (hp : ∀ i ∈ vs, ∀ x, HasEdge x → F i x)
    (hn : ∀ x, Generic x → ¬ ∀ i ∈ vs, F i x) :
    ∃ v, vs = star v := by
  by_cases hz : common vs = 0
  · apply stars_listed
    rw [← five_cases]
    exact List.mem_filter.mpr ⟨hv, by simp [hz]⟩
  · obtain ⟨x,hx,h⟩ := common_error vs hz F hi hp
    exact (hn x hx h).elim

def otherColumns (center omitted : Vertex) := common ((star center).erase omitted)

set_option maxHeartbeats 8000000 in
theorem exclusive_counts : ∀ c : Vertex, ∀ i ∈ star c,
    (otherColumns c i).cpop.toNat = (if i = c then 126 else 45) := by decide +kernel

set_option maxHeartbeats 8000000 in
theorem exclusive_flip_column : ∀ c : Vertex, ∀ i ∈ star c, ∀ j : Vertex,
    j ≠ i → otherColumns c i &&& column j ≠ 0 := by decide +kernel

theorem complete_remaining_support (c i : Vertex) (hi : i ∈ star c) (F : Vertex → Word → Prop)
    (homit : ∀ k ∈ star c, ignores (F k) k)
    (hpos : ∀ k ∈ star c, ∀ x, HasEdge x → F k x)
    (hneg : ∀ x, Generic x → ¬ ∀ k ∈ star c, F k x) :
    ∀ j, j ≠ i → ¬ ignores (F i) j := by
  intro j hji hnew
  have hz := exclusive_flip_column c i hi j hji
  have ex : ∃ k : Fin 468, (otherColumns c i &&& column j).getLsbD k.val = true := by
    by_contra! h
    apply hz
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    simpa using h ⟨n,hn⟩
  obtain ⟨k,hk⟩ := ex
  simp only [BitVec.getLsbD_and, Bool.and_eq_true, column_spec, decide_eq_true_eq] at hk
  apply hneg _ (boundary_checked _ (sample_mem k))
  intro v hv
  by_cases hvi : v = i
  · subst v
    exact projection_minimal _ j hnew (hpos i hi) _ (Or.inr hk.2)
  · have hm : v ∈ (star c).erase i := (List.mem_erase_of_ne hvi).mpr hv
    exact projection_minimal _ v (homit v hv) (hpos v hv) _
      (Or.inr ((common_spec _ k).mp hk.1 v hm))

/-- The raw input activating exactly the two ends of an incidence. -/
def pair (u v : Vertex) := pin u (pin v 0)

theorem pair_bits (u v w : Vertex) : selected (pair u v) w ↔ w = u ∨ w = v := by
  simp only [pair,selected_pin]
  have hz : ¬ selected 0 w := by simp [selected]
  tauto

theorem covers_from_tests (f : Word → Prop)
    (hm : ∀ x y, below x y = true → f x → f y)
    (hp : ∀ u v, adj u v = true → f (pair u v)) :
    ∀ x, HasEdge x → f x := by
  rintro x ⟨u,v,ha,hu,hv⟩
  apply hm _ _ _ (hp u v ha)
  apply (bits_iff _ _).mpr
  intro n hn h
  rcases (pair_bits u v ⟨n,hn⟩).mp h with h' | h'
  · exact (show selected x ⟨n,hn⟩ from h' ▸ hu)
  · exact (show selected x ⟨n,hn⟩ from h' ▸ hv)

theorem four_factor_obstruction (F : Fin 4 → Word → Prop) (missing : Fin 4 → Vertex)
    (hi : ∀ t, ignores (F t) (missing t))
    (hm : ∀ t x y, below x y = true → F t x → F t y)
    (hp : ∀ t u v, adj u v = true → F t (pair u v)) :
    ∃ x, Generic x ∧ ∀ t, F t x := by
  classical
  let used := Finset.univ.image missing
  let vs : List Vertex := (List.finRange 26).filter (fun i => i ∈ used)
  have hset : vs.toFinset = used := by ext; simp [vs]
  have hlen : vs.length ≤ 4 := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 26).filter _), hset]
    simpa [used] using (Finset.card_image_le (f := missing) (s := Finset.univ))
  let n : Fin 5 := ⟨vs.length,by omega⟩
  have hvs : vs ∈ combinations n.val :=
    List.mem_sublistsLen.mpr ⟨List.filter_sublist, rfl⟩
  let G (i : Vertex) (x : Word) := ∀ t, missing t = i → F t x
  have hign (i) : ignores (G i) i := by
    intro x
    constructor
    · intro h t ht; subst i; exact (hi t x).mp (h t rfl)
    · intro h t ht; subst i; exact (hi t x).mpr (h t rfl)
  obtain ⟨x,hg,h⟩ := small_error n vs hvs G (fun i _ => hign i)
    (fun _ _ y hy t _ => covers_from_tests _ (hm t) (hp t) y hy)
  exact ⟨x,hg,fun t => h (missing t) (by simp [vs,used]) t rfl⟩

theorem edge_incidence (x : Word) :
    HasEdge x ↔ ∃ p ∈ pts x, ∃ l ∈ lines x, inc p l := by
  have part : ∀ i : Vertex, (∃ p : V, i = Fin.castAdd 13 p) ∨ (∃ l : V, i = Fin.natAdd 13 l) := by decide +kernel
  have point (p : V) : selected x (Fin.castAdd 13 p) ↔ p ∈ pts x := by simp [selected,pts]
  have line (l : V) : selected x (Fin.natAdd 13 l) ↔ l ∈ lines x := by simp [selected,lines,Nat.add_comm]
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    rcases part u with ⟨p,rfl⟩|⟨l,rfl⟩ <;> rcases part v with ⟨p',rfl⟩|⟨l',rfl⟩
    · rw [(incidence_index _ _).2.2.1] at h; contradiction
    · exact ⟨p,(point p).mp hu,l',(line l').mp hv, of_decide_eq_true ((incidence_index p l').1.symm.trans h)⟩
    · exact ⟨p',(point p').mp hv,l,(line l).mp hu, of_decide_eq_true ((incidence_index p' l).2.1.symm.trans h)⟩
    · rw [(incidence_index _ _).2.2.2] at h; contradiction
  · rintro ⟨p,hp,l,hl,he⟩
    exact ⟨_,_,(incidence_index p l).1.trans (decide_eq_true he),(point p).mpr hp,(line l).mpr hl⟩

theorem star_rejects_generic (c : Vertex) (x : Word) (hx : Generic x) :
    ¬ ∀ i ∈ star c, projected i x := by
  intro h
  obtain ⟨p,hp,l,hl,hi⟩ := (edge_incidence x).mp ((star_exact c x).mp h)
  exact hx.1 p hp l hl hi

def pairCount (i j : Vertex) : Nat :=
  if i = j then 342 else if adj i j then 216 else
  if (i.val < 13 ↔ j.val < 13) then 243 else 264

set_option maxHeartbeats 8000000 in
theorem two_omission_counts : ∀ i j, (column i &&& column j).cpop.toNat = pairCount i j := by decide +kernel

theorem projection_pattern (vs : List Vertex) (k : Fin 468) :
    (∀ i ∈ vs, projected i (sample k)) ↔ (common vs).getLsbD k.val = true := by
  rw [common_spec]
  have hn : ¬ HasEdge (sample k) := by
    intro h
    obtain ⟨p,hp,l,hl,he⟩ := (edge_incidence _).mp h
    exact (boundary_checked _ (sample_mem k)).1 p hp l hl he
  simp [projected, hn]

end PEqualNP.Research.PlaneFactorSupport
