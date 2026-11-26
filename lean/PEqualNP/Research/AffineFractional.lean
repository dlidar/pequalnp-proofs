import PEqualNP.Research.AffineMatrix

namespace PEqualNP.Research.AffineFractional
open PEqualNP.Research.AffineRectangleCover
def boxes : Array (Nat × Nat) := #[(5893,816071234), (10794,826803364), (12595233,277616786), (20596,814778696), (25234176,36462661), (25190466,285782277), (328241,683935940), (9417,824251024), (4751908,151784490), (17961504,38323338), (25170968,338727106), (17843332,269607434), (101396,607395944), (655459,696783240), (9961993,136988806), (18834,810688801), (106755,541864468), (8487016,135829588), (12976704,193077441), (3416160,42044692), (10503712,327204964), (17836049,341909892), (533808,545592358), (3149064,270746676), (6300678,360973872), (202761,610812112), (21635080,84481155), (295110,688956176), (51777,554313804), (18907186,138712332), (10486097,413274436), (17307654,68961545), (213510,545841193), (16974032,136425609), (164632,677512290), (25952416,185876866), (9748496,68331782), (6832320,50534921), (3244672,174098984), (20974688,319882440), (8397460,270837795), (3166211,348275464), (19465217,69554700), (602688,581438081), (6298128,273026121), (18887040,308548353), (12601356,353896545), (4532352,38086801), (405522,616596865), (16793897,273240134), (345408,579936836), (590220,674316833), (5408770,71967800), (70818,538235032), (25329669,220733762), (5308485,143206936), (659072,589447336), (20972163,423895688), (561297,539367690), (1093644,69766674), (394284,553763922), (1442177,138633490), (574474,621941284), (9064704,42619139), (18383168,171443972), (1050194,276997260), (3801108,211879208), (12617088,35008562), (6488352,180424816), (10616970,151179313), (9443520,305269136), (17081856,50636294), (13172754,211030177), (2099365,285559064), (188576,591434018), (5268224,315105826), (21233940,135603267), (18153482,206619268), (811013,629213954), (1656864,35211308), (4198730,270145041), (10817540,75810897), (19286016,121717057), (141636,539567377), (4342801,75706442), (6586377,222431824), (301344,575931728), (9437478,412631344), (8653827,84304020), (2187288,71407653), (788568,538119301), (2884354,143017477), (2266176,35820632), (11053056,119802148), (283272,541248003), (9643008,111190192), (6034432,110233218), (18874956,421561921), (5243064,407963810), (21090304,106435144)]
def hits (p : P) (l : L) (b : Nat × Nat) : Bool := b.1.testBit p.val && b.2.testBit l.val
def multiplicity (p : P) (l : L) := boxes.countP (hits p l)
set_option maxRecDepth 80000
set_option maxHeartbeats 8000000
theorem box_count : boxes.size = 100 := rfl
private theorem row0 : ∀ l : L, multiplicity 0 l = if zero 0 l then 9 else 0 := by decide +kernel
private theorem row1 : ∀ l : L, multiplicity 1 l = if zero 1 l then 9 else 0 := by decide +kernel
private theorem row2 : ∀ l : L, multiplicity 2 l = if zero 2 l then 9 else 0 := by decide +kernel
private theorem row3 : ∀ l : L, multiplicity 3 l = if zero 3 l then 9 else 0 := by decide +kernel
private theorem row4 : ∀ l : L, multiplicity 4 l = if zero 4 l then 9 else 0 := by decide +kernel
private theorem row5 : ∀ l : L, multiplicity 5 l = if zero 5 l then 9 else 0 := by decide +kernel
private theorem row6 : ∀ l : L, multiplicity 6 l = if zero 6 l then 9 else 0 := by decide +kernel
private theorem row7 : ∀ l : L, multiplicity 7 l = if zero 7 l then 9 else 0 := by decide +kernel
private theorem row8 : ∀ l : L, multiplicity 8 l = if zero 8 l then 9 else 0 := by decide +kernel
private theorem row9 : ∀ l : L, multiplicity 9 l = if zero 9 l then 9 else 0 := by decide +kernel
private theorem row10 : ∀ l : L, multiplicity 10 l = if zero 10 l then 9 else 0 := by decide +kernel
private theorem row11 : ∀ l : L, multiplicity 11 l = if zero 11 l then 9 else 0 := by decide +kernel
private theorem row12 : ∀ l : L, multiplicity 12 l = if zero 12 l then 9 else 0 := by decide +kernel
private theorem row13 : ∀ l : L, multiplicity 13 l = if zero 13 l then 9 else 0 := by decide +kernel
private theorem row14 : ∀ l : L, multiplicity 14 l = if zero 14 l then 9 else 0 := by decide +kernel
private theorem row15 : ∀ l : L, multiplicity 15 l = if zero 15 l then 9 else 0 := by decide +kernel
private theorem row16 : ∀ l : L, multiplicity 16 l = if zero 16 l then 9 else 0 := by decide +kernel
private theorem row17 : ∀ l : L, multiplicity 17 l = if zero 17 l then 9 else 0 := by decide +kernel
private theorem row18 : ∀ l : L, multiplicity 18 l = if zero 18 l then 9 else 0 := by decide +kernel
private theorem row19 : ∀ l : L, multiplicity 19 l = if zero 19 l then 9 else 0 := by decide +kernel
private theorem row20 : ∀ l : L, multiplicity 20 l = if zero 20 l then 9 else 0 := by decide +kernel
private theorem row21 : ∀ l : L, multiplicity 21 l = if zero 21 l then 9 else 0 := by decide +kernel
private theorem row22 : ∀ l : L, multiplicity 22 l = if zero 22 l then 9 else 0 := by decide +kernel
private theorem row23 : ∀ l : L, multiplicity 23 l = if zero 23 l then 9 else 0 := by decide +kernel
private theorem row24 : ∀ l : L, multiplicity 24 l = if zero 24 l then 9 else 0 := by decide +kernel
theorem uniform (p : P) (l : L) : multiplicity p l = if zero p l then 9 else 0 := by
  fin_cases p
  · exact row0 l
  · exact row1 l
  · exact row2 l
  · exact row3 l
  · exact row4 l
  · exact row5 l
  · exact row6 l
  · exact row7 l
  · exact row8 l
  · exact row9 l
  · exact row10 l
  · exact row11 l
  · exact row12 l
  · exact row13 l
  · exact row14 l
  · exact row15 l
  · exact row16 l
  · exact row17 l
  · exact row18 l
  · exact row19 l
  · exact row20 l
  · exact row21 l
  · exact row22 l
  · exact row23 l
  · exact row24 l
theorem exact_weight (p : P) (l : L) (h : zero p l = true) : (multiplicity p l : ℚ) * (1/9) = 1 := by rw [uniform, h]; norm_num
theorem supported (p : P) (l : L) (h : zero p l = false) : multiplicity p l = 0 := by rw [uniform, h]; rfl
theorem weight_sum : (boxes.size : ℚ) * (1/9) = 100/9 := by rw [box_count]; norm_num
end PEqualNP.Research.AffineFractional
