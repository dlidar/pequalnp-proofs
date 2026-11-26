import Upper
import Cert0
import Cert1
import Cert2
import Cert3
import Cert4
import Cert5
import Cert6
import Cert7
import Cert8
import Cert9
import Cert10
import Cert11
import Cert12
import Cert13
import Cert14
import Cert15
import Cert16
import Cert17
import Cert18
import Cert19
import Cert20
import Cert21
import Cert22
import Cert23
import Cert24
import Cert25
import Cert26
import Cert27
import Cert28
import Cert29
import Cert30
import Cert31
import Cert32
import Cert33
import Cert34
import Cert35
import Cert36
import Cert37
import Cert38
import Cert39
import Cert40
import Cert41
import Cert42
import Cert43
import Cert44
import Cert45
import Cert46
import Cert47
import Cert48
import Cert49
import Cert50
import Cert51
import Cert52
import Cert53
import Cert54
import Cert55
import Cert56
import Cert57
import Cert58
import Cert59
import Cert60
import Cert61
import Cert62
import Cert63
import Cert64
import Cert65
import Cert66
import Cert67
import Cert68
import Cert69
import Cert70
import Cert71
import Cert72
import Cert73
import Cert74
import Cert75
import Cert76
import Cert77
import Cert78
import Cert79
import Cert80
import Cert81
namespace PEqualNP.Research.Cached9815
open TripleFormulaMass
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000
private def coveredKeys : List Key := C0.keys ++ (C1.keys ++ (C2.keys ++ (C3.keys ++ (C4.keys ++ (C5.keys ++ (C6.keys ++ (C7.keys ++ (C8.keys ++ (C9.keys ++ (C10.keys ++ (C11.keys ++ (C12.keys ++ (C13.keys ++ (C14.keys ++ (C15.keys ++ (C16.keys ++ (C17.keys ++ (C18.keys ++ (C19.keys ++ (C20.keys ++ (C21.keys ++ (C22.keys ++ (C23.keys ++ (C24.keys ++ (C25.keys ++ (C26.keys ++ (C27.keys ++ (C28.keys ++ (C29.keys ++ (C30.keys ++ (C31.keys ++ (C32.keys ++ (C33.keys ++ (C34.keys ++ (C35.keys ++ (C36.keys ++ (C37.keys ++ (C38.keys ++ (C39.keys ++ (C40.keys ++ (C41.keys ++ (C42.keys ++ (C43.keys ++ (C44.keys ++ (C45.keys ++ (C46.keys ++ (C47.keys ++ (C48.keys ++ (C49.keys ++ (C50.keys ++ (C51.keys ++ (C52.keys ++ (C53.keys ++ (C54.keys ++ (C55.keys ++ (C56.keys ++ (C57.keys ++ (C58.keys ++ (C59.keys ++ (C60.keys ++ (C61.keys ++ (C62.keys ++ (C63.keys ++ (C64.keys ++ (C65.keys ++ (C66.keys ++ (C67.keys ++ (C68.keys ++ (C69.keys ++ (C70.keys ++ (C71.keys ++ (C72.keys ++ (C73.keys ++ (C74.keys ++ (C75.keys ++ (C76.keys ++ (C77.keys ++ (C78.keys ++ (C79.keys ++ (C80.keys ++ (C81.keys)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem cover : ∀ k : Key,k∈coveredKeys := by decide +kernel
theorem every_key (k : Key) : Bound k := by
  have h := cover k
  simp only [coveredKeys,List.mem_append] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact C0.lower k h
  · exact C1.lower k h
  · exact C2.lower k h
  · exact C3.lower k h
  · exact C4.lower k h
  · exact C5.lower k h
  · exact C6.lower k h
  · exact C7.lower k h
  · exact C8.lower k h
  · exact C9.lower k h
  · exact C10.lower k h
  · exact C11.lower k h
  · exact C12.lower k h
  · exact C13.lower k h
  · exact C14.lower k h
  · exact C15.lower k h
  · exact C16.lower k h
  · exact C17.lower k h
  · exact C18.lower k h
  · exact C19.lower k h
  · exact C20.lower k h
  · exact C21.lower k h
  · exact C22.lower k h
  · exact C23.lower k h
  · exact C24.lower k h
  · exact C25.lower k h
  · exact C26.lower k h
  · exact C27.lower k h
  · exact C28.lower k h
  · exact C29.lower k h
  · exact C30.lower k h
  · exact C31.lower k h
  · exact C32.lower k h
  · exact C33.lower k h
  · exact C34.lower k h
  · exact C35.lower k h
  · exact C36.lower k h
  · exact C37.lower k h
  · exact C38.lower k h
  · exact C39.lower k h
  · exact C40.lower k h
  · exact C41.lower k h
  · exact C42.lower k h
  · exact C43.lower k h
  · exact C44.lower k h
  · exact C45.lower k h
  · exact C46.lower k h
  · exact C47.lower k h
  · exact C48.lower k h
  · exact C49.lower k h
  · exact C50.lower k h
  · exact C51.lower k h
  · exact C52.lower k h
  · exact C53.lower k h
  · exact C54.lower k h
  · exact C55.lower k h
  · exact C56.lower k h
  · exact C57.lower k h
  · exact C58.lower k h
  · exact C59.lower k h
  · exact C60.lower k h
  · exact C61.lower k h
  · exact C62.lower k h
  · exact C63.lower k h
  · exact C64.lower k h
  · exact C65.lower k h
  · exact C66.lower k h
  · exact C67.lower k h
  · exact C68.lower k h
  · exact C69.lower k h
  · exact C70.lower k h
  · exact C71.lower k h
  · exact C72.lower k h
  · exact C73.lower k h
  · exact C74.lower k h
  · exact C75.lower k h
  · exact C76.lower k h
  · exact C77.lower k h
  · exact C78.lower k h
  · exact C79.lower k h
  · exact C80.lower k h
  · exact C81.lower k h

theorem distinct_cache_bound (andGate : Bool) (a b : EdgeInput) (ordered : a<b)
    (f : Formula (Option EdgeInput)) (h : ∀ x,f.eval (fill andGate a b x)=target x) : 25 ≤ f.leaves := by
  obtain ⟨k,hk⟩ := every_pair andGate a b ordered
  exact every_key k f (fun x => by rw [key_extension hk];exact h x)
def identityRaw (a : EdgeInput) : Formula (Option EdgeInput) → Formula EdgeInput
  | .var i => .var (i.getD a)
  | .conj l r => .conj (identityRaw a l) (identityRaw a r)
  | .disj l r => .disj (identityRaw a l) (identityRaw a r)
theorem identity_size (a) (f) : (identityRaw a f).leaves=f.leaves := by
  induction f <;> simp_all [identityRaw,Formula.leaves]
theorem identity_eval (a) (g : Bool) (f) (x) : (identityRaw a f).eval x=f.eval (fill g a a x) := by
  induction f with
  | var i => cases i <;> cases g <;> simp [identityRaw,Formula.eval,fill]
  | conj l r ih jh => simp [identityRaw,Formula.eval,ih,jh]
  | disj l r ih jh => simp [identityRaw,Formula.eval,ih,jh]
theorem raw_cache_bound (andGate : Bool) (a b : EdgeInput)
    (f : Formula (Option EdgeInput)) (h : ∀ x,f.eval (fill andGate a b x)=target x) : 25 ≤ f.leaves := by
  rcases lt_trichotomy a b with ab|eq|ba
  · exact distinct_cache_bound andGate a b ab f h
  · subst b
    have e := ordinary_bound (identityRaw a f) (fun x => (identity_eval a andGate f x).trans (h x))
    rw [identity_size] at e
    omega
  · apply distinct_cache_bound andGate b a ba f
    intro x
    rw [← h]
    congr 1
    funext i
    cases i <;> cases andGate <;> simp [fill,Bool.and_comm,Bool.or_comm]
theorem best_cache_size (s : Nat) :
    (∃ g a b, ∃ f : Formula (Option EdgeInput),f.leaves≤s ∧ ∀ x,f.eval (fill g a b x)=target x) ↔ 25≤s := by
  constructor
  · rintro ⟨g,a,b,f,le,h⟩
    exact (raw_cache_bound g a b f h).trans le
  · intro h
    exact ⟨false,8,10,useful,by rwa [useful_size],useful_eval⟩
end PEqualNP.Research.Cached9815
