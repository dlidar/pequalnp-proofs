import Repair
namespace InverterRepair
variable {I : Type} [Fintype I] [DecidableEq I]

theorem necessary {f g b : Point I → Bool} (fm : Monotone f)
    (universal : ∀ d : Point I → Bool → Bool, (∀ t,Monotone (fun x => d x t)) →
      (∀ x,Monotone (d x)) → (∀ x,d x (!(g x))=f x) → ∀ x,d x (b x)=f x) :
    (∀ p,Lower f p → g p=false → b p=true) ∧
    (∀ n,Upper f n → g n=true → b n=false) := by
  classical
  constructor
  · intro p hp gp
    let d (x : Point I) (t : Bool) := f x && (t || decide (¬ x≤p))
    have hm (t : Bool) : Monotone (fun x => d x t) := by
      intro x y h
      apply inf_le_inf (fm h)
      apply sup_le_sup le_rfl
      by_cases e : x≤p
      · simp [e]
      · have v : ¬ y≤p := fun yp => e (h.trans yp)
        simp [v]
    have pass (x : Point I) : d x (!(g x))=f x := by
      by_cases h : x≤p
      · rcases h.eq_or_lt with rfl|lt
        · simp [d,gp]
        · simp [d,hp.2 x lt]
      · simp [d,h]
    have eq := universal d hm (fun x a b ab => inf_le_inf le_rfl (sup_le_sup ab le_rfl)) pass p
    simpa [d,hp.1] using eq
  · intro n hn gn
    let d (x : Point I) (t : Bool) := f x || (t && decide (n≤x))
    have hm (t : Bool) : Monotone (fun x => d x t) := by
      intro x y h
      apply sup_le_sup (fm h)
      apply inf_le_inf le_rfl
      by_cases e : n≤x
      · have v := e.trans h
        simp [v]
      · simp [e]
    have pass (x : Point I) : d x (!(g x))=f x := by
      by_cases h : n≤x
      · rcases h.eq_or_lt with rfl|lt
        · simp [d,gn]
        · simp [d,hn.2 x lt]
      · simp [d,h]
    have eq := universal d hm (fun x a b ab => sup_le_sup le_rfl (inf_le_inf ab le_rfl)) pass n
    simpa [d,hn.1] using eq

theorem iff_boundary {f g b : Point I → Bool} (fm : Monotone f) (bm : Monotone b) :
    (∀ d : Point I → Bool → Bool, (∀ t,Monotone (fun x => d x t)) →
      (∀ x,Monotone (d x)) → (∀ x,d x (!(g x))=f x) → ∀ x,d x (b x)=f x) ↔
    (∀ p,Lower f p → g p=false → b p=true) ∧
    (∀ n,Upper f n → g n=true → b n=false) :=
  ⟨necessary fm,fun h d dx dt eq => boundary_repair d dx dt bm eq h.1 h.2⟩
end InverterRepair
