import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_18917 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 x6 : ℕ) (x7 : Fin x1 → Bool),   PEqualNP.TopForm.IsAO2 x1 x2 →     x2.output = x1 + x3 →       x3 + (1 : ℕ) = x2.size →         x2.gates[x3]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } →           have x12 : ℕ → Bool := fun (x12 : ℕ) => (x2.wires (List.ofFn x7)).getD x12 Bool.false;           x12 x4 = Bool.false → x12 x5 = Bool.false → ∃ (x15 : ℕ → Bool), (∀ x16 < x1, x15 x16 = Decidable.decide (x16 = x6)) ∧ (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate) (x18 x19 : ℕ), x2.gates[x16]? = Option.some x17 → x17.inputs = [x18, x19] → (x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x15 (x1 + x16) = (x12 x18 && x15 x19 || x15 x18 && x12 x19)) ∧ (x17.op = PEqualNP.CircuitLowerBounds.GateOp.or → x15 (x1 + x16) = (x15 x18 || x15 x19))) ∧ x15 x2.output = Bool.false := by
  classical
  intro N C j a b seed x hao hout _ hlast
  dsimp only
  intro ha hb
  let w (i : ℕ) := (C.wires (List.ofFn x)).getD i false
  let step (t : ℕ) (prev : (i : ℕ) → i < t → Bool) : Bool :=
    if t < N then decide (t = seed) else
    let g := C.gates[t-N]?.getD ⟨GateOp.or, []⟩
    let u := g.inputs[0]?.getD 0
    let v := g.inputs[1]?.getD 0
    if hu : u < t then if hv : v < t then
      if g.op = GateOp.and then (w u && prev v hv) || (prev u hu && w v)
      else prev u hu || prev v hv
    else false else false
  let d (t : ℕ) : Bool := Nat.strongRecOn t step
  have unfoldD (t : ℕ) : d t = step t (fun i _ => d i) := Nat.strongRecOn_eq step t
  have gates (k : ℕ) (g : Gate) (u v : ℕ) (hk : C.gates[k]? = some g) (hg : g.inputs = [u,v]) :
      (g.op = .and → d (N+k) = ((w u && d v) || (d u && w v))) ∧
      (g.op = .or → d (N+k) = (d u || d v)) := by
    have eqg : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
      change C.gates.getD k _ = g
      simp [List.getD_eq_getElem?_getD, hk]
    have back := hao.2.1 k (List.getElem?_eq_some_iff.1 hk).1
    rw [eqg, hg] at back
    have hu := back u (by simp)
    have hv := back v (by simp)
    have big : ¬ N+k < N := by omega
    have eqk : N+k-N = k := by omega
    constructor <;> intro hop <;> rw [unfoldD] <;> simp [step,big,eqk,hk,hg,hu,hv,hop]
  refine ⟨d, ?_, gates, ?_⟩
  · intro i hi
    rw [unfoldD]
    simp [step, hi]
  · change w a = false at ha
    change w b = false at hb
    rw [hout, (gates j _ a b hlast rfl).1 rfl, ha, hb]
    simp
