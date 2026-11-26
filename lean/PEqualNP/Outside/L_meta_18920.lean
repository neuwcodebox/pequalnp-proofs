import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18920
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi


theorem le_iff (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem fnLe {n : ℕ} {x y : Fin n → Bool} (h : x ≤ y) (i : ℕ) :
    (List.ofFn x).getD i false ≤ (List.ofFn y).getD i false := by
  by_cases hi : i < n
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi] using h ⟨i, hi⟩
  · simp [List.getD_eq_default, List.length_ofFn, Nat.le_of_not_gt hi]

end PEqualNP.Outside.L_meta_18920
open PEqualNP.Outside.L_meta_18920 in
theorem PEqualNP.Outside.L_meta_18920 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → Monotone (PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x1) := by
  intro C hm x y h
  apply (le_iff _ _).mpr
  exact mono C.gates (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => (le_iff _ _).mp (fnLe h i)) (fun g hg => by simpa using (hm g hg).1) C.output
