import PEqualNP.Outside.L_meta_5484
import PEqualNP.Outside.L_meta_5497
import PEqualNP.Outside.L_meta_5505

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

namespace ExactSeven

def graph5484 : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 3)

def circuit5484 : Circuit := ⟨[⟨.or,[0,2]⟩, ⟨.or,[1,3]⟩, ⟨.and,[6,7]⟩, ⟨.and,[0,5]⟩, ⟨.and,[1,4]⟩, ⟨.or,[8,9]⟩, ⟨.or,[11,10]⟩],12⟩

theorem exact5484 (t : ℕ) : HasCircuitSize 6 graph5484 t ↔ 7 ≤ t := by
  refine ⟨PEqualNP.Outside.L_meta_5484 t, fun h => ?_⟩
  refine ⟨circuit5484,?_,h,?_⟩
  · intro g hg
    simp only [circuit5484, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp,by decide⟩
  · decide +kernel

def graph5497 : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)

def circuit5497 : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.or,[3,5]⟩, ⟨.and,[6,7]⟩, ⟨.or,[0,2]⟩, ⟨.or,[3,4]⟩, ⟨.and,[9,10]⟩, ⟨.or,[8,11]⟩],12⟩

theorem exact5497 (t : ℕ) : HasCircuitSize 6 graph5497 t ↔ 7 ≤ t := by
  refine ⟨PEqualNP.Outside.L_meta_5497 t, fun h => ?_⟩
  refine ⟨circuit5497,?_,h,?_⟩
  · intro g hg
    simp only [circuit5497, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp,by decide⟩
  · decide +kernel

def graph5505 : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4) || (x 2 && x 5)

def circuit5505 : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[3,4]⟩, ⟨.or,[7,5]⟩, ⟨.and,[0,6]⟩, ⟨.or,[0,6]⟩, ⟨.and,[10,8]⟩, ⟨.or,[9,11]⟩],12⟩

theorem exact5505 (t : ℕ) : HasCircuitSize 6 graph5505 t ↔ 7 ≤ t := by
  refine ⟨PEqualNP.Outside.L_meta_5505 t, fun h => ?_⟩
  refine ⟨circuit5505,?_,h,?_⟩
  · intro g hg
    simp only [circuit5505, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp,by decide⟩
  · decide +kernel

end ExactSeven
