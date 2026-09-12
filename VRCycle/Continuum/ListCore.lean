-- VRCycle.Continuum.ListCore — list facts the continuum needs, proved by hand on the EMPTY axiom list.
--
-- Core's `List.range_succ`, `List.map_append`, `List.length_append` reach `propext` through `simp`;
-- through them `Branch.take_succ`, and behind it the bar-soundness and dependent-choice theorems,
-- carried `propext` for no mathematical reason. These four inductions replace them.
-- Curator's bar, 2026-09-12: the empty list wherever it can be had.

namespace VRCycle.Continuum.ListCore

theorem append_assoc' {α : Type _} : ∀ (a b c : List α), (a ++ b) ++ c = a ++ (b ++ c)
  | [], _, _ => rfl
  | x :: t, b, c => congrArg (List.cons x) (append_assoc' t b c)

theorem map_append' {α β : Type _} (f : α → β) : ∀ (a b : List α), (a ++ b).map f = a.map f ++ b.map f
  | [], _ => rfl
  | x :: t, b => congrArg (List.cons (f x)) (map_append' f t b)

theorem length_append_singleton {α : Type _} (b : α) : ∀ (s : List α), (s ++ [b]).length = s.length + 1
  | [] => rfl
  | _ :: t => congrArg Nat.succ (length_append_singleton b t)

/-- `List.range` is `loop n []`; the accumulator is appended on the right. -/
theorem range_loop_append : ∀ (n : Nat) (acc : List Nat), List.range.loop n acc = List.range.loop n [] ++ acc
  | 0, _ => rfl
  | n + 1, acc => by
      show List.range.loop n (n :: acc) = List.range.loop n [n] ++ acc
      rw [range_loop_append n (n :: acc), range_loop_append n [n]]
      exact (append_assoc' (List.range.loop n []) [n] acc).symm

theorem range_succ' (n : Nat) : List.range (n + 1) = List.range n ++ [n] :=
  range_loop_append n [n]

end VRCycle.Continuum.ListCore
