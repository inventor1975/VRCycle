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

theorem append_nil' {α : Type _} : ∀ (l : List α), l ++ [] = l
  | [] => rfl
  | x :: t => congrArg (List.cons x) (append_nil' t)

theorem length_map' {α β : Type _} (f : α → β) : ∀ (l : List α), (l.map f).length = l.length
  | [] => rfl
  | _ :: t => congrArg Nat.succ (length_map' f t)

theorem length_range_loop : ∀ (n : Nat) (acc : List Nat), (List.range.loop n acc).length = n + acc.length
  | 0, _ => (Nat.zero_add _).symm
  | n + 1, acc => by
      show (List.range.loop n (n :: acc)).length = (n + 1) + acc.length
      rw [length_range_loop n (n :: acc)]
      show n + (acc.length + 1) = (n + 1) + acc.length
      rw [Nat.add_succ, Nat.succ_add]

theorem length_range' (n : Nat) : (List.range n).length = n := length_range_loop n []

/-- `a ++ [x] = b ++ [y]` forces `a = b`: peel from the left. -/
theorem append_singleton_inj_left {α : Type _} {x y : α} :
    ∀ {a b : List α}, a ++ [x] = b ++ [y] → a = b
  | [], [], _ => rfl
  | [], b :: bs, h => by
      have h' : x :: ([] : List α) = b :: (bs ++ [y]) := h
      have h2 : ([] : List α) = bs ++ [y] := (List.cons.inj h').2
      cases bs with
      | nil => cases (show ([] : List α) = y :: [] from h2)
      | cons hd tl => cases (show ([] : List α) = hd :: (tl ++ [y]) from h2)
  | a :: as, [], h => by
      have h' : a :: (as ++ [x]) = y :: ([] : List α) := h
      have h2 : as ++ [x] = ([] : List α) := (List.cons.inj h').2
      cases as with
      | nil => cases (show x :: [] = ([] : List α) from h2)
      | cons hd tl => cases (show hd :: (tl ++ [x]) = ([] : List α) from h2)
  | a :: as, b :: bs, h => by
      have h' : a :: (as ++ [x]) = b :: (bs ++ [y]) := h
      have h1 : a = b := (List.cons.inj h').1
      have h2 : as ++ [x] = bs ++ [y] := (List.cons.inj h').2
      rw [h1, append_singleton_inj_left h2]

/-- Halving without `/` and `%` (every core lemma about them reaches `propext`): the quotient and
the parity bit, by structural recursion two steps at a time. -/
def halve : Nat → Nat × Bool
  | 0 => (0, false)
  | 1 => (0, true)
  | n + 2 => ((halve n).1 + 1, (halve n).2)

theorem halve_double : ∀ q : Nat, halve (q + q) = (q, false)
  | 0 => rfl
  | q + 1 => by
      have e : (q + 1) + (q + 1) = (q + q) + 2 := congrArg Nat.succ (Nat.succ_add q q)
      rw [e]
      show ((halve (q + q)).1 + 1, (halve (q + q)).2) = (q + 1, false)
      rw [halve_double q]

theorem halve_double_succ : ∀ q : Nat, halve (q + q + 1) = (q, true)
  | 0 => rfl
  | q + 1 => by
      have e : (q + 1) + (q + 1) + 1 = (q + q + 1) + 2 := congrArg Nat.succ (congrArg Nat.succ (Nat.succ_add q q))
      rw [e]
      show ((halve (q + q + 1)).1 + 1, (halve (q + q + 1)).2) = (q + 1, true)
      rw [halve_double_succ q]

theorem halve_fst_le : ∀ n : Nat, (halve n).1 ≤ n
  | 0 => Nat.le_refl 0
  | 1 => Nat.zero_le 1
  | n + 2 => Nat.succ_le_succ (Nat.le_succ_of_le (halve_fst_le n))

end VRCycle.Continuum.ListCore
