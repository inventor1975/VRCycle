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


-- ------------------------------------------------------------
-- Reading entries and taking prefixes, on `[]` (added for SetsZTL.Stages, 2026-09-12).
-- Core's `l[i]?` reaches `propext` through its `GetElem?` instance; `nth` is the same reading
-- by structural recursion, and the prefix facts below replace `List.take_length`,
-- `List.take_append_of_le_length`, `List.length_append`, `List.ext_getElem`.
-- ------------------------------------------------------------

/-- The `i`-th entry of a list, or `none` past the end. -/
def nth {α : Type _} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, n + 1 => nth l n

theorem nth_append_left {α : Type _} :
    ∀ (l m : List α) (i : Nat), i < l.length → nth (l ++ m) i = nth l i
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: l, m, i + 1, h => nth_append_left l m i (Nat.lt_of_succ_lt_succ h)

theorem nth_append_length {α : Type _} (x : α) :
    ∀ (l : List α), nth (l ++ [x]) l.length = some x
  | [] => rfl
  | _ :: l => nth_append_length x l

theorem nth_eq_getElem {α : Type _} :
    ∀ (l : List α) (i : Nat) (h : i < l.length), nth l i = some l[i]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => nth_eq_getElem l i (Nat.lt_of_succ_lt_succ h)

theorem nth_eq_none {α : Type _} :
    ∀ (l : List α) (i : Nat), l.length ≤ i → nth l i = none
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: l, i + 1, h => nth_eq_none l i (Nat.le_of_succ_le_succ h)

/-- Two lists of equal length that read the same everywhere are equal. -/
theorem nth_ext {α : Type _} :
    ∀ (l m : List α), l.length = m.length → (∀ i, nth l i = nth m i) → l = m
  | [], [], _, _ => rfl
  | [], _ :: m, h, _ => by cases (show 0 = m.length + 1 from h)
  | _ :: l, [], h, _ => by cases (show l.length + 1 = 0 from h)
  | a :: l, b :: m, h, hn => by
      have h0 : some a = some b := hn 0
      rw [Option.some.inj h0, nth_ext l m (Nat.succ.inj h) (fun i => hn (i + 1))]

theorem length_append' {α : Type _} : ∀ (a b : List α), (a ++ b).length = a.length + b.length
  | [], b => (Nat.zero_add b.length).symm
  | _ :: a, b => by
      show (a ++ b).length + 1 = a.length + 1 + b.length
      rw [length_append' a b, Nat.succ_add]

theorem take_length' {α : Type _} : ∀ (l : List α), l.take l.length = l
  | [] => rfl
  | a :: l => congrArg (a :: ·) (take_length' l)

theorem take_append_of_le {α : Type _} :
    ∀ (l m : List α) (k : Nat), k ≤ l.length → (l ++ m).take k = l.take k
  | _, _, 0, _ => rfl
  | [], _, _ + 1, h => absurd h (Nat.not_succ_le_zero _)
  | a :: l, m, k + 1, h => congrArg (a :: ·) (take_append_of_le l m k (Nat.le_of_succ_le_succ h))

/-- A `some`-reading is a member. -/
theorem mem_of_nth {α : Type _} : ∀ (l : List α) (n : Nat) {x : α}, nth l n = some x → x ∈ l
  | [], _, _, h => by cases h
  | a :: l, 0, x, h => by cases Option.some.inj h; exact List.Mem.head l
  | a :: l, n + 1, x, h => List.Mem.tail a (mem_of_nth l n h)

/-- A member is read at some index. -/
theorem nth_of_mem {α : Type _} {x : α} : ∀ {l : List α}, x ∈ l → ∃ n, nth l n = some x
  | _, List.Mem.head l => ⟨0, rfl⟩
  | _, List.Mem.tail _ h =>
      match nth_of_mem h with
      | ⟨n, hn⟩ => ⟨n + 1, hn⟩

end VRCycle.Continuum.ListCore
