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
-- Reading entries and taking prefixes, on `[]` (added for ZTL.Stages, 2026-09-12).
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

-- ------------------------------------------------------------
-- Membership, on `[]` (added for Topology.Tychonoff, 2026-09-12).  Core's `List.mem_cons`,
-- `mem_append`, `mem_map`, `mem_filter`, `mem_flatMap`, `mem_sublists`, `Bool.not_eq_true'`,
-- `decide_eq_false_iff_not` and the `Decidable (a ∈ l)` instance all reach `propext`.
-- These are the same statements by induction on the list / cases on `List.Mem`.
-- NOTE: rewrite with them only through `.mp` / `.mpr` — `rw` with an `Iff` goes through `propext`.
-- ------------------------------------------------------------

theorem mem_cons_iff {α : Type _} {a b : α} {l : List α} : a ∈ b :: l ↔ a = b ∨ a ∈ l :=
  ⟨fun h => match h with
    | List.Mem.head _ => Or.inl rfl
    | List.Mem.tail _ h' => Or.inr h',
   fun h => match h with
    | Or.inl e => e ▸ List.Mem.head l
    | Or.inr h' => List.Mem.tail b h'⟩

theorem mem_append_iff {α : Type _} {a : α} : ∀ {l m : List α}, a ∈ l ++ m ↔ a ∈ l ∨ a ∈ m
  | [], m => ⟨fun h => Or.inr h, fun h => match h with
      | Or.inl h' => nomatch h'
      | Or.inr h' => h'⟩
  | b :: l, m =>
    ⟨fun h => match mem_cons_iff.mp h with
      | Or.inl e => Or.inl (e ▸ List.Mem.head l)
      | Or.inr h' => match (mem_append_iff (l := l) (m := m)).mp h' with
        | Or.inl hl => Or.inl (List.Mem.tail b hl)
        | Or.inr hm => Or.inr hm,
     fun h => match h with
      | Or.inl hl => match mem_cons_iff.mp hl with
        | Or.inl e => e ▸ List.Mem.head (l ++ m)
        | Or.inr hl' => List.Mem.tail b ((mem_append_iff (l := l) (m := m)).mpr (Or.inl hl'))
      | Or.inr hm => List.Mem.tail b ((mem_append_iff (l := l) (m := m)).mpr (Or.inr hm))⟩

theorem mem_map_iff {α β : Type _} {f : α → β} {b : β} :
    ∀ {l : List α}, b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b
  | [] => ⟨(fun h => nomatch h), (fun ⟨_, h, _⟩ => nomatch h)⟩
  | a :: l =>
    ⟨fun h => match mem_cons_iff.mp h with
      | Or.inl e => ⟨a, List.Mem.head l, e.symm⟩
      | Or.inr h' => match (mem_map_iff (l := l)).mp h' with
        | ⟨a', ha', e⟩ => ⟨a', List.Mem.tail a ha', e⟩,
     fun ⟨a', ha', e⟩ => match mem_cons_iff.mp ha' with
      | Or.inl e' => by rw [← e, e']; exact List.Mem.head _
      | Or.inr h' => List.Mem.tail (f a) ((mem_map_iff (l := l)).mpr ⟨a', h', e⟩)⟩

theorem mem_filter_iff {α : Type _} {p : α → Bool} {a : α} :
    ∀ {l : List α}, a ∈ l.filter p ↔ a ∈ l ∧ p a = true
  | [] => ⟨(fun h => nomatch h), (fun ⟨h, _⟩ => nomatch h)⟩
  | b :: l => by
    cases hb : p b with
    | true =>
      rw [List.filter_cons_of_pos hb]
      exact ⟨fun h => match mem_cons_iff.mp h with
          | Or.inl e => ⟨e ▸ List.Mem.head l, e ▸ hb⟩
          | Or.inr h' => match (mem_filter_iff (l := l)).mp h' with
            | ⟨hl, hp⟩ => ⟨List.Mem.tail b hl, hp⟩,
        fun ⟨h, hp⟩ => match mem_cons_iff.mp h with
          | Or.inl e => e ▸ List.Mem.head _
          | Or.inr h' => List.Mem.tail b ((mem_filter_iff (l := l)).mpr ⟨h', hp⟩)⟩
    | false =>
      rw [List.filter_cons_of_neg (fun e => Bool.noConfusion (hb.symm.trans e))]
      exact ⟨fun h => match (mem_filter_iff (l := l)).mp h with
          | ⟨hl, hp⟩ => ⟨List.Mem.tail b hl, hp⟩,
        fun ⟨h, hp⟩ => match mem_cons_iff.mp h with
          | Or.inl e => absurd (e ▸ hp) (fun e' => Bool.noConfusion (hb.symm.trans e'))
          | Or.inr h' => (mem_filter_iff (l := l)).mpr ⟨h', hp⟩⟩

theorem mem_flatMap_iff {α β : Type _} {f : α → List β} {b : β} :
    ∀ {l : List α}, b ∈ l.flatMap f ↔ ∃ a, a ∈ l ∧ b ∈ f a
  | [] => ⟨(fun h => nomatch h), (fun ⟨_, h, _⟩ => nomatch h)⟩
  | a :: l =>
    ⟨fun h => match (mem_append_iff (l := f a) (m := l.flatMap f)).mp h with
      | Or.inl h' => ⟨a, List.Mem.head l, h'⟩
      | Or.inr h' => match (mem_flatMap_iff (l := l)).mp h' with
        | ⟨a', ha', hb⟩ => ⟨a', List.Mem.tail a ha', hb⟩,
     fun ⟨a', ha', hb⟩ => match mem_cons_iff.mp ha' with
      | Or.inl e => (mem_append_iff (l := f a) (m := l.flatMap f)).mpr (Or.inl (e ▸ hb))
      | Or.inr h' => (mem_append_iff (l := f a) (m := l.flatMap f)).mpr
          (Or.inr ((mem_flatMap_iff (l := l)).mpr ⟨a', h', hb⟩))⟩

/-- `(!b) = true ↔ b = false`, by cases. -/
theorem bnot_eq_true_iff : ∀ {b : Bool}, (!b) = true ↔ b = false
  | true => ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  | false => ⟨fun _ => rfl, fun _ => rfl⟩

/-- `(!decide p) = true ↔ ¬ p`. -/
theorem bnot_decide_eq_true_iff {p : Prop} [Decidable p] : (!decide p) = true ↔ ¬ p :=
  ⟨fun h => of_decide_eq_false (bnot_eq_true_iff.mp h),
   fun h => bnot_eq_true_iff.mpr (decide_eq_false h)⟩

/-- Decidable membership by structural recursion (core's instance reaches `propext`
through `LawfulBEq`). -/
def decMem {α : Type _} [DecidableEq α] (a : α) : ∀ (l : List α), Decidable (a ∈ l)
  | [] => isFalse (fun h => nomatch h)
  | b :: l =>
    if h : a = b then isTrue (h ▸ List.Mem.head l)
    else match decMem a l with
      | isTrue h' => isTrue (List.Mem.tail b h')
      | isFalse h' => isFalse (fun hm => match mem_cons_iff.mp hm with
          | Or.inl e => h e
          | Or.inr hl => h' hl)

/-- All sublists of a list, by structural recursion: `subl (a :: l) = subl l ++ (subl l).map (a :: ·)`. -/
def subl {α : Type _} : List α → List (List α)
  | [] => [[]]
  | a :: l => subl l ++ (subl l).map (a :: ·)

/-- Every filter of `l` is one of its `subl`. -/
theorem filter_mem_subl {α : Type _} (p : α → Bool) : ∀ (l : List α), l.filter p ∈ subl l
  | [] => List.Mem.head _
  | a :: l => by
    cases hp : p a with
    | true =>
      rw [List.filter_cons_of_pos hp]
      exact (mem_append_iff).mpr (Or.inr ((mem_map_iff).mpr ⟨l.filter p, filter_mem_subl p l, rfl⟩))
    | false =>
      rw [List.filter_cons_of_neg (fun e => Bool.noConfusion (hp.symm.trans e))]
      exact (mem_append_iff).mpr (Or.inl (filter_mem_subl p l))


end VRCycle.Continuum.ListCore
