-- VR. A Formal System (DOI 10.5281/zenodo.20212092)
-- Формализация системы VR в Lean 4

namespace VR

-- ============================================================
-- §1. Primitives (Part I, §1)
-- ============================================================

-- Тип объектов VR: все объекты, порождённые из ∅ применением t.
-- Part I, §1 (Primitives) + A4 (Induction): O_n исчерпывают весь домен.
--
-- Конструктор void  — примитив ∅ (константа)
-- Конструктор succ  — примитив t (унарный оператор, succession)
--
-- Принцип индукции Lean (VRObj.rec) выражает A4:
-- любое свойство, истинное для void и наследуемое через succ,
-- истинно для всех объектов VR.
--
-- Препринт, A1: «F is identified with ∅ at the logical level».
-- Это семантическое отождествление двух точек: F в VRBool и void в VRObj —
-- одна и та же базовая точка, рассматриваемая в двух регистрах
-- (логическом и онтологическом). В формализации это явное отождествление
-- не используется ни одной теоремой VR. Если в дальнейшем (VR-Sets, VR-Forms)
-- появится формальное утверждение, требующее связи, мост будет введён тогда.
inductive VRObj : Type where
  | void : VRObj           -- ∅  (Def. 4: O₀ := ∅)
  | succ : VRObj → VRObj   -- t  (Def. 5: O_{n+1} := t(O_n))

-- ============================================================
-- §1–§2. Logical layer (Part I, §1 + §2)
-- ============================================================

-- Логический слой VR: {F, T}.
-- F отождествляется с ∅ на логическом уровне (A1).
-- T определяется как impl F F (Def. 1, §4).
inductive VRBool : Type where
  | F : VRBool   -- ложь / ∅
  | T : VRBool   -- истина

-- §1. Бинарный оператор impl (примитив → в VR).
-- A2 (§2): таблица истинности классической импликации.
-- Нотация намеренно не вводится на этом этапе,
-- чтобы избежать конфликтов с зарезервированными символами mathlib.
def impl : VRBool → VRBool → VRBool
  | VRBool.F, _        => VRBool.T
  | VRBool.T, VRBool.F => VRBool.F
  | VRBool.T, VRBool.T => VRBool.T

-- ============================================================
-- §2. Axioms A1 and A2 (Part I, §2)
-- ============================================================

-- A1 (§2). Генеративность.
-- impl F F = T и impl F T = T.
-- Из F через impl достижимы оба значения {F, T}.
-- A1 — первые две строки таблицы A2.
theorem A1_1 : impl VRBool.F VRBool.F = VRBool.T := rfl
theorem A1_2 : impl VRBool.F VRBool.T = VRBool.T := rfl

-- A1 (§2). Достижимость из F.
-- «From F, via →, both values {F, T} are reachable.»
-- Формализация через предикатное замыкание: {F} порождает весь VRBool.
-- Любое S, содержащее F и замкнутое под impl, содержит все элементы VRBool.
theorem A1_F_reaches_both : ∀ (b : VRBool) (S : VRBool → Prop),
    S VRBool.F →
    (∀ x y, S x → S y → S (impl x y)) →
    S b := by
  intro b S hF hClosed
  cases b with
  | F => exact hF
  | T => exact hClosed VRBool.F VRBool.F hF hF

-- A1 (§2). Достижимость из T.
-- «From T, via →, only T is reachable.»
-- Формализация через предикатное замыкание: {T} — минимальное замкнутое множество.
-- Если b входит в каждое S, содержащее T и замкнутое под impl, то b = T.
theorem A1_T_reaches_only_T : ∀ (b : VRBool),
    (∀ (S : VRBool → Prop),
      S VRBool.T →
      (∀ x y, S x → S y → S (impl x y)) →
      S b) →
    b = VRBool.T := by
  intro b hb
  exact hb (· = VRBool.T) rfl (by intro x y hx hy; subst hx; subst hy; rfl)

-- A2 (§2). Полная таблица истинности импликации.
-- impl есть функция {F,T}×{F,T} → {F,T}, заданная классической таблицей.
theorem A2_FF : impl VRBool.F VRBool.F = VRBool.T := rfl
theorem A2_FT : impl VRBool.F VRBool.T = VRBool.T := rfl
theorem A2_TF : impl VRBool.T VRBool.F = VRBool.F := rfl
theorem A2_TT : impl VRBool.T VRBool.T = VRBool.T := rfl

-- ============================================================
-- §3. Basis — derived logical operators (Part I, §3)
-- ============================================================

-- §3. Отрицание: ¬x := x → F
def vnot (x : VRBool) : VRBool := impl x VRBool.F

-- §3. Дизъюнкция: x ∨ y := (x → y) → y
def vor (x y : VRBool) : VRBool := impl (impl x y) y

-- §3. Конъюнкция: x ∧ y := ¬(¬x ∨ ¬y)
def vand (x y : VRBool) : VRBool := vnot (vor (vnot x) (vnot y))

-- §3. Биконъюнкция: x ↔ y := (x → y) ∧ (y → x)
def viff (x y : VRBool) : VRBool := vand (impl x y) (impl y x)

-- Таблицы истинности производных операторов.
-- Все доказываются rfl: определения разворачиваются в impl,
-- который разворачивается в конструкторы VRBool.

-- vnot
theorem vnot_F : vnot VRBool.F = VRBool.T := rfl
theorem vnot_T : vnot VRBool.T = VRBool.F := rfl

-- vor
theorem vor_FF : vor VRBool.F VRBool.F = VRBool.F := rfl
theorem vor_FT : vor VRBool.F VRBool.T = VRBool.T := rfl
theorem vor_TF : vor VRBool.T VRBool.F = VRBool.T := rfl
theorem vor_TT : vor VRBool.T VRBool.T = VRBool.T := rfl

-- vand
theorem vand_FF : vand VRBool.F VRBool.F = VRBool.F := rfl
theorem vand_FT : vand VRBool.F VRBool.T = VRBool.F := rfl
theorem vand_TF : vand VRBool.T VRBool.F = VRBool.F := rfl
theorem vand_TT : vand VRBool.T VRBool.T = VRBool.T := rfl

-- viff
theorem viff_FF : viff VRBool.F VRBool.F = VRBool.T := rfl
theorem viff_FT : viff VRBool.F VRBool.T = VRBool.F := rfl
theorem viff_TF : viff VRBool.T VRBool.F = VRBool.F := rfl
theorem viff_TT : viff VRBool.T VRBool.T = VRBool.T := rfl

-- ============================================================
-- §4. Definitions (Part I, §4)
-- ============================================================

-- Def. 1 (§4). T := impl F F.
-- В нашей формализации T — самостоятельный конструктор VRBool,
-- а равенство impl F F = T фиксируется как именованный факт.
theorem T_def : impl VRBool.F VRBool.F = VRBool.T := rfl

-- Def. 2 (§4). Leibnizian Equality.
-- «x = y := ∀p: p(x) ↔ p(y)»
--
-- Квантор по предикатам VRObj → Prop (Вариант II).
-- Используется Lean-iff (↔), а не viff из VRBool:
--   — препринт §10 интерпретирует «for all properties» как схему над всеми
--     формулами арифметики (= все предикаты Lean);
--   — Lean-iff напрямую поддерживает вывод, что делает Theorem 4 доказуемой.
-- Именуем vrEq, чтобы не конфликтовать с Lean-равенством =.
--
-- Методологическая заметка о двух уровнях ↔.
-- В препринте символ ↔ используется в двух разных смыслах:
--   (1) В §3 ↔ определён как viff — оператор на VRBool, двухзначный.
--   (2) В §4 (Def. 2) ↔ стоит между p(x) и p(y), которые при структурных
--       предикатах (используемых в §5, Th. 3, Th. 4) являются
--       метатеоретическими утверждениями, не значениями VRBool.
-- Структурные предикаты (например, «содержит x как элемент») не выразимы
-- в VRBool, поскольку mem рекурсивна по структуре объекта. Значит
-- фактическое употребление ↔ в Def. 2 — метатеоретическая эквивалентность,
-- отличная от ↔ §3. Lean-формализация это делает явным выбором Iff.
def vrEq (x y : VRObj) : Prop := ∀ (p : VRObj → Prop), p x ↔ p y

-- Def. 3 (§4). Distinctness.
-- «x ≠ y := ¬(x = y)»
def vrNe (x y : VRObj) : Prop := ¬ vrEq x y

-- Лемма-мост: Lean-равенство влечёт vrEq (одна сторона).
-- Обратное (vrEq → =) понадобится в Теореме 4 (шаг 5.5); вводится тогда.
theorem Eq_to_vrEq (x y : VRObj) (h : x = y) : vrEq x y := by
  intro p; subst h; exact Iff.rfl

-- ============================================================
-- §2. Axiom A3 — Succession (Part I, §2)
-- ============================================================

-- A3 (§2). Преемник.
-- «The operator t is defined on ∅ and on every object generated from it.
--  For every x in the domain of t: t(x) = x ∪ {x}, so x ∈ t(x) and x ⊂ t(x).»
--
-- В формализации t реализован как конструктор succ (см. VRObj выше).
-- Операции ∪ и {·} не вводятся как примитивы:
-- t(x) = x ∪ {x} — это определяющее уравнение, не теорема.
-- Содержательная часть A3 (x ∈ t(x) и x ⊂ t(x)) доказывается из mem.

-- Отношение принадлежности на VRObj.
-- x ∈ void  — ложно (пустое множество не содержит ничего).
-- x ∈ succ y — x = y (x и есть y) или x ∈ y (x лежит глубже).
-- Рекурсия структурная по второму аргументу (y убывает от succ y к y).
def mem : VRObj → VRObj → Prop
  | _, VRObj.void   => False
  | x, VRObj.succ y => x = y ∨ mem x y

-- Отношение включения на VRObj.
-- x ⊆ y — каждый элемент x принадлежит y.
def subset (x y : VRObj) : Prop := ∀ z, mem z x → mem z y

-- A3, часть 1 (§2): x ∈ t(x) для всякого x.
-- «x ∈ t(x)» = mem x (succ x) = (x = x ∨ mem x x) = True.
theorem A3_mem_self : ∀ x : VRObj, mem x (VRObj.succ x) :=
  fun _ => Or.inl rfl

-- A3, часть 2 (§2): x ⊆ t(x) для всякого x.
-- Если z ∈ x, то z ∈ succ x = (z = x ∨ z ∈ x), что истинно по Or.inr.
theorem A3_subset_succ : ∀ x : VRObj, subset x (VRObj.succ x) :=
  fun _ _ hz => Or.inr hz

-- ============================================================
-- §2. Axiom A4 — Induction (Part I, §2)
-- ============================================================

-- A4 (§2). Индукция.
-- «If P is a property of objects of the system, and:
--  (i) P(O₀) holds,
--  (ii) for every x: P(x) → P(t(x)),
--  then P(O_n) holds for all n.»
--
-- В Lean A4 не постулируется: она доказуема как теорема,
-- поскольку рекурсор VRObj.rec — автоматическое следствие
-- объявления индуктивного типа VRObj.
-- Это методологическое усиление: аксиома VR становится теоремой Lean.
theorem A4_induction (P : VRObj → Prop)
    (h0 : P VRObj.void)
    (hs : ∀ x, P x → P (VRObj.succ x)) :
    ∀ n, P n := by
  intro n
  induction n with
  | void    => exact h0
  | succ x ih => exact hs x ih

-- A4, эквивалентная формулировка (§2):
-- «The O_n exhaust all objects generated from ∅ via t.»
-- Каждый объект VRObj является либо void, либо succ чего-то —
-- третьего не дано.
theorem A4_exhaustion : ∀ x : VRObj, x = VRObj.void ∨ ∃ y, x = VRObj.succ y := by
  intro x
  cases x with
  | void   => exact Or.inl rfl
  | succ y => exact Or.inr ⟨y, rfl⟩

-- ============================================================
-- §5. Лемма: t(x) ≠ x (Part I, §5)
-- ============================================================

-- Доказательство §5 (t(x) ≠ x) реализовано чисто структурно,
-- без введения внешней меры (depth : VRObj → Nat). Ключевые компоненты:
--   (1) mem_succ_left — «понижающая» лемма;
--   (2) mem_asymm    — асимметрия mem через индукцию по y;
--   (3) not_mem_self — иррефлексивность как следствие асимметрии.
-- Это подтверждает, что ацикличность ∈ в VR доказуема внутренними
-- средствами индуктивного типа VRObj.

-- Вспомогательная: succ a ∈ b → a ∈ b.
-- Если «следующий» за a принадлежит b, то и сам a принадлежит b.
-- Доказывается индукцией по b; использует только mem и VRObj.rec.
private theorem mem_succ_left (b : VRObj) : ∀ a, mem (VRObj.succ a) b → mem a b := by
  induction b with
  | void => intro a h; exact h.elim
  | succ c ih =>
    intro a h
    have h' : VRObj.succ a = c ∨ mem (VRObj.succ a) c := h
    cases h' with
    | inl hac =>
      subst hac
      -- цель: mem a (succ (succ a)) = a = succ a ∨ mem a (succ a)
      -- mem a (succ a) = a = a ∨ mem a a; берём Or.inl rfl
      exact Or.inr (show mem a (VRObj.succ a) from Or.inl rfl)
    | inr hmc =>
      exact Or.inr (ih a hmc)

-- Антисимметрия: x ∈ y и y ∈ x несовместны.
-- Ключевой шаг для not_mem_self; доказывается индукцией по y
-- с использованием mem_succ_left.
private theorem mem_asymm (y : VRObj) : ∀ x, mem x y → ¬ mem y x := by
  induction y with
  | void => intro x h; exact h.elim
  | succ z ih =>
    intro x h hmyx
    have h' : x = z ∨ mem x z := h
    have hzx : mem z x := mem_succ_left x z hmyx
    cases h' with
    | inl hxz =>
      -- hxz : x = z; переписываем x → z в hzx, получаем mem z z
      rw [hxz] at hzx
      exact ih z hzx hzx
    | inr hxz =>
      -- hxz : mem x z, hzx : mem z x; ih x hxz : ¬ mem z x
      exact ih x hxz hzx

-- Лемма: ни один объект не содержит сам себя.
theorem not_mem_self : ∀ x : VRObj, ¬ mem x x :=
  fun x h => (mem_asymm x x h) h

-- §5 (Препринт, Часть I, §5): t(x) ≠ x для всякого x.
-- Если vrEq (succ x) x, то с предикатом p := mem x получаем
-- mem x (succ x) ↔ mem x x. Первое истинно (A3_mem_self),
-- второе ложно (not_mem_self). Противоречие.
theorem succ_ne_self : ∀ x : VRObj, vrNe (VRObj.succ x) x :=
  fun x heq => not_mem_self x ((heq (fun y => mem x y)).mp (A3_mem_self x))

-- ============================================================
-- §4, §6. Von Neumann ordinals — Defs. 4–6 (Part I, §4, §6)
-- ============================================================

-- Def. 4–6 (§4, §6). Конструкция von Neumann ординалов.
--
-- Функция O : Nat → VRObj отображает индексы метаязыка на объекты VR.
-- Lean-овский Nat здесь — внешний источник имён, не часть VR.
-- Сами объекты VR — образ O в VRObj:
--   O 0 = void, O 1 = succ void, O 2 = succ (succ void), ...
--
-- Сюръективность O на VRObj (т.е. ∀ x : VRObj, ∃ n, x = O n) выражает
-- A4_exhaustion на уровне именования. Биективность O : Nat → VRObj —
-- содержательное утверждение, которое будет доказано на Этапе 5
-- (Peano-эквивалентность, Theorem 11).
--
-- На текущем этапе O — конструктивное именование, не отождествление.
def O : Nat → VRObj
  | 0     => VRObj.void
  | n + 1 => VRObj.succ (O n)

-- ============================================================
-- §4. Concrete values (Part I, §4) — Def. 3.4
-- ============================================================

-- O₁ = {∅}, O₂ = {∅, {∅}}, O₃ = {∅, {∅}, {∅, {∅}}}.
-- В кодировке VRObj: последовательные применения succ к void.
-- Все теоремы доказываются rfl — прямое вычисление по def O.
theorem O_one   : O 1 = VRObj.succ VRObj.void                               := rfl
theorem O_two   : O 2 = VRObj.succ (VRObj.succ VRObj.void)                  := rfl
theorem O_three : O 3 = VRObj.succ (VRObj.succ (VRObj.succ VRObj.void))     := rfl

-- ============================================================
-- §6. Membership lemma (Part I, §6) — Def. 3.5
-- ============================================================

-- Лемма (§6): O_k ∈ O_n для всякого k < n.
-- «каждое O_n содержит все предыдущие O₀, ..., O_{n−1}»
--
-- Доказывается индукцией по доказательству k < n, т.е. по
-- конструкторам Nat.le (refl / step).
-- Не использует omega или арифметические леммы — только структуру Nat.le.
theorem O_mem_lt : ∀ k n : Nat, k < n → mem (O k) (O n) := by
  intro k n h
  induction h with
  | refl      => exact A3_mem_self (O k)
  | step _ ih => exact Or.inr ih

-- ============================================================
-- §7. Arithmetic operations (Part I, §7) — Defs. 7–9
-- ============================================================

-- Def. 7 (§7). Сложение на VRObj.
-- a + void   := a          (нейтральный элемент)
-- a + succ b := succ (a + b)  (шаг рекурсии)
-- Рекурсия структурная по второму аргументу.
def vadd : VRObj → VRObj → VRObj
  | a, VRObj.void   => a
  | a, VRObj.succ b => VRObj.succ (vadd a b)

-- Def. 8 (§7). Умножение на VRObj.
-- a × void   := void         (поглощающий нуль)
-- a × succ b := (a × b) + a  (шаг рекурсии)
-- Рекурсия структурная по второму аргументу; использует vadd.
def vmul : VRObj → VRObj → VRObj
  | _, VRObj.void   => VRObj.void
  | a, VRObj.succ b => vadd (vmul a b) a

-- Def. 9 (§7). Возведение в степень на VRObj.
-- a ^ void   := succ void  (= O₁ по Def. 4+5; база степени — единица)
-- a ^ succ b := (a ^ b) × a
-- Рекурсия структурная по показателю (второй аргумент). Использует vmul.
-- Примечание: succ void здесь — то же, что O₁ в препринте; равенство
-- vpow a void = O 1 доказуемо rfl через O_one, если понадобится в теоремах.
def vpow : VRObj → VRObj → VRObj
  | _, VRObj.void   => VRObj.succ VRObj.void
  | a, VRObj.succ b => vmul (vpow a b) a

-- ============================================================
-- §7. T1 — Commutativity of addition (Part I, §7)
-- ============================================================

-- Вспомогательная (для T1): левый нейтральный элемент vadd.
-- void + b = b  (правый нейтраль vadd a void = a следует из def напрямую)
-- Доказывается индукцией по b.
theorem vadd_zero_left : ∀ b : VRObj, vadd VRObj.void b = b := by
  intro b
  induction b with
  | void      => rfl
  | succ c ih => exact congrArg VRObj.succ ih

-- Вспомогательная (для T1): левый succ проходит сквозь vadd.
-- succ a + b = succ (a + b)  (правый аналог: vadd a (succ b) = succ (vadd a b) — def)
-- Доказывается индукцией по b.
theorem vadd_succ_left : ∀ a b : VRObj, vadd (VRObj.succ a) b = VRObj.succ (vadd a b) := by
  intro a b
  induction b with
  | void      => rfl
  | succ c ih => exact congrArg VRObj.succ ih

-- T1 (§7): коммутативность сложения.
-- a + b = b + a для всяких объектов VR.
-- Доказывается индукцией по b, используя vadd_zero_left и vadd_succ_left.
theorem T1_vadd_comm : ∀ a b : VRObj, vadd a b = vadd b a := by
  intro a b
  induction b with
  | void      => exact (vadd_zero_left a).symm
  | succ c ih =>
    rw [vadd_succ_left]
    exact congrArg VRObj.succ ih

-- ============================================================
-- §7. T2 — Associativity of addition (Part I, §7)
-- ============================================================

-- T2 (§7): ассоциативность сложения.
-- (a + b) + c = a + (b + c) для всяких объектов VR.
-- Доказывается прямой индукцией по c; вспомогательных лемм не требуется.
theorem T2_vadd_assoc : ∀ a b c : VRObj, vadd (vadd a b) c = vadd a (vadd b c) := by
  intro a b c
  induction c with
  | void      => rfl
  | succ d ih => exact congrArg VRObj.succ ih

-- ============================================================
-- §7. T3 — Distributivity (Part I, §7)
-- ============================================================

-- T3 (§7): дистрибутивность умножения относительно сложения.
-- a × (b + c) = (a × b) + (a × c) для всяких объектов VR.
-- Доказывается индукцией по c; использует T2_vadd_assoc. Новых лемм нет.
theorem T3_vmul_distrib : ∀ a b c : VRObj, vmul a (vadd b c) = vadd (vmul a b) (vmul a c) := by
  intro a b c
  induction c with
  | void      => rfl
  | succ d ih =>
    -- после def-редукции:
    -- LHS = vadd (vmul a (vadd b d)) a
    -- RHS = vadd (vmul a b) (vadd (vmul a d) a)
    -- ih переписывает первое слагаемое, T2 закрывает ассоциативность
    show vadd (vmul a (vadd b d)) a = vadd (vmul a b) (vadd (vmul a d) a)
    rw [ih]
    exact T2_vadd_assoc (vmul a b) (vmul a d) a

-- ============================================================
-- §7. T4 — O₁ + O₁ = O₂ (Part I, §7)
-- ============================================================

-- T4 (§7): O₁ + O₁ = O₂.
-- Доказывается rfl: две def-редукции vadd закрывают цель.
theorem T4_one_plus_one : vadd (O 1) (O 1) = O 2 := rfl

-- ============================================================
-- §9 (Part II). Peano correspondence — Step 5.1
-- ============================================================

-- Транслятор ℕ → VR (Часть II, §9).
-- Def-уравнения O выносятся в именованные теоремы для явной фиксации
-- соответствия «0 ↦ O₀, S ↦ t» из препринта §9.
-- Обе доказываются rfl по def O.

-- 0 ↦ O₀ = ∅
theorem O_zero : O 0 = VRObj.void := rfl

-- Nat.succ ↦ VRObj.succ (= t)
theorem O_succ : ∀ n : Nat, O (n + 1) = VRObj.succ (O n) := fun _ => rfl

-- ============================================================
-- §10. P1, P2 — absorbed by typing (Part II, §10)
-- ============================================================

-- §10, Theorems P1 и P2 в VR.
--
-- Препринт формулирует:
--   P1: «O₀ is an object of the system»
--   P2: «For every O_n, t(O_n) exists and is an object of the system»
--
-- В первопорядковой нетипизированной формулировке Пеано эти утверждения
-- требуют экзистенциального доказательства (существование объекта в ℕ).
-- В типизированной формализации Lean они переходят в типовые утверждения:
--   P1: O 0 : VRObj — по самому определению O (def O, первый случай).
--   P2: VRObj.succ : VRObj → VRObj — тотальная функция по сигнатуре типа.
--
-- В Lean не вводятся как отдельные теоремы — они стали синтаксисом.
-- Это методологическое наблюдение: типизация поглощает часть Пеано-аксиом.

-- ============================================================
-- §10. P3 — Theorem 4: t(O_n) ≠ O₀ (Part II, §10)
-- ============================================================

-- §10, Theorem 4 (P3 в VR): t(O_n) ≠ O₀.
-- succ x ≠ void для всякого x : VRObj.
--
-- Два пути доказательства:
--   (1) Через свойство mem (препринт §5): void содержит 0 элементов,
--       succ x содержит x как элемент (A3_mem_self). Если succ x = void,
--       то x ∈ void — ложь. Формально: A3_mem_self x ▸ h ▸ id.
--   (2) Через VRObj.noConfusion (Lean 4): void и succ — различные
--       конструкторы, равенство между ними опровергается автоматически.
--       Это более короткий путь; оба замыкают одно и то же утверждение.
-- Здесь используется путь (2); в комментарии зафиксирован путь (1).
theorem P3_succ_ne_zero : ∀ x : VRObj, VRObj.succ x ≠ VRObj.void := by
  intro x h
  exact VRObj.noConfusion h

-- ============================================================
-- §10. P4 — Theorem 5: инъективность t (Part II, §10)
-- ============================================================

-- §10, Theorem 5 (P4 в VR): инъективность t по Лейбницевой идентичности.
-- Точная форма препринта: = в Theorem 5 — vrEq (Def. 2, §4).
-- Доказательство через «разоблачающий» предикат:
--   q z := match z with | void => True | succ w => p w
-- Тогда q (succ x) = p x и q (succ y) = p y по def-редукции,
-- а vrEq (succ x) (succ y) применённый к q даёт p x ↔ p y напрямую.
theorem P4_succ_inj_leibniz :
    ∀ x y : VRObj, vrEq (VRObj.succ x) (VRObj.succ y) → vrEq x y :=
  fun _ _ h p =>
    h (fun z => match z with
      | VRObj.void   => True
      | VRObj.succ w => p w)

-- Практическая форма P4 через Lean Eq (нужна в Theorem 11, §5.7).
-- Доказывается независимо от P4_succ_inj_leibniz через VRObj.succ.injEq —
-- автоматически выводимый принцип инъективности конструктора.
-- Обратный мост vrEq → Eq не используется и не нужен.
theorem P4_succ_inj :
    ∀ x y : VRObj, VRObj.succ x = VRObj.succ y → x = y :=
  fun _ _ h =>
    congrArg (fun z => match z with | VRObj.void => VRObj.void | VRObj.succ w => w) h

-- ============================================================
-- §10. P5 — Theorem 6: принцип индукции (Part II, §10)
-- ============================================================

-- §10, Theorem 6 (P5 в VR): принцип индукции.
-- P5 — аксиома индукции Пеано в терминах VR.
-- Совпадает с A4_induction (§2, Этап 1): новое доказательство не требуется.
-- Вводится как именованный алиас для явного соответствия Пеано-аксиомам.
theorem P5_induction : ∀ (P : VRObj → Prop),
    P VRObj.void → (∀ x, P x → P (VRObj.succ x)) → ∀ n, P n :=
  A4_induction

-- ============================================================
-- §11. Theorem 11 — VR–PA equivalence (Part II, §11)
-- ============================================================

-- O_inv : VRObj → Nat — обратная к O.
--
-- Соответствует гёделевскому кодированию в §10 препринта:
--   ⌜∅⌝ := 0
--   ⌜t(x)⌝ := ⌜x⌝ + 1
-- Препринт описывает это как метатеоретическую процедуру.
-- В Lean это внутренняя структурная функция, проверяемая компилятором.
-- Это усиление: метатеория препринта становится первопорядковой функцией.
--
-- Существование O_inv как функции VRObj → Nat не вводит Nat в VR.
-- VRObj и Nat — два независимых типа; O и O_inv — мост между ними.
def O_inv : VRObj → Nat
  | VRObj.void   => 0
  | VRObj.succ x => O_inv x + 1

-- Левая обратность: O_inv (O n) = n.
-- Доказывается индукцией по n; congrArg (· + 1) разворачивает шаг.
theorem O_left_inv : ∀ n : Nat, O_inv (O n) = n := by
  intro n
  induction n with
  | zero      => rfl
  | succ k ih => exact congrArg (· + 1) ih

-- Правая обратность: O (O_inv x) = x.
-- Доказывается индукцией по x; congrArg succ разворачивает шаг.
theorem O_right_inv : ∀ x : VRObj, O (O_inv x) = x := by
  intro x
  induction x with
  | void      => rfl
  | succ y ih => exact congrArg VRObj.succ ih

-- Изоморфизм сложения: O (m + n) = vadd (O m) (O n).
-- Прямая индукция по n; T1–T4 не используются.
-- Рекурсия Nat.add и vadd симметрична по правому аргументу.
theorem O_add : ∀ m n : Nat, O (m + n) = vadd (O m) (O n) := by
  intro m n
  induction n with
  | zero      => rfl
  | succ k ih => exact congrArg VRObj.succ ih

-- Изоморфизм умножения: O (m * n) = vmul (O m) (O n).
-- Прямая индукция по n; использует O_add. T1–T4 не используются.
theorem O_mul : ∀ m n : Nat, O (m * n) = vmul (O m) (O n) := by
  intro m n
  induction n with
  | zero      => rfl
  | succ k ih =>
    -- Nat.mul: m * (k+1) = m*k + m  (def)
    -- vmul:   vmul (O m) (succ (O k)) = vadd (vmul (O m) (O k)) (O m)  (def)
    show O (m * k + m) = vadd (vmul (O m) (O k)) (O m)
    rw [O_add]
    exact congrArg (fun x => vadd x (O m)) ih

-- Изоморфизм степени: O (m ^ n) = vpow (O m) (O n).
-- Прямая индукция по n; использует O_mul. T1–T4 не используются.
theorem O_pow : ∀ m n : Nat, O (m ^ n) = vpow (O m) (O n) := by
  intro m n
  induction n with
  | zero      => rfl
  | succ k ih =>
    -- Nat.pow: m^(k+1) = m^k * m  (def)
    -- vpow:   vpow (O m) (succ (O k)) = vmul (vpow (O m) (O k)) (O m)  (def)
    show O (m ^ k * m) = vmul (vpow (O m) (O k)) (O m)
    rw [O_mul]
    exact congrArg (fun x => vmul x (O m)) ih

-- §11 (Часть II), Equivalence Theorem.
--
-- Препринт: «VR и PA арифметически эквивалентны: ℕ-теоретическое содержание
-- одной системы соответствует биективно ℕ-теоретическому содержанию другой».
-- Сформулировано как метатеоретическая эквивалентность множеств теорем.
--
-- Lean даёт усиленную форму: структурный изоморфизм Nat ≃ VRObj
-- как конкретный конструктивный объект, сохраняющий все операции.
-- Из этого препринтовая эквивалентность теорем следует тривиально:
-- любая теорема, доказанная для одной стороны, переносится через
-- forward/backward.
--
-- Девять полей покрывают:
--   биекцию (forward + backward + left_inv + right_inv),
--   сохранение нуля и преемника (preserve_zero + preserve_succ),
--   сохранение арифметики (preserve_add + preserve_mul + preserve_pow).
structure VR_PA_iso where
  forward       : Nat → VRObj
  backward      : VRObj → Nat
  left_inv      : ∀ n, backward (forward n) = n
  right_inv     : ∀ x, forward (backward x) = x
  preserve_zero : forward 0 = VRObj.void
  preserve_succ : ∀ n, forward (n + 1) = VRObj.succ (forward n)
  preserve_add  : ∀ m n, forward (m + n) = vadd (forward m) (forward n)
  preserve_mul  : ∀ m n, forward (m * n) = vmul (forward m) (forward n)
  preserve_pow  : ∀ m n, forward (m ^ n) = vpow (forward m) (forward n)

def Theorem_11_VR_PA : VR_PA_iso := {
  forward       := O
  backward      := O_inv
  left_inv      := O_left_inv
  right_inv     := O_right_inv
  preserve_zero := O_zero
  preserve_succ := O_succ
  preserve_add  := O_add
  preserve_mul  := O_mul
  preserve_pow  := O_pow
}

end VR
