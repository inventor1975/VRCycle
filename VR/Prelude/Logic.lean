-- VR/Prelude/Logic.lean — unique existence, on `[]` (Mathlib's `∃!`, reproduced so that the VR core
-- depends on Lean alone; curator, 2026-09-13). The notation is scoped: `open scoped VRCycle.Logic`.

namespace VRCycle

/-- `ExistsUnique p`: exactly one `x` with `p x`. -/
def ExistsUnique {α : Sort _} (p : α → Prop) : Prop := ∃ x, p x ∧ ∀ y, p y → y = x

namespace Logic
scoped syntax "∃! " ident ", " term : term
scoped macro_rules
  | `(∃! $x:ident, $p) => `(VRCycle.ExistsUnique fun $x => $p)
end Logic

end VRCycle
