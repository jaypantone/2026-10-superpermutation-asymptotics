import Mathlib.Data.List.Basic

/-! Small proved compatibility lemmas for the preserved source snapshots. -/

namespace List

theorem getD_eq_getElem {α : Type*} (l : List α) (fallback : α) {i : Nat}
    (hi : i < l.length) : l.getD i fallback = l[i]'hi := by
  rw [getD_eq_getElem?_getD, getElem?_eq_getElem hi]
  rfl

end List
