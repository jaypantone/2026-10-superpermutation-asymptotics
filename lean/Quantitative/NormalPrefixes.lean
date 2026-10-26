import Quantitative.NormalContour
import Mathlib.Data.List.Count

/-!
# Exact prefixes of the repeated normal target word

Stationary indices are descending physical ranks. At update index n, the
target rank is n modulo k. Every smaller rank has been updated once in
the current batch, and every rank has been updated floor(n/k) times in
the preceding complete batches. These are exact statements about the
actual repeated list, used to instantiate the normal sweep offsets.
-/

namespace CoefficientTwoPrecision.NormalPrefixes

open PositiveParking NormalContour

variable {k : Nat}

theorem take_repeatWord {β : Type} (order : List β) (total t ell : Nat)
    (ht : t < total) (hell : ell ≤ order.length) :
    (repeatWord total order).take (t * order.length + ell) =
      repeatWord t order ++ order.take ell := by
  induction t generalizing total with
  | zero =>
    cases total with
    | zero => omega
    | succ total =>
      simpa only [Nat.zero_mul, Nat.zero_add, repeatWord, List.nil_append] using
        (List.take_append_of_le_length (l₂ := repeatWord total order) hell)
  | succ t ih =>
    cases total with
    | zero => omega
    | succ total =>
      have hindex : (t + 1) * order.length + ell = order.length + (t * order.length + ell) := by
        rw [Nat.succ_mul]
        omega
      change (order ++ repeatWord total order).take ((t + 1) * order.length + ell) =
        (order ++ repeatWord t order) ++ order.take ell
      rw [hindex, List.take_length_add_append, ih total (by omega), List.append_assoc]

theorem getElem?_repeatWord {β : Type} (order : List β) (total t ell : Nat)
    (ht : t < total) (hell : ell < order.length) :
    (repeatWord total order)[t * order.length + ell]? = order[ell]? := by
  induction t generalizing total with
  | zero =>
    cases total with
    | zero => omega
    | succ total =>
      simp only [Nat.zero_mul, Nat.zero_add, repeatWord, List.getElem?_append_left hell]
  | succ t ih =>
    cases total with
    | zero => omega
    | succ total =>
      have hindex : (t + 1) * order.length + ell = order.length + (t * order.length + ell) := by
        rw [Nat.succ_mul]
        omega
      change (order ++ repeatWord total order)[(t + 1) * order.length + ell]? = _
      rw [hindex, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact ih total (by omega)

theorem finRange_take_count (ell : Nat) (hell : ell ≤ k) (target : Fin k) :
    ((List.finRange k).take ell).count target = if target.val < ell then 1 else 0 := by
  rw [← List.count_map_of_injective ((List.finRange k).take ell) Fin.val Fin.val_injective target,
    List.map_take, map_finRange_val, List.take_range, Nat.min_eq_left hell, List.count_range]

theorem normal_prefix_count (total t ell : Nat) (ht : t < total) (hell : ell ≤ k) (target : Fin k) :
    ((repeatWord total (List.finRange k)).take (t * k + ell)).count target =
      t + if target.val < ell then 1 else 0 := by
  have htake := take_repeatWord (List.finRange k) total t ell ht (by simpa only [List.length_finRange] using hell)
  rw [List.length_finRange] at htake
  rw [htake, List.count_append, count_repeatWord, finRange_take_count ell hell target]
  have hcount : (List.finRange k).count target = 1 :=
    List.count_eq_one_of_mem (List.nodup_finRange k) (List.mem_finRange target)
  rw [hcount, Nat.mul_one]

theorem normal_count_at_index (hk : 0 < k) (total n : Nat) (hn : n < total * k) (target : Fin k) :
    ((repeatWord total (List.finRange k)).take n).count target =
      n / k + if target.val < n % k then 1 else 0 := by
  have hbatch : n / k < total := (Nat.div_lt_iff_lt_mul hk).mpr hn
  have hrem : n % k < k := Nat.mod_lt n hk
  have hindex : n = (n / k) * k + n % k := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod n k).symm
  have h := normal_prefix_count total (n / k) (n % k) hbatch hrem.le target
  rw [← hindex] at h
  exact h

theorem normal_target_at_index (hk : 0 < k) (total n : Nat) (hn : n < total * k) :
    (repeatWord total (List.finRange k))[n]? = some (⟨n % k, Nat.mod_lt n hk⟩ : Fin k) := by
  have hbatch : n / k < total := (Nat.div_lt_iff_lt_mul hk).mpr hn
  have hrem : n % k < k := Nat.mod_lt n hk
  have hindex : n = (n / k) * k + n % k := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod n k).symm
  have h := getElem?_repeatWord (List.finRange k) total (n / k) (n % k) hbatch
    (by simpa only [List.length_finRange] using hrem)
  rw [List.length_finRange, ← hindex] at h
  have hright : (List.finRange k)[n % k]? = some (⟨n % k, hrem⟩ : Fin k) := by
    rw [List.getElem?_eq_getElem (by simpa only [List.length_finRange] using hrem), List.getElem_finRange]
    rfl
  exact h.trans hright

end CoefficientTwoPrecision.NormalPrefixes

#print axioms CoefficientTwoPrecision.NormalPrefixes.normal_count_at_index
#print axioms CoefficientTwoPrecision.NormalPrefixes.normal_target_at_index
