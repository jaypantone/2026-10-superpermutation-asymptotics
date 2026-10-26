import Std

/-!
# Integer control grid with at most one common control per distinct block

For r rows and Q=r*A columns, define block (a,b), with a<A and b<Q,
to contain (i,(a*i+b)%Q) for i<r.  No primality or finite-field hypothesis
is used.  Equality at two distinct rows forces equality of both parameters:
Q divides (a-a')*(i-j), whose absolute value is strictly less than Q.

The theorem `intersection_at_most_one` formalizes the incidence geometry.
It does not formalize the finite-set cardinality counts, affine collision
deletions, parking schedule, or the asymptotic amplification theorem.
-/

namespace IntegerControlGrid

/-- The column of the control selected by block (a,b) in row i. -/
def column (r A a b i : Nat) : Nat := (a * i + b) % (r * A)

/-- Membership in a block, expressed directly for natural-number coordinates. -/
def InBlock (r A a b : Nat) (p : Nat × Nat) : Prop :=
  p.1 < r ∧ p.2 = column r A a b p.1

theorem difference_natAbs_lt (x y bound : Nat) (hx : x < bound) (hy : y < bound) :
    ((x : Int) - (y : Int)).natAbs < bound := by
  rcases Int.natAbs_eq ((x : Int) - (y : Int)) with h | h <;> omega

theorem equal_remainders_dvd (x y q : Nat) (h : x % q = y % q) :
    (q : Int) ∣ (x : Int) - (y : Int) := by
  apply Int.dvd_of_emod_eq_zero
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
  simpa only [Int.natCast_emod] using congrArg (fun n : Nat => (n : Int)) h

/-- The bounded determinant has absolute value below the full column period. -/
theorem determinant_natAbs_lt (r A a a' i j : Nat)
    (ha : a < A) (ha' : a' < A) (hi : i < r) (hj : j < r) :
    (((a : Int) - (a' : Int)) * ((i : Int) - (j : Int))).natAbs < r * A := by
  rw [Int.natAbs_mul]
  have habs := difference_natAbs_lt a a' A ha ha'
  have hrows := difference_natAbs_lt i j r hi hj
  simpa only [Nat.mul_comm A r] using Nat.mul_lt_mul_of_lt_of_lt habs hrows

/-- Two shared distinct rows determine both the slope and intercept.
The bounds already imply r>0 and A>0; no additional positivity assumptions
are needed, and no cancellation modulo a nonprime modulus is assumed. -/
theorem two_shared_rows (r A a a' b b' i j : Nat)
    (ha : a < A) (ha' : a' < A) (hb : b < r * A) (hb' : b' < r * A)
    (hi : i < r) (hj : j < r) (hij : i ≠ j)
    (hci : column r A a b i = column r A a' b' i)
    (hcj : column r A a b j = column r A a' b' j) :
    a = a' ∧ b = b' := by
  have hdi : ((r * A : Nat) : Int) ∣
      ((a : Int) * (i : Int) + (b : Int)) -
        ((a' : Int) * (i : Int) + (b' : Int)) := by
    simpa only [Int.natCast_add, Int.natCast_mul] using
      equal_remainders_dvd (a * i + b) (a' * i + b') (r * A) hci
  have hdj : ((r * A : Nat) : Int) ∣
      ((a : Int) * (j : Int) + (b : Int)) -
        ((a' : Int) * (j : Int) + (b' : Int)) := by
    simpa only [Int.natCast_add, Int.natCast_mul] using
      equal_remainders_dvd (a * j + b) (a' * j + b') (r * A) hcj
  have hd := Int.dvd_sub hdi hdj
  have hdet :
      (((a : Int) * (i : Int) + (b : Int)) -
        ((a' : Int) * (i : Int) + (b' : Int))) -
      (((a : Int) * (j : Int) + (b : Int)) -
        ((a' : Int) * (j : Int) + (b' : Int))) =
      ((a : Int) - (a' : Int)) * ((i : Int) - (j : Int)) := by
    simp only [Int.sub_mul, Int.mul_sub]
    omega
  rw [hdet] at hd
  have hsmall :
      (((a : Int) - (a' : Int)) * ((i : Int) - (j : Int))).natAbs <
        ((r * A : Nat) : Int).natAbs := by
    simpa [Int.natAbs_mul] using determinant_natAbs_lt r A a a' i j ha ha' hi hj
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hsmall
  have hslope : a = a' := by
    rcases Int.mul_eq_zero.mp hz with hs | hr
    · omega
    · omega
  subst a'
  have hbexpr :
      ((a : Int) * (i : Int) + (b : Int)) -
        ((a : Int) * (i : Int) + (b' : Int)) = (b : Int) - (b' : Int) := by omega
  rw [hbexpr] at hdi
  have hbsmall : ((b : Int) - (b' : Int)).natAbs < ((r * A : Nat) : Int).natAbs := by
    simpa [Int.natAbs_mul] using difference_natAbs_lt b b' (r * A) hb hb'
  have hbzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdi hbsmall
  exact ⟨rfl, by omega⟩

/-- Common controls in distinct blocks must lie in the same row. -/
theorem common_row_unique (r A a a' b b' i j : Nat)
    (ha : a < A) (ha' : a' < A) (hb : b < r * A) (hb' : b' < r * A)
    (hdistinct : (a, b) ≠ (a', b')) (hi : i < r) (hj : j < r)
    (hci : column r A a b i = column r A a' b' i)
    (hcj : column r A a b j = column r A a' b' j) : i = j := by
  by_cases hij : i = j
  · exact hij
  · obtain ⟨hslope, hintercept⟩ :=
      two_shared_rows r A a a' b b' i j ha ha' hb hb' hi hj hij hci hcj
    exact False.elim (hdistinct (Prod.ext hslope hintercept))

/-- Any two elements of the intersection of distinct blocks are equal.
This is the at-most-one-intersection statement without a finite-set library. -/
theorem intersection_at_most_one (r A a a' b b' : Nat)
    (ha : a < A) (ha' : a' < A) (hb : b < r * A) (hb' : b' < r * A)
    (hdistinct : (a, b) ≠ (a', b')) (p q : Nat × Nat)
    (hp : InBlock r A a b p) (hp' : InBlock r A a' b' p)
    (hq : InBlock r A a b q) (hq' : InBlock r A a' b' q) : p = q := by
  have hci : column r A a b p.1 = column r A a' b' p.1 := hp.2.symm.trans hp'.2
  have hcj : column r A a b q.1 = column r A a' b' q.1 := hq.2.symm.trans hq'.2
  have hrow := common_row_unique r A a a' b b' p.1 q.1
    ha ha' hb hb' hdistinct hp.1 hq.1 hci hcj
  apply Prod.ext hrow
  rw [hp.2, hq.2, hrow]

end IntegerControlGrid

#print axioms IntegerControlGrid.determinant_natAbs_lt
#print axioms IntegerControlGrid.two_shared_rows
#print axioms IntegerControlGrid.intersection_at_most_one
