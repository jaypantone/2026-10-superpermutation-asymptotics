import Quantitative.SourceFamilyAdapter

/-!
# A source-contour certificate from the actual full run

The head-word validity and support fields follow from the first source row
of the run. They need not be checked separately by the schedule construction.
-/

namespace CoefficientTwoPrecision.SourceFamilyAdapter

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.Certificates.CircleBase
open CoefficientTwoPrecision.SafeConnectors CoefficientTwoPrecision.SourceAdvancement

def SourceContour.of_run (A : List Nat) (h : Nat) (rows : List (Row Nat))
    (hc : ClosedTrail rows) (hb : BasedOn A 9 rows)
    (H : List Nat) (mobile start R L : Nat) (hH : H.length = h + 1)
    (run : LiteralFRun rows start R H mobile)
    (hL : 0 < L) (hfit : portGcd rows h * L ≤ R) (hR : R ≤ h + 1)
    (hcover : h + 1 ≤ 2 * (portGcd rows h * L)) : SourceContour A h := by
  have hRpos : 0 < R := lt_of_lt_of_le (Nat.mul_pos (portGcd_pos rows h) hL) hfit
  have hstart : start < rows.length := by have := run.1; omega
  have hmem : rowAt rows start ∈ rows := by
    have he : rowAt rows start = rows[start]'hstart := by
      simp [rowAt, List.getElem?_eq_getElem (l := rows) hstart]
    rw [he]
    exact List.getElem_mem hstart
  have hbase : (rowAt rows start).base = H ++ [mobile] := by
    simpa using (run.2 0 hRpos).1
  have hnd : H.Nodup := by
    have hn := (hb _ hmem).1.1
    rw [hbase] at hn
    exact (List.nodup_append.mp hn).1
  have hsupport : ∀ a ∈ H, a ∈ A := by
    intro a ha
    apply (hb _ hmem).2.1.mem_iff.mp
    rw [hbase]
    exact List.mem_append_left _ ha
  exact ⟨rows, hc, hb, H, hH, hnd, hsupport, mobile, start, R, L,
    run, hL, hfit, hR, hcover⟩

end CoefficientTwoPrecision.SourceFamilyAdapter

#print axioms CoefficientTwoPrecision.SourceFamilyAdapter.SourceContour.of_run
