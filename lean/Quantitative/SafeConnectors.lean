import SuperpermutationUpperBound43586371.Levels
import SuperpermutationUpperBound.CircleTransport.Tracks

/-!
# Literal connector circles and tagged-port witnesses

The low and high insertion lists are actual finite circle lists. Their
literal rotations cover every local completion port, including the endpoint
port `H.length` separately from port zero. The final theorem derives actual
`SafeComp` from an explicit table of selected advanced row occurrences.

The remaining transport obligation is to construct that occurrence table
from a literal F-successor run and the port-orbit decomposition. It is not
assumed that compatible full rows automatically form an F-successor run.
`LiteralFRun` below records the stronger hypothesis needed for extraction.
-/

namespace CoefficientTwoPrecision.SafeConnectors

open SuperpermutationUpperBound SuperpermutationUpperBound.Transport
open SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Certificates.CircleBase
open SuperpermutationUpperBound43586371

/-- A full run follows the specified literal F successor with one fixed mobile. -/
def LiteralFRun (source : List (Row Nat)) (start R : Nat) (H : List Nat) (mobile : Nat) : Prop :=
  start + R ≤ source.length ∧ ∀ j < R,
    (rowAt source (start + j)).base = rot H j ++ [mobile] ∧
    (rowAt source (start + j)).visible = (rowAt source (start + j)).base.length

/-- Rotation before an inserted letter moves its insertion position down exactly. -/
theorem rotate_insert_before (H : List Nat) (f b j : Nat)
    (hj : j ≤ b) (hb : b ≤ H.length) :
    rot (insertLetter H f b) j = insertLetter (rot H j) f (b - j) := by
  induction j generalizing H b with
  | zero => simp
  | succ j ih =>
    have hbpos : 0 < b := by omega
    have hj' : j ≤ b - 1 := by omega
    have hb' : b - 1 ≤ (rot H 1).length := by simp only [rot_length]; omega
    calc
      rot (insertLetter H f b) (j + 1)
          = rot (rot (insertLetter H f b) 1) j := by rw [rot_add]; congr 1; omega
      _ = rot (insertLetter (rot H 1) f (b - 1)) j := by
          rw [rot_insertLetter_one_pos H f b hbpos hb]
      _ = insertLetter (rot (rot H 1) j) f ((b - 1) - j) := ih _ _ hj' hb'
      _ = insertLetter (rot H (j + 1)) f (b - (j + 1)) := by
          have hadd : 1 + j = j + 1 := Nat.add_comm 1 j
          have hsub : b - 1 - j = b - (j + 1) := by omega
          rw [rot_add, hadd, hsub]

/-- Rotating past the inserted letter realizes the distinct final literal port. -/
theorem rotate_insert_endpoint (H : List Nat) (f b : Nat) (hb : b ≤ H.length) :
    rot (insertLetter H f b) (b + 1) = insertLetter (rot H b) f H.length := by
  have htake : (H.take b).length = b := by simp [List.length_take, Nat.min_eq_left hb]
  calc
    rot (insertLetter H f b) (b + 1) = H.drop b ++ H.take b ++ [f] := by
      simpa only [htake] using rot_insertLetter_at_cut H f b
    _ = rot H b ++ [f] := by rw [rot_eq_drop_append_take_of_le H b hb]
    _ = insertLetter (rot H b) f H.length := by
      rw [← rot_length H b, insertLetter_at_length]

/-- The actual two lists of circles used for one advanced component. -/
def connectorCircles (H : List Nat) (f g L : Nat) : List (List Nat) :=
  ((List.range g).map (fun t => insertLetter H f (g * (L - 1) + t))) ++
    ((List.range g).map (fun t => insertLetter H f (H.length - g + t)))

@[simp] theorem connectorCircles_length (H : List Nat) (f g L : Nat) :
    (connectorCircles H f g L).length = 2 * g := by
  simp only [connectorCircles, List.length_append, List.length_map, List.length_range]
  omega

theorem connectorCircle_contains {H : List Nat} {f g L : Nat} {C : List Nat}
    (hC : C ∈ connectorCircles H f g L) : f ∈ C := by
  rcases List.mem_append.mp hC with hC | hC <;>
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hC <;> simp

theorem connectorCircle_length {H : List Nat} {f g L : Nat} {C : List Nat}
    (hC : C ∈ connectorCircles H f g L) : C.length = H.length + 1 := by
  rcases List.mem_append.mp hC with hC | hC <;>
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hC <;> simp

theorem connectorCircles_valid (H : List Nat) (f g L : Nat)
    (hH : H.Nodup) (hf : f ∉ H) :
    CircleFamilyValid (H.length + 1) (connectorCircles H f g L) := by
  intro C hC
  refine ⟨connectorCircle_length hC, ?_⟩
  rcases List.mem_append.mp hC with hC | hC <;>
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hC <;>
    exact insertLetter_nodup hH hf _

theorem connectorCircles_support {H : List Nat} {f g L : Nat} {C : List Nat}
    (hC : C ∈ connectorCircles H f g L) {a : Nat} (ha : a ∈ C) : a ∈ f :: H := by
  rcases List.mem_append.mp hC with hC | hC <;>
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hC <;>
    simpa using ha

private theorem grid_interval (a g L q : Nat) (hg : 0 < g) (hL : 0 < L)
    (hlo : a ≤ q) (hhi : q < a + g * L) :
    ∃ u < L, ∃ t < g, a + g * (L - 1) + t = g * u + q := by
  let v := (q - a) / g
  let t := (q - a) % g
  have ht : t < g := Nat.mod_lt _ hg
  have hdiv : t + g * v = q - a := Nat.mod_add_div (q - a) g
  have hv : v < L := by
    by_contra hv
    have hmul : g * L ≤ g * v := Nat.mul_le_mul_left g (by omega)
    omega
  let u := L - 1 - v
  have hu : u < L :=
    lt_of_le_of_lt (Nat.sub_le (L - 1) v) (Nat.sub_lt hL Nat.one_pos)
  have huv : u + v = L - 1 := by change L - 1 - v + v = L - 1; omega
  have hmul : g * u + g * v = g * (L - 1) := by rw [← Nat.mul_add, huv]
  refine ⟨u, hu, t, ht, ?_⟩
  omega

/-- The two insertion intervals cover all local ports by literal row-head equalities. -/
theorem covers_local_ports (H : List Nat) (f g L : Nat)
    (hg : 0 < g) (hL : 0 < L) (hgL : g * L ≤ H.length)
    (hcover : H.length ≤ 2 * (g * L))
    (q : Nat) (hq : q ≤ H.length) :
    ∃ u < L, ∃ C ∈ connectorCircles H f g L, ∃ k < C.length,
      rot C k = insertLetter (rot H (g * u)) f q := by
  have hbase : g * (L - 1) + g = g * L := by
    calc
      g * (L - 1) + g = g * ((L - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = g * L := by rw [Nat.sub_add_cancel (by omega : 1 ≤ L)]
  have hgH : g ≤ H.length := by omega
  by_cases hlast : q = H.length
  · subst q
    let b := g * (L - 1)
    have hb : b < H.length := by dsimp [b]; omega
    refine ⟨L - 1, by omega, insertLetter H f b, ?_, b + 1, ?_, ?_⟩
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨0, List.mem_range.mpr hg, by simp [b]⟩
    · simp only [insertLetter_length]
      omega
    · exact rotate_insert_endpoint H f b hb.le
  · have hqH : q < H.length := by omega
    by_cases hlow : q < g * L
    · obtain ⟨u, hu, t, ht, hgap⟩ := grid_interval 0 g L q hg hL (Nat.zero_le _) (by simpa using hlow)
      have hgap' : g * (L - 1) + t = g * u + q := by simpa using hgap
      have hb : g * (L - 1) + t < H.length := by omega
      refine ⟨u, hu, insertLetter H f (g * (L - 1) + t), ?_, g * u, ?_, ?_⟩
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩
      · simp only [insertLetter_length]
        omega
      · have hr := rotate_insert_before H f (g * (L - 1) + t) (g * u) (by omega) hb.le
        have he : g * (L - 1) + t - g * u = q := by omega
        simpa only [he] using hr
    · have hstart : H.length - g * L ≤ q := by omega
      have hsum : H.length - g * L + g * L = H.length := Nat.sub_add_cancel hgL
      obtain ⟨u, hu, t, ht, hgap⟩ := grid_interval (H.length - g * L) g L q hg hL hstart (by omega)
      have hbform : H.length - g * L + g * (L - 1) = H.length - g := by omega
      have hgap' : H.length - g + t = g * u + q := by simpa only [hbform] using hgap
      have hb : H.length - g + t < H.length := by omega
      refine ⟨u, hu, insertLetter H f (H.length - g + t), ?_, g * u, ?_, ?_⟩
      · apply List.mem_append_right
        exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩
      · simp only [insertLetter_length]
        omega
      · have hr := rotate_insert_before H f (H.length - g + t) (g * u) (by omega) hb.le
        have he : H.length - g + t - g * u = q := by omega
        simpa only [he] using hr

/-- Selected exceptional advanced occurrences, with their actual prefix port map.
This is the specific extraction obligation supplied by an F-run and the
advanced-prefix identity; it contains no safe-incidence assumption. -/
structure SelectedOccurrences (W : List (Row Nat)) (H : List Nat) (g L shift : Nat) where
  row : Fin L → Nat
  row_lt : ∀ u, row u < W.length
  head : ∀ u, (rowAt W (row u)).head = rot H (g * u.val)
  prefixShift : ∀ u, ∀ J : Fin (H.length + 1),
    completionExit (W.take (row u)) J.val = (J.val + shift) % (H.length + 1)

/-- A literal row occurrence and its true prefix port give semantic safe incidence. -/
theorem incidence_of_occurrence (W : List (Row Nat)) (C : List Nat) (f h : Nat)
    (J : Fin h) (i q k : Nat) (hi : i < W.length) (hf : f ∈ C) (hk : k < C.length)
    (he : completionExit (W.take i) J.val = q)
    (hr : rot C k = insertLetter (rowAt W i).head f q)
    (hn : 3 ≤ h + 1) (hlen : ∀ r ∈ W, r.base.length = h + 1)
    (hkind : ∀ r ∈ W, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    SafeIncidence W f J C := by
  let p : MixedPointer := ⟨0, J.val, 0, i, q, k⟩
  have hp : p.Valid [W] [C] f h := by
    exact ⟨by simp [p], J.isLt, by simp [p], hi, hf, hk, he, hr⟩
  have hs := p.sound hp hn hlen hkind
  simpa only [p, componentAt, circleAt, List.getElem?_cons_zero, Option.getD_some,
    Fin.eta] using hs

/-- Every tagged advanced completion port is safely met by the actual small circle list. -/
theorem safe_of_selected_occurrences (W : List (Row Nat)) (H : List Nat) (f g L shift : Nat)
    (hg : 0 < g) (hL : 0 < L) (hgL : g * L ≤ H.length)
    (hcover : H.length ≤ 2 * (g * L)) (hH : 1 ≤ H.length)
    (occ : SelectedOccurrences W H g L shift)
    (hlen : ∀ r ∈ W, r.base.length = H.length + 2)
    (hkind : ∀ r ∈ W, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    SafeComp W f (H.length + 1) (connectorCircles H f g L) := by
  intro J
  let q := (J.val + shift) % (H.length + 1)
  have hq : q ≤ H.length := by
    have := Nat.mod_lt (J.val + shift) (by omega : 0 < H.length + 1)
    dsimp [q]
    omega
  obtain ⟨u, hu, C, hC, k, hk, he⟩ := covers_local_ports H f g L hg hL hgL hcover q hq
  let u' : Fin L := ⟨u, hu⟩
  refine ⟨C, hC, incidence_of_occurrence W C f (H.length + 1) J (occ.row u') q k
    (occ.row_lt u') (connectorCircle_contains hC) hk (occ.prefixShift u' J) ?_ (by omega) ?_ hkind⟩
  · rw [occ.head]
    exact he
  · intro r hr
    simpa only [Nat.add_assoc] using hlen r hr

end CoefficientTwoPrecision.SafeConnectors

#print axioms CoefficientTwoPrecision.SafeConnectors.covers_local_ports
#print axioms CoefficientTwoPrecision.SafeConnectors.safe_of_selected_occurrences
