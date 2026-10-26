# Mathematical statements and Lean correspondence

Written proof, independent review and kernel compilation are separate columns.
The final unconditional theorems have passed Lean 4.35.0. Earlier interface
lemmas retain their explicit parameters; SparseFamilyConstruction discharges
those parameters. Per-module receipts record compiler results and hashes. The review column
records independent AI reviews held in the development archive; human review
remains pending. The manuscript sources named below are in `paper/`.

| Mathematical statement | Lean declaration or obligation | Written proof | Independent review | Lean status |
|---|---|---|---|---|
| Role cancellation and parking avoidance | `PositiveParking.parking_restores_all_labels`, `parking_avoids`, `normal_cleanup_endpoint` | geometry.tex | AI geometry review | Passed 4.35.0; literal endpoint reconstruction is still separate |
| Actual crossing inventory and monodromy | `CrossingInventory`, `TraceDisplacement.closed_trace_excess`, `ActualMonodromy.actual_portGcd_le` | geometry.tex | AI geometry review | Passed 4.35.0 for the actual closed trace; LocalSourceContour instantiates it |
| Integer grid intersection | `IntegerControlGrid.intersection_at_most_one` | global.tex | AI geometry review and global review | Passed 4.35.0; actual cardinality and incidence counts also passed in ActiveGrid/ActiveIncidence |
| Joint state catalogue and reset | `Quantitative.JointStates` | geometry.tex | AI geometry review | Passed 4.35.0; actual scheduled containment and closure passed in ClosedTrace/LiteralEnvelope |
| Robust frame supply and labelled packing | `EnvelopeDegree.degree_64`, `PhysicalEnvelope.literal_mem`, `UniformPacking.exists_uniform_literal_separated` | geometry.tex | AI geometry review | Passed 4.35.0, including exact floor size and one selection uniform over every background and control relabeling |
| Literal schedules, normal count and prefix states | `NormalExactCount.normal_counts`, `TargetTrace.row_prefix_state`, `GlobalSimplicity.scheduleRows_pairwise`, `RepairRowCounts.repaired_row_error` | geometry.tex | AI geometry review | Passed 4.35.0, including exact normal count and actual compiled-program perturbation bound |
| Shared stationary controls in actual cyclic bases | `FiniteRoles.two_matches`, `ActualMatching.matched_cuts_eq`, `all_matches_diagonal` | geometry.tex | AI geometry review | Passed 4.35.0 |
| Guard and proximity deletions | `GlobalRetention.retention_error`, `SourceSelection.exists_selection` | global.tex | AI transfer review and geometry review | Passed 4.35.0, including both congruence cases and the actual surviving fraction |
| Simultaneous repair and collision exclusion | `RepairedSourceContour.construct_repair`, `CompiledEventAvoidance.event_prefix_avoids`, `CandidateCollision.actual_rows_disjoint` | global.tex | AI transfer review and geometry review | Passed 4.35.0; CandidateRowState connects actual canonical coordinates and repair avoidance, and GlobalSourceFamily proves global distinctness |
| Safe advanced connectors | `InitialNormalRun.initial_normal_run`, `ConnectorGrid.grid_choice`, `LocalSourceContour.construct_program` | assembly.tex | AI assembly review | Passed 4.35.0; the actual repaired source constructor supplies the untouched normal F-run and connector grid |
| Canonical insertion list and actual complement | `SourceUniverse`, `SourceComplement.selected_remaining_perm`, `SourceErasure.insertionAbove_of_erasure` | assembly.tex | AI assembly review | Passed 4.35.0 |
| Arbitrary-width Stage | `StageExtension.advance_width`, distinct from width-three `Stage.advance` | assembly.tex | AI assembly review | Passed 4.35.0; SparseFamilyConstruction instantiates the actual family |
| Source family to all Stage fields | `CanonicalSourceFamily.widthBlock`, `StageSourceCertificate.from_contours` | assembly.tex | AI assembly review | Passed 4.35.0; GlobalSourceFamily constructs the globally distinct contour list |
| Actual source count estimates | `ActualCountEstimates.estimates` | global.tex | AI transfer review | Passed 4.35.0 from actual retained contour counts and per-contour geometric estimates |
| Pending-mass estimate | `CoefficientTwoPrecision.pending_invariant`, `pending_le_four_div` | transfer.tex | AI transfer review | Passed 4.35.0 |
| Exact cost telescoping | `CoefficientTwoPrecision.cost_invariant` | transfer.tex | AI transfer review | Passed 4.35.0 |
| Binary length and polynomial threshold | `FiniteParameters`, `ConstructionParameters`, `CompletionEstimates` | transfer.tex | AI transfer review | Passed 4.35.0, including actual ceiling-defined parameters |
| Scheduled numerical coefficient bound | `SparseStageIteration`, `DenseStageIteration`, `ActualStageAssembly.final_stage` | transfer.tex | AI transfer review | Passed 4.35.0; the proved SparseFamilyConstruction.supplier discharges the family interface |
| Real exponent from integer parameter | `parameter_inverse_real_bound`, `lower_error_real_bound` | transfer.tex | AI transfer review | Passed 4.35.0 |
| Original coverage and F3 bridges | `covers_iff_isSuperpermutation`, `cast_F3`, `integer_bound_iff` | Introduction and transfer | Statement inspection | Passed 4.35.0 |
| Actual finite covering word, coefficient 2+74/r | `CoefficientTwoPrecision.finite_covering_word`, `original_finite_bound` | Entire manuscript | AI assembly review and AI transfer review | Passed 4.35.0 unconditionally, with original Covers and actual word |
| Original L and lower2 bound | Supplied `ConstAsym.L`, `L_le_length`, `lower2_L`, `lower2_ratio` | Imported result, exact source cited | Supplied provenance | Entire 4.35.0 proof closure passed |
| Two-sided n^(-1/61) asymptotic | `CoefficientTwoPrecision.shortest_length_asymptotic` | transfer.tex; written hypotheses discharged there | AI transfer review | Passed 4.35.0 unconditionally, using original L, F3 and rebuilt lower2 bound |

Additional checked construction steps are `StationarySuccessor.positive_update_realizes`
(actual literal F/S update), `StageEndpoints.initial_padded` (actual empty initial
stages), and `StageEndpoints.word_of_stage` (actual covering word from the original
Stage). `ScheduleArithmetic` checks the exact rounded sizes and finite tail
contraction. The actual repaired source family is constructed in GlobalSourceFamily and
instantiated at each Stage in SparseFamilyConstruction. The original dense-tail proof through `UniR.RRate8` has also passed the
new compiler. The complete original lower-bound closure through Remainder8 has now passed.

The final theorem types and original definitions are printed by
`Quantitative.StatementAudit`. The final finite and asymptotic theorems have
only `propext`, `Classical.choice` and `Quot.sound` in their axiom lists.
