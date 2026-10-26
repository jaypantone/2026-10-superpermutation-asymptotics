# Verification records

The final Lean build and the independent NanoDa check both passed. The
published proof sources and manuscript PDF are identical to their checked
development versions. `release-manifest.json` in the repository root records
the published files; `tools/verify_release.py` checks those hashes and their
agreement with the final proof and manuscript audits.

| Record | What it establishes |
| --- | --- |
| `final-audit.json` | The final result, compiler and dependency pins, all 509 local source hashes, final axioms, and links to the other audits |
| `modules/` | A successful Lean compilation receipt for each published module |
| `last-build.json` | The complete final aggregate build and reused checked objects |
| `final-statements.txt` | Lean's printed final theorem types and original definitions |
| `nanoda/20261026T113051.730276Z.json` | Independent verification of the three final targets and their complete exported proof dependencies |
| `nanoda/20261026T113051.730276Z-statements.txt` | The target statements and axioms printed by NanoDa |
| `manuscript.json` | The exact TeX and PDF hashes, clean LaTeX diagnostics, and inspection of all 30 pages |
| `compatibility.json`, `compatibility.patch`, `provenance.json` | The supplied source identities and explicit development adaptations |
| `line-counts.json` | Physical and nonblank line counts, with their scope |

NanoDa checked **36,079 declarations with no errors**, using only `propext`,
`Classical.choice`, and `Quot.sound`. All three targets were exported as
theorems with proof terms. The exported data, compiler, exporter, and checker
have recorded hashes. The first NanoDa attempt stopped before proof checking
because the statement-output file did not exist. Its receipt is retained;
the successful attempt created the file and reused the hash-checked export.

The matching Lean kernel also replayed `Quantitative.MainTheorems` against
its checked imports. A separate optional `--fresh` replay tried to recheck
every declaration in the whole imported environment and reached its 120-second
limit. That attempt is recorded as incomplete. It was distinct from the
successful ordinary Lean build and from NanoDa's successful check of the
actual final proof dependencies. `replay/` preserves the exact scopes and
outcomes rather than treating the timed-out attempt as a pass.

The original receipts include paths to the development checkout and external
workspace on the checking machine. They are retained unchanged as historical
evidence, not portable file locations. The complete source archive they refer
to is not included; every Lean module needed for the released result is
included. Failed development attempts, large exports, and compiled objects
remain in the development archive. `source-provenance.json` maps inherited
sources to paths in this release.

The all-local-sources count in `line-counts.json` also describes three auxiliary
modules outside the final dependency closure. They are not part of this release.
The 509-module closure and 214-module Quantitative counts apply directly here.

These records establish formal checking of the stated Lean theorem and its
dependencies. Human mathematical review of the manuscript remains pending.
