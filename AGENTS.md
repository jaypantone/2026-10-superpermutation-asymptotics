# Working on this release

Preserve the mathematical meaning of the public theorem statements and the
attribution in NOTICE. Keep the proof, manuscript, and verification claims
consistent. The checked development uses Lean 4.35.0 and the exact Mathlib
revision in lean/lake-manifest.json.

On Jay's Mac, read /Users/jaypantone/Dropbox/Research/AI-work/LEAN_SETUP_FOR_AGENTS.md
before changing tooling. Reuse ~/.elan and ~/Library/Caches/LeanShared,
including expanded compiled dependencies. Keep compilers, dependency trees,
large exports, build products, and logs outside Dropbox. Use the guarded
runners and one compiler or checker at a time for this project. Do not raise
resource limits automatically or change a shared dependency store during builds.

The released Lean sources already passed Lean and NanoDa. Reorganizing
documentation does not require repeating expensive proof checks. If proof
sources change, check the changed modules and their affected dependents and
update the audit honestly. A file-hash check is not a new Lean or NanoDa run.

Do not add GitHub Actions. Keep build products, research archives, and large
export files out of Git. Retain successful verification records and distinguish
historical checks from checks of changed sources. Human mathematical review
has not yet been recorded.
