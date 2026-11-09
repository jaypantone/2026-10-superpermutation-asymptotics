# Superpermutation Almanac submission

This branch packages the result as a batch for the
[Superpermutation Almanac](https://superpermutations.com/lean). The released
proof in `lean/` is unchanged. The files at the root are:

- `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`, which make the
  root a Lake project that reads `lean/` as a library. Mathlib is pinned to
  the same commit, written with the address the Almanac requires.
- `AlmanacDefs.lean`, `AlmanacStatement.lean` and `AlmanacChallenge.lean`,
  the Almanac's scaffold files (version 5). The judge writes its own copies
  over them. `AlmanacChallenge.lean` is a placeholder containing `sorry`;
  nothing imports it.
- `AlmanacAdapter.lean`, which proves both statements from the released
  theorems. It first shows that `Covers` is the Almanac's
  `IsSuperpermutation` and that the Almanac's `fact` is `Nat.factorial`.
- `AlmanacSolution.lean`, which states the batch:
  - `asymptotic_upper_four : Almanac.AsymptoticUpperAt 4 2`, the template
    statement of the upper bound for the coefficient of `(n-4)!`;
  - `explicit_error : AlmanacAdapter.ExplicitError`, a custom statement: for
    every `n >= 8 * 10^12 * 352^4 * 6^61`,
    `|S(n) - F3(n) - 2(n-4)!| <= 400 (n-4)! n^(-1/61)`. The constant 400
    bounds `remainderConstant = 148 * C^(1/61) + 4`, where
    `C = 8 * 10^12 * 352^4`.

`python3 lean/almanac.py --objects-workspace <checked workspace>` checks
the new modules. It confirms that each of the 506 released modules in the
import closure has a successful checked object built from the identical
source. It then compiles the three root modules under the same guard as
`build.py`, prints the statements' axioms, and checks both statements with
NanoDa. The record in `verification/almanac/` shows that Lean compiled the
new modules and that both statements use only `propext`, `Classical.choice`
and `Quot.sound`. NanoDa 0.4.19 checked their 36,092 declarations with no
errors. This check did not recompile the released modules; the October build
and NanoDa records cover them.

The release files listed in `release-manifest.json` are unchanged, so
`python3 tools/verify_release.py` still passes on this branch. The new
record is `verification/almanac/20261109T212143.488205Z.json`, with the
statements NanoDa printed beside it.
