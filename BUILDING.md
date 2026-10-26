# Reproducing the result

The project pins Lean `leanprover/lean4:v4.35.0` and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
`lean/lake-manifest.json` also pins the auxiliary packages. Do not run
`lake update` when reproducing this snapshot.

## The existing shared installation on this Mac

From the repository root:

```sh
python3 lean/build.py --inventory
python3 lean/build.py Precision
python3 lean/nanoda.py
```

The inventory command checks the complete import closure and the existing
expanded dependency objects without invoking Lean. The build stages project
sources and writes its objects under `~/Library/Caches/LeanShared/workspaces/`.
It reuses the fixed expanded dependency store and the compiler under `~/.elan`.
It does not install a compiler, clone Mathlib, or modify the dependency store.

The runners use one project lock and one compiler or checker at a time.
Lean runs with `-M4096 -j1`, one Lean thread, and priority `nice 10`.
The guard enforces a 120-second limit per module, a three-hour build-stage
limit, an aggregate sampled RSS threshold of 6 GiB, normal host memory
pressure, at least 25 percent reported free host memory, and a 15 GiB disk
reserve. Sampling is not an operating-system hard memory limit. An unchanged
object is reused only when its successful stamp, source, imports, compiler,
dependency lock, and object hash match. A relocated checkout has its own
workspace; the release does not include or claim a second set of compiled objects.

The recorded successful build was made from the development location.
The release audit checks that all 509 published Lean sources match that
build. Relocation and documentation changes do not alter those proof sources.
The guarded runners require macOS host-monitoring tools. Existing projects
on this Mac must continue sharing the central dependencies; they should not
create a private Lake dependency tree inside Dropbox.

## A separate machine

The `lean/` directory is also a standard pinned Lake project. With the pinned
Lean toolchain and dependencies available, its ordinary build target is:

```sh
cd lean
lake build Precision
```

On a machine without the pinned dependency cache, the standard Mathlib cache
command is `lake exe cache get`. This downloads dependencies and compiled
cache files; use an existing matching expanded cache when one is available.
Keep the checkout and build products outside synchronized storage. The
standard Lake invocation does not provide this project's macOS resource guard.

The aggregate imports `Quantitative.StatementAudit` and the additional
trace-rotation infrastructure. The public mathematical theorems are in
`Quantitative.MainTheorems`. Every printed final axiom list should contain
only `propext`, `Classical.choice`, and `Quot.sound`.

## Independent verification with NanoDa

After a guarded build, `python3 lean/nanoda.py` uses the installed `leanexport`
and `nanoda_bin` beside the pinned Lean executable. The successful record used
lean4export 3.1.0 and NanoDa 0.4.19. The runner exports these targets together
with all their transitive declaration dependencies and proof bodies:

```text
CoefficientTwoPrecision.finite_covering_word
CoefficientTwoPrecision.shortest_length_error
CoefficientTwoPrecision.shortest_length_asymptotic
```

The exporter command is `leanexport Quantitative.MainTheorems --` followed
by those three names, in the built project environment. The NanoDa configuration
is included in the successful receipt. It permits exactly the three standard
axioms, rejects unpermitted axioms, enables the natural-number and string
extensions, and uses one thread. Export and checking have separate 120-second
limits under the same guard. The successful check took 24.924 seconds.

The 284,148,854-byte export stays in external build storage. Small receipts
and the target statements printed by NanoDa are saved under `verification/nanoda/`.
The published receipts preserve the historical paths and hashes from the
successful run; those paths are evidence of that run, not installation paths
required on another machine.

## The manuscript

The LaTeX entry point is `paper/main.tex`. With `pdflatex`, `bibtex`, and the
packages named in that source installed:

```sh
python3 tools/build_paper.py
```

The script builds in a temporary directory outside Dropbox and writes the
result to `paper/manuscript.pdf`. It does not modify the recorded verification
receipt. PDF metadata can make a rebuilt PDF's hash differ even with unchanged
TeX sources. The included PDF is the original visually inspected 30-page file.
