# Preimage-Chain Lower Bounds for Superpermutations

[English](README.md) | [简体中文](README.zh-CN.md)

This repository provides a Lean 4 formalization of the paper *Preimage-Chain Corrections, Primitive-Block Rigidity, and New Lower Bounds for Superpermutations*. The project proves the corrected unconditional pathwise lower bound and lifts it to a global lower bound for superpermutations, together with direct numerical corollaries for `k = 5, …, 14`.

The formalization uses Lean 4.31.0 and precisely fixes the Hunter–Raudvere baseline and mathlib versions through locked Lake dependencies.

## Main Results

The public entry point [``PreimageChain.lean``](PreimageChain.lean) exports the following final theorems:

| Lean theorem | Description |
| --- | --- |
| ``PreimageChain.actual_reduced_pathwise_bound_closed`` | Every `σ²`-reduced Hamiltonian path satisfies the corrected pathwise lower bound |
| ``PreimageChain.pathwise_new_bound_closed`` | Every Hamiltonian path satisfies the unconditional `PathwiseNewBound` |
| ``PreimageChain.superperm_new_bound_closed`` | For all `k ≥ 5`, establishes the unconditional global lower bound for superpermutations |
| ``PreimageChain.superperm_numerical_bounds_closed`` | Directly proves the ten lower bounds for `k = 5, …, 14` listed in the paper's numerical table |

The global theorem is formally stated as follows:

```lean
theorem superperm_new_bound_closed
    {k : ℕ} (hk : 5 ≤ k) :
    Numerics.hunterBound k + Numerics.gamma k hk ≤ Hunter.Ssuper k
```

The numerical corollaries have been fully closed as follows:

| `k` | Lower bound for `Ssuper k` | `k` | Lower bound for `Ssuper k` |
| ---: | ---: | ---: | ---: |
| 5 | 153 | 10 | 4,033,080 |
| 6 | 869 | 11 | 43,916,235 |
| 7 | 5,892 | 12 | 522,610,764 |
| 8 | 46,118 | 13 | 6,746,523,219 |
| 9 | 408,418 | 14 | 93,890,256,441 |

## Paper

- [English PDF](paper/pdfs/Preimage_Chain_New_Lower_Bounds_EN_Academic_Polished.pdf)
- [Chinese PDF](paper/pdfs/Preimage_Chain_New_Lower_Bounds_ZH_Academic_Polished.pdf)
- [Bilingual PDF, English followed by Chinese](paper/pdfs/Preimage_Chain_New_Lower_Bounds_Bilingual_EN_then_ZH_Academic_Polished.pdf)
- [Formalization and Deterministic-Computational Audit Supplement](anc/Preimage_Chain_New_Lower_Bounds_Supplement_v4_Lean.zip)

The supplement is version `4.0.1-lean-formalized-release`, with SHA-256:

```text
8ce335b549b5c52c4ffbbe91f1a75528ebdbd8d9e3de49d21002c32d14a0dd65
```

## Pinned Environment

| Component | Pinned version |
| --- | --- |
| Lean | `4.31.0` |
| Hunter–Raudvere Lean library | `d45222190031d162feb1f6f3cf5fe2d11fab726d` |
| mathlib | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` jointly pin the complete build environment.

Hunter and mathlib are retrieved by Lake and are not included in this repository as vendored source code.

## Reproducibility and Verification

After installing [elan](https://github.com/leanprover/elan) and Git, run the following commands from the repository root:

```bash
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

To check that the active Lean source contains no `sorry`, `admit`, or project-defined `axiom` declarations:

```bash
rg -n '\bsorry\b|\badmit\b|^\s*axiom\b' \
  --glob '*.lean' \
  --glob '!.lake/**' .
```

The expected output is empty.

An isolated verification can also be performed with Docker:

```bash
docker build -t preimage-chain-verify .
docker run --rm preimage-chain-verify
```

The GitHub Actions workflow is manually triggered through `workflow_dispatch` and runs the same build, axiom-audit, and placeholder-scan checks.

## Trust Boundary

[`AxiomCheck.lean`](AxiomCheck.lean) runs `#print axioms` on the principal intermediate results and final public theorems.

The audit results for all four final theorems contain only:

```text
propext Classical.choice Quot.sound
```

There are no unfinished proofs or newly introduced axioms in the active source code.

The underlying permutation definitions, overlap graphs, Hunter transformations, and Hunter–Raudvere baseline results are provided by the Hunter Lean library at the pinned commit. Accordingly, the precise claim of this repository is that the paper's new unconditional pathwise lower bound, global superpermutation lower bound, and corresponding hierarchical combinatorial arguments have been formalized.

This repository does not claim to reverify the Lean kernel, mathlib, the Hunter library, or all external software from first principles.

For the complete verification scope and reproducibility specification, see [`VERIFICATION.md`](VERIFICATION.md).

## Repository Structure

```text
PreimageChain/       Formal definitions, intermediate lemmas, and final proof modules
PreimageChain.lean   Unified public entry point
AxiomCheck.lean      Entry point for auditing axiom dependencies
lean-toolchain       Lean version pin
lakefile.toml        Lake project configuration and direct dependency declarations
lake-manifest.json   Complete dependency lockfile
Dockerfile           Isolated reproducibility environment
VERIFICATION.md      Build, axiom, and placeholder-audit specification
CITATION.cff         Software citation metadata
paper/               English, Chinese, and bilingual paper PDFs
anc/                 Formalization and deterministic-computation audit supplement
```

## Citation

When citing this formalization project, please use the metadata provided in [`CITATION.cff`](CITATION.cff) and cite the corresponding version of the paper as well.

## License

Unless otherwise stated for third-party materials, the original code, documentation, and paper materials in this repository are licensed under the [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/) license (CC BY 4.0).

Copyright © 2026 Xiaolong Liu.

See [`LICENSE`](LICENSE) for the complete terms.

Third-party dependencies are not covered by this repository's license and remain subject to their respective licenses.
