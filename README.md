# Equivalence Theorem — Lean 4 Formalization

Machine-checked formalization of **The Equivalence Theorem** from:

> *The Equivalence Theorem: First-Class Relationships for Structurally Complete Database Systems*
> Matthew Alford — [ORCID](https://orcid.org/0009-0007-3856-8362)
> Network Service Group, 2026

## What's Formalized

This Lean 4 project formalizes the core mathematical content of the paper:

| Paper Section | Lean 4 |
|---|---|
| Definition 5 (First-Class Object) | `FirstClassOps` structure |
| Definition 3 (P1: N-ary + Attributes) | `SatisfiesP1` structure |
| Definition 4 (P2: Temporal Validity) | `SatisfiesP2` structure |
| Definition 5 (P3: Uncertainty Quantification) | `SatisfiesP3` structure |
| Definition 6 (P4: Causal Relationships) | `SatisfiesP4` structure |
| Lemma 1 (Binary Decomposition Failure) | `binary_decomposition_failure` |
| Lemma 1 (FC ⇒ P1 ∧ P2 ∧ P3 ∧ P4) | `fc_implies_p1`, `fc_implies_p2`, `fc_implies_p3`, `fc_implies_p4` |
| Lemma 2 (P1 ⇒ FC) | `p1_implies_fc` |
| Lemma 3 (P2 ⇒ FC) | `p2_implies_fc` |
| Lemma 4 (P3 ⇒ FC) | `p3_implies_fc` |
| Lemma 5 (P4 ⇒ FC) | `p4_implies_fc` |
| **Theorem 1 (Equivalence Theorem)** | `equivalenceTheorem` |
| Corollary (All or Nothing) | `all_or_nothing` |
| Theorem 2 (Frame Problem Resolution) | `frame_problem_resolved`, `frame_persistence_chain` |
| Expressiveness Hierarchy | `hierarchy_strict` |
| Uncertainty Propagation | `chainConfidence`, `noisyOr` |

## Proof Status

All theorems type-check with **zero errors and zero `sorry`s**. `lake build` should complete with no warnings.

## Prerequisites

Install Lean 4 via [elan](https://github.com/leanprover/elan):

```bash
# Linux / macOS / WSL
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Windows (PowerShell)
Invoke-WebRequest -Uri https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 -OutFile elan-init.ps1
powershell -ExecutionPolicy Bypass -File elan-init.ps1
```

## Build & Type-Check

```bash
cd equivalence-lean4
lake build
```

If this is your first build, Lake will download the Lean toolchain (specified in `lean-toolchain`) automatically. The build takes ~1 minute.

A successful build with no errors means **every theorem and definition type-checks** — the proofs are machine-verified.

## Project Structure

```
equivalence-lean4/
├── lakefile.lean                    # Lake build configuration
├── lean-toolchain                   # Lean version (v4.14.0)
├── EquivalenceTheorem.lean          # Root import
├── EquivalenceTheorem/
│   └── Basic.lean                   # All definitions and proofs
└── README.md                        # This file
```

## How to Read the Code

If you're new to Lean 4, here's a quick guide:

- **`structure`** defines a record type (like a struct with fields)
- **`theorem`** states a proposition and provides its proof
- **`def`** defines a computable function or construction
- **`:=`** introduces the proof or definition body
- **`by`** enters tactic mode (step-by-step proof construction)
- **`sorry`** marks an incomplete proof (the type-checker accepts it but flags it)
- **`#eval`** runs a computation at compile time (used for sanity checks)

The formalization follows the paper section by section. Each Lean definition has a docstring (`/-- ... -/`) explaining the correspondence to the paper.

## Citation

If you use this formalization, please cite the paper:

```bibtex
@article{alford2026equivalence,
  title={The Equivalence Theorem: First-Class Relationships for Structurally Complete Database Systems},
  author={Alford, Matthew},
  year={2026},
  note={ORCID: 0009-0007-3856-8362}
}
```
