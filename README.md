# First-Class Relationships as a Representation Threshold: Lean 4 development

Lean 4 code accompanying version 2 of arXiv:2603.13603:

> *First-Class Relationships as a Representation Threshold: Identity, Time,
> Confidence, and Causation*
> Matthew Alford ([ORCID](https://orcid.org/0009-0007-3856-8362)), 2026

Version 1 of the paper, *The Equivalence Theorem: First-Class Relationships
for Structurally Complete Database Systems*, claimed that four requirements
were mutually equivalent. That claim is withdrawn. The formalization that
accompanied version 1 is kept at the tag [`v1`](../../tree/v1); it is not
maintained and its statements should not be cited as results.

## What is proved

The development covers weakened forms of parts (b) and (c) of the paper's
Theorem 2. It models a representation with one relationship construct whose
participant slots may or may not hold relationships.

| Paper | Lean (`FirstClass/Threshold.lean`) |
|---|---|
| COMPOSE: every relationship can occupy a participant slot and be read back | `Compose` |
| First-class relationships, in this model: COMPOSE plus a relationship builder | `FC` |
| P3, evidential-basis clause (one assessment per relationship) | `P3` |
| P4, causal links between relationships (no roles or attributes) | `P4` |
| Theorem 2 (b): P3 implies COMPOSE; P4 implies COMPOSE | `p3_compose`, `p4_compose` |
| Theorem 2 (c): COMPOSE with a builder represents P3 and P4 | `fc_to_p3`, `fc_to_p4` |
| Given a builder, P3 (or P4) holds exactly when FC does | `p3_iff_fc`, `p4_iff_fc` |
| A construct of n-ary rows in which no slot denotes a row has a builder but no COMPOSE, hence no P4 | `relational_not_compose`, `relational_not_p4` |
| Counting fact behind Lemma 1: a binary edge among three distinct participants omits one | `binary_decomposition_failure` |

## What is not proved

Read these limits before relying on the code.

- `p3_compose` and `p4_compose` follow directly from the definitions of `P3`
  and `P4`; the paper says so in its remark on scope.
- `P3` has one assessment per relationship and does not model the source,
  method or assessed value. `P4` has no roles or attributes.
- `FC` here is COMPOSE together with a builder, and the builder does not
  store attributes. STORE, RETRIEVE, QUERY, ATTACH, arity, confidence values
  and valid time are not modelled, so Theorem 2 (a) and Lemma 1 are argued
  in the paper only.
- The `relational` construct has no row-denoting slot by construction. It
  does not model SQL, where a key can denote a row.
- Corollary 3 (what must be built) is not formalized.
- `binary_decomposition_failure` is a standalone fact; it is not connected
  to `System`.

## Build

Install Lean 4 with [elan](https://github.com/leanprover/elan), then:

```bash
lake build
```

Lake downloads the toolchain named in `lean-toolchain` (Lean 4.14.0) on the
first build. The development uses only core Lean, has no `sorry`, and its
theorems depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`; check with `#print axioms`).

## Layout

```
lakefile.lean             Lake build configuration
lean-toolchain            Lean version
FirstClass.lean           Root import
FirstClass/Threshold.lean All definitions and proofs
```

## Citation

```bibtex
@article{alford2026threshold,
  title={First-Class Relationships as a Representation Threshold: Identity, Time, Confidence, and Causation},
  author={Alford, Matthew},
  year={2026},
  eprint={2603.13603},
  archivePrefix={arXiv},
  primaryClass={cs.DB},
  note={Version 2. ORCID: 0009-0007-3856-8362}
}
```
