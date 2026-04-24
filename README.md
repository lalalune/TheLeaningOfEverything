# The Leaning Of Everything

`TheLeaningOfEverything` is a Lean 4 project for building a checked foundation of mathematics
and mathematical physics. The goal is to prove the structural results that let major areas of
mathematics explain each other: algebra, analysis, geometry, probability, information theory,
quantum theory, relativity, statistical mechanics, field theory, and the connective tissue between
them.

The repository started from finite-dimensional quantum information theory. It is now growing into a
broader formal library: a place where foundational definitions, theorem statements, and proofs are
made precise enough that Lean can check them.

## What This Is

This project is not a collection of informal notes. It is a proof engineering effort.

The intended standard is:

- state concepts in reusable mathematical language
- prove the lemmas needed to move between fields
- keep definitions close to mathlib conventions when possible
- isolate reusable infrastructure under `ForMathlib` namespaces
- replace sketchy theorem shells with Lean-checked proofs before treating code as part of the
  supported surface

The long-term ambition is a unified formal account of major mathematics: not separate islands of
formalization, but a network of shared foundations that can support serious theorem proving across
physics, information, and pure mathematics.

## Current Scope

The active library surface includes:

- `QuantumInfo`: finite-dimensional quantum states, channels, entropy, capacity, entanglement,
  resource theory, and supporting operator facts
- `ClassicalInfo`: probability distributions, classical channels, entropy, and capacity
- `StatMech`: statistical mechanics foundations and examples
- `Mathematics`, `Units`, and `Meta`: shared infrastructure, dimensional analysis, and project
  tooling
- physics-oriented libraries including `QuantumMechanics`, `Relativity`, `QFT`, `QEC`,
  `ClassicalMechanics`, `Electromagnetism`, `Thermodynamics`, `Particles`, `Cosmology`,
  `CondensedMatter`, `Optics`, `SpaceAndTime`, and `StringTheory`

Some areas are mature enough to serve as dependencies for other files. Others are active
formalization fronts. The build is the source of truth: code that is imported by `lakefile.lean`
must elaborate under Lean.

## Repository Layout

- `QuantumInfo/ForMathlib/`: reusable matrix, Hermitian, unitary, convexity, and analysis facts that
  are candidates for eventual upstreaming or mathlib-style reuse
- `QuantumInfo/Finite/`: finite-dimensional quantum information theory
- `ClassicalInfo/`: classical information theory
- `StatMech/`: statistical mechanics
- domain folders such as `Relativity/`, `QFT/`, `QuantumMechanics/`, `Units/`, and
  `Mathematics/`: broader formalization targets
- `lakefile.lean`: the authoritative list of Lean libraries built by the package

## Build

```bash
lake exe cache get
lake build
```

Useful targeted builds:

```bash
lake build QuantumInfo
lake build ClassicalInfo
lake build StatMech
```

The project tracks Lean through `lean-toolchain` and dependency revisions through
`lake-manifest.json`.

## Direction

The near-term work is to keep extracting reusable proof infrastructure while tightening the proof
standard:

- remove or replace unfinished theorem shells
- prove the analytic and order-theoretic lemmas needed by entropy and information theory
- make finite-dimensional quantum information a stable core library
- connect physics-facing definitions back to shared mathematical foundations
- upstream broadly useful lemmas when they are clean enough for mathlib

The long-term goal is simple to state and hard to execute: make the foundations of major
mathematics and mathematical physics explicit, composable, and checked by Lean.

## License and Citation

This repository is released under the MIT License; see [LICENSE](./LICENSE).

If you cite the repository, use:

```bibtex
@misc{theleaningofeverything,
  author = {Meiburg, Alex and contributors},
  title = {The Leaning Of Everything},
  year = {2026},
  publisher = {GitHub},
  journal = {GitHub repository},
  howpublished = {\url{https://github.com/lalalune/TheLeaningOfEverything}},
}
```
