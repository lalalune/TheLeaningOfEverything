# Library Readiness Report

Generated status: **in progress**

## Required Gates

- [ ] Full `lake build` on clean checkout
  Current: dependency/config loading succeeds, but root build currently fails later in
  `QuantumInfo.ForMathlib.HermitianMat.CFC`.
- [x] Foundation audit (`tools/foundation_audit.sh --skip-build`)
  Current: passes with no skip globs and no static placeholder debt.
- [x] Layer import check (`tools/check_import_layers.sh`)
- [x] Theorem index regenerated (`tools/generate_theorem_index.sh`)
- [x] Consumer tests build (`Test.Consumer.Level1/2/3`)
- [ ] CI workflow green

## Current Notes

- Architecture/API/course prelude scaffolding is in place.
- Enforcement scripts and CI are defined in repository.
- `docs/THEOREM_INDEX.md` has been generated.
- Recent validation results:
  - `lake env lean --version` -> Lean 4.28.0.
  - `lake -R check-build` -> pass.
  - Manifest package checkouts match `lake-manifest.json`.
  - `lake build` -> fails in `QuantumInfo.ForMathlib.HermitianMat.CFC`.
  - `lake build Test` -> pass (Level1/2/3 consumer tests all pass).
  - `tools/check_import_layers.sh` -> pass.
  - `tools/generate_theorem_index.sh` -> pass.
  - `tools/library_gate.sh` -> not rerun in this pass.
- Final readiness remains blocked by the current root build failure and CI status,
  not by static `sorry`/`axiom`/vacuous-stub placeholders.
