/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.VonNeumann
import QuantumInfo.Finite.Entropy.Klein

/-!
This module keeps the maintained finite-dimensional quantum relative entropy interface.

The broader sandwiched Renyi development previously living here depended on unfinished analytic
proofs. It is intentionally not exposed as theorem declarations until that proof stack is completed.
-/

noncomputable section

variable {d d₂ : Type*}
variable [Fintype d] [Fintype d₂]
variable [DecidableEq d] [DecidableEq d₂]

open scoped InnerProductSpace RealInnerProductSpace HermitianMat
open Classical

/-- Klein's inequality for density matrices, in relative-entropy inner-product form. -/
theorem inner_log_sub_log_nonneg {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  simpa [HermitianMat.log] using
    HermitianMat.klein_inequality ρ.M σ.M ρ.zero_le σ.zero_le ρ.tr σ.tr h

/-- The quantum relative entropy `𝐃(ρ‖σ) := Tr[ρ (log ρ - log σ)]`, with value `⊤`
when the support condition fails. -/
def qRelativeEnt (ρ σ : MState d) : ENNReal :=
  if σ.M.ker ≤ ρ.M.ker then
    ENNReal.ofReal ⟪ρ.M, ρ.M.log - σ.M.log⟫
  else
    ⊤

notation "𝐃(" ρ "‖" σ ")" => qRelativeEnt ρ σ

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are contained. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    𝐃(ρ‖σ).toEReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  simp [qRelativeEnt, h, EReal.coe_ennreal_ofReal, max_eq_left (inner_log_sub_log_nonneg h)]
