/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import StatMech.Hamiltonian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder

noncomputable section
namespace MicroHamiltonian

variable {D : Type} (H : MicroHamiltonian D) (d : D)

/-- The partition function corresponding to a given MicroHamiltonian. This is a function taking a thermodynamic β, not a temperature.
It also depends on the data D defining the system extrinsincs.

 * Ideally this would be an NNReal, but ∫ (NNReal) doesn't work right now, so it would just be a separate proof anyway
-/
def PartitionZ (β : ℝ) : ℝ :=
  ∫ (config : H.dim d → ℝ),
    let E := H.H config
    if h : E = ⊤ then 0 else Real.exp (-β * (E.untop h))

/-- The partition function as a function of temperature T instead of β. -/
def PartitionZT (T : ℝ) : ℝ :=
  PartitionZ H d (1/T)

/-- The Internal Energy, U or E, defined as -∂(ln Z)/∂β. Parameterized here with β. -/
def InternalU (β : ℝ) : ℝ :=
  -deriv (fun β' ↦ (PartitionZ H d β').log) β

/-- The Helmholtz Free Energy, -T * ln Z. Also denoted F. Parameterized here with temperature T, not β. -/
def HelmholtzA (T : ℝ) : ℝ :=
  -T * (PartitionZT H d T).log

/-- The entropy, defined as the -∂A/∂T. Function of T. -/
def EntropyS (T : ℝ) : ℝ :=
  -deriv (HelmholtzA H d) T

/-- The entropy, defined as ln Z + β*U. Function of β. -/
def EntropySβ (β : ℝ) : ℝ :=
  (PartitionZ H d β).log + β * InternalU H d β

/-- To be able to compute or define anything from a Hamiltonian, we need its partition function to be
a computable integral. A Hamiltonian is ZIntegrable at β if PartitionZ is Lesbegue integrable and nonzero.
-/
def ZIntegrable (β : ℝ) : Prop :=
  MeasureTheory.Integrable (fun (config : H.dim d → ℝ) ↦
    let E := H.H config;
    if h : E = ⊤ then 0 else Real.exp (-β * (E.untop h))
  ) ∧ (H.PartitionZ d β ≠ 0)

/--
This Prop defines the most common case of ZIntegrable, that it is integrable at all finite temperatures
(aka all positive β).
-/
def PositiveβIntegrable : Prop :=
  ∀ β > 0, H.ZIntegrable d β

variable {H d}

/-
Need the fact that the partition function Z is differentiable. Assume it's integrable.
Letting μ⁻(H,E) be the measure of {x | H(x) ≤ E}, then for nonzero β,
∫_0..∞ exp(-βE) (dμ⁻/dE) dE =
∫ exp(-βH) dμ =
∫ (1/β * ∫_H..∞ exp(-βE) dE) dμ =
∫ (1/β * ∫_-∞..∞ exp(-βE) χ(E ≤ H) dE) dμ =
1/β * ∫ (∫ exp(-βE) χ(E ≤ H) dμ) dE =
1/β * ∫ exp(-βE) * μ⁻(H,E) dE

so this will be differentiable if
∫ exp(-βE) * μ⁻(H,E) dE
is, aka if the Laplace transform is differentiable.
See e.g. https://math.stackexchange.com/q/84382/127777
For this we really want the fact that the Laplace transform is analytic wherever it's absolutely convergent,
which is (as Wikipedia informs) an easy consequence of Fubini's theorem + Morera's theorem. However, Morera's
theorem isn't in mathlib yet. So this proof is still pending
-/
/- The analytic identities relating `PartitionZ`, `EntropyS`, `EntropySβ`, and `InternalU`
require Laplace-transform smoothness results that are not yet formalized in mathlib.
We therefore keep only the definitions in this file and leave the differential identities
to the concrete ensemble developments that establish the needed regularity hypotheses. -/

end MicroHamiltonian

--! Specializing to a system of particles in space

namespace NVEHamiltonian
open MicroHamiltonian

variable (H : NVEHamiltonian) (d : ℕ × ℝ)

/-- Pressure, as a function of T. Defined as the conjugate variable to volume. -/
def Pressure (T : ℝ) : ℝ :=
  let (n, V) := d;
  -deriv (fun V' ↦ HelmholtzA H (n, V') T) V

end NVEHamiltonian
