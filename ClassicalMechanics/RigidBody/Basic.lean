/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import SpaceAndTime.Space.Derivatives.Curl
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.LinearAlgebra.Matrix.Spectrum
/-!

# Rigid bodies

A rigid body is one where the distance and relative orientation between particles does not change.
In other words, the body remains undeformed.

In this module we will define the basic properties of a rigid body, including
- mass
- center of mass
- inertia tensor

## References
- Landau and Lifshitz, Mechanics, page 100, Section 32
-/

open Manifold

-- NOTE (`MEX5S`): The rigid-body definition currently uses linear maps from
-- smooth functions to `ℝ`; where possible this should be upgraded to
-- *continuous* linear maps.

/-- A Rigid body defined by its mass distribution. -/
structure RigidBody (d : ℕ) where
  /-- The mass distribution of the rigid body. -/
  ρ : C^⊤⟮𝓘(ℝ, Space d), Space d; 𝓘(ℝ, ℝ), ℝ⟯ →ₗ[ℝ] ℝ

namespace RigidBody

/-- The total mass of the rigid body. -/
def mass {d : ℕ} (R : RigidBody d) : ℝ := R.ρ ⟨fun _ => 1, contMDiff_const⟩

/-- The center of mass of the rigid body. -/
noncomputable def centerOfMass {d : ℕ} (R : RigidBody d) : Space d := ⟨fun i =>
  (1 / R.mass) • R.ρ ⟨fun x => x i, ContDiff.contMDiff (Space.eval_contDiff (d := d) (n := ⊤) i)⟩⟩

/-- The inertia tensor of the rigid body. -/
noncomputable def inertiaTensor {d : ℕ} (R : RigidBody d) :
    Matrix (Fin d) (Fin d) ℝ := fun i j =>
  R.ρ ⟨fun x => (if i = j then 1 else 0) * ∑ k : Fin d, (x k)^2 - x i * x j,
    ContDiff.contMDiff <| by
      have hsum : ContDiff ℝ ⊤ (fun x : Space d => ∑ k : Fin d, (x k)^2) := by
        simpa using
          (ContDiff.sum (s := (Finset.univ : Finset (Fin d)))
            (f := fun k : Fin d => fun x : Space d => (x k)^2)
            (fun k hk => (Space.eval_contDiff (d := d) (n := ⊤) k).pow 2))
      have hprod : ContDiff ℝ ⊤ (fun x : Space d => x i * x j) :=
        (Space.eval_contDiff (d := d) (n := ⊤) i).mul
          (Space.eval_contDiff (d := d) (n := ⊤) j)
      exact (contDiff_const.mul hsum).sub hprod⟩

lemma inertiaTensor_symmetric {d : ℕ} (R : RigidBody d) (i j : Fin d) :
    R.inertiaTensor i j = R.inertiaTensor j i := by
  simp only [inertiaTensor]
  congr
  funext x
  congr 1
  · congr 2
    exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)
  · ring

lemma inertiaTensor_isHermitian {d : ℕ} (R : RigidBody d) : R.inertiaTensor.IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp [R.inertiaTensor_symmetric]

/-- The principal moments of inertia, defined as the eigenvalues of the inertia tensor. -/
noncomputable def principalMoments {d : ℕ} (R : RigidBody d) : Fin d → ℝ :=
  Matrix.IsHermitian.eigenvalues R.inertiaTensor_isHermitian

/-- An orthogonal change of basis whose columns are principal axes of inertia. -/
noncomputable def principalAxes {d : ℕ} (R : RigidBody d) :
    Matrix.orthogonalGroup (Fin d) ℝ :=
  R.inertiaTensor_isHermitian.eigenvectorUnitary

/-- The translational contribution to the kinetic energy of a rigid body. -/
noncomputable def translationalKineticEnergy {d : ℕ} (R : RigidBody d) (V : Space d) : ℝ :=
  (1 / (2 : ℝ)) * R.mass * ⟪V, V⟫_ℝ

/-- The rotational contribution to the kinetic energy of a rigid body. -/
noncomputable def rotationalKineticEnergy {d : ℕ} (R : RigidBody d) (ω : Space d) : ℝ :=
  (1 / (2 : ℝ)) * ⟪ω, R.inertiaTensor.mulVec ω⟫_ℝ

/-- The kinetic energy of a rigid body splits into translational and rotational parts. -/
noncomputable def kineticEnergy {d : ℕ} (R : RigidBody d) (V ω : Space d) : ℝ :=
  R.translationalKineticEnergy V + R.rotationalKineticEnergy ω

/-- One can describe the motion of rigid body with a fixed (inertial) coordinate system (X,Y,Z)
    and a moving system (x₁,x₂,x₃) rigidly attached to the body. -/
structure coordinate_system (d : ℕ) where
  /-- The chosen origin of the coordinate system. -/
  origin : Space d
  /-- An orthogonal matrix encoding the coordinate axes. -/
  axes : Matrix.orthogonalGroup (Fin d) ℝ

/-- A rigid body in three-dimensional space has six degrees of freedom:
    three translational (for the position of its centre of mass) and three
    rotational (for its orientation). -/
/- Pending rigid-body formalization targets documented in this section:
- A three-dimensional rigid body has six degrees of freedom.
- Point velocities decompose as `v = V + Ω × r`.
- Angular velocity is independent of the chosen body-fixed coordinates.
- Motion decomposes into translation plus rotation about a reference point.
- The centre of mass moves as a particle carrying the total mass.
- Angular momentum about a point splits into orbital and spin parts.
- Inertial-frame translational dynamics satisfy `dP/dt = F`.
- Inertial-frame rotational dynamics satisfy `dM/dt = K`.
- Kinetic energy splits into translational and rotational contributions.
- The parallel-axis theorem relates inertia tensors at displaced origins.
-/

/-- Because the inertia tensor is real symmetric, there exists an orthogonal change of basis in
which it is diagonal. The columns of this matrix are principal axes of inertia. -/
theorem principal_axes_of_inertia {d : ℕ} (R : RigidBody d) :
    ∃ U : Matrix.orthogonalGroup (Fin d) ℝ,
      R.inertiaTensor = U.1 * Matrix.diagonal (RCLike.ofReal ∘ R.principalMoments) * U.1ᵀ := by
  refine ⟨R.principalAxes, ?_⟩
  simpa [principalAxes, principalMoments] using R.inertiaTensor_isHermitian.spectral_theorem

/-- None of the principal moments of inertia can exceed the sum of other two. -/
/- Pending formalization target:
none of the principal moments of inertia exceeds the sum of the other two.
-/

/-- An asymmetrical top is a three-dimensional rigid body whose principal moments are pairwise
distinct. -/
def asymmetrical_top (R : RigidBody 3) : Prop :=
  Pairwise fun i j => R.principalMoments i ≠ R.principalMoments j

/-- A symmetrical top is a three-dimensional rigid body for which exactly two principal moments of
inertia coincide. -/
def symmetrical_top (R : RigidBody 3) : Prop :=
  ∃ i j k : Fin 3,
    i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
    R.principalMoments i = R.principalMoments j ∧
    R.principalMoments j ≠ R.principalMoments k

/-- A spherical top is a three-dimensional rigid body whose principal moments are all equal. -/
def spherical_top (R : RigidBody 3) : Prop :=
  ∀ i j, R.principalMoments i = R.principalMoments j

/-- A rotating body-fixed frame is a coordinate system attached to the body
    that rotates with the body relative to an inertial (fixed) frame. The frame
    is characterised by its angular velocity vector Ω(t). -/
structure RotatingFrame (d : ℕ) extends coordinate_system d where
  /-- The instantaneous angular-velocity vector of the frame. -/
  angularVelocity : Space d

/-- The time derivative in the rotating frame, d'/dt, is the derivative
    of the components of a vector with respect to time when expressed in the
    rotating (body-fixed) frame. -/
/- The rotating-frame derivative is intentionally left as prose here; it has not been
introduced as a placeholder definition. -/

/-- For any vector field A(t), its inertial-frame time derivative equals the rotating-frame
    derivative plus the contribution from the frame rotation:
      (dA/dt)_inertial = (dA/dt)_rotating + Ω × A.
    Here Ω is the angular velocity of the rotating frame. -/
/- Pending rotating-frame formalization targets documented in this section:
- The inertial and rotating derivatives are related by the standard transport law.
- Linear momentum in a rotating frame satisfies `d'P/dt + Ω × P = F`.
- Angular momentum in a rotating frame satisfies `d'M/dt + Ω × M = K`.
- In principal axes, rotational dynamics reduce to Euler's equations.
- Steady rotations about principal axes admit the usual stability conditions.
- The intermediate-axis instability should follow from the linearized Euler system.
- Planar rigid-body motion reduces to a two-dimensional single-angular-velocity model.
- Power splits into translational and rotational contributions.
- Small oscillations about equilibrium are governed by the linearized energy expansion.
-/

end RigidBody
