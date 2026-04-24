/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

/-!
# Dimensional Analysis

Physical dimensions represented as vectors of integer exponents over the seven
SI base dimensions: length (L), mass (M), time (T), electric current (I),
thermodynamic temperature (Θ), amount of substance (N), luminous intensity (J).

* `Dimension` : tuple of exponents forming an abelian group under multiplication
* Standard SI base and derived dimensions
* Dimensional consistency theorems for physical laws

## References

* Bureau International des Poids et Mesures, *The International System of Units (SI)*
-/

/-- Physical dimension as SI base dimension exponents: L, M, T, I, Θ, N, J. -/
structure Dimension where
  length : ℤ
  mass : ℤ
  time : ℤ
  current : ℤ
  temperature : ℤ
  amount : ℤ
  luminosity : ℤ
  deriving DecidableEq, Repr

namespace Dimension

def dimensionless : Dimension := ⟨0, 0, 0, 0, 0, 0, 0⟩

instance : One Dimension := ⟨dimensionless⟩

def mul (d₁ d₂ : Dimension) : Dimension :=
  ⟨d₁.length + d₂.length, d₁.mass + d₂.mass, d₁.time + d₂.time,
   d₁.current + d₂.current, d₁.temperature + d₂.temperature,
   d₁.amount + d₂.amount, d₁.luminosity + d₂.luminosity⟩

instance : Mul Dimension := ⟨mul⟩

def inv (d : Dimension) : Dimension :=
  ⟨-d.length, -d.mass, -d.time, -d.current, -d.temperature, -d.amount, -d.luminosity⟩

instance : Inv Dimension := ⟨inv⟩

def div (d₁ d₂ : Dimension) : Dimension :=
  ⟨d₁.length - d₂.length, d₁.mass - d₂.mass, d₁.time - d₂.time,
   d₁.current - d₂.current, d₁.temperature - d₂.temperature,
   d₁.amount - d₂.amount, d₁.luminosity - d₂.luminosity⟩

instance : Div Dimension := ⟨div⟩

/-- Raise a dimension to an integer power. -/
def zpow (d : Dimension) (n : ℤ) : Dimension :=
  ⟨d.length * n, d.mass * n, d.time * n,
   d.current * n, d.temperature * n, d.amount * n, d.luminosity * n⟩

theorem mul_comm (d₁ d₂ : Dimension) : d₁ * d₂ = d₂ * d₁ := by
  simp [HMul.hMul, Mul.mul, mul, Int.add_comm]

theorem mul_assoc (d₁ d₂ d₃ : Dimension) : d₁ * d₂ * d₃ = d₁ * (d₂ * d₃) := by
  simp [HMul.hMul, Mul.mul, mul, Int.add_assoc]

theorem mul_one (d : Dimension) : d * 1 = d := by
  show mul d dimensionless = d
  cases d; simp [mul, dimensionless]

theorem one_mul (d : Dimension) : 1 * d = d := by rw [mul_comm]; exact mul_one d

theorem mul_inv (d : Dimension) : d * d⁻¹ = 1 := by
  show mul d (inv d) = dimensionless
  cases d; simp [mul, inv, dimensionless]

theorem div_eq_mul_inv (d₁ d₂ : Dimension) : d₁ / d₂ = d₁ * d₂⁻¹ := by
  simp [HDiv.hDiv, Div.div, div, HMul.hMul, Mul.mul, mul, Inv.inv, inv, sub_eq_add_neg]

/-! ## SI base dimensions -/

def Length : Dimension := ⟨1, 0, 0, 0, 0, 0, 0⟩
def Mass : Dimension := ⟨0, 1, 0, 0, 0, 0, 0⟩
def Time : Dimension := ⟨0, 0, 1, 0, 0, 0, 0⟩
def Current : Dimension := ⟨0, 0, 0, 1, 0, 0, 0⟩
def Temperature : Dimension := ⟨0, 0, 0, 0, 1, 0, 0⟩
def Amount : Dimension := ⟨0, 0, 0, 0, 0, 1, 0⟩
def Luminosity : Dimension := ⟨0, 0, 0, 0, 0, 0, 1⟩

/-! ## Derived dimensions -/

def Velocity : Dimension := Length / Time
def Acceleration : Dimension := Velocity / Time
def Force : Dimension := Mass * Acceleration
def Energy : Dimension := Force * Length
def Power : Dimension := Energy / Time
def Pressure : Dimension := Force / (Length.zpow 2)
def Momentum : Dimension := Mass * Velocity
def AngularMomentum : Dimension := Momentum * Length
def Charge : Dimension := Current * Time
def Voltage : Dimension := Energy / Charge
def Entropy : Dimension := Energy / Temperature

/-! ## Dimensional consistency proofs -/

private theorem simp_dim (d₁ d₂ : Dimension) : d₁ = d₂ ↔
    d₁.length = d₂.length ∧ d₁.mass = d₂.mass ∧ d₁.time = d₂.time ∧
    d₁.current = d₂.current ∧ d₁.temperature = d₂.temperature ∧
    d₁.amount = d₂.amount ∧ d₁.luminosity = d₂.luminosity := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro ⟨h1, h2, h3, h4, h5, h6, h7⟩; cases d₁; cases d₂; simp_all

/-- Force: `[M L T⁻²]`. -/
theorem force_dim : Force = ⟨1, 1, -2, 0, 0, 0, 0⟩ := by
  simp [Force, Mass, Acceleration, Velocity, Length, Time,
        HDiv.hDiv, Div.div, div, HMul.hMul, Mul.mul, mul]

/-- Energy: `[M L² T⁻²]`. -/
theorem energy_dim : Energy = ⟨2, 1, -2, 0, 0, 0, 0⟩ := by
  simp [Energy, Force, Mass, Acceleration, Velocity, Length, Time,
        HDiv.hDiv, Div.div, div, HMul.hMul, Mul.mul, mul]

/-- Power: `[M L² T⁻³]`. -/
theorem power_dim : Power = ⟨2, 1, -3, 0, 0, 0, 0⟩ := by
  simp [Power, Energy, Force, Mass, Acceleration, Velocity, Length, Time,
        HDiv.hDiv, Div.div, div, HMul.hMul, Mul.mul, mul]

/-- Momentum: `[M L T⁻¹]`. -/
theorem momentum_dim : Momentum = ⟨1, 1, -1, 0, 0, 0, 0⟩ := by
  simp [Momentum, Mass, Velocity, Length, Time,
        HDiv.hDiv, Div.div, div, HMul.hMul, Mul.mul, mul]

/-- Charge: `[I T]`. -/
theorem charge_dim : Charge = ⟨0, 0, 1, 1, 0, 0, 0⟩ := by
  simp [Charge, Current, Time, HMul.hMul, Mul.mul, mul]

/-- `Force` is defined as `Mass * Acceleration`, so this is true by definition.
    The non-trivial consistency checks are below (e.g. `kinetic_energy_dim`). -/
theorem force_def_unfold :
    Mass * Acceleration = Force := by simp [Force]

/-- Kinetic energy `½mv²` has dimensions of energy. -/
theorem kinetic_energy_dim :
    Mass * (Velocity * Velocity) = Energy := by
  simp [Energy, Force, Velocity, Acceleration, Mass, Length, Time,
        HMul.hMul, Mul.mul, mul, HDiv.hDiv, Div.div, div]

/-- The ideal gas law `PV = nRT` is dimensionally consistent:
    `[Pressure × Volume] = [Energy]`. -/
theorem ideal_gas_law_dim :
    Pressure * (Length.zpow 3) = Energy := by decide +kernel

/-! ## Verification Tests -/

section Tests

/-- The seven base dimensions are all distinct. -/
example : Length ≠ Mass := by decide
example : Length ≠ Time := by decide
example : Mass ≠ Time := by decide
example : Current ≠ Temperature := by decide

/-- Dimensionless is the identity for multiplication. -/
example (d : Dimension) : d * 1 = d := mul_one d
example (d : Dimension) : 1 * d = d := one_mul d

/-- Every dimension has an inverse. -/
example (d : Dimension) : d * d⁻¹ = 1 := mul_inv d

/-- Associativity of dimension multiplication. -/
example (a b c : Dimension) : a * b * c = a * (b * c) := mul_assoc a b c

/-- Commutativity of dimension multiplication. -/
example (a b : Dimension) : a * b = b * a := mul_comm a b

/-- Division is multiplication by inverse. -/
example (a b : Dimension) : a / b = a * b⁻¹ := div_eq_mul_inv a b

/-- Velocity: `[L T⁻¹]`. -/
theorem velocity_dim : Velocity = ⟨1, 0, -1, 0, 0, 0, 0⟩ := by
  simp [Velocity, Length, Time, HDiv.hDiv, Div.div, div]

/-- Acceleration: `[L T⁻²]`. -/
theorem acceleration_dim : Acceleration = ⟨1, 0, -2, 0, 0, 0, 0⟩ := by
  simp [Acceleration, Velocity, Length, Time,
        HDiv.hDiv, Div.div, div]

/-- Pressure: `[M L⁻¹ T⁻²]`. -/
theorem pressure_dim : Pressure = ⟨-1, 1, -2, 0, 0, 0, 0⟩ := by decide +kernel

/-- Angular momentum: `[M L² T⁻¹]`. -/
theorem angular_momentum_dim : AngularMomentum = ⟨2, 1, -1, 0, 0, 0, 0⟩ := by
  simp [AngularMomentum, Momentum, Mass, Velocity, Length, Time,
        HDiv.hDiv, Div.div, div, HMul.hMul, Mul.mul, mul]

/-- Voltage: `[M L² T⁻³ I⁻¹]`. -/
theorem voltage_dim : Voltage = ⟨2, 1, -3, -1, 0, 0, 0⟩ := by
  simp [Voltage, Energy, Charge, Force, Mass, Acceleration, Velocity,
        Length, Time, Current,
        HDiv.hDiv, Div.div, div, HMul.hMul, Mul.mul, mul]

/-- Entropy: `[M L² T⁻² Θ⁻¹]`. -/
theorem entropy_dim : Entropy = ⟨2, 1, -2, 0, -1, 0, 0⟩ := by
  simp [Entropy, Energy, Force, Mass, Acceleration, Velocity,
        Length, Time, Temperature,
        HDiv.hDiv, Div.div, div, HMul.hMul, Mul.mul, mul]

/-- Coulomb's constant `k` in `F = kq₁q₂/r²` has dimensions `[M L³ T⁻⁴ I⁻²]`. -/
theorem coulombs_law_dim :
    Force * Length * Length / (Charge * Charge) =
    ⟨3, 1, -4, -2, 0, 0, 0⟩ := by
  simp [Force, Charge, Mass, Acceleration, Velocity,
        Length, Time, Current,
        HDiv.hDiv, Div.div, div, HMul.hMul, Mul.mul, mul]

/-- Gravitational constant `G` has dimensions `[L³ M⁻¹ T⁻²]`. -/
theorem gravitational_constant_dim :
    Force * Length * Length / (Mass * Mass) =
    ⟨3, -1, -2, 0, 0, 0, 0⟩ := by
  simp [Force, Mass, Acceleration, Velocity, Length, Time,
        HDiv.hDiv, Div.div, div, HMul.hMul, Mul.mul, mul]

/-- Squaring a dimension doubles all exponents. -/
example : Length.zpow 2 = ⟨2, 0, 0, 0, 0, 0, 0⟩ := by simp [zpow, Length]
example : Time.zpow 3 = ⟨0, 0, 3, 0, 0, 0, 0⟩ := by simp [zpow, Time]
example : Mass.zpow (-1) = ⟨0, -1, 0, 0, 0, 0, 0⟩ := by simp [zpow, Mass]

end Tests

end Dimension
