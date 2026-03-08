import Lake
open System Lake DSL

package «quantumInfo»

require "mathlib" from git "https://github.com/leanprover-community/mathlib4.git" @ "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib QuantumInfo

lean_lib ClassicalInfo

lean_lib StatMech

lean_lib Meta
lean_lib Thermodynamics
lean_lib Units
lean_lib Mathematics
lean_lib Mechanics
lean_lib ClassicalMechanics
lean_lib Electromagnetism
lean_lib Optics
lean_lib QuantumMechanics
lean_lib Relativity
lean_lib SpaceAndTime
lean_lib Particles
lean_lib QFT
lean_lib QEC
lean_lib CondensedMatter
lean_lib Cosmology
lean_lib StringTheory
lean_lib Physics
