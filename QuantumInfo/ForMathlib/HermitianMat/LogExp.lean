/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Log

/-!
Compatibility shim for older imports that expected a combined `LogExp` module.

`HermitianMat.exp` lives in `CFC.lean`, which is already imported by `Log.lean`.
-/
