/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Data.Fin.Basic
/-! # Literal dependent two-entry families

Intended upstream module:
`Aglib.Data.Fin.TwoCases`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.OriginalCorrectionNormDiagram`, `Norm.OriginalPairNormDiagram`.
-/

@[expose] public section
namespace Fin

/-- A dependent two-entry family with literal numeral evaluation rules. -/
def twoCases {M : Fin 2 → Sort _} (a : M 0) (b : M 1) : ∀ i, M i :=
  Fin.cases a (Fin.cases b (fun i => Fin.elim0 i))

@[simp] theorem twoCases_zero {M : Fin 2 → Sort _} (a : M 0) (b : M 1) :
    twoCases a b 0 = a := rfl

@[simp] theorem twoCases_one {M : Fin 2 → Sort _} (a : M 0) (b : M 1) :
    twoCases a b 1 = b := rfl

@[simp] theorem twoCases_mk_zero {M : Fin 2 → Sort _}
    (a : M 0) (b : M 1) (h : 0 < 2) : twoCases a b ⟨0, h⟩ = a := rfl

@[simp] theorem twoCases_mk_one {M : Fin 2 → Sort _}
    (a : M 0) (b : M 1) (h : 1 < 2) : twoCases a b ⟨1, h⟩ = b := rfl

end Fin
