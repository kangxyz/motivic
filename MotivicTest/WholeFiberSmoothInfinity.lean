/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.WholeFiberSmoothInfinity
public import Lean

/-! # The same retained rows supply smoothness and infinity avoidance -/
public noncomputable section
open QuadraticIncidence
universe u

example (k : Type u) [Field k] {N : Type u} (d : ℕ)
    (a : N → k) (c : Fin d × N → k) (i : Fin d) (e : N) :
    prependParameters k d a c (i.succ, e) = c (i, e) := rfl

open Lean in
run_cmd do
  for name in #[``exists_wholeFiber_smooth_infinity,
      ``exists_specializeAuxiliary_ne_zero, ``eval_specializeAuxiliary] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Same original rows: whole-fiber smoothness and infinity avoidance, standard foundations."
