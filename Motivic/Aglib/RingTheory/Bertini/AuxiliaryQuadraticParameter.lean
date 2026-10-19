/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticInfinityAvoidance

/-! # A compactifying coordinate inside the unchanged quadratic parameter family -/
@[expose] public noncomputable section
open _root_.MvPolynomial
universe u
namespace QuadraticIncidence
variable (k : Type u) [Field k] {N : Type u} (d : ℕ)

/-- One auxiliary row is adjoined without changing any of the original `d` rows. -/
def prependParameters (a : N → k) (c : Fin d × N → k) : Fin (d + 1) × N → k :=
  fun q => Fin.cases (a q.2) (fun i => c (i, q.2)) q.1

/-- Substitute only the auxiliary coefficients, retaining every original parameter. -/
def specializeAuxiliary (a : N → k) :
    MvPolynomial (Fin (d + 1) × N) k →ₐ[k] MvPolynomial (Fin d × N) k :=
  aeval (fun q => Fin.cases (C (a q.2)) (fun i => X (i, q.2)) q.1)

/-- Literal specialization commutes with evaluation in the unchanged original rows. -/
theorem eval_specializeAuxiliary (a : N → k) (c : Fin d × N → k)
    (f : MvPolynomial (Fin (d + 1) × N) k) :
    eval c (specializeAuxiliary k d a f) = eval (prependParameters k d a c) f := by
  have he : (eval c).comp (specializeAuxiliary k d a).toRingHom =
      eval (prependParameters k d a c) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [specializeAuxiliary]
    · rintro ⟨i, e⟩
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [specializeAuxiliary, prependParameters]
  exact DFunLike.congr_fun he f

/-- A nonzero condition on the full same-family space leaves a nonempty principal
open on the original rows after choosing one auxiliary row over the infinite ground field. -/
theorem exists_specializeAuxiliary_ne_zero [Infinite k]
    (f : MvPolynomial (Fin (d + 1) × N) k) (hf : f ≠ 0) :
    ∃ a : N → k, specializeAuxiliary k d a f ≠ 0 := by
  by_contra! h
  apply hf
  apply MvPolynomial.funext
  intro c
  let a := fun e => c (0, e)
  let b := fun q : Fin d × N => c (q.1.succ, q.2)
  have he : prependParameters k d a b = c := by
    funext q
    rcases q with ⟨i, e⟩
    exact Fin.cases rfl (fun _ => rfl) i
  have hz := congrArg (eval b) (h a)
  simpa only [eval_specializeAuxiliary, he, map_zero] using hz

end QuadraticIncidence
