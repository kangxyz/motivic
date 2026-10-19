/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Single.Tensor.Elements
public import Aglib.Algebra.Homology.ShortComplex.ModuleQuasiIso

/-!
# Elementwise homology tests for Koszul tensor invariance

Quasi-isomorphisms of module complexes lift cycles modulo actual boundaries and
reflect boundaries. These elementary criteria will be applied to the two-column
coordinates of the actual Koszul tensor product.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-isomorphism lifts cycles modulo boundaries and reflects boundaries. -/
theorem moduleQuasiIso_iff
    {S T : ShortComplex (ModuleCat.{u} R)} (φ : S ⟶ T) :
    ShortComplex.QuasiIso φ ↔
      (∀ y : T.X₂, T.g y = 0 →
        ∃ (x : S.X₂) (w : T.X₁), S.g x = 0 ∧ φ.τ₂ x = y + T.f w) ∧
      (∀ x : S.X₂, S.g x = 0 →
        (∃ y : T.X₁, T.f y = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x) := by
  let γ : ShortComplex.LeftHomologyMapData φ
      S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData := default
  have hK (x : LinearMap.ker S.g.hom) : (γ.φK x).val = φ.τ₂ x.val := by
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp γ.commi) x
  have hH (x : LinearMap.ker S.g.hom) :
      γ.φH (Submodule.Quotient.mk x) = Submodule.Quotient.mk (γ.φK x) :=
    ConcreteCategory.congr_hom γ.commπ x
  rw [γ.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  constructor
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro y hy
      obtain ⟨x, hx⟩ := hsurj (Submodule.Quotient.mk (⟨y, hy⟩ : LinearMap.ker T.g.hom))
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [hH, Submodule.Quotient.eq] at hx
        obtain ⟨w, hw⟩ := hx
        refine ⟨x.val, w, x.property, ?_⟩
        have hw' := congrArg Subtype.val hw
        change T.f w = (γ.φK x).val - y at hw'
        rw [hK] at hw'
        exact (sub_eq_iff_eq_add.mp hw'.symm).trans (add_comm _ _)
    · intro x hx h
      obtain ⟨y, hy⟩ := h
      have hz : γ.φH (Submodule.Quotient.mk (⟨x, hx⟩ : LinearMap.ker S.g.hom)) = 0 := by
        rw [hH]
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        refine ⟨y, ?_⟩
        apply Subtype.ext
        exact hy.trans (hK ⟨x, hx⟩).symm
      have hz' := hinj (hz.trans (map_zero γ.φH.hom).symm)
      obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz'
      exact ⟨z, congrArg Subtype.val hz⟩
  · rintro ⟨hcycle, hboundary⟩
    constructor
    · apply (injective_iff_map_eq_zero γ.φH.hom).mpr
      intro x hx
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [hH] at hx
        obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
        obtain ⟨z, hz⟩ := hboundary x.val x.property
          ⟨y, (congrArg Subtype.val hy).trans (hK x)⟩
        exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, Subtype.ext hz⟩
    · intro y
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        obtain ⟨x, w, hx, hxy⟩ := hcycle y.val y.property
        refine ⟨Submodule.Quotient.mk (⟨x, hx⟩ : LinearMap.ker S.g.hom), ?_⟩
        rw [hH, Submodule.Quotient.eq]
        refine ⟨w, Subtype.ext ?_⟩
        change T.f w = (γ.φK ⟨x, hx⟩).val - y.val
        rw [hK, hxy, add_sub_cancel_left]

variable {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)

/-- A homology class in degree `n` has a cycle lift modulo an actual boundary. -/
theorem quasiIso_lift_cycle [QuasiIso f] (n : ℕ) (y : L.X n)
    (hy : L.d n (n - 1) y = 0) :
    ∃ (x : K.X n) (w : L.X (n + 1)),
      K.d n (n - 1) x = 0 ∧ f.f n x = y + L.d (n + 1) n w := by
  have h := (quasiIsoAt_iff' f (n + 1) n (n - 1)
    (by simp) (by cases n <;> simp)).mp (inferInstanceAs (QuasiIsoAt f n))
  exact ((moduleQuasiIso_iff _).mp h).1 y hy

/-- A cycle whose image is a boundary was already a boundary. -/
theorem quasiIso_reflect_boundary [QuasiIso f] (n : ℕ) (x : K.X n)
    (hx : K.d n (n - 1) x = 0) (y : L.X (n + 1))
    (hy : L.d (n + 1) n y = f.f n x) :
    ∃ z : K.X (n + 1), K.d (n + 1) n z = x := by
  have h := (quasiIsoAt_iff' f (n + 1) n (n - 1)
    (by simp) (by cases n <;> simp)).mp (inferInstanceAs (QuasiIsoAt f n))
  exact ((moduleQuasiIso_iff _).mp h).2 x hx ⟨y, hy⟩

/-- The elementwise homology test for a nonnegative chain map. -/
theorem quasiIso_of_lift_cycle_of_reflect_boundary
    (hcycle : ∀ (n : ℕ) (y : L.X n), L.d n (n - 1) y = 0 →
      ∃ (x : K.X n) (w : L.X (n + 1)),
        K.d n (n - 1) x = 0 ∧ f.f n x = y + L.d (n + 1) n w)
    (hboundary : ∀ (n : ℕ) (x : K.X n), K.d n (n - 1) x = 0 →
      ∀ y : L.X (n + 1), L.d (n + 1) n y = f.f n x →
        ∃ z : K.X (n + 1), K.d (n + 1) n z = x) : QuasiIso f := by
  constructor
  intro n
  rw [quasiIsoAt_iff' f (n + 1) n (n - 1) (by simp) (by cases n <;> simp),
    moduleQuasiIso_iff]
  exact ⟨hcycle n, fun x hx ⟨y, hy⟩ => hboundary n x hx y hy⟩

end ChainComplex.Koszul
