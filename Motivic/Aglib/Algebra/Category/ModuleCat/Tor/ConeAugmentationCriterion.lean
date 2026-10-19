/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The actual nonnegative homotopy cofiber criterion

The criterion below uses cycles lifted modulo boundaries. In particular it does
not assume the stronger property that every target cycle has a literal cycle
preimage. The resulting cone criterion includes homology in degree zero.
-/

@[expose] public section

universe u

open CategoryTheory HomologicalComplex

namespace ModuleCat.TorComparison

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- The actual module homology map is invertible exactly when cycles lift modulo
boundaries and boundaries of cycles are reflected. -/
theorem moduleQuasiIso_iff_liftCycles_mod_boundaries
    {S T : ShortComplex (ModuleCat.{u} R)} (φ : S ⟶ T) :
    ShortComplex.QuasiIso φ ↔
      (∀ y : T.X₂, T.g y = 0 → ∃ x : S.X₂, ∃ z : T.X₁,
        S.g x = 0 ∧ φ.τ₂ x - y = T.f z) ∧
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
      obtain ⟨x, hx⟩ := hsurj (Submodule.Quotient.mk ⟨y, hy⟩)
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [hH] at hx
        obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).mp hx
        refine ⟨x.val, z, x.property, ?_⟩
        have h := congrArg Subtype.val hz
        change T.f z = (γ.φK x).val - y at h
        rw [hK] at h
        exact h.symm
    · intro x hx hboundary
      obtain ⟨y, hy⟩ := hboundary
      have hz : γ.φH (Submodule.Quotient.mk ⟨x, hx⟩) = 0 := by
        rw [hH]
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact ⟨y, Subtype.ext (hy.trans (hK ⟨x, hx⟩).symm)⟩
      have hxz : (Submodule.Quotient.mk ⟨x, hx⟩ : S.moduleCatLeftHomologyData.H) = 0 :=
        hinj (hz.trans (map_zero γ.φH.hom).symm)
      obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hxz
      exact ⟨z, congrArg Subtype.val hz⟩
  · rintro ⟨hlift, hboundary⟩
    constructor
    · apply (injective_iff_map_eq_zero γ.φH.hom).mpr
      intro x hx
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [hH] at hx
        obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
        obtain ⟨z, hz⟩ := hboundary x.val x.property ⟨y,
          (congrArg Subtype.val hy).trans (hK x)⟩
        exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, Subtype.ext hz⟩
    · intro y
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        obtain ⟨x, z, hx, hxy⟩ := hlift y.val y.property
        refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
        rw [hH]
        apply (Submodule.Quotient.eq _).mpr
        refine ⟨z, Subtype.ext ?_⟩
        change T.f z = (γ.φK ⟨x, hx⟩).val - y.val
        rw [hK]
        exact hxy.symm

section

set_option backward.defeqAttrib.useBackward true

/-- The consecutive nonnegative chain indices have the required relation. -/
theorem cone_rel (n : ℕ) : (ComplexShape.down ℕ).Rel (n + 1) n := rfl

variable {A B : ChainComplex (ModuleCat.{u} R) ℕ} (f : A ⟶ B)

open homotopyCofiber

set_option backward.isDefEq.respectTransparency false in
/-- At a positive degree, the two actual cofiber coordinates determine an element. -/
theorem cone_ext_succ (n : ℕ) {x y : (homotopyCofiber f).X (n + 1)}
    (h₁ : fstX f (n + 1) n (cone_rel n) x = fstX f (n + 1) n (cone_rel n) y)
    (h₂ : sndX f (n + 1) x = sndX f (n + 1) y) : x = y := by
  have h : fstX f (n + 1) n (cone_rel n) ≫ inlX f n (n + 1) (cone_rel n) +
      sndX f (n + 1) ≫ inrX f (n + 1) = 𝟙 _ := by
    apply ext_to_X f (n + 1) n (cone_rel n) <;>
      simp [Preadditive.add_comp, Category.assoc, inlX_fstX, inrX_fstX, inlX_sndX]
  have hx := ConcreteCategory.congr_hom h x
  have hy := ConcreteCategory.congr_hom h y
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
    ModuleCat.id_apply] at hx hy
  rw [h₁, h₂] at hx
  exact hx.symm.trans hy

set_option backward.isDefEq.respectTransparency false in
/-- Degree zero has just the target coordinate; there is no negative source term. -/
theorem cone_ext_zero {x y : (homotopyCofiber f).X 0}
    (h : sndX f 0 x = sndX f 0 y) : x = y := by
  have he := sndX_inrX f 0 (by simp)
  have hx := ConcreteCategory.congr_hom he x
  have hy := ConcreteCategory.congr_hom he y
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hx hy
  rw [h] at hx
  exact hx.symm.trans hy

/-- Elementwise exactness with the actual next differential, valid also at zero. -/
theorem chain_exactAt_iff (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.ExactAt n ↔ ∀ x : K.X n, K.d n ((ComplexShape.down ℕ).next n) x = 0 →
      ∃ y : K.X (n + 1), K.d (n + 1) n y = x := by
  rw [K.exactAt_iff' (n + 1) n ((ComplexShape.down ℕ).next n) (by simp) rfl,
    ShortComplex.moduleCat_exact_iff]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Cofiber exactness lifts target cycles modulo boundaries, in every degree. -/
theorem cone_liftCycles (hC : (homotopyCofiber f).Acyclic) (n : ℕ)
    (y : B.X n) (hy : B.d n ((ComplexShape.down ℕ).next n) y = 0) :
    ∃ x : A.X n, ∃ z : B.X (n + 1),
      A.d n ((ComplexShape.down ℕ).next n) x = 0 ∧
        f.f n x - y = B.d (n + 1) n z := by
  have hyC : (homotopyCofiber f).d n ((ComplexShape.down ℕ).next n) (inrX f n y) = 0 := by
    change homotopyCofiber.d f n ((ComplexShape.down ℕ).next n) (inrX f n y) = 0
    have h := ConcreteCategory.congr_hom (inrX_d f n ((ComplexShape.down ℕ).next n)) y
    simpa only [ModuleCat.comp_apply, hy, map_zero] using h
  obtain ⟨w, hw⟩ := (chain_exactAt_iff _ n).mp (hC n) _ hyC
  dsimp only [homotopyCofiber] at w hw
  refine ⟨fstX f (n + 1) n (cone_rel n) w, -sndX f (n + 1) w, ?_, ?_⟩
  · cases n with
    | zero => simp
    | succ n =>
      have h := ConcreteCategory.congr_hom
        (d_fstX f (n + 2) (n + 1) n (cone_rel (n + 1)) (cone_rel n)) w
      have hr := ConcreteCategory.congr_hom (inrX_fstX f (n + 1) n (cone_rel n)) y
      change fstX f (n + 1) n (cone_rel n) (homotopyCofiber.d f (n + 2) (n + 1) w) =
        -(A.d (n + 1) n (fstX f (n + 2) (n + 1) (cone_rel (n + 1)) w)) at h
      change fstX f (n + 1) n (cone_rel n) (inrX f (n + 1) y) = 0 at hr
      rw [hw, hr] at h
      rw [ComplexShape.next_eq' _ (cone_rel n)]
      exact neg_eq_zero.mp h.symm
  · have h := ConcreteCategory.congr_hom (d_sndX f (n + 1) n (cone_rel n)) w
    have hr := ConcreteCategory.congr_hom (inrX_sndX f n) y
    change sndX f n (homotopyCofiber.d f (n + 1) n w) =
      f.f n (fstX f (n + 1) n (cone_rel n) w) + B.d (n + 1) n (sndX f (n + 1) w) at h
    change sndX f n (inrX f n y) = y at hr
    rw [hw, hr] at h
    rw [map_neg, h]
    abel

/-- The source inclusion has identity source coordinate. -/
@[simp] theorem cone_fst_inl (n : ℕ) (x : A.X n) :
    fstX f (n + 1) n (cone_rel n) (inlX f n (n + 1) (cone_rel n) x) = x :=
  ConcreteCategory.congr_hom (inlX_fstX f n (n + 1) (cone_rel n)) x

/-- The source inclusion has zero target coordinate. -/
@[simp] theorem cone_snd_inl (n : ℕ) (x : A.X n) :
    sndX f (n + 1) (inlX f n (n + 1) (cone_rel n) x) = 0 :=
  ConcreteCategory.congr_hom (inlX_sndX f n (n + 1) (cone_rel n)) x

/-- The target inclusion has zero source coordinate. -/
@[simp] theorem cone_fst_inr (n : ℕ) (x : B.X (n + 1)) :
    fstX f (n + 1) n (cone_rel n) (inrX f (n + 1) x) = 0 :=
  ConcreteCategory.congr_hom (inrX_fstX f (n + 1) n (cone_rel n)) x

/-- The target inclusion has identity target coordinate, including at zero. -/
@[simp] theorem cone_snd_inr (n : ℕ) (x : B.X n) :
    sndX f n (inrX f n x) = x :=
  ConcreteCategory.congr_hom (inrX_sndX f n) x

/-- The source coordinate of the actual differential is the negative source differential. -/
theorem cone_d_fst (n : ℕ) (x : (homotopyCofiber f).X (n + 2)) :
    fstX f (n + 1) n (cone_rel n) ((homotopyCofiber f).d (n + 2) (n + 1) x) =
      -A.d (n + 1) n (fstX f (n + 2) (n + 1) (cone_rel (n + 1)) x) := by
  dsimp only [homotopyCofiber] at x ⊢
  exact ConcreteCategory.congr_hom
    (d_fstX f (n + 2) (n + 1) n (cone_rel (n + 1)) (cone_rel n)) x

/-- The target coordinate includes both the map and the target differential. -/
theorem cone_d_snd (n : ℕ) (x : (homotopyCofiber f).X (n + 1)) :
    sndX f n ((homotopyCofiber f).d (n + 1) n x) =
      f.f n (fstX f (n + 1) n (cone_rel n) x) +
        B.d (n + 1) n (sndX f (n + 1) x) := by
  dsimp only [homotopyCofiber] at x ⊢
  exact ConcreteCategory.congr_hom (d_sndX f (n + 1) n (cone_rel n)) x

/-- Cofiber exactness reflects boundaries of source cycles. -/
theorem cone_reflectBoundaries (hC : (homotopyCofiber f).Acyclic) (n : ℕ)
    (x : A.X n) (hx : A.d n ((ComplexShape.down ℕ).next n) x = 0)
    (y : B.X (n + 1)) (hy : B.d (n + 1) n y = f.f n x) :
    ∃ z : A.X (n + 1), A.d (n + 1) n z = x := by
  let c : (homotopyCofiber f).X (n + 1) :=
    inlX f n (n + 1) (cone_rel n) x - inrX f (n + 1) y
  have hc : (homotopyCofiber f).d (n + 1) n c = 0 := by
    cases n with
    | zero =>
      apply cone_ext_zero f
      rw [cone_d_snd]
      simp [c, hy]
    | succ n =>
      apply cone_ext_succ f n
      · rw [cone_d_fst]
        rw [ComplexShape.next_eq' _ (cone_rel n)] at hx
        simp [c, hx]
      · rw [cone_d_snd]
        simp [c, hy]
  have hc' : (homotopyCofiber f).d (n + 1)
      ((ComplexShape.down ℕ).next (n + 1)) c = 0 := by
    rwa [ComplexShape.next_eq' _ (cone_rel n)]
  obtain ⟨w, hw⟩ := (chain_exactAt_iff _ (n + 1)).mp (hC (n + 1)) c hc'
  refine ⟨-fstX f (n + 2) (n + 1) (cone_rel (n + 1)) w, ?_⟩
  have h := congrArg (fstX f (n + 1) n (cone_rel n)) hw
  rw [cone_d_fst] at h
  simpa [c] using h

/-- A nonnegative chain map is a quasi-isomorphism iff the usual elementwise
cycle and boundary conditions hold in every degree. -/
theorem chain_quasiIsoAt_iff (n : ℕ) : QuasiIsoAt f n ↔
    (∀ y : B.X n, B.d n ((ComplexShape.down ℕ).next n) y = 0 →
      ∃ x : A.X n, ∃ z : B.X (n + 1),
        A.d n ((ComplexShape.down ℕ).next n) x = 0 ∧
          f.f n x - y = B.d (n + 1) n z) ∧
    (∀ x : A.X n, A.d n ((ComplexShape.down ℕ).next n) x = 0 →
      (∃ y : B.X (n + 1), B.d (n + 1) n y = f.f n x) →
        ∃ z : A.X (n + 1), A.d (n + 1) n z = x) := by
  rw [quasiIsoAt_iff' f (n + 1) n ((ComplexShape.down ℕ).next n) (by simp) rfl,
    moduleQuasiIso_iff_liftCycles_mod_boundaries]
  rfl

/-- Actual cofiber acyclicity implies a quasi-isomorphism, including degree zero. -/
theorem quasiIso_of_homotopyCofiber_acyclic (hC : (homotopyCofiber f).Acyclic) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [chain_quasiIsoAt_iff]
  exact ⟨cone_liftCycles f hC n, fun x hx ⟨y, hy⟩ => cone_reflectBoundaries f hC n x hx y hy⟩

/-- A quasi-isomorphism has acyclic actual homotopy cofiber over nonnegative modules. -/
theorem homotopyCofiber_acyclic_of_quasiIso [QuasiIso f] :
    (homotopyCofiber f).Acyclic := by
  have hQ (n : ℕ) := (chain_quasiIsoAt_iff f n).mp (inferInstance : QuasiIsoAt f n)
  intro n
  rw [chain_exactAt_iff]
  intro c hc
  cases n with
  | zero =>
    obtain ⟨x, z, _, hz⟩ := (hQ 0).1 (sndX f 0 c) (by simp)
    refine ⟨inlX f 0 1 (cone_rel 0) x - inrX f 1 z, ?_⟩
    apply cone_ext_zero f
    rw [cone_d_snd]
    simp only [map_sub, cone_fst_inl, cone_fst_inr, sub_zero,
      cone_snd_inl, cone_snd_inr, zero_sub, map_neg]
    rw [← hz]
    abel
  | succ n =>
    rw [ComplexShape.next_eq' _ (cone_rel n)] at hc
    have hx : A.d n ((ComplexShape.down ℕ).next n)
        (fstX f (n + 1) n (cone_rel n) c) = 0 := by
      cases n with
      | zero => simp
      | succ n =>
        have h := congrArg (fstX f (n + 1) n (cone_rel n)) hc
        rw [cone_d_fst, map_zero] at h
        rw [ComplexShape.next_eq' _ (cone_rel n)]
        exact neg_eq_zero.mp h
    have hy : B.d (n + 1) n (-sndX f (n + 1) c) =
        f.f n (fstX f (n + 1) n (cone_rel n) c) := by
      have h := congrArg (sndX f n) hc
      rw [cone_d_snd, map_zero] at h
      rw [map_neg]
      exact (eq_neg_of_add_eq_zero_left h).symm
    obtain ⟨a, ha⟩ := (hQ n).2 _ hx ⟨-sndX f (n + 1) c, hy⟩
    have ht : B.d (n + 1) ((ComplexShape.down ℕ).next (n + 1))
        (sndX f (n + 1) c + f.f (n + 1) a) = 0 := by
      rw [ComplexShape.next_eq' _ (cone_rel n), map_add]
      have hf := ConcreteCategory.congr_hom (f.comm (n + 1) n) a
      change B.d (n + 1) n (f.f (n + 1) a) = f.f n (A.d (n + 1) n a) at hf
      rw [hf, ha, ← hy, map_neg]
      exact add_neg_cancel _
    obtain ⟨b, z, hb, hz⟩ := (hQ (n + 1)).1 _ ht
    rw [ComplexShape.next_eq' _ (cone_rel n)] at hb
    refine ⟨inlX f (n + 1) (n + 2) (cone_rel (n + 1)) (-a + b) -
      inrX f (n + 2) z, ?_⟩
    apply cone_ext_succ f n
    · rw [cone_d_fst]
      simp [ha, hb]
    · rw [cone_d_snd]
      simp only [map_sub, cone_fst_inl, cone_fst_inr, sub_zero,
        cone_snd_inl, cone_snd_inr, map_neg, map_add]
      rw [← hz]
      abel

/-- The exact cofiber criterion for actual nonnegative module chain maps. -/
theorem homotopyCofiber_acyclic_iff_quasiIso :
    (homotopyCofiber f).Acyclic ↔ QuasiIso f := by
  constructor
  · exact quasiIso_of_homotopyCofiber_acyclic f
  · intro h
    exact homotopyCofiber_acyclic_of_quasiIso f

end

end ModuleCat.TorComparison
