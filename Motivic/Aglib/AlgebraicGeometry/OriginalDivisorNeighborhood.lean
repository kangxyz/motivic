/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineCylinderIso
public import Motivic.Aglib.AlgebraicGeometry.EtaleNeighborhoodTransport

/-! # Retaining the original restricted closed scheme in an étale comparison -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- An affine presentation of a closed fiber transports a polynomial comparison
to the original restricted closed scheme and its literal cylinder. -/
theorem exists_original_open_divisor_comparison
    {k B D : Type u} [CommRing k] [CommRing B] [CommRing D]
    {Z X V : Scheme.{u}} (i : Z ⟶ X) (p : X ⟶ Spec (.of k))
    (u : Spec (.of B) ⟶ X) [IsOpenImmersion u]
    (d : Spec (.of D) ⟶ Spec (.of B)) (s : Spec (.of D) ⟶ Z)
    (h : IsPullback d s u i) (z : Z) (hz : i z ∈ Set.range u)
    (a : V ⟶ Spec (.of B)) (b : V ⟶ Spec (.of (Polynomial D)))
    [Etale a] [Etale b] (j : Spec (.of D) ⟶ V)
    (ha : IsPullback j (𝟙 _) a d)
    (hb : IsPullback j (𝟙 _) b
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : D))))) :
    ∃ U : X.Opens, IsAffineOpen U ∧ i z ∈ U ∧
      ∃ (a' : V ⟶ U.toScheme)
        (b' : V ⟶ Scheme.Hom.cylinder k ((i ⁻¹ᵁ U).ι ≫ i ≫ p))
        (j' : (i ⁻¹ᵁ U).toScheme ⟶ V),
        Etale a' ∧ Etale b' ∧
        IsPullback j' (𝟙 _) a' (i ∣_ U) ∧
        IsPullback j' (𝟙 _) b'
          (Scheme.Hom.cylinderZeroSection k ((i ⁻¹ᵁ U).ι ≫ i ≫ p)) := by
  let U := u.opensRange
  let eX : Spec (.of B) ≅ U.toScheme :=
    IsOpenImmersion.isoOfRangeEq u U.ι (by simp [U])
  have heX : eX.hom ≫ U.ι = u := IsOpenImmersion.isoOfRangeEq_hom_fac ..
  have h' : IsPullback (d ≫ eX.hom) s U.ι i := by
    apply h.of_iso (Iso.refl _) eX (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simpa using heX.symm
    · simp
  let eZ : (i ⁻¹ᵁ U).toScheme ≅ Spec (.of D) :=
    (isPullback_morphismRestrict i U).isoPullback ≪≫ h'.isoPullback.symm
  have heZ : eZ.hom ≫ d = (i ∣_ U) ≫ eX.inv := by
    apply (cancel_mono eX.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [eZ, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, h'.isoPullback_inv_fst]
    exact (isPullback_morphismRestrict i U).isoPullback_hom_fst
  let f : k →+* D := (Spec.preimage
    (eZ.inv ≫ (i ⁻¹ᵁ U).ι ≫ i ≫ p)).hom
  have hf : (i ⁻¹ᵁ U).ι ≫ i ≫ p =
      eZ.hom ≫ Spec.map (CommRingCat.ofHom f) := by
    simp [f]
  let eY := Scheme.Hom.affineCylinderIso k D f eZ _ hf
  have heY := Scheme.Hom.cylinderZeroSection_affineCylinderIso k D f eZ _ hf
  obtain ⟨ha', hb', hpa, hpb⟩ := transport_common_etale_neighborhood
    a b j d (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : D))))
    ha hb eZ eX.symm eY (i ∣_ U)
    (Scheme.Hom.cylinderZeroSection k ((i ⁻¹ᵁ U).ι ≫ i ≫ p)) heZ heY.symm
  exact ⟨U, isAffineOpen_opensRange u, hz, _, _, _, ha', hb', hpa, hpb⟩

end AlgebraicGeometry.Scheme
