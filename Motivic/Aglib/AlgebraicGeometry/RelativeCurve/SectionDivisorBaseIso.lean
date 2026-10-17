module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.SerreDivisorPairs
/-! # Finite-flat section divisors retain their original affine source -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph
lemma sectionDivisorFiniteFlat_comp_iso_iff {C U S T : Scheme.{u}}
    (q : C ⟶ S) (j : U ⟶ C) (e : S ≅ T) (L : LineBundle C)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val) :
    SectionDivisorFiniteFlat (q ≫ e.hom) j L s ↔ SectionDivisorFiniteFlat q j L s := by
  have hf {W : Scheme.{u}} (f : W ⟶ S) : IsFinite (f ≫ e.hom) ↔ IsFinite f :=
    by
      constructor
      · intro h
        have : IsFinite (f ≫ e.hom) := h
        have hh : IsFinite ((f ≫ e.hom) ≫ e.inv) := inferInstance
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh
      · intro h
        have : IsFinite f := h
        infer_instance
  have ht {W : Scheme.{u}} (f : W ⟶ S) : Flat (f ≫ e.hom) ↔ Flat f :=
    by
      constructor
      · intro h
        have : Flat (f ≫ e.hom) := h
        have hh : Flat ((f ≫ e.hom) ≫ e.inv) := inferInstance
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh
      · intro h
        have : Flat f := h
        infer_instance
  simp only [SectionDivisorFiniteFlat, ← Category.assoc, hf, ht]
end AlgebraicGeometry.Scheme.CoherentGraph
