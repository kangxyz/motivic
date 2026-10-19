module

public import Motivic.Aglib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Admissible

/-! # Degree and boundary value of actual admissible rational functions -/

@[expose] public noncomputable section

namespace Polynomial.BoundaryOneRationalFunctions

variable {R : Type*} [CommRing R]

/-- Equality of actual fractions preserves their numerator-minus-denominator degree. -/
theorem fraction_degree_independent (p q r s : denominators R)
    (h : fraction p q = fraction r s) :
    ((p : R[X]).natDegree : ℤ) - (q : R[X]).natDegree =
      ((r : R[X]).natDegree : ℤ) - (s : R[X]).natDegree := by
  have he := congrArg Polynomial.natDegree ((fraction_eq_iff p q r s).mp h)
  rw [p.2.1.natDegree_mul s.2.1, r.2.1.natDegree_mul q.2.1] at he
  omega

/-- The degree difference exists independently of a presentation. -/
theorem exists_fraction_degree (f : admissibleGroup R) :
    ∃ d : ℤ, ∀ p q : denominators R, f.val = fraction p q →
      d = ((p : R[X]).natDegree : ℤ) - (q : R[X]).natDegree := by
  obtain ⟨p, q, hf⟩ := f.property
  exact ⟨_, fun r s h => fraction_degree_independent p q r s (hf.symm.trans h)⟩

/-- The genuine order difference of an admissible rational function. -/
def fractionDegree (f : admissibleGroup R) : ℤ := (exists_fraction_degree f).choose

theorem fractionDegree_eq (f : admissibleGroup R) (p q : denominators R)
    (h : f.val = fraction p q) :
    fractionDegree f = ((p : R[X]).natDegree : ℤ) - (q : R[X]).natDegree :=
  (exists_fraction_degree f).choose_spec p q h

@[simp] theorem fractionDegree_fraction (p q : denominators R) :
    fractionDegree (admissibleFraction p q) =
      ((p : R[X]).natDegree : ℤ) - (q : R[X]).natDegree :=
  fractionDegree_eq _ p q rfl

/-- Degree is an additive invariant of actual multiplicative fractions. -/
def degreeHom : admissibleGroup R →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (fractionDegree f)
  map_one' := by
    change fractionDegree 1 = 0
    rw [fractionDegree_eq 1 1 1 (fraction_self 1).symm]
    simp
  map_mul' f g := by
    obtain ⟨p, q, hf⟩ := f.property
    obtain ⟨r, s, hg⟩ := g.property
    change fractionDegree (f * g) = fractionDegree f + fractionDegree g
    rw [fractionDegree_eq f p q hf, fractionDegree_eq g r s hg,
      fractionDegree_eq (f * g) (p * r) (q * s) (by
        change f.val * g.val = _
        rw [hf, hg, fraction_mul])]
    change ((((p : R[X]) * r).natDegree : ℤ) - ((q : R[X]) * s).natDegree) = _
    rw [p.2.1.natDegree_mul r.2.1, q.2.1.natDegree_mul s.2.1]
    push_cast
    ring

/-- Evaluation of the actual rational unit at zero. -/
def zeroValueHom : admissibleGroup R →* Rˣ :=
  (Units.map (zeroValue R).toMonoidHom).comp (admissibleGroup R).subtype

/-- The constant coefficient, as a unit, of an admissible denominator. -/
def denominatorConstant (p : denominators R) : Rˣ :=
  Units.map (zeroValue R).toMonoidHom (polynomialUnit p)

@[simp] theorem denominatorConstant_val (p : denominators R) :
    (denominatorConstant p : R) = (p : R[X]).coeff 0 :=
  zeroValue_algebraMap R p

@[simp] theorem zeroValueHom_fraction (p q : denominators R) :
    zeroValueHom (admissibleFraction p q) = denominatorConstant p / denominatorConstant q := by
  change Units.map (zeroValue R).toMonoidHom (polynomialUnit p / polynomialUnit q) = _
  exact _root_.map_div _ _ _

/-- The unsigned boundary invariants vanish precisely on the original boundary-one subgroup. -/
theorem boundary_iff_degree_zeroValue (f : admissibleGroup R) :
    f.val ∈ group R ↔ fractionDegree f = 0 ∧ zeroValueHom f = 1 := by
  obtain ⟨p, q, hf⟩ := f.property
  have hf' : f = admissibleFraction p q := Subtype.ext hf
  subst f
  rw [fractionDegree_fraction, zeroValueHom_fraction, div_eq_one]
  constructor
  · rintro ⟨r, s, hd, hc, he⟩
    have hdeg := fraction_degree_independent p q r s he
    constructor
    · omega
    · have hz := congrArg (Units.map (zeroValue R).toMonoidHom) he
      change Units.map (zeroValue R).toMonoidHom (fraction p q) =
        Units.map (zeroValue R).toMonoidHom (fraction r s) at hz
      simp only [fraction, _root_.map_div] at hz
      change denominatorConstant p / denominatorConstant q =
        denominatorConstant r / denominatorConstant s at hz
      have hrs : denominatorConstant r = denominatorConstant s := Units.ext (by simpa using hc)
      rw [hrs] at hz
      simp only [div_self'] at hz
      exact div_eq_one.mp hz
  · rintro ⟨hd, hc⟩
    refine ⟨p, q, by omega, ?_, rfl⟩
    simpa using congrArg (fun u : Rˣ => (u : R)) hc

/-- The signed constant coefficient invariant used in the divisor sequence. -/
def signedValueHom : admissibleGroup R →* Rˣ where
  toFun f := (-1 : Rˣ) ^ fractionDegree f * zeroValueHom f
  map_one' := by
    have hd : fractionDegree (1 : admissibleGroup R) = 0 :=
      congrArg Multiplicative.toAdd (degreeHom.map_one)
    simp [hd]
  map_mul' f g := by
    have hd : fractionDegree (f * g) = fractionDegree f + fractionDegree g :=
      congrArg Multiplicative.toAdd (degreeHom.map_mul f g)
    simp only [hd, zpow_add, map_mul]
    ac_rfl

/-- The full degree and signed-unit invariant of a genuine rational fraction. -/
def boundaryInvariant : admissibleGroup R →* Multiplicative ℤ × Rˣ :=
  degreeHom.prod signedValueHom

/-- Exactness at genuine rational functions: the kernel is exactly M*. -/
theorem boundaryInvariant_eq_one_iff (f : admissibleGroup R) :
    boundaryInvariant f = 1 ↔ f.val ∈ group R := by
  rw [boundary_iff_degree_zeroValue]
  change (Multiplicative.ofAdd (fractionDegree f),
    (-1 : Rˣ) ^ fractionDegree f * zeroValueHom f) = (1, 1) ↔ _
  constructor
  · intro h
    have hd : fractionDegree f = 0 := congrArg (fun z => Multiplicative.toAdd z.1) h
    exact ⟨hd, by simpa [hd] using congrArg Prod.snd h⟩
  · rintro ⟨hd, hv⟩
    simp [hd, hv]

/-- The original boundary inclusion is injective. -/
theorem boundaryInclusion_injective : Function.Injective (boundaryInclusion (R := R)) := by
  intro f g h
  apply Subtype.ext
  exact congrArg (fun x : admissibleGroup R => x.val) h

section Nontrivial

variable [Nontrivial R]

/-- A degree-one polynomial with any specified invertible constant term. -/
def linearDenominator (u : Rˣ) : denominators R :=
  ⟨X + C (u : R), monic_X_add_C _, by simp [u.isUnit]⟩

@[simp] theorem linearDenominator_natDegree (u : Rˣ) :
    (linearDenominator u : R[X]).natDegree = 1 := natDegree_X_add_C _

omit [Nontrivial R] in
@[simp] theorem denominatorConstant_linear (u : Rˣ) :
    denominatorConstant (linearDenominator u) = u := by
  apply Units.ext
  simp [linearDenominator]

/-- Every degree and zero-value pair occurs as an actual admissible fraction. -/
theorem degree_zeroValue_surjective (d : ℤ) (u : Rˣ) :
    ∃ f : admissibleGroup R, fractionDegree f = d ∧ zeroValueHom f = u := by
  let a := admissibleFraction (linearDenominator (1 : Rˣ)) 1
  let b := admissibleFraction (linearDenominator u) (linearDenominator (1 : Rˣ))
  have da : degreeHom a = Multiplicative.ofAdd (1 : ℤ) := by
    change Multiplicative.ofAdd (fractionDegree _) = _
    simp [a]
  have db : degreeHom b = 1 := by
    change Multiplicative.ofAdd (fractionDegree _) = _
    simp [b]
  have va : zeroValueHom a = 1 := by
    rw [zeroValueHom_fraction, denominatorConstant_linear]
    have h : denominatorConstant (1 : denominators R) = 1 := by
      apply Units.ext
      simp
    simp [h]
  have vb : zeroValueHom b = u := by simp [b]
  refine ⟨a ^ d * b, ?_, ?_⟩
  · have he := (degreeHom (R := R)).map_mul (a ^ d) b
    rw [map_zpow, da, db, mul_one] at he
    have ht := congrArg Multiplicative.toAdd he
    change fractionDegree (a ^ d * b) = d • (1 : ℤ) at ht
    simpa only [smul_eq_mul, mul_one] using ht
  · rw [map_mul, map_zpow, va, vb, one_zpow, one_mul]


/-- Every degree and signed-unit pair occurs as a genuine admissible fraction. -/
theorem boundaryInvariant_surjective : Function.Surjective (boundaryInvariant (R := R)) := by
  rintro ⟨d, u⟩
  obtain ⟨f, hd, hv⟩ := degree_zeroValue_surjective d.toAdd
    (((-1 : Rˣ) ^ d.toAdd)⁻¹ * u)
  refine ⟨f, ?_⟩
  change (Multiplicative.ofAdd (fractionDegree f),
    (-1 : Rˣ) ^ fractionDegree f * zeroValueHom f) = (d, u)
  rw [hd, hv]
  simp

end Nontrivial

variable {S : Type*} [CommRing S]

/-- Coefficient pullback of the actual admissible rational functions. -/
def admissibleMap (φ : R →+* S) : admissibleGroup R →* admissibleGroup S where
  toFun f := ⟨Units.map (ringMap φ).toMonoidHom f.val, by
    obtain ⟨p, q, hf⟩ := f.property
    exact ⟨denominatorMap φ p, denominatorMap φ q, by rw [hf, ringMap_fraction]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' f g := Subtype.ext (map_mul _ _ _)

@[simp] theorem admissibleMap_fraction (φ : R →+* S) (p q : denominators R) :
    admissibleMap φ (admissibleFraction p q) =
      admissibleFraction (denominatorMap φ p) (denominatorMap φ q) :=
  Subtype.ext (ringMap_fraction φ p q)

@[simp] theorem denominatorConstant_map (φ : R →+* S) (p : denominators R) :
    denominatorConstant (denominatorMap φ p) =
      Units.map φ.toMonoidHom (denominatorConstant p) := by
  apply Units.ext
  simp [denominatorMap]

/-- The zero-value invariant is natural for arbitrary coefficient maps. -/
theorem zeroValueHom_natural (φ : R →+* S) (f : admissibleGroup R) :
    zeroValueHom (admissibleMap φ f) = Units.map φ.toMonoidHom (zeroValueHom f) := by
  obtain ⟨p, q, hf⟩ := f.property
  have hf' : f = admissibleFraction p q := Subtype.ext hf
  subst f
  simp only [admissibleMap_fraction, zeroValueHom_fraction,
    denominatorConstant_map, _root_.map_div]

/-- The degree difference is natural over every nonempty target affine scheme. -/
theorem fractionDegree_natural [Nontrivial S] (φ : R →+* S) (f : admissibleGroup R) :
    fractionDegree (admissibleMap φ f) = fractionDegree f := by
  obtain ⟨p, q, hf⟩ := f.property
  have hf' : f = admissibleFraction p q := Subtype.ext hf
  subst f
  rw [admissibleMap_fraction, fractionDegree_fraction, fractionDegree_fraction]
  change (((p : R[X]).map φ).natDegree : ℤ) - ((q : R[X]).map φ).natDegree = _
  rw [p.2.1.natDegree_map φ, q.2.1.natDegree_map φ]

/-- The signed invariant is natural for coefficient pullback. -/
theorem signedValueHom_natural [Nontrivial S] (φ : R →+* S) (f : admissibleGroup R) :
    signedValueHom (admissibleMap φ f) = Units.map φ.toMonoidHom (signedValueHom f) := by
  change (-1 : Sˣ) ^ fractionDegree (admissibleMap φ f) *
    zeroValueHom (admissibleMap φ f) = Units.map φ.toMonoidHom
      ((-1 : Rˣ) ^ fractionDegree f * zeroValueHom f)
  rw [fractionDegree_natural, zeroValueHom_natural, map_mul, map_zpow]
  congr 2
  apply Units.ext
  simp

/-- Pullback commutes with the original boundary inclusion. -/
theorem boundaryInclusion_natural (φ : R →+* S) (f : group R) :
    admissibleMap φ (boundaryInclusion f) = boundaryInclusion (map φ f) := rfl

end Polynomial.BoundaryOneRationalFunctions
