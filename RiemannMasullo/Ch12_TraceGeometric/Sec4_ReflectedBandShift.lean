module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedCoordinateInverse
public import RiemannMasullo.ForMathlib.Analysis.Fourier.L2Translation

/-!
# The full-band trace sees only the cutoff relative to the band edge

At Sobolev order zero, #7854 factors the upper-cutoff test action on the full band of radius `B`
through the reflected coordinates, where the band becomes the functions on `[-log B, ∞)`. This file
shows that the trace of the compressed operator depends on the band radius and the cutoff profile
`ρ` (a function of the log-norm) only through `ρ` read from the band edge: moving the band from `B`
to `B'` and the profile from `ρ` to `ρ (· + log B' - log B)` keeps the trace.

* `hilbertTrace_eq_halfLine`. Transfer of the compressed trace to the half-line space
  `l2HalfLine a`, through the angular lift `L` and the inverse phase `U`.
* `hilbertTrace_eq_of_halfLine_shift`. Translation, which commutes with the Fourier multiplier `U`,
  carries one half-line operator to the other and keeps its trace.
* `hilbertTrace_sLocalFullPW_upperCutoff_eq_of_shift_orderZero`. The statement for the actual
  operators of #7854.

Since the spatial cutoff at log-norm `log Λ` and the band radius `B` enter only through
`log Λ + log B`, the trace depends on the two cutoffs only through the product `Λ B`.

`bandShift_adjoint_apply`, `bandShift_isNuclearOperator_conj`,
`bandShift_isNuclearOperator_comp_right`, `bandShiftConj` and `hilbertTrace_bandShiftConj` repeat
general facts proved in `Sec4_RationalLevelIdentification` of #7791, under new names, so that the
two pull requests can merge in either order.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal FourierTransform NNReal NumberField.AdeleRing Topology InnerProductSpace SchwartzMap

namespace RiemannMasullo.Isolated

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "fourierL2" => Lp.fourierTransformₗᵢ ℝ ℂ

section Transport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The adjoint of a linear isometry is a left inverse of it. -/
theorem bandShift_adjoint_apply (W : E →ₗᵢ[ℂ] F) (x : E) :
    ContinuousLinearMap.adjoint W.toContinuousLinearMap (W x) = x := by
  refine ext_inner_right ℂ fun y ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact W.inner_map_map x y

/-- Conjugating a nuclear series by a continuous linear map on each side gives a nuclear
series. -/
theorem bandShift_isNuclearOperator_conj {T : E →L[ℂ] E} (hT : IsNuclearOperator T)
    (R : E →L[ℂ] F) (S : F →L[ℂ] E) : IsNuclearOperator (R.comp (T.comp S)) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hT
  refine (isNuclearOperator_iff_isBanachNuclear _).mpr ⟨c, fun n ↦ (φ n).comp S, fun n ↦ R (y n),
    hc, ?_, ?_, fun x ↦ ?_⟩
  · have h := (((ContinuousLinearMap.compL ℂ F E ℂ).flip S).continuous.tendsto 0).comp hφ
    rw [map_zero] at h
    exact h.congr fun n ↦ rfl
  · have h := (R.continuous.tendsto 0).comp hy
    rw [map_zero] at h
    exact h
  · simpa only [ContinuousLinearMap.comp_apply, map_smul] using R.hasSum (hsum (S x))

/-- Precomposing a nuclear series with a continuous linear map gives a nuclear series. -/
theorem bandShift_isNuclearOperator_comp_right {T : E →L[ℂ] E} (hT : IsNuclearOperator T)
    (S : F →L[ℂ] E) : IsNuclearOperator (T.comp S) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear T).mp hT
  refine (isNuclearOperator_iff_isBanachNuclear _).mpr ⟨c, fun n ↦ (φ n).comp S, y,
    hc, ?_, hy, fun x ↦ hsum (S x)⟩
  have h := (((ContinuousLinearMap.compL ℂ F E ℂ).flip S).continuous.tendsto 0).comp hφ
  rw [map_zero] at h
  exact h.congr fun n ↦ rfl

/-- The conjugate `W T W†` of a nuclear endomorphism by a linear isometry. -/
def bandShiftConj (W : E →ₗᵢ[ℂ] F) (T : nuclearEndomorphisms E) : nuclearEndomorphisms F :=
  ⟨W.toContinuousLinearMap.comp (T.val.comp (ContinuousLinearMap.adjoint W.toContinuousLinearMap)),
    bandShift_isNuclearOperator_conj T.property _ _⟩

theorem bandShiftConj_apply (W : E →ₗᵢ[ℂ] F) (T : nuclearEndomorphisms E) (x : F) :
    (bandShiftConj W T).val x =
      W (T.val (ContinuousLinearMap.adjoint W.toContinuousLinearMap x)) :=
  rfl

/-- Conjugating a nuclear endomorphism by a linear isometry keeps its trace. -/
theorem hilbertTrace_bandShiftConj (W : E →ₗᵢ[ℂ] F) (T : nuclearEndomorphisms E) :
    hilbertTrace (bandShiftConj W T) = hilbertTrace T := by
  let Wc := W.toContinuousLinearMap
  have hA₀ := bandShift_isNuclearOperator_comp_right T.property (ContinuousLinearMap.adjoint Wc)
  have h := nuclearTrace_factor_comps (hilbert_approximationProperty (H := E))
    (hilbert_approximationProperty (H := F)) Wc W.injective _ hA₀
  have e : (T.val.comp (ContinuousLinearMap.adjoint Wc)).comp Wc = T.val := by
    ext x
    change T.val (ContinuousLinearMap.adjoint W.toContinuousLinearMap (W x)) = T.val x
    rw [bandShift_adjoint_apply]
  have hc : ∀ (A B : E →L[ℂ] E) (_ : A = B) (hA : IsNuclearOperator A) (hB : IsNuclearOperator B),
      nuclearTrace (hilbert_approximationProperty (H := E)) A hA =
        nuclearTrace (hilbert_approximationProperty (H := E)) B hB := by
    rintro A B rfl hA hB
    rfl
  rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
  exact h.symm.trans (hc _ _ e _ _)

end Transport

section HalfLineLift

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The half-line space carried into `W` by the inverse phase and the angular lift. -/
def halfLineLift (L : FlatL2 →ₗᵢ[ℂ] W) (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2) (a : ℝ) :
    RiemannMasullo.l2HalfLine a →ₗᵢ[ℂ] W :=
  (L.comp U.symm.toLinearIsometry).comp (RiemannMasullo.l2HalfLine a).subtypeₗᵢ

theorem halfLineLift_apply (L : FlatL2 →ₗᵢ[ℂ] W) (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2) (a : ℝ)
    (r : RiemannMasullo.l2HalfLine a) : halfLineLift L U a r = L (U.symm r) :=
  rfl

variable (Q : W →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W) (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2)
  (V : Submodule ℂ W) [V.HasOrthogonalProjection] (a : ℝ)

theorem halfLineLift_mem
    (hRec : ∀ u ∈ V, L (Q u) = u)
    (hRange : Set.range (fun u : V ↦ U (Q u.val)) =
      {r : FlatL2 | ∀ᵐ x : ℝ ∂volume, x < a → r x = 0})
    (r : RiemannMasullo.l2HalfLine a) : halfLineLift L U a r ∈ V := by
  have hr : (r : FlatL2) ∈ Set.range (fun u : V ↦ U (Q u.val)) := by
    rw [hRange]
    exact r.property
  obtain ⟨⟨u, hu⟩, hru⟩ := hr
  rw [halfLineLift_apply, ← hru]
  change L (U.symm (U (Q u))) ∈ V
  rw [LinearIsometryEquiv.symm_apply_apply, hRec u hu]
  exact hu

theorem exists_halfLineLift_eq
    (hRec : ∀ u ∈ V, L (Q u) = u)
    (hRange : Set.range (fun u : V ↦ U (Q u.val)) =
      {r : FlatL2 | ∀ᵐ x : ℝ ∂volume, x < a → r x = 0})
    (u : W) (hu : u ∈ V) : ∃ r : RiemannMasullo.l2HalfLine a, halfLineLift L U a r = u := by
  have hmem : U (Q u) ∈ RiemannMasullo.l2HalfLine a := by
    change U (Q u) ∈ {r : FlatL2 | ∀ᵐ x : ℝ ∂volume, x < a → r x = 0}
    rw [← hRange]
    exact ⟨⟨u, hu⟩, rfl⟩
  refine ⟨⟨U (Q u), hmem⟩, ?_⟩
  rw [halfLineLift_apply]
  change L (U.symm (U (Q u))) = u
  rw [LinearIsometryEquiv.symm_apply_apply, hRec u hu]

theorem halfLineLift_adjoint_apply
    (hRec : ∀ u ∈ V, L (Q u) = u)
    (hRange : Set.range (fun u : V ↦ U (Q u.val)) =
      {r : FlatL2 | ∀ᵐ x : ℝ ∂volume, x < a → r x = 0}) (w : W) :
    halfLineLift L U a
        (ContinuousLinearMap.adjoint (halfLineLift L U a).toContinuousLinearMap w) =
      V.starProjection w := by
  let I := halfLineLift L U a
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (halfLineLift_mem Q L U V a hRec hRange _) fun v hv ↦ ?_
  obtain ⟨r, rfl⟩ := exists_halfLineLift_eq Q L U V a hRec hRange v hv
  rw [inner_sub_left, I.inner_map_map]
  have h : ⟪w, I r⟫_ℂ = ⟪ContinuousLinearMap.adjoint I.toContinuousLinearMap w, r⟫_ℂ :=
    (ContinuousLinearMap.adjoint_inner_left I.toContinuousLinearMap r w).symm
  rw [h, sub_self]

theorem halfLineLift_adjoint_starProjection
    (hRec : ∀ u ∈ V, L (Q u) = u)
    (hRange : Set.range (fun u : V ↦ U (Q u.val)) =
      {r : FlatL2 | ∀ᵐ x : ℝ ∂volume, x < a → r x = 0}) (w : W) :
    ContinuousLinearMap.adjoint (halfLineLift L U a).toContinuousLinearMap (V.starProjection w) =
      ContinuousLinearMap.adjoint (halfLineLift L U a).toContinuousLinearMap w := by
  refine ext_inner_right ℂ fun r ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  change ⟪V.starProjection w, halfLineLift L U a r⟫_ℂ = ⟪w, halfLineLift L U a r⟫_ℂ
  have h := Submodule.starProjection_inner_eq_zero (K := V) w _
    (halfLineLift_mem Q L U V a hRec hRange r)
  rw [inner_sub_left, sub_eq_zero] at h
  exact h.symm

theorem halfLineLift_adjoint_lift (y : FlatL2) :
    ((ContinuousLinearMap.adjoint (halfLineLift L U a).toContinuousLinearMap (L y) :
        RiemannMasullo.l2HalfLine a) : FlatL2) =
      (RiemannMasullo.l2HalfLine a).starProjection (U y) := by
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.coe_mem _) fun r hr ↦ ?_
  have h : ⟪(ContinuousLinearMap.adjoint (halfLineLift L U a).toContinuousLinearMap (L y) :
      RiemannMasullo.l2HalfLine a), ⟨r, hr⟩⟫_ℂ = ⟪U y, r⟫_ℂ := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    change ⟪L y, L (U.symm r)⟫_ℂ = ⟪U y, r⟫_ℂ
    rw [L.inner_map_map]
    rw [← U.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  have h2 : ⟪((ContinuousLinearMap.adjoint (halfLineLift L U a).toContinuousLinearMap (L y) :
      RiemannMasullo.l2HalfLine a) : FlatL2), r⟫_ℂ = ⟪U y, r⟫_ℂ := h
  rw [inner_sub_left, h2, sub_self]

/-- Reconstruction: when `X` restricted to `V` factors as `L ∘ K`, the compression of `X` to `V`
has the same trace as the operator `r ↦ P_a (U (K (L (U⁻¹ r))))` on the half-line space. -/
theorem hilbertTrace_eq_halfLine
    (hRec : ∀ u ∈ V, L (Q u) = u)
    (hRange : Set.range (fun u : V ↦ U (Q u.val)) =
      {r : FlatL2 | ∀ᵐ x : ℝ ∂volume, x < a → r x = 0})
    (X : W →L[ℂ] W) (K : V →L[ℂ] FlatL2)
    (hXK : X.comp V.subtypeL = L.toContinuousLinearMap.comp K)
    (Full : nuclearEndomorphisms W) (hFull : Full.val = V.starProjection * X * V.starProjection) :
    ∃ Y : nuclearEndomorphisms (RiemannMasullo.l2HalfLine a),
      hilbertTrace Full = hilbertTrace Y ∧
      ∀ r : RiemannMasullo.l2HalfLine a, ((Y.val r : RiemannMasullo.l2HalfLine a) : FlatL2) =
        (RiemannMasullo.l2HalfLine a).starProjection
          (U (K ⟨halfLineLift L U a r, halfLineLift_mem Q L U V a hRec hRange r⟩)) := by
  let I := halfLineLift L U a
  let Ic := I.toContinuousLinearMap
  let Y : nuclearEndomorphisms (RiemannMasullo.l2HalfLine a) :=
    ⟨(ContinuousLinearMap.adjoint Ic).comp (Full.val.comp Ic),
      bandShift_isNuclearOperator_conj Full.property _ _⟩
  have hP (w : W) : V.starProjection (V.starProjection w) = V.starProjection w :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  have hconj : bandShiftConj I Y = Full := by
    apply Subtype.ext
    refine ContinuousLinearMap.ext fun w ↦ ?_
    change I (ContinuousLinearMap.adjoint Ic (Full.val (I (ContinuousLinearMap.adjoint Ic w)))) =
      Full.val w
    rw [halfLineLift_adjoint_apply Q L U V a hRec hRange,
      halfLineLift_adjoint_apply Q L U V a hRec hRange, hFull]
    change V.starProjection (V.starProjection (X (V.starProjection (V.starProjection w)))) =
      V.starProjection (X (V.starProjection w))
    rw [hP, hP]
  refine ⟨Y, by rw [← hconj, hilbertTrace_bandShiftConj], fun r ↦ ?_⟩
  have hmem := halfLineLift_mem Q L U V a hRec hRange r
  have hI : V.starProjection (I r) = I r := Submodule.starProjection_eq_self_iff.mpr hmem
  have hX : X (I r) = L (K ⟨I r, hmem⟩) := by
    have := congrArg (fun G : V →L[ℂ] W ↦ G ⟨I r, hmem⟩) hXK
    exact this
  change ((ContinuousLinearMap.adjoint Ic (Full.val (I r)) : RiemannMasullo.l2HalfLine a) :
    FlatL2) = _
  rw [hFull]
  change ((ContinuousLinearMap.adjoint Ic (V.starProjection (X (V.starProjection (I r)))) :
    RiemannMasullo.l2HalfLine a) : FlatL2) = _
  rw [hI, halfLineLift_adjoint_starProjection Q L U V a hRec hRange, hX,
    halfLineLift_adjoint_lift L U a]

end HalfLineLift

section Shift

/-- Restriction of `l2Translate s` to the half-line spaces, for `a + s = a'`. -/
def halfLineTranslate (a s a' : ℝ) (h : a + s = a') :
    RiemannMasullo.l2HalfLine a →ₗᵢ[ℂ] RiemannMasullo.l2HalfLine a' where
  toFun r := ⟨RiemannMasullo.l2Translate s r, h ▸
    (RiemannMasullo.l2Translate_mem_l2HalfLine_iff a s r).mpr r.property⟩
  map_add' r w := Subtype.ext (map_add (RiemannMasullo.l2Translate s) (r : FlatL2) (w : FlatL2))
  map_smul' c r := Subtype.ext (map_smul (RiemannMasullo.l2Translate s) c (r : FlatL2))
  norm_map' r := (RiemannMasullo.l2Translate s).norm_map r

theorem halfLineTranslate_coe (a s a' : ℝ) (h : a + s = a') (r : RiemannMasullo.l2HalfLine a) :
    ((halfLineTranslate a s a' h r : RiemannMasullo.l2HalfLine a') : FlatL2) =
      RiemannMasullo.l2Translate s r :=
  rfl

theorem halfLineTranslate_surjective (a s a' : ℝ) (h : a + s = a') :
    Function.Surjective (halfLineTranslate a s a' h) := by
  subst h
  intro w
  refine ⟨⟨(RiemannMasullo.l2Translate s).symm w, ?_⟩, Subtype.ext ?_⟩
  · exact (RiemannMasullo.l2Translate_mem_l2HalfLine_iff a s _).mp (by
      rw [LinearIsometryEquiv.apply_symm_apply]; exact w.property)
  · exact (RiemannMasullo.l2Translate s).apply_symm_apply w

/-- Reconstruction: two operators of the form `r ↦ P_a (U (κ r))` on half-line spaces whose
inputs `κ` are carried into each other by translation have the same trace, when `U` acts on the
Plancherel side as multiplication by a fixed function. -/
theorem hilbertTrace_eq_of_halfLine_shift (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2) (m : ℝ → ℂ)
    (hU : ∀ v, (fourierL2 (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ m ξ * fourierL2 v ξ)
    (a s a' : ℝ) (h : a + s = a') (κ : RiemannMasullo.l2HalfLine a → FlatL2)
    (κ' : RiemannMasullo.l2HalfLine a' → FlatL2)
    (hκ : ∀ r, RiemannMasullo.l2Translate s (κ r) = κ' (halfLineTranslate a s a' h r))
    (Y : nuclearEndomorphisms (RiemannMasullo.l2HalfLine a))
    (Y' : nuclearEndomorphisms (RiemannMasullo.l2HalfLine a'))
    (hY : ∀ r, ((Y.val r : RiemannMasullo.l2HalfLine a) : FlatL2) =
      (RiemannMasullo.l2HalfLine a).starProjection (U (κ r)))
    (hY' : ∀ r, ((Y'.val r : RiemannMasullo.l2HalfLine a') : FlatL2) =
      (RiemannMasullo.l2HalfLine a').starProjection (U (κ' r))) :
    hilbertTrace Y' = hilbertTrace Y := by
  subst h
  have hconj : bandShiftConj (halfLineTranslate a s (a + s) rfl) Y = Y' := by
    apply Subtype.ext
    refine ContinuousLinearMap.ext fun w ↦ ?_
    obtain ⟨r, rfl⟩ := halfLineTranslate_surjective a s (a + s) rfl w
    rw [bandShiftConj_apply, bandShift_adjoint_apply]
    apply Subtype.ext
    change RiemannMasullo.l2Translate s ((Y.val r : RiemannMasullo.l2HalfLine a) : FlatL2) =
      ((Y'.val (halfLineTranslate a s (a + s) rfl r) : RiemannMasullo.l2HalfLine (a + s)) :
        FlatL2)
    rw [hY, hY', ← RiemannMasullo.starProjection_l2HalfLine_l2Translate,
      ← RiemannMasullo.l2Translate_comm_of_fourierMultiplier U m hU, hκ]
  rw [← hconj, hilbertTrace_bandShiftConj]

end Shift


section Project

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "modulus" => continuousSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "ν(" s ")" => intervalSobolevMeasure μJ ℓ 0 0 s
local notation "W(" s ")" => CompactIntervalSobolev μJ ℓ 0 0 s
local notation "fullBand(" ω "," B ")" =>
  Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0) le_rfl
    (show (0 : ℝ) < 1 / 2 by norm_num) ω B

theorem measurable_logNorm_comp {ρ : ℝ → ℝ} (hρm : Measurable ρ) :
    Measurable (ρ ∘ ℓ) :=
  hρm.comp (Real.measurable_log.comp (NNReal.continuous_coe.comp
    (Units.continuous_val.comp (continuousSIdeleQuotientNorm F S).continuous)).measurable)

set_option maxHeartbeats 2000000 in
/-- Paper: Theorem 12.4.1.1, pp. 515–518, the trace on the full band at Sobolev order zero.
Reconstruction: the trace of the upper-cutoff test action compressed to the full band of radius
`B` is unchanged when the band radius becomes `B'` and the cutoff profile `ρ`, a function of the
log-norm, becomes `ρ (· + log B' - log B)`. So the trace depends on the band and the cutoff only
through the cutoff measured from the band edge, and a cutoff at log-norm `log Λ` enters with the
band only through the product `Λ B`. The proof transports the trace to the reflected half-line of
#7854 and translates there.
Deviation: Sobolev order zero, with the upper-cutoff operators of #7854. -/
theorem hilbertTrace_sLocalFullPW_upperCutoff_eq_of_shift_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) (ω : PontryaginDual J₁)
    (Φ : BruhatCompactSupport Jₛ) {B B' : ℝ} (hB : 0 < B) (hB' : 0 < B')
    (Tmax : ℝ) (ρ ρ' : ℝ → ℝ) (hρm : Measurable ρ) (hρm' : Measurable ρ')
    (hρ : ∀ x, |ρ x| ≤ 1) (hρ' : ∀ x, |ρ' x| ≤ 1) (hρT : ∀ x, Tmax < x → ρ x = 0)
    (hshift : ∀ x, ρ' x = ρ (x + Real.log B' - Real.log B))
    (Full Full' : nuclearEndomorphisms W(0)) :
    let V : Submodule ℂ W(0) := fullBand(ω,B)
    let V' : Submodule ℂ W(0) := fullBand(ω,B')
    letI : CompleteSpace V :=
      (show IsClosed (V : Set W(0)) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
    letI : CompleteSpace V' :=
      (show IsClosed (V' : Set W(0)) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let A : W(0) →L[ℂ] W(0) := hardySobolevTestAction μJ modulus 0 0 0 le_rfl le_rfl Φ
    let M : W(0) →L[ℂ] W(0) := lpCutoffMultiplier ν(0) (ρ ∘ ℓ) (measurable_logNorm_comp hρm)
      (fun g ↦ hρ (ℓ g))
    let M' : W(0) →L[ℂ] W(0) := lpCutoffMultiplier ν(0) (ρ' ∘ ℓ) (measurable_logNorm_comp hρm')
      (fun g ↦ hρ' (ℓ g))
    Full.val = V.starProjection * (M.comp A) * V.starProjection →
    Full'.val = V'.starProjection * (M'.comp A) * V'.starProjection →
    hilbertTrace Full' = hilbertTrace Full := by
  intro V V' A M M' hFull hFull'
  have : CompleteSpace V :=
    (show IsClosed (V : Set W(0)) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have : CompleteSpace V' :=
    (show IsClosed (V' : Set W(0)) from Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨χ, Q, L, U, hχ, hsec, -, -, hL, hU, hGen, hBands, hQL, -⟩ :=
    exists_sLocalFullReflectedCoordinates_coeffLift_orderZero (F := F) (S := S) τ hτ ω
  let T : W(0) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) := U.toLinearIsometry.toContinuousLinearMap.comp Q
  have hSupp (b : ℝ) (hb : 0 < b) :
      ∀ u ∈ fullBand(ω,b), ∀ᵐ x : ℝ ∂volume, x < -Real.log b → T u x = 0 := by
    intro u hu
    have hr : T u ∈ Set.range (fun u : fullBand(ω,b) ↦ U (Q u.val)) := ⟨⟨u, hu⟩, rfl⟩
    exact (Set.ext_iff.mp (hBands b hb).2 (T u)).mp hr
  have hTI (a : ℝ) (r : RiemannMasullo.l2HalfLine a) : T (halfLineLift L U a r) = r := by
    change U (Q (L (U.symm r))) = r
    rw [hQL, LinearIsometryEquiv.apply_symm_apply]
  have hρT' : ∀ x, Tmax - Real.log B' + Real.log B < x → ρ' x = 0 := fun x hx ↦ by
    rw [hshift]
    exact hρT _ (by linarith)
  obtain ⟨k, q, K, hk, hq, -, hMK, hK⟩ := exists_sLocalFullPW_upperCutoff_factor_orderZero
    τ hτ ω χ hχ hsec B T L hGen (hSupp B hB) hL Φ Tmax ρ hρm hρ hρT
  obtain ⟨k', q', K', hk', hq', -, hMK', hK'⟩ := exists_sLocalFullPW_upperCutoff_factor_orderZero
    τ hτ ω χ hχ hsec B' T L hGen (hSupp B' hB') hL Φ (Tmax - Real.log B' + Real.log B) ρ' hρm' hρ'
    hρT'
  have hkk : k' = k := SchwartzMap.ext fun x ↦ (hk' x).trans (hk x).symm
  have hqq : q' = q := by
    apply (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).injective
    apply SchwartzMap.ext
    intro ξ
    change 𝓕 (q' : ℝ → ℂ) ξ = 𝓕 (q : ℝ → ℂ) ξ
    rw [hq', hq, hkk]
  subst hqq hkk
  obtain ⟨Y, hTr, hY⟩ := hilbertTrace_eq_halfLine Q L U V (-Real.log B) (hBands B hB).1
    (hBands B hB).2 (M.comp A) K hMK Full hFull
  obtain ⟨Y', hTr', hY'⟩ := hilbertTrace_eq_halfLine Q L U V' (-Real.log B') (hBands B' hB').1
    (hBands B' hB').2 (M'.comp A) K' hMK' Full' hFull'
  set s : ℝ := -Real.log B' + Real.log B with hs
  have hss : -Real.log B + s = -Real.log B' := by rw [hs]; ring
  rw [hTr, hTr']
  refine hilbertTrace_eq_of_halfLine_shift U (fun ξ ↦ star (sLocalRhoFactor
      (quasiCharacterNormTwist (G := Jₛ) (sIdeleQuotientNorm F S)
        (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F S))
        ((ContinuousMonoidHom.mk Circle.coeHom continuous_subtype_val : Circle →ₜ* ℂ).comp χ)
        (sLocalRadialThetaCriticalParameter ξ)))) hU (-Real.log B) s (-Real.log B') hss
    (fun r ↦ K ⟨halfLineLift L U _ r, halfLineLift_mem Q L U V _ (hBands B hB).1
      (hBands B hB).2 r⟩)
    (fun r ↦ K' ⟨halfLineLift L U _ r, halfLineLift_mem Q L U V' _ (hBands B' hB').1
      (hBands B' hB').2 r⟩) (fun r ↦ ?_) Y Y' hY hY'
  apply Lp.ext
  set r' := halfLineTranslate (-Real.log B) s (-Real.log B') hss r
  have hr' : ((r' : RiemannMasullo.l2HalfLine (-Real.log B')) : Lp ℂ 2 (volume : Measure ℝ)) =
      RiemannMasullo.l2Translate s r := rfl
  have h1 := hK ⟨halfLineLift L U _ r, halfLineLift_mem Q L U V _ (hBands B hB).1
    (hBands B hB).2 r⟩
  have h2 := hK' ⟨halfLineLift L U _ r', halfLineLift_mem Q L U V' _ (hBands B' hB').1
    (hBands B' hB').2 r'⟩
  simp only [hTI] at h1 h2
  filter_upwards [RiemannMasullo.l2Translate_ae s (K ⟨halfLineLift L U _ r,
      halfLineLift_mem Q L U V _ (hBands B hB).1 (hBands B hB).2 r⟩),
    RiemannMasullo.ae_comp_sub h1 s, h2] with x hx₁ hx₂ hx₃
  rw [hx₁, hx₂, hx₃, hshift]
  have hconv : (∫ y, q' (x - y) * ((r' : RiemannMasullo.l2HalfLine (-Real.log B')) :
      Lp ℂ 2 (volume : Measure ℝ)) y) = ∫ y, q' (x - s - y) * (r : Lp ℂ 2 (volume : Measure ℝ)) y := by
    rw [hr']
    rw [integral_congr_ae ((RiemannMasullo.l2Translate_ae s r).mono fun y hy ↦
      congrArg (fun z ↦ q' (x - y) * z) hy)]
    have hshift' := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y : ℝ ↦ q' (x - y) * (r : Lp ℂ 2 (volume : Measure ℝ)) (y - s)) s
    rw [← hshift']
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    simp only [add_sub_cancel_right]
    congr 2
    ring
  have hxs : x - s = x + Real.log B' - Real.log B := by rw [hs]; ring
  rw [hconv, hxs]

end Project

end RiemannMasullo.Isolated
