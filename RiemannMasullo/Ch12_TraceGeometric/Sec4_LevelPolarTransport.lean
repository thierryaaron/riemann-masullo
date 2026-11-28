module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_LevelPolarComplement
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedLogTransport

/-!
# The full band in logarithmic coordinates

`Sec4_WeightedLogCoefficient` constructs, for a character `ω` of the norm-one group, a contraction
`Q` from the weighted quotient space to `L²(ℝ)` in the logarithmic norm coordinate.
`sLocalWeightedAngularLogCoefficient_onTheta` computes `Q` on the theta class of a polar-free test
at twist `1/2`: it is `√C` times the radial half-density `e^(x/2) Θ f(τ(e^x))`, where `C` is the
norm-one Tamagawa mass.

This file extends that computation to every test, polar-free or not, through the full theta map
of `Sec4_LevelPolarComplement` (`sLocalWeightedAngularLogCoefficient_onFullTheta`). So the image
under `Q` of the full band, and in particular of the polar complement of the level, lies in the
closure of the radial half-densities of the tests of the product region
(`map_sLocalFullPWSobolev_le`).

The helpers `levelPolarTransport_ae_of_withDensity` and `levelPolarTransport_logProduct` repeat
private lemmas of `Ch11_ShellStructure/Sec2b` and `Sec4_WeightedLogTransport`.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo.Isolated

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "m" => continuousSIdeleQuotientNorm F S
local notation "μ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))

/-- An almost-everywhere statement for a measure with a positive density holds almost everywhere
for the base measure. -/
theorem levelPolarTransport_ae_of_withDensity {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {w : α → ℝ} (hm : AEMeasurable w ν) (hw : ∀ x, 0 < w x) {P : α → Prop}
    (h : ∀ᵐ x ∂(ν.withDensity fun x ↦ ENNReal.ofReal (w x)), P x) : ∀ᵐ x ∂ν, P x := by
  have := withDensity_absolutelyContinuous' (f := fun x ↦ ENNReal.ofReal (w x))
    hm.ennreal_ofReal (Filter.Eventually.of_forall fun x ↦ (ENNReal.ofReal_pos.2 (hw x)).ne')
  exact this.ae_le h

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
Reconstruction: the full theta class of a test is represented, almost everywhere for the quotient
Tamagawa measure, by its weighted homogeneous theta function. -/
theorem sLocalFullPWThetaSobolevMap_apply {s a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁)
    (f : ℬₛ) :
    (sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f : Jₛ → ℂ) =ᵐ[μ]
      modulationWeight m a (sLocalHomogeneousAdelicThetaLinearMap F S ω f) := by
  have : OpensMeasurableSpace Jₛ := ⟨le_of_eq rfl⟩
  have hm : Measurable (fun g : Jₛ ↦ Real.log (((m) g).val : ℝ)) :=
    Real.measurable_log.comp ((measurable_coe_nnreal_real).comp
      ((Units.continuous_val.comp (m).continuous).measurable))
  have hd : Measurable (intervalSobolevDensity 0 0 s) := by
    unfold intervalSobolevDensity
    fun_prop
  exact levelPolarTransport_ae_of_withDensity (hd.comp hm).aemeasurable
    (fun _ ↦ mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _))
    (MemLp.coeFn_toLp (sLocalFullPWTheta_memLp (F := F) (S := S) (s := s) ha ω f))

section CanonicalLogProduct

local instance instLevelPolarTransportNormOneMeasurable : MeasurableSpace J₁ := borel _
local notation "expUnit" => fun x : ℝ ↦ Units.mk0 (Real.toNNReal (Real.exp x)) (by positivity)

/-- The quotient Haar measure is the product of the norm-one Tamagawa measure and Lebesgue
measure in the logarithmic norm. -/
theorem levelPolarTransport_logProduct
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) :
    MeasurePreserving
      (fun p : J₁ × ℝ ↦ p.1.val * (QuotientGroup.mk (τ (expUnit p.2)) : Jₛ))
      ((η).prod volume) μ := by
  let : BorelSpace J₁ := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let p (z : J₁ × ℝ≥0ˣ) : Jₛ := z.1.val * QuotientGroup.mk (τ z.2)
  have hτc : Continuous (fun t : ℝ≥0ˣ ↦ (QuotientGroup.mk (τ t) : Jₛ)) :=
    QuotientGroup.continuous_mk.comp τ.continuous
  have hp : Measurable p :=
    (continuous_subtype_val.measurable.comp measurable_fst).mul (hτc.measurable.comp measurable_snd)
  have he : Measurable expUnit :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hExpMap : Measure.map expUnit volume = positiveRealHaar := rfl
  have hProdMap : Measure.map (Prod.map (id : J₁ → J₁) expUnit) ((η).prod volume) =
      (η).prod positiveRealHaar := by
    rw [← Measure.map_prod_map η volume measurable_id he, Measure.map_id, hExpMap]
  have hQuotient : ((η).prod positiveRealHaar).map p = μ :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
  have hProdMeasurable : Measurable (Prod.map (id : J₁ → J₁) expUnit) :=
    measurable_id.prodMap he
  change MeasurePreserving (p ∘ Prod.map id expUnit) ((η).prod volume) μ
  exact ⟨hp.comp hProdMeasurable, (Measure.map_map hp hProdMeasurable).symm.trans
    ((congrArg (Measure.map p) hProdMap).trans hQuotient)⟩

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488, with Theorem 12.4.1.1, Step II, p. 517.
Reconstruction: at twist `1/2` the logarithmic character coefficient `Q` of the full theta class
of any test `f`, polar-free or not, is `√C` times the radial half-density
`e^(x/2) Θ f(τ(e^x))`, where `C` is the norm-one Tamagawa mass. For polar-free tests this is
`sLocalWeightedAngularLogCoefficient_onTheta`, and the proof is the same. -/
theorem sLocalWeightedAngularLogCoefficient_onFullTheta {s : ℝ}
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁)
    (Q : CompactIntervalSobolev μ (logSIdeleQuotientNorm F S) 0 0 s →L[ℂ]
      Lp ℂ 2 (volume : Measure ℝ))
    (hQ : ∀ u, (Q u : ℝ → ℂ) =ᵐ[volume] fun x ↦
      (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ *
        ∫ h : J₁, (ω h : ℂ) * u (h.val * QuotientGroup.mk (τ (expUnit x))) ∂η)
    (f : ℬₛ) :
    (Q (sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) (a := 1 / 2) (by norm_num) ω f) :
        ℝ → ℂ) =ᵐ[volume] fun x ↦
      (Real.sqrt (Measure.real η univ) : ℂ) * ((Real.exp (x / 2) : ℂ) *
        sLocalHomogeneousAdelicThetaLinearMap F S ω f (QuotientGroup.mk (τ (expUnit x)))) := by
  let u := sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) (a := 1 / 2) (by norm_num) ω f
  let q (x : ℝ) : Jₛ := QuotientGroup.mk (τ (expUnit x))
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S ω f
  let U := modulationWeight m (1 / 2) θ
  have hRep : (u : Jₛ → ℂ) =ᵐ[μ] U :=
    sLocalFullPWThetaSobolevMap_apply (F := F) (S := S) (s := s) (a := 1 / 2) (by norm_num) ω f
  let : BorelSpace J₁ := ⟨rfl⟩
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : Measure.IsHaarMeasure η :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
  have hChart := levelPolarTransport_logProduct τ hτ
  have hFiber : ∀ᵐ x ∂volume, ∀ᵐ h : J₁ ∂η,
      u (h.val * q x) = U (h.val * q x) :=
    Measure.ae_ae_of_ae_prod
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
        (hChart.quasiMeasurePreserving.ae_eq_comp hRep))
  let c := Measure.real η univ
  let d := Real.sqrt c
  have hc : 0 < c := measureReal_univ_pos
  have hd : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hc).ne'
  have hSquare : (d : ℂ) * (d : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul]
    exact congrArg Complex.ofReal (Real.mul_self_sqrt hc.le)
  have hScale : (d : ℂ)⁻¹ * (c : ℂ) = (d : ℂ) := by
    rw [← hSquare, inv_mul_cancel_left₀ hd]
  filter_upwards [hQ u, hFiber] with x hx hux
  let w : ℂ := (Real.exp (x / 2) : ℂ) * θ (q x)
  have hConst : (∫ h : J₁, (ω h : ℂ) * u (h.val * q x) ∂η) = (c : ℂ) * w := by
    calc
      _ = ∫ _ : J₁, w ∂η := by
        apply integral_congr_ae
        filter_upwards [hux] with h hh
        rw [hh]
        have hn : m (h.val * q x) = expUnit x := by
          change sIdeleQuotientNorm F S (h.val * q x) = _
          rw [map_mul, MonoidHom.mem_ker.mp h.property, one_mul]
          exact (sIdeleQuotientNorm_mk F S (τ (expUnit x))).trans (hτ _)
        have hv : ((expUnit x).val : ℝ) = Real.exp x :=
          Real.coe_toNNReal _ (Real.exp_pos _).le
        have hθ : (ω h : ℂ) * θ (h.val * q x) = θ (q x) := by
          symm
          simpa only [θ, sLocalHomogeneousAdelicThetaLinearMap, inv_mul_cancel_left] using
            (sLocalHomogeneousAdelicTheta_homogeneous F S η ω f h (h.val * q x))
        with_unfolding_all change (ω h : ℂ) *
          (((((m (h.val * q x)).val : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * θ (h.val * q x)) =
          (Real.exp (x / 2) : ℂ) * θ (q x)
        rw [hn, hv, ← Real.exp_mul, mul_one_div, mul_left_comm, hθ]
      _ = _ := by rw [integral_const, Complex.real_smul]
  change (Q u : ℝ → ℂ) x = (d : ℂ) * w
  calc
    _ = (d : ℂ)⁻¹ * (∫ h : J₁, (ω h : ℂ) * u (h.val * q x) ∂η) := hx
    _ = (d : ℂ)⁻¹ * ((c : ℂ) * w) := congrArg ((d : ℂ)⁻¹ * ·) hConst
    _ = ((d : ℂ)⁻¹ * (c : ℂ)) * w := (mul_assoc _ _ _).symm
    _ = _ := congrArg (· * w) hScale

end CanonicalLogProduct

/-- Paper: Definition 11.2.1.3(1), p. 488, and Theorem 12.4.1.1, Step II, p. 517.
Reconstruction: a bounded operator from the weighted quotient space sends the full band at
twist `1/2`, and so the polar complement of the level, into the closure of its values on the
theta classes of the tests of the product region. For the logarithmic coefficient `Q` of
`Sec4_WeightedLogCoefficient` those values are the radial half-densities of
`sLocalWeightedAngularLogCoefficient_onFullTheta`. -/
theorem map_sLocalFullPWSobolev_le {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual J₁) (Λ : ℝ)
    (Q : CompactIntervalSobolev μ (logSIdeleQuotientNorm F S) 0 0 s →L[ℂ]
      Lp ℂ 2 (volume : Measure ℝ)) :
    (sLocalFullPWSobolev (F := F) (S := S) hs (a := 1 / 2) (by norm_num) ω Λ).map
        (Q : CompactIntervalSobolev μ (logSIdeleQuotientNorm F S) 0 0 s →ₗ[ℂ]
          Lp ℂ 2 (volume : Measure ℝ)) ≤
      ((sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S Λ)).map
        ((Q : CompactIntervalSobolev μ (logSIdeleQuotientNorm F S) 0 0 s →ₗ[ℂ]
          Lp ℂ 2 (volume : Measure ℝ)) ∘ₗ
          sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) (a := 1 / 2) (by norm_num) ω)).topologicalClosure := by
  rw [Submodule.map_comp]
  exact Submodule.topologicalClosure_map Q _

end RiemannMasullo.Isolated
