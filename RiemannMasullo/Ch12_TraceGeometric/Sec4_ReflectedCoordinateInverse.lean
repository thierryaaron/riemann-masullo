module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualFixedBandTraceClass

/-!
# The angular coefficient inverts the angular lift

`exists_sLocalFullReflectedCoordinates_uniform_orderZero` gives, at Sobolev order zero, an angular
coefficient `Q`, an angular lift `L` and an inverse Tate phase `U`, with `L (Q u) = u` on every
full band. This file proves the other composition, `Q (L v) = v` for every `v` in `L²(ℝ)`, so
that the reflected map `T = U ∘ Q` satisfies `T (L v) = U v`.

* `dense_setOf_ae_eq_zero_lt`. The functions in `L²(ℝ)` that vanish below some point are dense.
* `coeff_lift_eq_self_of_bands`. In any inner product space, if `L (Q u) = u` on a family of
  subspaces whose images under `U ∘ Q` are the functions vanishing below `-log B`, then
  `Q (L v) = v` for every `v`.
* `exists_sLocalFullReflectedCoordinates_coeffLift_orderZero`. The coordinates of
  `exists_sLocalFullReflectedCoordinates_uniform_orderZero` satisfy `Q (L v) = v` and
  `T (L v) = U v`.
-/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal FourierTransform NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)

section Dense

/-- The functions in `L²(ℝ)` that vanish almost everywhere below some point are dense. -/
theorem dense_setOf_ae_eq_zero_lt :
    Dense {r : FlatL2 | ∃ a : ℝ, ∀ᵐ x ∂volume, x < a → r x = 0} := by
  refine Metric.dense_iff.mpr fun r ε hε ↦ ?_
  obtain ⟨g, hgc, hle, -, hgm⟩ := (Lp.memLp r).exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (ε := ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  refine ⟨hgm.toLp g, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_comm, Lp.dist_def]
    have hae : (⇑r - ⇑(hgm.toLp g)) =ᵐ[volume] (⇑r - g) :=
      (hgm.coeFn_toLp).mono fun x hx ↦ by simp [hx]
    rw [eLpNorm_congr_ae hae]
    have hfin : eLpNorm (⇑r - g) 2 volume ≠ ∞ := (hle.trans_lt ENNReal.ofReal_lt_top).ne
    calc (eLpNorm (⇑r - g) 2 volume).toReal ≤ (ENNReal.ofReal (ε / 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = ε / 2 := ENNReal.toReal_ofReal (half_pos hε).le
      _ < ε := half_lt_self hε
  · obtain ⟨b, hb⟩ := hgc.isCompact.bddBelow
    refine ⟨b, (hgm.coeFn_toLp).mono fun x hx hxb ↦ ?_⟩
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport fun hmem ↦ (not_le.mpr hxb) (hb hmem)

end Dense

section Abstract

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- If `L (Q u) = u` on a family of subspaces whose images under `U ∘ Q` are the functions
vanishing below `-log B`, then `Q` inverts `L` on all of `L²(ℝ)`. -/
theorem coeff_lift_eq_self_of_bands (Q : W →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W)
    (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2) (V : ℝ → Submodule ℂ W)
    (hRecover : ∀ B : ℝ, 0 < B → ∀ u ∈ V B, L (Q u) = u)
    (hRange : ∀ B : ℝ, 0 < B → Set.range (fun u : V B ↦ U (Q u.val)) =
      {r : FlatL2 | ∀ᵐ x ∂volume, x < -Real.log B → r x = 0}) (v : FlatL2) :
    Q (L v) = v := by
  let G : FlatL2 →L[ℂ] FlatL2 := Q.comp L.toContinuousLinearMap
  let D : Set FlatL2 := {r : FlatL2 | ∃ a : ℝ, ∀ᵐ x ∂volume, x < a → r x = 0}
  have hEq : EqOn G id (U.symm '' D) := by
    rintro _ ⟨r, ⟨a, ha⟩, rfl⟩
    have hB : 0 < Real.exp (-a) := Real.exp_pos _
    have hr : r ∈ Set.range (fun u : V (Real.exp (-a)) ↦ U (Q u.val)) := by
      rw [hRange _ hB, Real.log_exp, neg_neg]
      exact ha
    obtain ⟨⟨u, hu⟩, rfl⟩ := hr
    change Q (L (U.symm (U (Q u)))) = U.symm (U (Q u))
    rw [LinearIsometryEquiv.symm_apply_apply, hRecover _ hB u hu]
  have hdense : Dense (U.symm '' D) :=
    U.symm.surjective.denseRange.dense_image U.symm.continuous dense_setOf_ae_eq_zero_lt
  exact congrFun (Continuous.ext_on hdense G.continuous continuous_id hEq) v

end Abstract

section Coordinates

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "W(" s ")" => CompactIntervalSobolev μJ (logSIdeleQuotientNorm F S) 0 0 s
local notation "expUnit" => fun x : ℝ ↦ Units.mk0 (Real.toNNReal (Real.exp x)) (by positivity)
local notation "include₁" =>
  (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
    continuous_subtype_val : J₁ →ₜ* Jₛ)
local notation "circleCoe" =>
  (ContinuousMonoidHom.mk Circle.coeHom continuous_subtype_val : Circle →ₜ* ℂ)
local notation "chart" =>
  quasiCharacterNormTwist (G := Jₛ) (sIdeleQuotientNorm F S)
    (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F S))

/-- Paper: Theorem 12.4.1.1, pp. 515–518, the order-zero reflected coordinates of #7354.
Reconstruction: the angular coefficient `Q`, the angular lift `L` and the inverse Tate phase `U`
of `exists_sLocalFullReflectedCoordinates_uniform_orderZero` also satisfy `Q (L v) = v` for every
`v` in `L²(ℝ)`. So the reflected map `T = U ∘ Q` sends `L v` to `U v`: read through `L`, `T` is
the Fourier multiplier by the conjugate of the S-local Tate factor `m`. -/
theorem exists_sLocalFullReflectedCoordinates_coeffLift_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) :
    ∃ (χ : PontryaginDual Jₛ) (Q : W(0) →L[ℂ] FlatL2) (L : FlatL2 →ₗᵢ[ℂ] W(0))
      (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2),
      χ.comp include₁ = ω ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧ ‖Q‖ ≤ 1 ∧
      (∀ u, (Q u : ℝ → ℂ) =ᵐ[volume] fun x ↦
        (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ *
          ∫ h : J₁, (ω h : ℂ) * u (h.val * QuotientGroup.mk (τ (expUnit x))) ∂η) ∧
      (∀ v, (L v : Jₛ → ℂ) =ᵐ[intervalSobolevMeasure μJ (logSIdeleQuotientNorm F S) 0 0 0]
        fun q ↦ (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ * (χ q : ℂ)⁻¹ *
          v (logSIdeleQuotientNorm F S q)) ∧
      (let m (ξ : ℝ) : ℂ :=
        sLocalRhoFactor (chart ((circleCoe).comp χ) (sLocalRadialThetaCriticalParameter ξ))
      ∀ v, (Lp.fourierTransformₗᵢ ℝ ℂ (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
        star (m ξ) * (Lp.fourierTransformₗᵢ ℝ ℂ v : FlatL2) ξ) ∧
      sLocalFullReflectedGenAE τ ω χ (U.toLinearIsometry.toContinuousLinearMap.comp Q) ∧
      (∀ B : ℝ, 0 < B →
        let V : Submodule ℂ W(0) := Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0)
          le_rfl (a := 1 / 2) (by norm_num) ω B
        (∀ u ∈ V, L (Q u) = u) ∧
        Set.range (fun u : V ↦ U (Q u.val)) =
          {r : FlatL2 | ∀ᵐ x : ℝ ∂volume, x < -Real.log B → r x = 0}) ∧
      (∀ v, Q (L v) = v) ∧ (∀ v, U (Q (L v)) = U v) := by
  obtain ⟨χ, Q, L, U, hχ, hsec, hQn, hQ, hL, hU, hGen, hB⟩ :=
    exists_sLocalFullReflectedCoordinates_uniform_orderZero (F := F) (S := S) τ hτ ω
  have hBands (B : ℝ) (hB0 : 0 < B) :
      let V : Submodule ℂ W(0) := Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0)
        le_rfl (a := 1 / 2) (by norm_num) ω B
      (∀ u ∈ V, L (Q u) = u) ∧
      Set.range (fun u : V ↦ U (Q u.val)) =
        {r : FlatL2 | ∀ᵐ x : ℝ ∂volume, x < -Real.log B → r x = 0} := by
    obtain ⟨hRec, -, hRange, -⟩ := hB B hB0
    exact ⟨hRec, hRange⟩
  have hQL (v : FlatL2) : Q (L v) = v :=
    coeff_lift_eq_self_of_bands Q L U
      (fun B ↦ Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0)
        le_rfl (a := 1 / 2) (by norm_num) ω B)
      (fun B hB0 ↦ (hBands B hB0).1) (fun B hB0 ↦ (hBands B hB0).2) v
  exact ⟨χ, Q, L, U, hχ, hsec, hQn, hQ, hL, hU, hGen, hBands, hQL, fun v ↦ by rw [hQL v]⟩

end Coordinates

end RiemannMasullo.Isolated
