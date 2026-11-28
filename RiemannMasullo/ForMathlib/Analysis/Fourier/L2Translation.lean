module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.L2Phase
public import RiemannMasullo.ForMathlib.Analysis.Fourier.Integrable
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Translations and half-lines in `L²(ℝ)`

* `l2Translate s` is the translation `v ↦ v (· - s)`, a linear isometry equivalence of `L²(ℝ)`.
* `fourier_l2Translate`. Its Plancherel transform is the transform of `v` times the phase
  `e (-s ξ)`.
* `l2Translate_comm_of_fourierMultiplier`. It commutes with every operator that acts on the
  Plancherel side as multiplication by a fixed function.
* `l2HalfLine a` is the closed subspace of classes vanishing almost everywhere below `a`, and
  `l2Translate s` maps it onto `l2HalfLine (a + s)`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform

namespace RiemannMasullo

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "fourierL2" => Lp.fourierTransformₗᵢ ℝ ℂ

section Translate

/-- Translation by `s` is onto. -/
theorem l2Translate_surjective (s : ℝ) :
    Function.Surjective (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ ↦ x - s)
      (measurePreserving_sub_right volume s) : FlatL2 → FlatL2) := by
  intro w
  refine ⟨Lp.compMeasurePreserving (fun x : ℝ ↦ x + s) (measurePreserving_add_right volume s) w, ?_⟩
  change Lp.compMeasurePreserving (fun x : ℝ ↦ x - s) (measurePreserving_sub_right volume s)
    (Lp.compMeasurePreserving (fun x : ℝ ↦ x + s) (measurePreserving_add_right volume s) w) = w
  rw [← Lp.compMeasurePreserving_comp_apply]
  apply Lp.ext
  refine (Lp.coeFn_compMeasurePreserving _ _).trans (ae_of_all _ fun x ↦ ?_)
  simp

/-- Translation by `s` on `L²(ℝ)`, `v ↦ v (· - s)`. -/
def l2Translate (s : ℝ) : FlatL2 ≃ₗᵢ[ℂ] FlatL2 :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ ↦ x - s) (measurePreserving_sub_right volume s))
    (l2Translate_surjective s)

theorem l2Translate_ae (s : ℝ) (v : FlatL2) :
    (l2Translate s v : ℝ → ℂ) =ᵐ[volume] fun x ↦ v (x - s) :=
  Lp.coeFn_compMeasurePreserving v (measurePreserving_sub_right volume s)

/-- A property holding almost everywhere still holds almost everywhere after translation. -/
theorem ae_comp_sub {p : ℝ → Prop} (h : ∀ᵐ x ∂volume, p x) (s : ℝ) :
    ∀ᵐ x ∂volume, p (x - s) :=
  (measurePreserving_sub_right volume s).quasiMeasurePreserving.tendsto_ae.eventually h

theorem l2Translate_ext {s : ℝ} {v w : FlatL2}
    (h : ∀ᵐ x ∂volume, w x = v (x - s)) : l2Translate s v = w := by
  apply Lp.ext
  filter_upwards [l2Translate_ae s v, h] with x h₁ h₂
  rw [h₁, h₂]

theorem l2Translate_symm_apply (s : ℝ) (v : FlatL2) :
    (l2Translate s).symm v = l2Translate (-s) v := by
  apply (l2Translate s).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  refine (l2Translate_ext ?_).symm
  filter_upwards [ae_comp_sub (l2Translate_ae (-s) v) s] with x hx
  rw [hx, sub_neg_eq_add, sub_add_cancel]

/-- The Plancherel transform of a translate of an integrable class. -/
private theorem fourier_l2Translate_of_integrable (s : ℝ) (v : FlatL2)
    (hv : Integrable (v : ℝ → ℂ)) :
    (fourierL2 (l2Translate s v) : ℝ → ℂ) =ᵐ[volume]
      fun ξ ↦ (Real.fourierChar (-(s * ξ)) : ℂ) * fourierL2 v ξ := by
  have hS : Integrable (l2Translate s v : ℝ → ℂ) := by
    refine (Integrable.congr ?_ (l2Translate_ae s v).symm)
    exact hv.comp_sub_right s
  have h1 := fourier_L2_coeFn_of_integrable (l2Translate s v) hS
  have h2 := fourier_L2_coeFn_of_integrable v hv
  filter_upwards [h1, h2] with ξ hξ₁ hξ₂
  change (𝓕 (l2Translate s v) : FlatL2) ξ =
    (Real.fourierChar (-(s * ξ)) : ℂ) * (𝓕 v : FlatL2) ξ
  rw [hξ₁, hξ₂]
  have hcongr : 𝓕 (l2Translate s v : ℝ → ℂ) ξ = 𝓕 (fun x ↦ v (x - s)) ξ :=
    Real.fourier_congr_ae (l2Translate_ae s v) ξ
  rw [hcongr, Real.fourier_real_eq, Real.fourier_real_eq]
  have hshift := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun x : ℝ ↦ Real.fourierChar (-(x * ξ)) • v (x - s)) s
  rw [← hshift, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [add_sub_cancel_right, Circle.smul_def, smul_eq_mul]
  rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 3
  ring

/-- The Plancherel transform of a translate is the transform times the phase `e (-s ξ)`. -/
theorem fourier_l2Translate (s : ℝ) (v : FlatL2) :
    (fourierL2 (l2Translate s v) : ℝ → ℂ) =ᵐ[volume]
      fun ξ ↦ (Real.fourierChar (-(s * ξ)) : ℂ) * fourierL2 v ξ := by
  let e : ℝ → ℂ := fun ξ ↦ (Real.fourierChar (-(s * ξ)) : ℂ)
  have he : Continuous e :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_const.mul continuous_id).neg)
  obtain ⟨E, hE, -⟩ := exists_L2_unitModulusMultiplier volume e he.aestronglyMeasurable
    (ae_of_all _ fun ξ ↦ by simp [e])
  let A : FlatL2 →L[ℂ] FlatL2 :=
    (fourierL2 : FlatL2 ≃ₗᵢ[ℂ] FlatL2).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (l2Translate s).toContinuousLinearEquiv.toContinuousLinearMap
  let B : FlatL2 →L[ℂ] FlatL2 :=
    E.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (fourierL2 : FlatL2 ≃ₗᵢ[ℂ] FlatL2).toContinuousLinearEquiv.toContinuousLinearMap
  have hAB : (A : FlatL2 → FlatL2) = B := by
    refine (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) (μ := (volume : Measure ℝ))
      (by norm_num)).equalizer A.continuous B.continuous ?_
    funext φ
    change fourierL2 (l2Translate s (φ.toLp 2 volume)) = E (fourierL2 (φ.toLp 2 volume))
    apply Lp.ext
    have hint : Integrable ((φ.toLp 2 volume : FlatL2) : ℝ → ℂ) :=
      (φ.integrable (μ := volume)).congr (φ.coeFn_toLp 2 volume).symm
    filter_upwards [fourier_l2Translate_of_integrable s _ hint, hE (fourierL2 (φ.toLp 2 volume))]
      with ξ h₁ h₂
    rw [h₁, h₂]
  have hv : fourierL2 (l2Translate s v) = E (fourierL2 v) := congrFun hAB v
  rw [hv]
  exact hE _

/-- Translation commutes with every operator acting on the Plancherel side as multiplication
by a fixed function. -/
theorem l2Translate_comm_of_fourierMultiplier (U : FlatL2 → FlatL2) (m : ℝ → ℂ)
    (hU : ∀ v, (fourierL2 (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ m ξ * fourierL2 v ξ)
    (s : ℝ) (v : FlatL2) : U (l2Translate s v) = l2Translate s (U v) := by
  apply (fourierL2 : FlatL2 ≃ₗᵢ[ℂ] FlatL2).injective
  apply Lp.ext
  filter_upwards [hU (l2Translate s v), fourier_l2Translate s v, fourier_l2Translate s (U v),
    hU v] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  ring

end Translate

section HalfLine

/-- The classes in `L²(ℝ)` that vanish almost everywhere below `a`. -/
def l2HalfLine (a : ℝ) : Submodule ℂ FlatL2 where
  carrier := {r | ∀ᵐ x ∂volume, x < a → r x = 0}
  add_mem' {r w} hr hw := by
    change ∀ᵐ x ∂volume, x < a → (r + w : FlatL2) x = 0
    filter_upwards [hr, hw, Lp.coeFn_add r w] with x h₁ h₂ h₃ hx
    rw [h₃, Pi.add_apply, h₁ hx, h₂ hx, add_zero]
  zero_mem' := by
    change ∀ᵐ x ∂volume, x < a → (0 : FlatL2) x = 0
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx _
    rw [hx, Pi.zero_apply]
  smul_mem' c r hr := by
    change ∀ᵐ x ∂volume, x < a → (c • r : FlatL2) x = 0
    filter_upwards [hr, Lp.coeFn_smul c r] with x h₁ h₂ hx
    rw [h₂, Pi.smul_apply, h₁ hx, smul_zero]

theorem mem_l2HalfLine {a : ℝ} {r : FlatL2} :
    r ∈ l2HalfLine a ↔ ∀ᵐ x ∂volume, x < a → r x = 0 := Iff.rfl

theorem isClosed_l2HalfLine (a : ℝ) : IsClosed (l2HalfLine a : Set FlatL2) := by
  refine isClosed_of_closure_subset fun r hr ↦ ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hr
  have hmeas : TendstoInMeasure volume (fun n ↦ (u n : ℝ → ℂ)) atTop r :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' u r).mp hlim)
  obtain ⟨ns, -, hns⟩ := hmeas.exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂volume, ∀ n, x < a → u (ns n) x = 0 :=
    ae_all_iff.mpr fun n ↦ hu (ns n)
  filter_upwards [hns, hall] with x hx hzero hxa
  have h0 : (fun i ↦ (u (ns i) : ℝ → ℂ) x) = fun _ ↦ 0 := funext fun i ↦ hzero i hxa
  rw [h0] at hx
  exact (tendsto_nhds_unique hx tendsto_const_nhds)

instance (a : ℝ) : CompleteSpace (l2HalfLine a) :=
  (isClosed_l2HalfLine a).completeSpace_coe

/-- Translation by `s` maps the classes vanishing below `a` onto those vanishing below
`a + s`. -/
theorem l2Translate_mem_l2HalfLine_iff (a s : ℝ) (r : FlatL2) :
    l2Translate s r ∈ l2HalfLine (a + s) ↔ r ∈ l2HalfLine a := by
  constructor
  · intro h
    rw [mem_l2HalfLine] at h ⊢
    filter_upwards [ae_comp_sub (h.and (l2Translate_ae s r)) (-s)] with x ⟨h₁, h₂⟩ hx
    rw [sub_neg_eq_add] at h₁ h₂
    rw [add_sub_cancel_right] at h₂
    rw [← h₂]
    exact h₁ (by linarith)
  · intro h
    rw [mem_l2HalfLine] at h ⊢
    filter_upwards [ae_comp_sub h s, l2Translate_ae s r] with x h₁ h₂ hx
    rw [h₂]
    exact h₁ (by linarith)

theorem l2HalfLine_map_l2Translate (a s : ℝ) :
    (l2HalfLine a).map ((l2Translate s).toLinearEquiv : FlatL2 →ₗ[ℂ] FlatL2) =
      l2HalfLine (a + s) := by
  ext w
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (l2Translate_mem_l2HalfLine_iff a s r).mpr hr
  · intro hw
    refine ⟨(l2Translate s).symm w, ?_, (l2Translate s).apply_symm_apply w⟩
    exact (l2Translate_mem_l2HalfLine_iff a s _).mp (by
      rw [LinearIsometryEquiv.apply_symm_apply]; exact hw)

/-- Translation conjugates the orthogonal projection onto one half-line space into the
projection onto the translated one. -/
theorem starProjection_l2HalfLine_l2Translate (a s : ℝ) (r : FlatL2) :
    (l2HalfLine (a + s)).starProjection (l2Translate s r) =
      l2Translate s ((l2HalfLine a).starProjection r) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw ↦ ?_
  · exact (l2Translate_mem_l2HalfLine_iff a s _).mpr (Submodule.starProjection_apply_mem _ _)
  · have hw' : (l2Translate s).symm w ∈ l2HalfLine a :=
      (l2Translate_mem_l2HalfLine_iff a s _).mp (by
        rw [LinearIsometryEquiv.apply_symm_apply]; exact hw)
    rw [← map_sub, ← (l2Translate s).apply_symm_apply w, LinearIsometryEquiv.inner_map_map]
    exact Submodule.starProjection_inner_eq_zero r _ hw'

end HalfLine

end RiemannMasullo
