module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
public import RiemannMasullo.AppC_LCTVS.Sec3a
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # A nuclear factor through the flat Schwartz space in §12.4, for a cutoff with an inner radius

Theorem 12.4.1.1, p. 515, asserts a nuclear factor through `E` for the truncated operator, so
that Lemma C.3.2.2, p. 695, reduces its trace to `E`. In the model `F = ℚ`, `S = {∞}`, the
sibling file `Sec4_RealPWFactorization_Printed.lean` shows that with the spatial cutoff of
Step II, p. 516, which is one near zero, the range of the operator does not even lie in `E`.

This file treats the other reading: Definition 9.3.3.1(4)–(6), p. 427, and footnote 2 on
p. 514 give the cutoff a positive inner radius. For a smooth compactly supported cutoff `ρ`
that vanishes near zero, the same composite

`ψ ↦ (x ↦ ρ x • ∫ g in [1, 2], φ g • (𝓕⁻ ψ) (x / g))`

is a nuclear operator from the Fourier side `L²([-Y, Y])` of the Paley–Wiener level into the
flat Schwartz space `realSchwartzFlatAtOrigin` (`sLocalTrace_realAnnularPW_nuclearFactor`).
The argument is the one sketched by @dyknapp on issue #7354 ("Annular replacement at fixed
cutoffs"): expand the band-limited function in powers of `x / g`; the coefficient functionals
are bounded on `L²` of the band with a factorial denominator, and the functions
`ρ x (x / (2A))ⁿ` form a bounded family of flat Schwartz functions when `ρ` is supported in
`[-A, A]`.

The general step is `exists_isNuclearOperator_of_summable_of_bounded`: a series of rank-one
maps with summable coefficients, bounded functionals and a bounded family of vectors in a
complete space is nuclear in the sense of §C.3.1.
-/

@[expose] public noncomputable section

open Filter Function Set Topology Bornology Metric MeasureTheory Real
open scoped NNReal ENNReal ContDiff FourierTransform SchwartzMap

namespace RiemannMasullo

section AbstractNuclear

/- The next three lemmas repeat `spectralBoundary_gauge_image`, `spectralBoundary_disc_image`
and `spectralBoundary_bounded_common_disc` of `Ch07_SchauderBasesZeta/Sec4.lean`, which are
private there. If those are made public, these copies can go. -/

/-- A linear equivalence carries the gauge of a set to the gauge of its image. -/
private theorem annularNuclear_gauge_image {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (φ : M ≃ₗ[ℂ] N) (s : Set M) (x : M) :
    gauge (φ '' s) (φ x) = gauge s x := by
  unfold gauge
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ ↦ ?_
  simp only [Set.mem_smul_set, Set.exists_mem_image]
  refine exists_congr fun y ↦ and_congr_right fun _ ↦ ?_
  rw [show r • φ y = φ (r • y) from (LinearMap.map_smul_of_tower φ.toLinearMap r y).symm]
  exact φ.injective.eq_iff

/-- The image of a Banach disc under an injective continuous linear map is a Banach disc. -/
private theorem annularNuclear_disc_image {Y Z : Type*}
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [PolynormableSpace ℂ Y] [T2Space Y]
    [AddCommGroup Z] [Module ℂ Z] [UniformSpace Z] [IsUniformAddGroup Z]
    [PolynormableSpace ℂ Z] [T2Space Z]
    {sourceSpace : Set Y} (hB : IsBanachDisc sourceSpace) (T : Y →L[ℂ] Z) (hT : Injective T) :
    IsBanachDisc (T '' sourceSpace) := by
  let S := Submodule.span ℂ sourceSpace
  let S' := Submodule.span ℂ (T '' sourceSpace)
  have hSS : S.map T.toLinearMap = S' := (Submodule.span_image T.toLinearMap).symm
  let φ : S ≃ₗ[ℂ] S' :=
    (Submodule.equivMapOfInjective T.toLinearMap hT S).trans (LinearEquiv.ofEq _ _ hSS)
  have himage : ((↑) ⁻¹' (T '' sourceSpace) : Set S') = φ '' ((↑) ⁻¹' sourceSpace : Set S) := by
    ext z
    constructor
    · rintro ⟨b, hb, hbz⟩
      exact ⟨⟨b, Submodule.subset_span hb⟩, hb, Subtype.ext hbz⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  have bB : Balanced ℂ ((↑) ⁻¹' (T '' sourceSpace) : Set S') :=
    himage ▸ hB.balanced.image φ.toLinearMap
  have cB : Convex ℝ ((↑) ⁻¹' (T '' sourceSpace) : Set S') :=
    himage ▸ hB.convex.linear_image (φ.toLinearMap.restrictScalars ℝ)
  have aB : Absorbent ℝ ((↑) ⁻¹' (T '' sourceSpace) : Set S') :=
    himage ▸ Absorbent.image_of_surjective (f := φ.toLinearMap.restrictScalars ℝ)
      φ.surjective hB.absorbent
  let p := gaugeSeminorm hB.balanced hB.convex hB.absorbent
  let p' := gaugeSeminorm bB cB aB
  have hnorm (z : S') : p' z = p (φ.symm z) := by
    change gauge _ z = gauge _ (φ.symm z)
    rw [himage, ← annularNuclear_gauge_image φ, φ.apply_symm_apply]
  let ψ : WithLocalSeminorm p' → WithLocalSeminorm p := fun z ↦ (φ.symm (show S' from z) : S)
  have hψ : Isometry ψ := Isometry.of_dist_eq fun x y ↦ by
    rw [dist_eq_norm, dist_eq_norm]
    change p (φ.symm (show S' from x) - φ.symm (show S' from y)) =
      p' ((show S' from x) - (show S' from y))
    rw [← map_sub]
    exact (hnorm _).symm
  have hinj : Injective ψ := fun a b h ↦ φ.symm.injective h
  have hsurj : Surjective ψ := fun z ↦ ⟨(φ (show S from z) : S'), φ.symm_apply_apply _⟩
  have := hB.separated
  exact ⟨hB.bounded.image T, bB, cB, aB,
    T2Space.of_injective_continuous hinj hψ.continuous,
    (hψ.isUniformInducing.completeSpace_congr hsurj).mpr hB.complete⟩

/-- Every bounded sequence in a complete Hausdorff locally convex space lies in one Banach
disc: the image of the unit ball of `ℓ¹` modulo the kernel of the synthesis map. -/
private theorem annularNuclear_bounded_common_disc {I E : Type*} [DecidableEq I]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    (v : I → E) (bnd : IsVonNBounded ℂ (range v)) :
    ∃ D : Set E, IsBanachDisc D ∧ ∀ i, v i ∈ D := by
  classical
  let X := lp (fun _ : I ↦ ℂ) 1
  let hp := PolynormableSpace.withSeminorms ℂ E
  have bounded_q (q : {q : Seminorm ℂ E // Continuous q}) :
      ∃ C > (0:ℝ), ∀ i, q.val (v i) ≤ C := by
    obtain ⟨C,hC,h⟩ := hp.isVonNBounded_iff_seminorm_bounded.mp bnd q
    exact ⟨C,hC,fun i ↦ (h _ (mem_range_self i)).le⟩
  have normsum (x : X) : HasSum (fun i ↦ ‖x i‖) ‖x‖ := by
    simpa using (lp.hasSum_norm (p := (1:ℝ≥0∞)) (by simp) x)
  have hterms (x : X) : Summable (fun i ↦ x i • v i) := by
    apply summable_iff_cauchySeq_finset.mpr
    apply cauchySeq_finset_iff_sum_vanishing.mpr
    intro region hU
    obtain ⟨p,hp0,hpU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hU
    obtain ⟨C,hC,hh⟩ := bounded_q ⟨p,hp0⟩
    have hmajor := (normsum x).summable.mul_left C
    obtain ⟨s,hs⟩ := cauchySeq_finset_iff_sum_vanishing.mp
      (summable_iff_cauchySeq_finset.mp hmajor) (Iio 1) (Iio_mem_nhds zero_lt_one)
    refine ⟨s,fun u hu ↦ hpU (p.mem_ball_zero.mpr (lt_of_le_of_lt ?_ (hs u hu)))⟩
    calc
      p (∑ i ∈ u, x i • v i) ≤ ∑ i ∈ u, p (x i • v i) :=
        Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦ by
        rw [map_smul_eq_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hh i) (norm_nonneg _)
  let A : X →ₗ[ℂ] E :=
    { toFun := fun x ↦ ∑' i, x i • v i
      map_add' := fun x y ↦ by
        simpa [add_smul] using (hterms x).tsum_add (hterms y)
      map_smul' := fun c x ↦ by
        change (∑' i, (c * x i) • v i) = c • _
        simpa [smul_smul] using (hterms x).tsum_const_smul c }
  have cont : Continuous A := by
    apply hp.continuous_of_continuous_comp A
    intro q
    obtain ⟨C,hC,h⟩ := bounded_q q
    apply Seminorm.continuous' (r := C+1)
    refine mem_of_superset (Metric.ball_mem_nhds (0:X) one_pos) fun x hx ↦ ?_
    rw [Metric.mem_ball,dist_zero_right] at hx
    have hlimit := q.property.continuousAt.tendsto.comp (hterms x).hasSum
    have hmajor := ((normsum x).mul_left C)
    have hbound : q.val (A x) ≤ C * ‖x‖ :=
      le_of_tendsto_of_tendsto' hlimit hmajor (fun s ↦ by
        change q.val (∑ i ∈ s, x i • v i) ≤ ∑ i ∈ s, C * ‖x i‖
        refine (Finset.le_sum_of_subadditive q.val (map_zero q.val).le
          (map_add_le_add q.val) _ _).trans ?_
        apply Finset.sum_le_sum
        intro i _
        rw [map_smul_eq_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (h i) (norm_nonneg _))
    apply (q.val.comp A).mem_closedBall_zero.mpr
    change q.val (A x) ≤ C+1
    nlinarith
  let S : X →L[ℂ] E := ⟨A,cont⟩
  let K := S.ker
  let : IsClosed (K : Set X) := S.isClosed_ker
  let L₀ := K.liftQ S.toLinearMap (le_refl K)
  let L : (X ⧸ K) →L[ℂ] E :=
    ⟨L₀, (Submodule.isQuotientMap_mkQ K).continuous_iff.mpr S.continuous⟩
  have inj : Injective L :=
    LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot S.toLinearMap le_rfl le_rfl)
  refine ⟨L '' Metric.closedBall (0:X ⧸ K) 1,
    annularNuclear_disc_image isBanachDisc_closedUnitBall L inj,?_⟩
  intro i
  let e : X := lp.single (E := fun _ : I ↦ ℂ) 1 i (1:ℂ)
  refine ⟨K.mkQ e,?_,?_⟩
  · rw [Metric.mem_closedBall,dist_zero_right]
    apply (Submodule.Quotient.norm_mk_le K e).trans
    dsimp only [e]
    rw [lp.norm_single (by norm_num), norm_one]
  · change (∑' j : I, lp.single (E := fun _ : I ↦ ℂ) 1 i (1:ℂ) j • v j) = v i
    simpa [lp.single_apply] using
      (tsum_eq_single i (f := fun j : I ↦ lp.single (E := fun _ : I ↦ ℂ) 1 i (1:ℂ) j • v j)
        (fun j hj ↦ by simp [lp.single_apply,hj]))

/-- Paper: (C.3.1.3) and Lemma C.3.1.2, p. 694. A series of rank-one maps with summable
coefficients, uniformly bounded functionals on a normed space, and a bounded family of vectors
in a complete Hausdorff locally convex space converges pointwise to a nuclear operator.
Deviation: The paper defines nuclearity by such a presentation with the vectors in a Banach
disc. Here the disc is constructed from boundedness and completeness. -/
theorem exists_isNuclearOperator_of_summable_of_bounded {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E]
    (c : ℕ → ℂ) (hc : Summable fun n ↦ ‖c n‖) (f : ℕ → D →L[ℂ] ℂ) {K : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ K) (v : ℕ → E) (hv : IsVonNBounded ℂ (range v)) :
    ∃ A : D →L[ℂ] E, IsNuclearOperator A ∧
      ∀ x, HasSum (fun n ↦ (c n * f n x) • v n) (A x) := by
  classical
  have hK : 0 ≤ K := (norm_nonneg _).trans (hf 0)
  let hp := PolynormableSpace.withSeminorms ℂ E
  have bounded_q (q : {q : Seminorm ℂ E // Continuous q}) :
      ∃ C > (0:ℝ), ∀ i, q.val (v i) ≤ C := by
    obtain ⟨C, hC, h⟩ := hp.isVonNBounded_iff_seminorm_bounded.mp hv q
    exact ⟨C, hC, fun i ↦ (h _ (mem_range_self i)).le⟩
  have hcoef (x : D) (n : ℕ) : ‖c n * f n x‖ ≤ ‖c n‖ * (K * ‖x‖) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (((f n).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)))
      (norm_nonneg _)
  have hsumnorm (x : D) : Summable fun n ↦ ‖c n * f n x‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (hcoef x) (hc.mul_right _)
  have hterms (x : D) : Summable fun n ↦ (c n * f n x) • v n := by
    apply summable_iff_cauchySeq_finset.mpr
    apply cauchySeq_finset_iff_sum_vanishing.mpr
    intro region hU
    obtain ⟨p, hp0, hpU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hU
    obtain ⟨C, hC, hh⟩ := bounded_q ⟨p, hp0⟩
    have hmajor := (hsumnorm x).mul_left C
    obtain ⟨s, hs⟩ := cauchySeq_finset_iff_sum_vanishing.mp
      (summable_iff_cauchySeq_finset.mp hmajor) (Iio 1) (Iio_mem_nhds zero_lt_one)
    refine ⟨s, fun u hu ↦ hpU (p.mem_ball_zero.mpr (lt_of_le_of_lt ?_ (hs u hu)))⟩
    calc
      p (∑ i ∈ u, (c i * f i x) • v i) ≤ ∑ i ∈ u, p ((c i * f i x) • v i) :=
        Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦ by
        rw [map_smul_eq_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hh i) (norm_nonneg _)
  let A₀ : D →ₗ[ℂ] E :=
    { toFun := fun x ↦ ∑' n, (c n * f n x) • v n
      map_add' := fun x y ↦ by
        simpa [mul_add, add_smul] using (hterms x).tsum_add (hterms y)
      map_smul' := fun a x ↦ by
        change (∑' n, (c n * f n (a • x)) • v n) = a • _
        rw [← (hterms x).tsum_const_smul a]
        congr 1
        funext n
        rw [map_smul, smul_eq_mul, smul_smul]
        ring_nf }
  have cont : Continuous A₀ := by
    apply hp.continuous_of_continuous_comp A₀
    intro q
    obtain ⟨C, hC, h⟩ := bounded_q q
    apply Seminorm.continuous' (r := C * ((∑' n, ‖c n‖) * K) + 1)
    refine mem_of_superset (Metric.ball_mem_nhds (0 : D) one_pos) fun x hx ↦ ?_
    rw [Metric.mem_ball, dist_zero_right] at hx
    have hlimit := q.property.continuousAt.tendsto.comp (hterms x).hasSum
    have hmajor := (hsumnorm x).hasSum.mul_left C
    have hbound : q.val (A₀ x) ≤ C * ∑' n, ‖c n * f n x‖ :=
      le_of_tendsto_of_tendsto' hlimit hmajor (fun s ↦ by
        change q.val (∑ i ∈ s, (c i * f i x) • v i) ≤ ∑ i ∈ s, C * ‖c i * f i x‖
        refine (Finset.le_sum_of_subadditive q.val (map_zero q.val).le
          (map_add_le_add q.val) _ _).trans ?_
        apply Finset.sum_le_sum
        intro i _
        rw [map_smul_eq_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (h i) (norm_nonneg _))
    have htsum : ∑' n, ‖c n * f n x‖ ≤ (∑' n, ‖c n‖) * K := by
      calc ∑' n, ‖c n * f n x‖ ≤ ∑' n, ‖c n‖ * (K * ‖x‖) :=
            (hsumnorm x).tsum_le_tsum (hcoef x) (hc.mul_right _)
        _ = (∑' n, ‖c n‖) * (K * ‖x‖) := tsum_mul_right
        _ ≤ (∑' n, ‖c n‖) * K := by
            apply mul_le_mul_of_nonneg_left _ (tsum_nonneg fun _ ↦ norm_nonneg _)
            nlinarith [norm_nonneg x]
    apply (q.val.comp A₀).mem_closedBall_zero.mpr
    change q.val (A₀ x) ≤ C * ((∑' n, ‖c n‖) * K) + 1
    have := mul_le_mul_of_nonneg_left htsum hC.le
    linarith
  obtain ⟨Disc, hDisc, hmem⟩ := annularNuclear_bounded_common_disc v hv
  let A : D →L[ℂ] E := ⟨A₀, cont⟩
  refine ⟨A, (isNuclearOperator_iff_nonempty_presentation A).mpr ⟨
    { coeff := c
      functional := f
      disc := Disc
      isBanachDisc := hDisc
      vector := fun n ↦ ⟨v n, Submodule.subset_span (hmem n)⟩
      vector_mem := hmem
      summable_coeff := hc
      equicontinuous := ?_
      hasSum := fun x ↦ (hterms x).hasSum }⟩, fun x ↦ (hterms x).hasSum⟩
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : D) (div_pos hε (by positivity : (0 : ℝ) < K + 1))]
    with x hx n
  rw [Metric.mem_ball, dist_zero_right] at hx
  rw [map_zero, dist_zero_left]
  calc ‖f n x‖ ≤ ‖f n‖ * ‖x‖ := (f n).le_opNorm x
    _ ≤ K * ‖x‖ := mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)
    _ ≤ (K + 1) * ‖x‖ := by nlinarith [norm_nonneg x]
    _ < (K + 1) * (ε / (K + 1)) := by
        apply mul_lt_mul_of_pos_left hx (by positivity)
    _ = ε := by field_simp

end AbstractNuclear

section AnnularFamily

/-- The iterated derivatives of a scaled monomial. -/
private theorem annular_iteratedDeriv_div_pow (B : ℝ) (n j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun x : ℝ ↦ (x / B) ^ n) x =
      (n.descFactorial j : ℝ) / B ^ j * (x / B) ^ (n - j) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv j (fun x : ℝ ↦ (x / B) ^ n) =
        fun x ↦ (n.descFactorial j : ℝ) / B ^ j * (x / B) ^ (n - j) := funext ih
    rw [hfun]
    have h1 : HasDerivAt (fun x : ℝ ↦ x / B) (1 / B) x := (hasDerivAt_id x).div_const B
    have hd : HasDerivAt (fun x : ℝ ↦ (n.descFactorial j : ℝ) / B ^ j * (x / B) ^ (n - j))
        ((n.descFactorial j : ℝ) / B ^ j * (((n - j : ℕ) : ℝ) * (x / B) ^ (n - j - 1) * (1 / B)))
        x := (h1.pow (n - j)).const_mul ((n.descFactorial j : ℝ) / B ^ j)
    rw [hd.deriv, Nat.descFactorial_succ, Nat.sub_sub]
    push_cast
    ring

/-- On `|x| ≤ A` with `B = 2 A`, the derivatives of `(x / B) ^ n` are bounded uniformly in `n`. -/
private theorem annular_iteratedDeriv_div_pow_bound {A : ℝ} (hA : 0 < A) (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (x : ℝ), |x| ≤ A →
      ‖iteratedDeriv j (fun x : ℝ ↦ (x / (2 * A)) ^ n) x‖ ≤ M := by
  obtain ⟨M₀, hM₀⟩ := (tendsto_pow_const_div_const_pow_of_one_lt j one_lt_two).bddAbove_range
  have hM₀' (n : ℕ) : (n : ℝ) ^ j / 2 ^ n ≤ M₀ := hM₀ (mem_range_self n)
  have hM₀nn : 0 ≤ M₀ := le_trans (by positivity) (hM₀' 0)
  refine ⟨(2 / (2 * A)) ^ j * M₀, by positivity, fun n x hx ↦ ?_⟩
  rw [annular_iteratedDeriv_div_pow, norm_mul, norm_div, norm_pow, norm_pow, Real.norm_natCast,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * A)]
  have hhalf : |x| / (2 * A) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hpow : (|x| / (2 * A)) ^ (n - j) ≤ 2 ^ j / 2 ^ n := by
    calc (|x| / (2 * A)) ^ (n - j) ≤ (1 / 2 : ℝ) ^ (n - j) :=
          pow_le_pow_left₀ (by positivity) hhalf _
      _ = (1 / 2 : ℝ) ^ (n - j) * (1 / 2) ^ j * 2 ^ j := by
          rw [mul_assoc, ← mul_pow]; norm_num
      _ = (1 / 2 : ℝ) ^ (n - j + j) * 2 ^ j := by rw [pow_add]
      _ ≤ (1 / 2 : ℝ) ^ n * 2 ^ j := by
          gcongr ?_ * _
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 2 ^ j / 2 ^ n := by rw [one_div, inv_pow]; ring
  have hdesc : (n.descFactorial j : ℝ) ≤ (n : ℝ) ^ j := by
    exact_mod_cast Nat.descFactorial_le_pow n j
  calc (n.descFactorial j : ℝ) / (2 * A) ^ j * (|x| / (2 * A)) ^ (n - j)
      ≤ (n : ℝ) ^ j / (2 * A) ^ j * (2 ^ j / 2 ^ n) := by gcongr
    _ = (2 / (2 * A)) ^ j * ((n : ℝ) ^ j / 2 ^ n) := by rw [div_pow]; ring
    _ ≤ (2 / (2 * A)) ^ j * M₀ := by gcongr; exact hM₀' n

/-- The functions `ρ x * (x / (2 A)) ^ n`, for a smooth `ρ` supported in `[-A, A]`, form a
bounded family of Schwartz functions: every Schwartz seminorm is bounded uniformly in `n`. -/
private theorem annular_monomial_family (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) {A : ℝ} (hA : 0 < A)
    (hρA : tsupport ρ ⊆ Icc (-A) A) :
    ∃ w : ℕ → 𝓢(ℝ, ℂ), (∀ n x, w n x = ((ρ x * (x / (2 * A)) ^ n : ℝ) : ℂ)) ∧
      ∀ k m : ℕ, ∃ C : ℝ, ∀ n, SchwartzMap.seminorm ℂ k m (w n) ≤ C := by
  have hρc : HasCompactSupport ρ := isCompact_Icc.of_isClosed_subset isClosed_closure hρA
  have hq (n : ℕ) : ContDiff ℝ ∞ fun x : ℝ ↦ (x / (2 * A)) ^ n := by fun_prop
  have hr (n : ℕ) : ContDiff ℝ ∞ fun x : ℝ ↦ ρ x * (x / (2 * A)) ^ n := hρ.mul (hq n)
  have hsm (n : ℕ) : ContDiff ℝ ∞ fun x : ℝ ↦ ((ρ x * (x / (2 * A)) ^ n : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hr n)
  have hcs (n : ℕ) : HasCompactSupport fun x : ℝ ↦ ((ρ x * (x / (2 * A)) ^ n : ℝ) : ℂ) :=
    (hρc.mul_right (f' := fun x : ℝ ↦ (x / (2 * A)) ^ n)).comp_left Complex.ofReal_zero
  refine ⟨fun n ↦ (hcs n).toSchwartzMap (hsm n), fun n x ↦ rfl, fun k m ↦ ?_⟩
  -- bounds for the derivatives of `ρ` and of the monomials
  have hR (i : ℕ) : ∃ R : ℝ, ∀ x, ‖iteratedFDeriv ℝ i ρ x‖ ≤ R :=
    ⟨_, fun x ↦ (hρc.toSchwartzMap hρ).norm_iteratedFDeriv_le_seminorm ℝ i x⟩
  choose R hR using hR
  choose M hM0 hM using fun j ↦ annular_iteratedDeriv_div_pow_bound hA j
  have hRnn (i : ℕ) : 0 ≤ R i := (norm_nonneg _).trans (hR i 0)
  refine ⟨A ^ k * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * R i * M (m - i), fun n ↦ ?_⟩
  have hSnn : 0 ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * R i * M (m - i) :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (by positivity) (hRnn i)) (hM0 _)
  refine SchwartzMap.seminorm_le_bound ℂ k m _ (by positivity) fun x ↦ ?_
  have hnorm : ‖iteratedFDeriv ℝ m (fun x : ℝ ↦ ((ρ x * (x / (2 * A)) ^ n : ℝ) : ℂ)) x‖ =
      ‖iteratedFDeriv ℝ m (fun x : ℝ ↦ ρ x * (x / (2 * A)) ^ n) x‖ :=
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left (n := ∞) (hr n).contDiffAt
      (by exact_mod_cast le_top)
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x : ℝ ↦ ((ρ x * (x / (2 * A)) ^ n : ℝ) : ℂ)) x‖ ≤ _
  rw [hnorm]
  have hprod := norm_iteratedFDeriv_mul_le (N := ∞) hρ (hq n) x (n := m)
    (by exact_mod_cast le_top)
  by_cases hx : x ∈ tsupport ρ
  · have hxA : |x| ≤ A := abs_le.mpr (hρA hx)
    have hsum : ‖iteratedFDeriv ℝ m (fun x : ℝ ↦ ρ x * (x / (2 * A)) ^ n) x‖ ≤
        ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * R i * M (m - i) := by
      refine hprod.trans (Finset.sum_le_sum fun i _ ↦ ?_)
      have h2 : ‖iteratedFDeriv ℝ (m - i) (fun x : ℝ ↦ (x / (2 * A)) ^ n) x‖ ≤ M (m - i) := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact hM (m - i) n x hxA
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hR i x) (by positivity)) h2
        (norm_nonneg _) (mul_nonneg (by positivity) (hRnn i))
    have hxk : ‖x‖ ^ k ≤ A ^ k := pow_le_pow_left₀ (norm_nonneg _) hxA k
    exact mul_le_mul hxk hsum (norm_nonneg _) (by positivity)
  · have hzero : ‖iteratedFDeriv ℝ m (fun x : ℝ ↦ ρ x * (x / (2 * A)) ^ n) x‖ ≤ 0 := by
      refine hprod.trans (le_of_eq (Finset.sum_eq_zero fun i _ ↦ ?_))
      have : iteratedFDeriv ℝ i ρ x = 0 := by
        by_contra h
        exact hx (support_iteratedFDeriv_subset i h)
      rw [this, norm_zero, mul_zero, zero_mul]
    have : ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x : ℝ ↦ ρ x * (x / (2 * A)) ^ n) x‖ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hzero
    exact this.trans (by positivity)

end AnnularFamily

section KernelSeries

/-- Moments of an integrable function on a band are bounded by powers of the half-width. -/
private theorem annular_moment_integrable (Y : ℝ) (ψ : ℝ → ℂ)
    (hψ : Integrable ψ (volume.restrict (Icc (-Y) Y))) (n : ℕ) :
    Integrable (fun ξ : ℝ ↦ ψ ξ * (ξ : ℂ) ^ n) (volume.restrict (Icc (-Y) Y)) ∧
      ∫ ξ in Icc (-Y) Y, ‖ψ ξ * (ξ : ℂ) ^ n‖ ≤ |Y| ^ n * ∫ ξ in Icc (-Y) Y, ‖ψ ξ‖ := by
  have hb : ∀ᵐ ξ : ℝ ∂(volume.restrict (Icc (-Y) Y)), ‖(ξ : ℂ) ^ n‖ ≤ |Y| ^ n := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with ξ hξ
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_le.mpr hξ).trans (le_abs_self Y)) n
  have hint : Integrable (fun ξ : ℝ ↦ ψ ξ * (ξ : ℂ) ^ n) (volume.restrict (Icc (-Y) Y)) :=
    hψ.mul_bdd (by fun_prop) hb
  refine ⟨hint, ?_⟩
  calc ∫ ξ in Icc (-Y) Y, ‖ψ ξ * (ξ : ℂ) ^ n‖
      ≤ ∫ ξ in Icc (-Y) Y, |Y| ^ n * ‖ψ ξ‖ := by
        refine integral_mono_ae hint.norm (hψ.norm.const_mul _) ?_
        filter_upwards [hb] with ξ hξ
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
    _ = |Y| ^ n * ∫ ξ in Icc (-Y) Y, ‖ψ ξ‖ := integral_const_mul _ _

/-- The norm of a term of the exponential series of `2 π i u`. -/
private theorem annular_norm_pow_div_factorial (u : ℝ) (n : ℕ) :
    ‖(2 * π * Complex.I * u) ^ n / (n.factorial : ℂ)‖ = (2 * π * |u|) ^ n / n.factorial := by
  rw [norm_div, norm_pow, Complex.norm_natCast]
  congr 2
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
    Complex.norm_ofNat, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

/-- Termwise integration of the exponential series against an integrable function on a band. -/
private theorem annular_fourier_hasSum (Y : ℝ) (ψ : ℝ → ℂ)
    (hψ : Integrable ψ (volume.restrict (Icc (-Y) Y))) (u : ℝ) :
    HasSum (fun n : ℕ ↦ (2 * π * Complex.I * u) ^ n / n.factorial *
        ∫ ξ in Icc (-Y) Y, ψ ξ * (ξ : ℂ) ^ n)
      (∫ ξ in Icc (-Y) Y, ψ ξ * Complex.exp (2 * π * Complex.I * ξ * u)) := by
  set μ := volume.restrict (Icc (-Y) Y) with hμ
  let F : ℕ → ℝ → ℂ := fun n ξ ↦ (2 * π * Complex.I * u) ^ n / n.factorial * (ψ ξ * (ξ : ℂ) ^ n)
  have hF_int (n : ℕ) : Integrable (F n) μ := (annular_moment_integrable Y ψ hψ n).1.const_mul _
  have hnorm (n : ℕ) := annular_norm_pow_div_factorial u n
  have hF_sum : Summable fun n ↦ ∫ ξ, ‖F n ξ‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      ((Real.summable_pow_div_factorial (2 * π * |u| * |Y|)).mul_right (∫ ξ, ‖ψ ξ‖ ∂μ))
    have h1 : ∫ ξ, ‖F n ξ‖ ∂μ = (2 * π * |u|) ^ n / n.factorial * ∫ ξ, ‖ψ ξ * (ξ : ℂ) ^ n‖ ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun ξ ↦ ?_)
      change ‖(2 * π * Complex.I * u) ^ n / (n.factorial : ℂ) * (ψ ξ * (ξ : ℂ) ^ n)‖ = _
      rw [norm_mul, hnorm]
    rw [h1]
    calc (2 * π * |u|) ^ n / n.factorial * ∫ ξ, ‖ψ ξ * (ξ : ℂ) ^ n‖ ∂μ
        ≤ (2 * π * |u|) ^ n / n.factorial * (|Y| ^ n * ∫ ξ, ‖ψ ξ‖ ∂μ) := by
          apply mul_le_mul_of_nonneg_left (annular_moment_integrable Y ψ hψ n).2
          positivity
      _ = (2 * π * |u| * |Y|) ^ n / n.factorial * ∫ ξ, ‖ψ ξ‖ ∂μ := by
          rw [mul_pow (2 * π * |u|)]; ring
  have h := hasSum_integral_of_summable_integral_norm hF_int hF_sum
  have hpt (ξ : ℝ) : ∑' n, F n ξ = ψ ξ * Complex.exp (2 * π * Complex.I * ξ * u) := by
    have hexp : HasSum (fun n : ℕ ↦ (2 * π * Complex.I * ξ * u) ^ n / (n.factorial : ℂ))
        (Complex.exp (2 * π * Complex.I * ξ * u)) := by
      rw [Complex.exp_eq_exp_ℂ]
      exact NormedSpace.expSeries_div_hasSum_exp _
    have h2 := hexp.mul_left (ψ ξ)
    refine HasSum.tsum_eq (h2.congr_fun fun n ↦ ?_)
    change (2 * π * Complex.I * u) ^ n / (n.factorial : ℂ) * (ψ ξ * (ξ : ℂ) ^ n) = _
    rw [mul_pow (2 * π * Complex.I * ξ) (u : ℂ), mul_pow (2 * π * Complex.I) (ξ : ℂ),
      mul_pow (2 * π * Complex.I) (u : ℂ)]
    ring
  simp_rw [hpt] at h
  refine h.congr_fun fun n ↦ ?_
  change _ = ∫ ξ, (2 * π * Complex.I * u) ^ n / (n.factorial : ℂ) * (ψ ξ * (ξ : ℂ) ^ n) ∂μ
  rw [integral_const_mul]

/-- The dilation average of a band-limited inverse transform, as a power series in `x`: the
`n`-th term is a moment of `φ`, a term of the exponential series and a moment of `ψ`. -/
private theorem annular_kernel_hasSum (Y : ℝ) (ψ : ℝ → ℂ)
    (hψ : Integrable ψ (volume.restrict (Icc (-Y) Y))) (φ : ℝ → ℝ)
    (hφ : Integrable φ (volume.restrict (Icc (1 : ℝ) 2))) (x : ℝ) :
    HasSum (fun n : ℕ ↦ ((∫ g in Icc (1 : ℝ) 2, φ g * g⁻¹ ^ n : ℝ) : ℂ) *
        ((2 * π * Complex.I * x) ^ n / n.factorial * ∫ ξ in Icc (-Y) Y, ψ ξ * (ξ : ℂ) ^ n))
      (∫ g in Icc (1 : ℝ) 2, φ g • ∫ ξ in Icc (-Y) Y,
        ψ ξ * Complex.exp (2 * π * Complex.I * ξ * ((x / g : ℝ) : ℂ))) := by
  set ν := volume.restrict (Icc (1 : ℝ) 2) with hν
  let L : ℕ → ℂ := fun n ↦ ∫ ξ in Icc (-Y) Y, ψ ξ * (ξ : ℂ) ^ n
  let Z : ℕ → ℂ := fun n ↦ (2 * π * Complex.I * x) ^ n / n.factorial * L n
  let G : ℕ → ℝ → ℂ := fun n g ↦ (φ g * g⁻¹ ^ n) • Z n
  have hpt (g : ℝ) : HasSum (fun n ↦ G n g) (φ g • ∫ ξ in Icc (-Y) Y,
      ψ ξ * Complex.exp (2 * π * Complex.I * ξ * ((x / g : ℝ) : ℂ))) := by
    have h := (annular_fourier_hasSum Y ψ hψ (x / g)).const_smul (φ g)
    refine h.congr_fun fun n ↦ ?_
    change (φ g * g⁻¹ ^ n) • ((2 * π * Complex.I * x) ^ n / (n.factorial : ℂ) * L n) =
      φ g • ((2 * π * Complex.I * ((x / g : ℝ) : ℂ)) ^ n / (n.factorial : ℂ) * L n)
    have hxg : (2 * π * Complex.I * ((x / g : ℝ) : ℂ)) = (2 * π * Complex.I * x) * (g : ℂ)⁻¹ := by
      push_cast
      ring
    rw [Complex.real_smul, Complex.real_smul, hxg, mul_pow]
    push_cast
    ring
  have hb (n : ℕ) : ∀ᵐ g : ℝ ∂ν, ‖g⁻¹ ^ n‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with g hg
    have hg0 : (0 : ℝ) < g := by linarith [hg.1]
    rw [norm_pow, norm_inv, Real.norm_eq_abs, abs_of_pos hg0]
    exact pow_le_one₀ (inv_nonneg.mpr hg0.le) (inv_le_one_of_one_le₀ hg.1)
  have hr (n : ℕ) : Integrable (fun g : ℝ ↦ φ g * g⁻¹ ^ n) ν :=
    hφ.mul_bdd (measurable_inv.pow_const n).aestronglyMeasurable (hb n)
  have hG_int (n : ℕ) : Integrable (G n) ν := (hr n).smul_const (Z n)
  have hZ (n : ℕ) : ‖Z n‖ ≤ (2 * π * |x| * |Y|) ^ n / n.factorial *
      ∫ ξ in Icc (-Y) Y, ‖ψ ξ‖ := by
    have hL : ‖L n‖ ≤ |Y| ^ n * ∫ ξ in Icc (-Y) Y, ‖ψ ξ‖ :=
      (norm_integral_le_integral_norm _).trans (annular_moment_integrable Y ψ hψ n).2
    calc ‖Z n‖ = (2 * π * |x|) ^ n / n.factorial * ‖L n‖ := by
          rw [norm_mul, annular_norm_pow_div_factorial]
      _ ≤ (2 * π * |x|) ^ n / n.factorial * (|Y| ^ n * ∫ ξ in Icc (-Y) Y, ‖ψ ξ‖) := by
          apply mul_le_mul_of_nonneg_left hL
          positivity
      _ = (2 * π * |x| * |Y|) ^ n / n.factorial * ∫ ξ in Icc (-Y) Y, ‖ψ ξ‖ := by
          rw [mul_pow (2 * π * |x|)]; ring
  have hG_sum : Summable fun n ↦ ∫ g, ‖G n g‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      (((Real.summable_pow_div_factorial (2 * π * |x| * |Y|)).mul_right
        (∫ ξ in Icc (-Y) Y, ‖ψ ξ‖)).mul_left (∫ g, ‖φ g‖ ∂ν))
    calc ∫ g, ‖G n g‖ ∂ν ≤ ∫ g, ‖φ g‖ * ‖Z n‖ ∂ν := by
          refine integral_mono_ae (hG_int n).norm (hφ.norm.mul_const _) ?_
          filter_upwards [hb n] with g hg
          change ‖(φ g * g⁻¹ ^ n) • Z n‖ ≤ ‖φ g‖ * ‖Z n‖
          rw [norm_smul, norm_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_of_le_one_right (norm_nonneg _) hg) (norm_nonneg _)
      _ = (∫ g, ‖φ g‖ ∂ν) * ‖Z n‖ := integral_mul_const _ _
      _ ≤ (∫ g, ‖φ g‖ ∂ν) * ((2 * π * |x| * |Y|) ^ n / n.factorial *
            ∫ ξ in Icc (-Y) Y, ‖ψ ξ‖) :=
          mul_le_mul_of_nonneg_left (hZ n) (integral_nonneg fun _ ↦ norm_nonneg _)
  have h := hasSum_integral_of_summable_integral_norm hG_int hG_sum
  simp_rw [fun g ↦ (hpt g).tsum_eq] at h
  refine h.congr_fun fun n ↦ ?_
  change _ = ∫ g, (φ g * g⁻¹ ^ n) • Z n ∂ν
  rw [integral_smul_const, Complex.real_smul]

end KernelSeries

section NuclearFactor

/-- A Schwartz function that vanishes near the origin is flat there. -/
private theorem realPWAnnular_mem_flat (h : 𝓢(ℝ, ℂ)) (h0 : (h : ℝ → ℂ) =ᶠ[𝓝 0] 0) :
    h ∈ realSchwartzFlatAtOrigin := by
  rw [mem_realSchwartzFlatAtOrigin_iff]
  intro k
  rw [h0.iteratedDeriv_eq k]
  simp

/-- The moments of `φ` against the powers of `g⁻¹` on `[1, 2]` are bounded by the integral
of `‖φ‖`. -/
private theorem annular_dilation_moment_le (φ : ℝ → ℝ)
    (hφ : Integrable φ (volume.restrict (Icc (1 : ℝ) 2))) (n : ℕ) :
    |∫ g in Icc (1 : ℝ) 2, φ g * g⁻¹ ^ n| ≤ ∫ g in Icc (1 : ℝ) 2, ‖φ g‖ := by
  have hb : ∀ᵐ g : ℝ ∂(volume.restrict (Icc (1 : ℝ) 2)), ‖g⁻¹ ^ n‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with g hg
    have hg0 : (0 : ℝ) < g := by linarith [hg.1]
    rw [norm_pow, norm_inv, Real.norm_eq_abs, abs_of_pos hg0]
    exact pow_le_one₀ (inv_nonneg.mpr hg0.le) (inv_le_one_of_one_le₀ hg.1)
  have hr : Integrable (fun g : ℝ ↦ φ g * g⁻¹ ^ n) (volume.restrict (Icc (1 : ℝ) 2)) :=
    hφ.mul_bdd (measurable_inv.pow_const n).aestronglyMeasurable hb
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_ae hr.norm hφ.norm ?_)
  filter_upwards [hb] with g hg
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hg

/-- Paper: Theorem 12.4.1.1, proof, pp. 515–517, with Lemma C.3.2.2, p. 695. In the rational
real-place model, with a spatial cutoff `ρ` that vanishes near zero, the cutoff–dilation
composite is a nuclear operator from the Fourier side `L²([-Y, Y])` of the Paley–Wiener level
into the flat Schwartz space.
Reconstruction: The paper does not state this. It is the positive counterpart of
`sLocalTrace_realUpperBallPWFlatRange` (refuted in `Sec4_RealPWFactorization_Printed.lean`),
for the cutoff with an inner radius of Definition 9.3.3.1(4)–(6), p. 427, and footnote 2 on
p. 514, and it is not known whether it is what the author intends. The argument is the sketch
"Annular replacement at fixed cutoffs" posted by @dyknapp on issue #7354.
Deviation: The operator is written on the Fourier side. A band-limited test `f` of the level
corresponds to `ψ = 𝓕 f` restricted to `[-Y, Y]`, and `∫ ξ in [-Y, Y], ψ ξ * exp (2πi ξ u)` is
`f u` by Fourier inversion. The map `f ↦ 𝓕 f` is bounded from any norm on the level that
dominates the `L²` norm, as the weighted norms with weight at least one do. As in the sibling
statement, `φ` absorbs the factor `g⁻³ᐟ²` from untwisting and Haar measure, and only its
values on `[1, 2]` enter. No evenness or vanishing at zero of the test is needed.
Nothing in the Lean uses this statement. It gives the nuclear factor `A₀` of Lemma C.3.2.2 in
this model for a fixed cutoff; it does not give the comparison of the diagonal with the sharp
orbital masses (I398), which stays open. -/
theorem sLocalTrace_realAnnularPW_nuclearFactor (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (hρ0 : ρ =ᶠ[𝓝 0] 0) (φ : 𝓢(ℝ, ℝ)) {Y : ℝ} (hY : 0 < Y) :
    ∃ A₀ : Lp ℂ 2 (volume.restrict (Icc (-Y) Y)) →L[ℂ] realSchwartzFlatAtOrigin,
      IsNuclearOperator A₀ ∧
      ∀ (ψ : Lp ℂ 2 (volume.restrict (Icc (-Y) Y))) (x : ℝ),
        (A₀ ψ : 𝓢(ℝ, ℂ)) x = ρ x • ∫ g in Icc (1 : ℝ) 2, φ g •
          ∫ ξ in Icc (-Y) Y, ψ ξ * Complex.exp (2 * π * Complex.I * ξ * ((x / g : ℝ) : ℂ)) := by
  classical
  set μ := volume.restrict (Icc (-Y) Y) with hμ
  -- the support of the cutoff
  obtain ⟨r, hr⟩ := hρc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨A, hA, hrA⟩ : ∃ A : ℝ, 0 < A ∧ r ≤ A := ⟨max r 1, by positivity, le_max_left _ _⟩
  have hρA : tsupport ρ ⊆ Icc (-A) A := fun x hx ↦ by
    have h := hr hx
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at h
    exact abs_le.mp (h.trans hrA)
  -- the bounded family of flat vectors
  obtain ⟨w, hw, hwb⟩ := annular_monomial_family ρ hρ hA hρA
  have hwflat (n : ℕ) : w n ∈ realSchwartzFlatAtOrigin := by
    apply realPWAnnular_mem_flat
    filter_upwards [hρ0] with x hx
    rw [hw, hx]
    simp
  let v : ℕ → realSchwartzFlatAtOrigin := fun n ↦ ⟨w n, hwflat n⟩
  have hcompl : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  have hcompl' : CompleteSpace realSchwartzFlatAtOrigin :=
    realSchwartzFlatAtOrigin_isClosed.completeSpace_coe
  have huag : IsUniformAddGroup realSchwartzFlatAtOrigin :=
    realSchwartzFlatAtOrigin.toAddSubgroup.isUniformAddGroup
  have hpoly : PolynormableSpace ℂ 𝓢(ℝ, ℂ) := (schwartz_withSeminorms ℂ ℝ ℂ).toPolynormableSpace
  have hv : IsVonNBounded ℂ (range v) := by
    have hws := (Topology.IsInducing.subtypeVal (t := (realSchwartzFlatAtOrigin : Set 𝓢(ℝ, ℂ)))
      |>.withSeminorms (f := realSchwartzFlatAtOrigin.subtype) (schwartz_withSeminorms ℂ ℝ ℂ))
    rw [hws.isVonNBounded_iff_seminorm_bounded]
    rintro ⟨k, m⟩
    obtain ⟨C, hC⟩ := hwb k m
    refine ⟨max C 0 + 1, by positivity, ?_⟩
    rintro _ ⟨n, rfl⟩
    change SchwartzMap.seminorm ℂ k m (w n) < _
    exact lt_of_le_of_lt ((hC n).trans (le_max_left _ _)) (lt_add_one _)
  -- the normalized moment functionals on `L²` of the band
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun ξ : ℝ ↦ (((ξ / Y) ^ n : ℝ) : ℂ)) μ :=
    (by fun_prop : Continuous fun ξ : ℝ ↦ (((ξ / Y) ^ n : ℝ) : ℂ)).aestronglyMeasurable
  have hbd (n : ℕ) : ∀ᵐ ξ : ℝ ∂μ, ‖(((ξ / Y) ^ n : ℝ) : ℂ)‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with ξ hξ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_pow]
    refine pow_le_one₀ (abs_nonneg _) ?_
    rw [abs_div, abs_of_pos hY, div_le_one hY]
    exact abs_le.mpr hξ
  have hmem (n : ℕ) : MemLp (fun ξ : ℝ ↦ (((ξ / Y) ^ n : ℝ) : ℂ)) 2 μ :=
    MemLp.of_bound (hmeas n) 1 (hbd n)
  let f : ℕ → Lp ℂ 2 μ →L[ℂ] ℂ := fun n ↦ innerSL ℂ ((hmem n).toLp _)
  have hf (n : ℕ) : ‖f n‖ ≤ (μ univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal 1).toReal := by
    change ‖innerSL ℂ ((hmem n).toLp _)‖ ≤ _
    rw [innerSL_apply_norm, Lp.norm_toLp]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)) ENNReal.ofReal_ne_top)
      (eLpNorm_le_of_ae_bound (hmeas n) (hbd n))
  have hfapply (n : ℕ) (ψ : Lp ℂ 2 μ) :
      f n ψ = (Y : ℂ)⁻¹ ^ n * ∫ ξ, ψ ξ * (ξ : ℂ) ^ n ∂μ := by
    change inner ℂ ((hmem n).toLp _) ψ = _
    rw [L2.inner_def, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [(hmem n).coeFn_toLp] with ξ hξ
    rw [hξ, RCLike.inner_apply, Complex.conj_ofReal]
    push_cast
    rw [div_pow, div_eq_mul_inv, inv_pow]
    ring
  -- the coefficients
  have hφint : Integrable (φ : ℝ → ℝ) (volume.restrict (Icc (1 : ℝ) 2)) :=
    φ.continuous.integrableOn_Icc
  let κ : ℕ → ℝ := fun n ↦ ∫ g in Icc (1 : ℝ) 2, φ g * g⁻¹ ^ n
  let c : ℕ → ℂ := fun n ↦
    (κ n : ℂ) * ((2 * π * Complex.I * ((2 * A * Y : ℝ) : ℂ)) ^ n / n.factorial)
  have hc : Summable fun n ↦ ‖c n‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      ((Real.summable_pow_div_factorial (2 * π * |2 * A * Y|)).mul_left
        (∫ g in Icc (1 : ℝ) 2, ‖φ g‖))
    change ‖(κ n : ℂ) * ((2 * π * Complex.I * ((2 * A * Y : ℝ) : ℂ)) ^ n / n.factorial)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, annular_norm_pow_div_factorial]
    exact mul_le_mul_of_nonneg_right (annular_dilation_moment_le φ hφint n) (by positivity)
  obtain ⟨A₀, hnuc, hsum⟩ := exists_isNuclearOperator_of_summable_of_bounded c hc f hf v hv
  refine ⟨A₀, hnuc, fun ψ x ↦ ?_⟩
  -- evaluate the series at `x`
  have hψint : Integrable (ψ : ℝ → ℂ) μ := (Lp.memLp ψ).integrable one_le_two
  let ev : realSchwartzFlatAtOrigin →L[ℂ] ℂ :=
    ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)).comp realSchwartzFlatAtOrigin.subtypeL
  have h1 := (hsum ψ).mapL ev
  have h2 := (annular_kernel_hasSum Y ψ hψint φ hφint x).mul_left (ρ x : ℂ)
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hY0 : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hterm (n : ℕ) : ev ((c n * f n ψ) • v n) = (ρ x : ℂ) * ((κ n : ℂ) *
      ((2 * π * Complex.I * x) ^ n / n.factorial * ∫ ξ in Icc (-Y) Y, ψ ξ * (ξ : ℂ) ^ n)) := by
    change ((κ n : ℂ) * ((2 * π * Complex.I * ((2 * A * Y : ℝ) : ℂ)) ^ n / n.factorial) *
      f n ψ) * w n x = _
    have hcast : ((ρ x * (x / (2 * A)) ^ n : ℝ) : ℂ) =
        (ρ x : ℂ) * (((x / (2 * A) : ℝ)) : ℂ) ^ n := by push_cast; ring
    have key : (2 * π * Complex.I * ((2 * A * Y : ℝ) : ℂ)) ^ n * (Y : ℂ)⁻¹ ^ n *
        (((x / (2 * A) : ℝ) : ℂ)) ^ n = (2 * π * Complex.I * x) ^ n := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      push_cast
      field_simp
    rw [hw, hfapply, hcast, ← key]
    ring
  have h3 : ev (A₀ ψ) = (ρ x : ℂ) * ∫ g in Icc (1 : ℝ) 2, φ g •
      ∫ ξ in Icc (-Y) Y, ψ ξ * Complex.exp (2 * π * Complex.I * ξ * ((x / g : ℝ) : ℂ)) :=
    h1.unique (h2.congr_fun hterm)
  rw [Complex.real_smul]
  exact h3

/-- Paper: Theorem 12.4.1.1, proof, pp. 515–517, with Lemma C.3.2.2, p. 695. On the
band-limited Schwartz tests of `sLocalTrace_realUpperBallPWFlatRange`, the nuclear operator of
`sLocalTrace_realAnnularPW_nuclearFactor` is the cutoff–dilation composite
`f ↦ (x ↦ ρ x • ∫ g in [1, 2], φ g • f (x / g))` of that statement, now with a cutoff `ρ` that
vanishes near zero.
Reconstruction: The paper does not state this; see `sLocalTrace_realAnnularPW_nuclearFactor`.
Deviation: The test enters through the class `ψ` of its Fourier transform in `L²` of the band.
The Fourier cutoff of the sibling statement fixes such a test and is omitted. -/
theorem sLocalTrace_realAnnularPW_nuclearFactor_bandlimited (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (hρ0 : ρ =ᶠ[𝓝 0] 0) (φ : 𝓢(ℝ, ℝ)) {Y : ℝ} (hY : 0 < Y) :
    ∃ A₀ : Lp ℂ 2 (volume.restrict (Icc (-Y) Y)) →L[ℂ] realSchwartzFlatAtOrigin,
      IsNuclearOperator A₀ ∧
      ∀ (f : 𝓢(ℝ, ℂ)) (ψ : Lp ℂ 2 (volume.restrict (Icc (-Y) Y))),
        tsupport ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ⊆ Icc (-Y) Y →
        (ψ : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-Y) Y)] ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) →
        ∀ x : ℝ, (A₀ ψ : 𝓢(ℝ, ℂ)) x = ρ x • ∫ g in Icc (1 : ℝ) 2, φ g • f (x / g) := by
  obtain ⟨A₀, hnuc, hA⟩ := sLocalTrace_realAnnularPW_nuclearFactor ρ hρ hρc hρ0 φ hY
  refine ⟨A₀, hnuc, fun f ψ hband hψ x ↦ ?_⟩
  rw [hA ψ x]
  have hinv (u : ℝ) :
      ∫ ξ in Icc (-Y) Y, ψ ξ * Complex.exp (2 * π * Complex.I * ξ * (u : ℂ)) = f u := by
    have h1 : ∫ ξ in Icc (-Y) Y, ψ ξ * Complex.exp (2 * π * Complex.I * ξ * (u : ℂ)) =
        ∫ ξ in Icc (-Y) Y,
          (𝓕 f : 𝓢(ℝ, ℂ)) ξ * Complex.exp (2 * π * Complex.I * ξ * (u : ℂ)) := by
      refine integral_congr_ae ?_
      filter_upwards [hψ] with ξ hξ
      rw [hξ]
    rw [h1, setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hξ (hband h)), zero_mul])]
    have h2 : f u = (𝓕⁻ ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u := by
      rw [← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]
    rw [h2, Real.fourierInv_eq']
    refine integral_congr_ae (ae_of_all _ fun ξ ↦ ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    simp only [Real.inner_apply]
    push_cast
    ring
  simp_rw [hinv]

end NuclearFactor

end RiemannMasullo
