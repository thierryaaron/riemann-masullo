module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
public import RiemannMasullo.Ch12_TraceGeometric.Sec4

/-!
# The polar complement of the Paley–Wiener level, for every number field

Theorem 12.4.1.1 (p. 514) is stated for cutoff operators compressed to the polar-free level
`sLocalInvariantPWSobolev` of Definition 11.2.1.3 (p. 488). That level is the closure of the
weighted theta functions of the tests whose two moments vanish, the value `f(0)` and the value
`f̂(0)` of the Fourier transform. Step III of the proof (p. 517) compares the trace on the level
with the summed sharp orbital masses of (12.4.1.22)–(12.4.1.24). For `ℚ` with no finite place
#7791 shows that the comparison fails by an explicit polar term. This file does the part of that
argument that holds for every number field and every finite set of places.

The Sobolev inclusion of `Sec1` in chapter 10 holds for every test, so the weighted theta class
of every test lies in the local Sobolev space (`sLocalFullPWTheta_memLp`,
`sLocalFullPWThetaSobolevMap`). The full band `sLocalFullPWSobolev` is the closure of the theta
image of all tests of the product region, with or without zero moments.

* `sLocalPWSobolev_polarComplement`. The level lies in the full band, and its complement there
  has dimension at most two. Each vector `e` of the complement represents the two moments:
  `⟪e, Θ f⟫ = c₀ f(0) + c₁ f̂(0)` on the tests of the region.
* `hilbertTrace_sLocalFullPWSobolev_compress`. For a nuclear operator, the trace compressed to the
  full band is the trace compressed to the level plus the diagonal entries on an orthonormal
  basis of the complement.
* `tendsto_inner_mul_mul`. For operators `M A K` whose outer factors tend to the identity at a
  vector, the diagonal entries at that vector tend to those of `A`.
* `sLocalLevel_trace_asymptotic_of_full_comparison`. If the traces compressed to the full band
  agree with the summed sharp masses up to `o(1)`, then on the level the conclusion of
  Theorem 12.4.1.1 holds with the polar term `∑ ⟪e i, A (e i)⟫` subtracted.
  `sLocalLevel_comparison_not_tendsto_zero`: when that term is not zero, the comparison of
  Step III fails on the level.

* `sLocalFullPWSobolev_eq_of_ne_one`. For a nontrivial norm-one character the full band is the
  level, so the polar complement is zero. A norm-one translate preserves the product region and
  the value at zero, multiplies the Fourier value at zero by a nonnegative constant and the theta
  function by `ω h ≠ 1`, and two differences remove both moments without changing the theta
  function. `sLocalLevel_trace_asymptotic_of_ne_one`: for such a character, given the comparison
  on the full band, Theorem 12.4.1.1 holds on the level as printed, with no polar term.

The Hilbert-space statements behind these are `polarComplement_spec`,
`hilbertTrace_nuclearCompress_eq` and `tendsto_hilbertTrace_nuclearCompress_sub`.

Not done here: the comparison on the full band, which is the hypothesis `hFull` and needs the
descended orbit kernel, and, for the trivial character, the evaluation of the polar term as
Mellin values of the test, which #7791 does for `ℚ` with no finite place.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology InnerProductSpace

namespace RiemannMasullo.Isolated

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A linear map that vanishes on the kernel of a map to `ℂ × ℂ` factors through that map. -/
theorem exists_comp_eq_of_ker_le {X W : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup W]
    [Module ℂ W] (q : X →ₗ[ℂ] ℂ × ℂ) (π : X →ₗ[ℂ] W) (h : LinearMap.ker q ≤ LinearMap.ker π) :
    ∃ g : ℂ × ℂ →ₗ[ℂ] W, g ∘ₗ q = π := by
  let π' := (LinearMap.ker q).liftQ π h
  let g₀ : LinearMap.range q →ₗ[ℂ] W := π' ∘ₗ q.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend g₀
  refine ⟨g, LinearMap.ext fun x ↦ ?_⟩
  have h1 : g (q x) = g₀ ⟨q x, LinearMap.mem_range_self q x⟩ := by
    rw [← hg]
    rfl
  rw [LinearMap.comp_apply, h1]
  simp only [g₀, π', LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- Reconstruction: let `Θ` send tests to a Hilbert space, let `Y` be a space of tests and let
`ℓ` record two moments of a test. Let `B` be the closure of the image of `Y`, and `V` the closure
of the image of the tests in `Y` whose two moments vanish (`hB`, `hV`). Then `V ≤ B`, the complement of `V` in
`B` has dimension at most two, and `B` is `V` plus that complement. Each vector `e` of the
complement represents the moments: `⟪e, Θ f⟫` is a linear function of `ℓ f` on `Y`. -/
theorem polarComplement_spec {X : Type*} [AddCommGroup X] [Module ℂ X]
    (Θ : X →ₗ[ℂ] H) (Y : Submodule ℂ X) (ℓ : X →ₗ[ℂ] ℂ × ℂ) (B V : Submodule ℂ H)
    (hB : B = (Y.map Θ).topologicalClosure)
    (hV : V = ((Y ⊓ LinearMap.ker ℓ).map Θ).topologicalClosure) :
    V ≤ B ∧ B = V ⊔ (B ⊓ Vᗮ) ∧ FiniteDimensional ℂ ↥(B ⊓ Vᗮ) ∧
      Module.finrank ℂ ↥(B ⊓ Vᗮ) ≤ 2 ∧
      ∀ e ∈ B ⊓ Vᗮ, ∃ c : ℂ × ℂ →ₗ[ℂ] ℂ, ∀ f ∈ Y, ⟪e, Θ f⟫_ℂ = c (ℓ f) := by
  subst hB hV
  set B := (Y.map Θ).topologicalClosure
  set V := ((Y ⊓ LinearMap.ker ℓ).map Θ).topologicalClosure
  have hVB : V ≤ B := Submodule.topologicalClosure_mono (Submodule.map_mono inf_le_left)
  have hVc : IsClosed (V : Set H) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace V := hVc.completeSpace_coe
  have hmemV : ∀ f ∈ Y, ℓ f = 0 → Θ f ∈ V := fun f hf hℓ ↦
    Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem ⟨hf, hℓ⟩)
  have hmemB : ∀ f ∈ Y, Θ f ∈ B := fun f hf ↦
    Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hf)
  let P : H →L[ℂ] H := Vᗮ.starProjection
  let q : Y →ₗ[ℂ] ℂ × ℂ := ℓ ∘ₗ Y.subtype
  let π : Y →ₗ[ℂ] H := P.toLinearMap ∘ₗ Θ ∘ₗ Y.subtype
  have hker : LinearMap.ker q ≤ LinearMap.ker π := by
    intro y hy
    simp only [LinearMap.mem_ker, q, π, LinearMap.comp_apply, Submodule.coe_subtype] at hy ⊢
    exact (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (Submodule.le_orthogonal_orthogonal V (hmemV y y.2 hy))
  obtain ⟨g, hg⟩ := exists_comp_eq_of_ker_le q π hker
  have hπg : LinearMap.range π ≤ LinearMap.range g := by
    rw [← hg, LinearMap.range_comp]
    exact LinearMap.map_le_range
  have hfin : FiniteDimensional ℂ (LinearMap.range π) :=
    Submodule.finiteDimensional_of_le hπg
  have hrange : B ⊓ Vᗮ = LinearMap.range π := by
    apply le_antisymm
    · intro e he
      have hcl : IsClosed (LinearMap.range π : Set H) := Submodule.isClosed_of_finiteDimensional _
      have hBle : B ≤ (LinearMap.range π).comap P.toLinearMap := by
        refine Submodule.topologicalClosure_minimal _ ?_ (hcl.preimage P.continuous)
        rintro _ ⟨f, hf, rfl⟩
        exact ⟨⟨f, hf⟩, rfl⟩
      have h1 := hBle he.1
      rwa [Submodule.mem_comap, ContinuousLinearMap.coe_coe,
        show P e = e from Submodule.starProjection_eq_self_iff.mpr he.2] at h1
    · rintro _ ⟨y, rfl⟩
      refine ⟨?_, Submodule.starProjection_apply_mem _ _⟩
      change Vᗮ.starProjection (Θ y) ∈ B
      rw [Submodule.starProjection_orthogonal_val]
      exact B.sub_mem (hmemB y y.2) (hVB (Submodule.starProjection_apply_mem V _))
  refine ⟨hVB, ?_, ?_, ?_, ?_⟩
  · rw [inf_comm]
    exact (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hVB).symm
  · rw [hrange]
    exact hfin
  · rw [hrange]
    calc Module.finrank ℂ (LinearMap.range π) ≤ Module.finrank ℂ (LinearMap.range g) :=
          Submodule.finrank_mono hπg
      _ ≤ Module.finrank ℂ (ℂ × ℂ) := LinearMap.finrank_range_le g
      _ = 2 := by simp
  · intro e he
    let lam : Y →ₗ[ℂ] ℂ := (innerSL ℂ e).toLinearMap ∘ₗ Θ ∘ₗ Y.subtype
    have hkerLam : LinearMap.ker q ≤ LinearMap.ker lam := by
      intro y hy
      simp only [LinearMap.mem_ker, q, lam, LinearMap.comp_apply, Submodule.coe_subtype,
        ContinuousLinearMap.coe_coe, innerSL_apply_apply] at hy ⊢
      exact Submodule.inner_left_of_mem_orthogonal (hmemV y y.2 hy) he.2
    obtain ⟨c, hc⟩ := exists_comp_eq_of_ker_le q lam hkerLam
    refine ⟨c, fun f hf ↦ ?_⟩
    have h1 := LinearMap.congr_fun hc ⟨f, hf⟩
    simpa [q, lam] using h1.symm

/-- The compression `P T P` of a nuclear operator by a bounded operator `P`. -/
def nuclearCompress (P : H →L[ℂ] H) (T : nuclearEndomorphisms H) : nuclearEndomorphisms H :=
  ⟨P * T.val * P, mul_mem_nuclearEndomorphisms_right P ⟨P * T.val,
    mul_mem_nuclearEndomorphisms_left P T⟩⟩

/-- Reconstruction: for closed subspaces `V ≤ B` whose relative complement `K = B ⊓ Vᗮ` is
finite dimensional, the trace of a nuclear operator compressed to `B` is its trace compressed to
`V` plus its diagonal entries on an orthonormal basis of `K`. -/
theorem hilbertTrace_nuclearCompress_eq (T : nuclearEndomorphisms H) (V B : Submodule ℂ H)
    [V.HasOrthogonalProjection] [B.HasOrthogonalProjection] (hVB : V ≤ B) {ι : Type*}
    [Fintype ι] [(B ⊓ Vᗮ).HasOrthogonalProjection] (e : OrthonormalBasis ι ℂ ↥(B ⊓ Vᗮ)) :
    hilbertTrace (nuclearCompress B.starProjection T) =
      hilbertTrace (nuclearCompress V.starProjection T) +
        ∑ i, ⟪(e i : H), T.val (e i)⟫_ℂ := by
  let PB : H →L[ℂ] H := B.starProjection
  let PV : H →L[ℂ] H := V.starProjection
  have hK : ∀ x, (B ⊓ Vᗮ).starProjection x = PB x - PV x := by
    intro x
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ⟨?_, ?_⟩ ?_
    · exact B.sub_mem (Submodule.starProjection_apply_mem B x)
        (hVB (Submodule.starProjection_apply_mem V x))
    · have h1 : PV x = PV (PB x) := by
        refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
          (Submodule.starProjection_apply_mem V x) fun w hw ↦ ?_).symm
        have h2 := Submodule.starProjection_inner_eq_zero (K := B) x w (hVB hw)
        have h3 := Submodule.starProjection_inner_eq_zero (K := V) x w hw
        have h4 : PB x - PV x = (x - PV x) - (x - PB x) := by abel
        calc ⟪PB x - PV x, w⟫_ℂ = ⟪x - PV x, w⟫_ℂ - ⟪x - PB x, w⟫_ℂ := by
              rw [h4, inner_sub_left]
          _ = 0 := by simp only [PB, PV, h2, h3, sub_zero]
      rw [h1]
      change PB x - V.starProjection (PB x) ∈ Vᗮ
      rw [← Submodule.starProjection_orthogonal_val]
      exact Submodule.starProjection_apply_mem _ _
    · intro w hw
      have h2 := Submodule.starProjection_inner_eq_zero (K := B) x w hw.1
      have h3 : ⟪PV x, w⟫_ℂ = 0 :=
        Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem V x) hw.2
      have h4 : x - (PB x - PV x) = (x - PB x) + PV x := by abel
      rw [h4, inner_add_left, h2, h3, add_zero]
  have hKsum : ∀ x, PB x - PV x = ∑ i, ⟪(e i : H), x⟫_ℂ • (e i : H) := by
    intro x
    rw [← hK, e.starProjection_eq_sum_rankOne]
    simp [InnerProductSpace.rankOne_apply]
  have heB : ∀ i, PB (e i) = e i := fun i ↦
    Submodule.starProjection_eq_self_iff.mpr (e i).2.1
  have heV : ∀ i, PV (e i) = 0 := fun i ↦
    (Submodule.starProjection_apply_eq_zero_iff _).mpr (e i).2.2
  let R₁ : ι → nuclearEndomorphisms H := fun i ↦
    ⟨((innerSL ℂ (e i : H)).comp (T.val * PB)).smulRight (e i : H),
      smulRight_mem_nuclearEndomorphisms _ _⟩
  let R₂ : ι → nuclearEndomorphisms H := fun i ↦
    ⟨(innerSL ℂ (e i : H)).smulRight (PV (T.val (e i))), smulRight_mem_nuclearEndomorphisms _ _⟩
  have hsplit : nuclearCompress PB T = nuclearCompress PV T + ∑ i, R₁ i + ∑ i, R₂ i := by
    refine Subtype.ext (ContinuousLinearMap.ext fun x ↦ ?_)
    simp only [nuclearCompress, Submodule.coe_add, Submodule.coe_sum, R₁, R₂,
      add_apply, sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      mul_apply_eq_comp, innerSL_apply_apply]
    have h1 := hKsum (T.val (PB x))
    have h2 := hKsum x
    have h3 : PV (T.val (PB x)) = PV (T.val (PV x)) + ∑ i, ⟪(e i : H), x⟫_ℂ • PV (T.val (e i)) := by
      have h5 : PB x = PV x + ∑ i, ⟪(e i : H), x⟫_ℂ • (e i : H) := by rw [← h2]; abel
      rw [h5, map_add, map_add, map_sum, map_sum]
      simp only [map_smul]
    have h1' : PB (T.val (PB x)) = PV (T.val (PB x)) +
        ∑ i, ⟪(e i : H), T.val (PB x)⟫_ℂ • (e i : H) := by
      rw [← h1]
      abel
    rw [h1', h3]
    abel
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  rw [← htr, ← htr, hsplit, map_add, map_add, map_sum, map_sum]
  simp only [htr, R₁, R₂, hilbertTrace_smulRight, ContinuousLinearMap.comp_apply,
    mul_apply_eq_comp, innerSL_apply_apply, heB]
  have h0 : ∑ i, ⟪(e i : H), PV (T.val (e i))⟫_ℂ = 0 := by
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← Submodule.inner_starProjection_left_eq_right]
    change ⟪PV (e i), T.val (e i)⟫_ℂ = 0
    rw [heV, inner_zero_left]
  rw [h0, add_zero]

/-- If the multipliers on either side of a bounded operator converge to the identity at a vector
`e`, the diagonal entries at `e` converge. -/
theorem tendsto_inner_mul_mul {α : Type*} {l : Filter α} (M K : α → H →L[ℂ] H) (A : H →L[ℂ] H)
    (e : H) (hM : Tendsto (fun t ↦ (M t).adjoint e) l (𝓝 e))
    (hK : Tendsto (fun t ↦ K t e) l (𝓝 e)) :
    Tendsto (fun t ↦ ⟪e, (M t * A * K t) e⟫_ℂ) l (𝓝 ⟪e, A e⟫_ℂ) := by
  have h := Filter.Tendsto.inner (𝕜 := ℂ) hM ((A.continuous.tendsto e).comp hK)
  refine h.congr fun t ↦ ?_
  simp only [Function.comp_apply, mul_apply_eq_comp]
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- Reconstruction: with `V ≤ B` and an orthonormal basis `e` of the relative complement, suppose
the traces compressed to `B` agree with given values `M t` up to `o(1)` and the diagonal entries at
`e i` converge to those of `A`. Then the traces compressed to `V` differ from `M t` by a quantity
that tends to minus the sum of the diagonal entries of `A` on the complement. -/
theorem tendsto_hilbertTrace_nuclearCompress_sub {α : Type*} {l : Filter α}
    (T : α → nuclearEndomorphisms H) (V B : Submodule ℂ H) [V.HasOrthogonalProjection]
    [B.HasOrthogonalProjection] (hVB : V ≤ B) {ι : Type*} [Fintype ι]
    [(B ⊓ Vᗮ).HasOrthogonalProjection] (e : OrthonormalBasis ι ℂ ↥(B ⊓ Vᗮ)) (A : H →L[ℂ] H)
    (M : α → ℂ)
    (hFull : Tendsto (fun t ↦ hilbertTrace (nuclearCompress B.starProjection (T t)) - M t) l
      (𝓝 0))
    (hDiag : ∀ i, Tendsto (fun t ↦ ⟪(e i : H), (T t).val (e i)⟫_ℂ) l
      (𝓝 ⟪(e i : H), A (e i)⟫_ℂ)) :
    Tendsto (fun t ↦ hilbertTrace (nuclearCompress V.starProjection (T t)) - M t) l
      (𝓝 (-∑ i, ⟪(e i : H), A (e i)⟫_ℂ)) := by
  have hsum := tendsto_finsetSum Finset.univ fun i _ ↦ hDiag i
  have h := hFull.sub hsum
  rw [zero_sub] at h
  refine h.congr fun t ↦ ?_
  rw [hilbertTrace_nuclearCompress_eq (T t) V B hVB e]
  ring

end Abstract

section Levels

open IsDedekindDomain NumberField
open scoped NNReal NumberField NumberField.AdeleRing

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))} {s : ℝ}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSIdeleQuotientMeasurableSpaceSec1

local notation "mₛ(" S ")" =>
  (continuousSIdeleQuotientNorm F S : SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "logNorm(" m ")" => (fun g ↦ Real.log (((m) g).val : ℝ))
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "localWMeasure" => (sLocalQuotientTamagawaMeasure F S).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm(mₛ(S)) g)))
local notation "LocalW" => Lp ℂ 2 localWMeasure
local notation "fullTheta(" a ", " ω ", " f ")" =>
  modulationWeight (mₛ(S)) a (sLocalHomogeneousAdelicThetaLinearMap F S ω f)
local notation "tests(" Λ ")" =>
  sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S Λ)

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
Reconstruction: the weighted homogeneous theta function of every S-adelic test, polar-free or
not, is a vector of the local Sobolev space at positive twist. The proof is that of
`sLocalPWTheta_memLp`, whose Sobolev inclusion (`exists_sLocalHomogeneousThetaSobolevInclusion`)
holds for every test. -/
theorem sLocalFullPWTheta_memLp {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (f : ℬₛ) :
    MemLp (fullTheta(a, ω, f)) 2 localWMeasure := by
  let : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩
  let μ := sLocalQuotientTamagawaMeasure F S
  let r (g : SIdeleQuotient F S) : ℝ := (mₛ(S) g).val
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S ω f
  let t := max s 0
  let b := a / 2
  have hb : 0 < b := half_pos ha
  have hbb : b + b = a := add_halves a
  have hr (g) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hc : Continuous r :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (mₛ(S)).continuous)
  obtain ⟨j, -, -, hj⟩ := exists_sLocalHomogeneousThetaSobolevInclusion (F := F) (S := S)
    hb (le_refl b) (show 0 ≤ t from le_max_right _ _) hb ω
  let u := (j (Submodule.Quotient.mk f)).val.val
  have hi := (globalThetaSobolev_norm_aux μ r hr hc.measurable b b b t θ u (hj f).2).1
  rw [hbb] at hi
  let d (g : SIdeleQuotient F S) := intervalSobolevDensity 0 0 t (Real.log (r g))
  have hd (g) : 0 ≤ d g := by dsimp [d, intervalSobolevDensity]; positivity
  have hm : Measurable d := by dsimp [d, intervalSobolevDensity]; fun_prop
  let Z (g : SIdeleQuotient F S) : ℂ := ((r g ^ a : ℝ) : ℂ) * θ g
  have hZ : Continuous Z := (Complex.continuous_ofReal.comp
    (hc.rpow_const fun g ↦ Or.inl (hr g).ne')).mul θ.continuous
  have mem : MemLp Z 2 (μ.withDensity fun g ↦ ENNReal.ofReal (d g)) := by
    apply (memLp_two_iff_integrable_sq_norm hZ.aestronglyMeasurable).2
    apply (integrable_withDensity_iff_integrable_smul' (ENNReal.measurable_ofReal.comp hm)
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2
    refine hi.congr (.of_forall fun g ↦ ?_)
    change ‖θ g‖ ^ 2 * intervalSobolevDensity a a t (Real.log (r g)) =
      (ENNReal.ofReal (d g)).toReal • ‖Z g‖ ^ 2
    rw [ENNReal.toReal_ofReal (hd g), smul_eq_mul]
    simp only [Z, d, norm_mul, mul_pow, Complex.norm_real,
      Real.rpow_def_of_pos (hr g), Real.norm_of_nonneg (Real.exp_pos _).le]
    have he := globalThetaSobolev_norm_density a 0 0 t (Real.log (r g))
    simp only [add_zero] at he
    rw [← he, mul_comm (Real.log (r g)) a]
    ring
  apply mem.mono_measure (withDensity_mono (.of_forall fun g ↦ ?_))
  apply ENNReal.ofReal_le_ofReal
  unfold d intervalSobolevDensity
  apply mul_le_mul_of_nonneg_left _ (le_trans (Real.exp_pos _).le (le_max_left _ _))
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Real.log (r g))])
    (div_le_div_of_nonneg_right (le_max_left s 0) (by norm_num))

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
Reconstruction: the weighted homogeneous theta class of every S-adelic test, as a linear map
into the local Sobolev space. On polar-free tests it is `sLocalPWThetaSobolevMap`
(`sLocalFullPWThetaSobolevMap_polar`). -/
def sLocalFullPWThetaSobolevMap {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) :
    ℬₛ →ₗ[ℂ] LocalW where
  toFun f := (sLocalFullPWTheta_memLp (s := s) ha ω f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (.of_forall fun x ↦ by
      simp only [map_add, ContinuousMap.coe_add, Pi.add_apply])
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_forall fun x ↦ by
      simp only [map_smul, ContinuousMap.coe_smul, Pi.smul_apply])

/-- On a polar-free test the full theta map is the theta map of the level. -/
theorem sLocalFullPWThetaSobolevMap_polar {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁)
    (f : sAdelePolarSubspace F S) :
    sLocalFullPWThetaSobolevMap (s := s) ha ω f.val =
      sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f :=
  rfl

/-- Paper: Equation (7.2.2.3), p. 340. The two polar values of a test, its value at zero and the
value of its Fourier transform at zero, as a linear map. Its kernel is the polar subspace. -/
def sAdelePolarValuesMap : ℬₛ →ₗ[ℂ] ℂ × ℂ :=
  IsLinearMap.mk' (fun f : ℬₛ ↦ (f (Multiplicative.ofAdd 0),
    sAdeleSchwartzFourier f (Multiplicative.ofAdd 0))) sAdelePolarValues_isLinear

theorem sAdelePolarValuesMap_apply (f : ℬₛ) :
    sAdelePolarValuesMap f =
      (f (Multiplicative.ofAdd 0), sAdeleSchwartzFourier f (Multiplicative.ofAdd 0)) :=
  rfl

theorem ker_sAdelePolarValuesMap :
    LinearMap.ker (sAdelePolarValuesMap (F := F) (S := S)) = sAdelePolarSubspace F S :=
  rfl

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), p. 488, without the zero-moment condition.
Reconstruction: the full band is the closure of the weighted theta image of all tests with
compact Fourier support in the product-norm region of size `Λ`, polar-free or not. The level
`sLocalInvariantPWSobolev` is the closure of the image of the polar-free ones. -/
def sLocalFullPWSobolev (_hs : 0 ≤ s) {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ) :
    Submodule ℂ LocalW :=
  ((tests(Λ)).map (sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω)).topologicalClosure

/-- The level is the closure of the image of the polar-free tests of the product region. -/
theorem sLocalInvariantPWSobolev_eq_closure_map (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a)
    (ω : PontryaginDual J₁) (Λ : ℝ) :
    sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω Λ =
      ((tests(Λ) ⊓ LinearMap.ker (sAdelePolarValuesMap (F := F) (S := S))).map
        (sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω)).topologicalClosure := by
  unfold sLocalInvariantPWSobolev
  congr 1
  rw [← Submodule.span_eq (tests(Λ) ⊓ LinearMap.ker (sAdelePolarValuesMap (F := F) (S := S))),
    ← Submodule.span_image]
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_image, SetLike.mem_coe, Submodule.mem_inf]
  constructor
  · rintro ⟨⟨⟨g, hg⟩, htest⟩, rfl⟩
    exact ⟨g, ⟨htest, hg⟩, rfl⟩
  · rintro ⟨g, ⟨htest, hg⟩, rfl⟩
    exact ⟨⟨⟨g, hg⟩, htest⟩, rfl⟩

theorem completeSpace_sLocalFullPWSobolev (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a)
    (ω : PontryaginDual J₁) (Λ : ℝ) :
    CompleteSpace (sLocalFullPWSobolev (F := F) (S := S) hs ha ω Λ) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem completeSpace_sLocalInvariantPWSobolev (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a)
    (ω : PontryaginDual J₁) (Λ : ℝ) :
    CompleteSpace (sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω Λ) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

attribute [local instance] completeSpace_sLocalFullPWSobolev
  completeSpace_sLocalInvariantPWSobolev

local notation "fullB(" hs ", " ha ", " ω ", " Λ ")" =>
  sLocalFullPWSobolev (F := F) (S := S) hs ha ω Λ
local notation "levelV(" hs ", " ha ", " ω ", " Λ ")" =>
  sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω Λ

/-- Paper: Definition 11.2.1.3(1), p. 488, and Theorem 12.4.1.1, Step III, p. 517.
Reconstruction: the polar-free level lies in the full band, and its complement there has
dimension at most two. Every vector `e` of the complement represents the two polar values on the
tests of the product region: `⟪e, Θ f⟫ = c₀ f(0) + c₁ f̂(0)` for constants `c₀, c₁`. -/
theorem sLocalPWSobolev_polarComplement (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a)
    (ω : PontryaginDual J₁) (Λ : ℝ) :
    levelV(hs, ha, ω, Λ) ≤ fullB(hs, ha, ω, Λ) ∧
      fullB(hs, ha, ω, Λ) = levelV(hs, ha, ω, Λ) ⊔
        (fullB(hs, ha, ω, Λ) ⊓ (levelV(hs, ha, ω, Λ))ᗮ) ∧
      FiniteDimensional ℂ ↥(fullB(hs, ha, ω, Λ) ⊓ (levelV(hs, ha, ω, Λ))ᗮ) ∧
      Module.finrank ℂ ↥(fullB(hs, ha, ω, Λ) ⊓ (levelV(hs, ha, ω, Λ))ᗮ) ≤ 2 ∧
      ∀ e ∈ fullB(hs, ha, ω, Λ) ⊓ (levelV(hs, ha, ω, Λ))ᗮ, ∃ c₀ c₁ : ℂ, ∀ f ∈ tests(Λ),
        ⟪e, sLocalFullPWThetaSobolevMap (s := s) ha ω f⟫_ℂ =
          c₀ * f (Multiplicative.ofAdd 0) + c₁ * sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := polarComplement_spec (H := LocalW) (X := ℬₛ)
    (sLocalFullPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω) (tests(Λ))
    (sAdelePolarValuesMap (F := F) (S := S)) (fullB(hs, ha, ω, Λ)) (levelV(hs, ha, ω, Λ)) rfl
    (sLocalInvariantPWSobolev_eq_closure_map hs ha ω Λ)
  refine ⟨h1, h2, h3, h4, fun e he ↦ ?_⟩
  obtain ⟨c, hc⟩ := h5 e he
  refine ⟨c (1, 0), c (0, 1), fun f hf ↦ ?_⟩
  rw [hc f hf, sAdelePolarValuesMap_apply]
  have hsplit : (f (Multiplicative.ofAdd 0), sAdeleSchwartzFourier f (Multiplicative.ofAdd 0)) =
      f (Multiplicative.ofAdd 0) • ((1 : ℂ), (0 : ℂ)) +
        sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) • ((0 : ℂ), (1 : ℂ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm (c (1, 0)),
    mul_comm (c (0, 1))]

/-- Paper: Theorem 12.4.1.1, Step III, p. 517.
Reconstruction: the complement of the level in the full band is finite dimensional, so it has
orthogonal projections. -/
theorem hasOrthogonalProjection_polarComplement (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a)
    (ω : PontryaginDual J₁) (Λ : ℝ) :
    (fullB(hs, ha, ω, Λ) ⊓ (levelV(hs, ha, ω, Λ))ᗮ).HasOrthogonalProjection :=
  have := (sLocalPWSobolev_polarComplement hs ha ω Λ).2.2.1
  inferInstance

attribute [local instance] hasOrthogonalProjection_polarComplement

/-- Paper: Theorem 12.4.1.1, Step III, p. 517.
Reconstruction: for every nuclear operator on the local Sobolev space, the trace compressed to the
full band is the trace compressed to the polar-free level plus the diagonal entries on an
orthonormal basis of the complement, which has at most two vectors. -/
theorem hilbertTrace_sLocalFullPWSobolev_compress (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a)
    (ω : PontryaginDual J₁) (Λ : ℝ) (T : nuclearEndomorphisms LocalW) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ ↥(fullB(hs, ha, ω, Λ) ⊓ (levelV(hs, ha, ω, Λ))ᗮ)) :
    hilbertTrace (nuclearCompress (fullB(hs, ha, ω, Λ)).starProjection T) =
      hilbertTrace (nuclearCompress (levelV(hs, ha, ω, Λ)).starProjection T) +
        ∑ i, ⟪(e i : LocalW), T.val (e i)⟫_ℂ :=
  hilbertTrace_nuclearCompress_eq T _ _ (sLocalPWSobolev_polarComplement hs ha ω Λ).1 e

/-! ### A nontrivial norm-one character: the polar complement is zero -/

/-- The S-adelic Fourier transform of a unit translate of a test is a nonnegative multiple of the
dilate of its Fourier transform by the same unit. The proof repeats a private lemma of
`Ch07_SchauderBasesZeta/Sec3b`, with the Haar properties of the private `sAdele_fourierMeasure`
of `Ch03_IdelicZeta/Sec3`. -/
theorem levelPolar_translate_fourier (u : (SAdeleRing F S)ˣ) :
    ∃ b : ℝ≥0, ∀ (f : ℬₛ) (y : SAdeleRing F S),
      sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u f) (Multiplicative.ofAdd y) =
        ((b : ℝ) : ℂ) * sAdeleSchwartzFourier f (Multiplicative.ofAdd ((u : SAdeleRing F S) * y)) := by
  let A := SAdeleRing F S
  let G := Multiplicative A
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace A :=
    inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let μ : Measure G := sAdditiveTamagawaMeasure F S
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace A)
  let : T2Space A := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space G := ‹T2Space A›
  let : SigmaCompactSpace A := inferInstanceAs (SigmaCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace A := inferInstanceAs (BorelSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace G := ‹BorelSpace A›
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let hμ : (sAdditiveTamagawaMeasure F S).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.map_add_left_eq_self x.toAdd }
  let : μ.Regular := addHaar_regular_of_sigmaCompactSpace (sAdditiveTamagawaMeasure F S)
  let d : G ≃ₜ* G :=
    { toFun := fun x ↦ Multiplicative.ofAdd ((↑u⁻¹ : A) * x.toAdd)
      invFun := fun x ↦ Multiplicative.ofAdd ((u : A) * x.toAdd)
      left_inv := fun x ↦ Multiplicative.ext (by simp [← mul_assoc])
      right_inv := fun x ↦ Multiplicative.ext (by simp [← mul_assoc])
      map_mul' := fun x y ↦ Multiplicative.ext (mul_add _ _ _)
      continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
      continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
  let ν := μ.map d
  let : ν.IsHaarMeasure := d.isHaarMeasure_map μ
  let : ν.Regular := Measure.Regular.map d.toHomeomorph
  refine ⟨ν.haarScalarFactor μ, fun f y ↦ ?_⟩
  let k : G → ℂ := fun x ↦
    f x * star ((sAdeleStandardCharacter F S (x.toAdd * ((u : A) * y)) : Circle) : ℂ)
  have h1 : (∫ x : G, k (d.toHomeomorph.toMeasurableEquiv x) ∂μ) =
      ((ν.haarScalarFactor μ : ℝ) : ℂ) * ∫ x : G, k x ∂μ := by
    rw [← integral_map_equiv d.toHomeomorph.toMeasurableEquiv k]
    change (∫ x : G, k x ∂ν) = _
    calc
      _ = ∫ x : G, k x ∂(ν.haarScalarFactor μ • μ) :=
        congrArg (fun m : Measure G ↦ ∫ x : G, k x ∂m)
          (Measure.isMulLeftInvariant_eq_smul_of_regular ν μ)
      _ = _ := by
        rw [integral_smul_nnreal_measure]
        rfl
  refine Eq.trans ?_ h1
  change (∫ x : A, f (Multiplicative.ofAdd ((↑u⁻¹ : A) * x)) *
    star ((sAdeleStandardCharacter F S (x * y) : Circle) : ℂ) ∂(sAdditiveTamagawaMeasure F S)) =
    ∫ x : A, f (Multiplicative.ofAdd ((↑u⁻¹ : A) * x)) *
      star ((sAdeleStandardCharacter F S (((↑u⁻¹ : A) * x) * ((u : A) * y)) : Circle) : ℂ)
      ∂(sAdditiveTamagawaMeasure F S)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  change _ * star ((sAdeleStandardCharacter F S (x * y) : Circle) : ℂ) =
    _ * star ((sAdeleStandardCharacter F S (((↑u⁻¹ : A) * x) * ((u : A) * y)) : Circle) : ℂ)
  rw [mul_mul_mul_comm, Units.inv_mul, one_mul]

/-- A function that is a multiple of another composed with a homeomorphism has compact support,
contained in the preimage of the support of the other. -/
theorem levelPolar_translate_support {G : Type*} [TopologicalSpace G]
    (e : G ≃ₜ G) (b : ℂ) (φ ψ : G → ℂ) (hψ : ∀ x, ψ x = b * φ (e x)) (s t : Set G)
    (hs : e ⁻¹' s ⊆ t) (hc : HasCompactSupport φ) (hφ : tsupport φ ⊆ s) :
    HasCompactSupport ψ ∧ tsupport ψ ⊆ t := by
  have hsub : tsupport ψ ⊆ e ⁻¹' tsupport φ := by
    refine closure_minimal (fun x hx ↦ ?_) ((isClosed_tsupport φ).preimage e.continuous)
    refine subset_tsupport φ ?_
    intro h0
    exact hx ((hψ x).trans (by rw [h0, mul_zero]))
  have hcomp : IsCompact (e ⁻¹' tsupport φ) := e.isCompact_preimage.mpr hc
  exact ⟨hcomp.of_isClosed_subset (isClosed_tsupport ψ) hsub,
    hsub.trans ((Set.preimage_mono hφ).trans hs)⟩

/-- The transition of tests from a stage to itself is the identity. -/
theorem levelPolar_transition_self (f : ℬₛ) :
    sAdeleSchwartzTransition F (le_rfl (a := S)) f = f := by
  classical
  apply Subtype.ext
  funext x
  rw [← show Multiplicative.ofAdd x.toAdd = x from rfl, sAdeleSchwartzTransition_apply,
    ite_eq_left (fun w hw ↦ (hw w.property).elim)]

/-- The product of the normalized local absolute values of an S-adele. -/
def levelPolarProduct (x : SAdeleRing F S) : ℝ :=
  (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * ∏ v : S, ‖x.2 v‖

theorem levelPolarProduct_unit (a : (SAdeleRing F S)ˣ) :
    levelPolarProduct a.val = ((sIdeleNorm F S a).val : ℝ) := by
  let evaluate : ((SAdeleRing F S)ˣ →* ℝ≥0ˣ) →* ℝ :=
    NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp (MonoidHom.eval a))
  change levelPolarProduct a.val = evaluate (sIdeleNorm F S)
  simp only [sIdeleNorm, map_mul, map_prod, map_pow]
  rfl

theorem levelPolarProduct_mul (x y : SAdeleRing F S) :
    levelPolarProduct (x * y) = levelPolarProduct x * levelPolarProduct y := by
  unfold levelPolarProduct
  change (∏ w : InfinitePlace F, ‖x.1 w * y.1 w‖ ^ w.mult) *
    (∏ v : S, ‖x.2 v * y.2 v‖) = _
  simp only [norm_mul, mul_pow, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

/-- Paper: Definition 7.3.2.3(1), p. 355. Multiplication by an S-idele of norm one preserves the
product region. -/
theorem unit_mul_mem_sLocalPWProductRegion {u : (SAdeleRing F S)ˣ} (hu : sIdeleNorm F S u = 1)
    (Λ : ℝ) (y : SAdeleRing F S) :
    (u : SAdeleRing F S) * y ∈ sLocalPWProductRegion S Λ ↔ y ∈ sLocalPWProductRegion S Λ := by
  change levelPolarProduct ((u : SAdeleRing F S) * y) ≤ Λ ↔ levelPolarProduct y ≤ Λ
  rw [levelPolarProduct_mul, levelPolarProduct_unit, hu, Units.val_one, NNReal.coe_one, one_mul]

/-- Paper: Proposition 7.3.2.4(3), p. 356, for norm-one translates of tests.
Translation by an S-idele of norm one preserves the tests of the product region. -/
theorem unitTranslate_mem_sLocalPWTests {u : (SAdeleRing F S)ˣ} (hu : sIdeleNorm F S u = 1)
    {Λ : ℝ} {f : ℬₛ} (hf : f ∈ tests(Λ)) : schwartzBruhatUnitTranslate u f ∈ tests(Λ) := by
  obtain ⟨h, hh, hband⟩ := (mem_sLocalPWTests le_rfl _ f).mp hf
  rw [levelPolar_transition_self] at hh
  subst hh
  refine (mem_sLocalPWTests le_rfl _ _).mpr
    ⟨schwartzBruhatUnitTranslate u h, levelPolar_transition_self _, ?_⟩
  obtain ⟨b, hb⟩ := levelPolar_translate_fourier u
  let e : Multiplicative (SAdeleRing F S) ≃ₜ Multiplicative (SAdeleRing F S) :=
    { toFun := fun y ↦ Multiplicative.ofAdd ((u : SAdeleRing F S) * y.toAdd)
      invFun := fun y ↦ Multiplicative.ofAdd ((↑u⁻¹ : SAdeleRing F S) * y.toAdd)
      left_inv := fun y ↦ Multiplicative.ext (by simp [← mul_assoc])
      right_inv := fun y ↦ Multiplicative.ext (by simp [← mul_assoc])
      continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
      continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
  exact levelPolar_translate_support e ((b : ℝ) : ℂ) (sAdeleSchwartzFourier h).val
    (sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u h)).val (fun y ↦ hb h y.toAdd)
    (Multiplicative.toAdd ⁻¹' sLocalPWProductRegion S Λ)
    (Multiplicative.toAdd ⁻¹' sLocalPWProductRegion S Λ)
    (fun y hy ↦ (unit_mul_mem_sLocalPWProductRegion hu Λ y.toAdd).mp hy) hband.1 hband.2

/-- Two tests with the same homogeneous theta function have the same full theta class. -/
theorem sLocalFullPWThetaSobolevMap_congr {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁)
    {f g : ℬₛ} (h : sLocalHomogeneousAdelicThetaLinearMap F S ω f =
      sLocalHomogeneousAdelicThetaLinearMap F S ω g) :
    sLocalFullPWThetaSobolevMap (s := s) ha ω f = sLocalFullPWThetaSobolevMap (s := s) ha ω g := by
  simp only [sLocalFullPWThetaSobolevMap, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.toLp_congr _ _ (.of_forall fun x ↦ by rw [h])

/-- Paper: Equation (7.3.3.25), p. 363, and Definition 11.2.1.3(1), p. 488.
Reconstruction: for a nontrivial norm-one character `ω`, every test of the product region has
the same homogeneous theta function as a polar-free test of the same region. So the full band is
the polar-free level, and the polar complement is zero. This is the band-limited form of
`sLocalZeroMomentTheta_eq_top`: a norm-one translate preserves the region and the value at zero,
multiplies the Fourier value at zero by a nonnegative constant and the theta function by
`ω h ≠ 1`, and two differences remove both moments. -/
theorem sLocalFullPWSobolev_eq_of_ne_one (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a)
    (ω : PontryaginDual J₁) (hω : ω ≠ 1) (Λ : ℝ) :
    fullB(hs, ha, ω, Λ) = levelV(hs, ha, ω, Λ) := by
  refine le_antisymm ?_ (sLocalPWSobolev_polarComplement hs ha ω Λ).1
  rw [sLocalInvariantPWSobolev_eq_closure_map hs ha ω Λ]
  refine Submodule.topologicalClosure_mono ?_
  have hex : ∃ h : J₁, (ω h : ℂ) ≠ 1 :=
    not_forall.mp fun hall ↦ hω (PontryaginDual.ext fun x ↦ Subtype.ext (hall x))
  obtain ⟨h, hh⟩ := hex
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective h.val
  have hnorm : sIdeleNorm F S u = 1 := by
    have h1 : sIdeleQuotientNorm F S (QuotientGroup.mk u) = 1 := by
      rw [hu]
      exact MonoidHom.mem_ker.mp h.2
    exact h1
  obtain ⟨b, hb⟩ := levelPolar_translate_fourier u
  have hne : (ω h : ℂ) ≠ ((b : ℝ) : ℂ) := by
    intro he
    have hb1 : (b : ℝ) = 1 :=
      (Real.norm_of_nonneg b.property).symm.trans
        ((Complex.norm_real _).symm.trans ((congrArg norm he).symm.trans (Circle.norm_coe _)))
    exact hh (he.trans (by exact_mod_cast hb1))
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S ω
  let p := sAdelePolarValuesMap (F := F) (S := S)
  let t := schwartzBruhatUnitTranslate u
  have hp : ∀ f, p (t f) = ((p f).1, ((b : ℝ) : ℂ) * (p f).2) := by
    intro f
    apply Prod.ext
    · exact congrArg f (congrArg Multiplicative.ofAdd (mul_zero _))
    · change sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u f) (Multiplicative.ofAdd 0) = _
      rw [hb f 0, mul_zero]
      rfl
  have hθ : ∀ f, θ (t f) = (ω h : ℂ) • θ f := fun f ↦
    sLocalHomogeneousTheta_unitTranslate ω h u hu f
  have ht : ∀ f ∈ tests(Λ), t f ∈ tests(Λ) := fun f hf ↦ unitTranslate_mem_sLocalPWTests hnorm hf
  rintro _ ⟨f, hf, rfl⟩
  let aa : ℂ := ω h
  let bb : ℂ := ((b : ℝ) : ℂ)
  let k := t f - f
  let g := t k - bb • k
  let c := (aa - bb) * (aa - 1)
  have hc : c ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hne) (sub_ne_zero.mpr hh)
  have hk : k ∈ tests(Λ) := Submodule.sub_mem _ (ht f hf) hf
  have hg : g ∈ tests(Λ) := Submodule.sub_mem _ (ht k hk) (Submodule.smul_mem _ _ hk)
  have hk1 : (p k).1 = 0 := by simp [k, hp]
  have hgp : p g = 0 := by
    change p (t k - bb • k) = 0
    rw [map_sub, map_smul, hp, sub_eq_zero]
    exact Prod.ext (by simp [hk1]) (by simp [bb])
  have hθk : θ k = (aa - 1) • θ f := by simp [k, hθ, sub_smul, aa]
  have hθg : θ g = c • θ f := by
    change θ (t k - bb • k) = _
    rw [map_sub, map_smul, hθ, ← sub_smul, hθk, smul_smul]
  refine ⟨c⁻¹ • g, ⟨Submodule.smul_mem _ _ hg, ?_⟩, ?_⟩
  · change p (c⁻¹ • g) = 0
    rw [map_smul, hgp, smul_zero]
  · refine sLocalFullPWThetaSobolevMap_congr ha ω ?_
    change θ (c⁻¹ • g) = θ f
    rw [map_smul, hθg, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Levels

section Assembly

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))} {s : ℝ}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b

local notation "mₛ(" S ")" =>
  (continuousSIdeleQuotientNorm F S : SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "logNorm(" m ")" => (fun g ↦ Real.log (((m) g).val : ℝ))
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "localWMeasure" => (sLocalQuotientTamagawaMeasure F S).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm(mₛ(S)) g)))
local notation "LocalW" => Lp ℂ 2 localWMeasure
local notation "fullB(" hs ", " ha ", " ω ", " Λ ")" =>
  sLocalFullPWSobolev (F := F) (S := S) hs ha ω Λ
local notation "levelV(" hs ", " ha ", " ω ", " Λ ")" =>
  sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω Λ

attribute [local instance] completeSpace_sLocalFullPWSobolev
  completeSpace_sLocalInvariantPWSobolev hasOrthogonalProjection_polarComplement

local instance instSIdeleT2LevelPolar : T2Space (SAdeleRing F S)ˣ :=
  (sIdeleGroup_description F S).2.1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Hₛ" => sProjectedDiagonal F S
local notation "classAtS(" g ")" => (QuotientGroup.mk (sIdeleInsertion F S g) : C𝔽)
local notation "volume₁" => ((sLocalNormOneQuotientMeasure F S) univ).toReal
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : S) → BruhatCompactSupport (v.val.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "principalValues(" a "," b ")" =>
  ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑ v : S, ((Real.log (v.val.asIdeal.absNorm : ℝ) / finiteVolume(v.val) : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v.val 1 (b v))

/-- Paper: Theorem 12.4.1.1, p. 514, with Step III, p. 517, for every number field.
Reconstruction: take cutoff operators `T p` on the local Sobolev space. Suppose that, compressed
to the full band, their traces agree with the summed sharp orbital masses at radius `p.1 p.2`
up to `o(1)` (`hFull`), and that their diagonal entries on an orthonormal basis `e` of the polar
complement converge to those of an operator `A` (`hDiag`). Then, compressed to the polar-free
level, the traces less `volume₁ φ(1) log (p.1 p.2)` tend to `volume₁` times the sum of the local
principal values minus the polar term `∑ ⟪e i, A (e i)⟫`. This is the conclusion of
Theorem 12.4.1.1 with the polar term subtracted.
Deviation: The comparison on the full band is a hypothesis. The bandwidth `Λ` is fixed. -/
theorem sLocalLevel_trace_asymptotic_of_full_comparison
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)))
    (hRamified : ∀ v : HeightOneSpectrum (𝓞 F), differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ ↥(fullB(hs, ha, ω, Λ) ⊓ (levelV(hs, ha, ω, Λ))ᗮ))
    (T : ℝ × ℝ → nuclearEndomorphisms LocalW) (A : LocalW →L[ℂ] LocalW) (M : ℝ → ℂ)
    (hSum : ∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (M R))
    (hFull : Tendsto (fun p : ℝ × ℝ ↦
        hilbertTrace (nuclearCompress (fullB(hs, ha, ω, Λ)).starProjection (T p)) -
          M (p.1 * p.2)) (atTop ×ˢ atTop) (𝓝 0))
    (hDiag : ∀ i, Tendsto (fun p ↦ ⟪(e i : LocalW), (T p).val (e i)⟫_ℂ) (atTop ×ˢ atTop)
      (𝓝 ⟪(e i : LocalW), A (e i)⟫_ℂ)) :
    ∃ (pa : archTest) (pb : finiteTest),
      (∀ (w : InfinitePlace F) (x : w.Completionˣ), (pa w).val x = φ.val (archClass(w) x)) ∧
      (∀ (v : S) (x : (v.val.adicCompletion F)ˣ), (pb v).val x = φ.val (finiteClass(v.val) x)) ∧
      Tendsto (fun p : ℝ × ℝ ↦
          hilbertTrace (nuclearCompress (levelV(hs, ha, ω, Λ)).starProjection (T p)) -
            (volume₁ : ℂ) * φ.val 1 * (Real.log (p.1 * p.2) : ℂ)) (atTop ×ˢ atTop)
        (𝓝 ((volume₁ : ℂ) * principalValues(pa, pb) - ∑ i, ⟪(e i : LocalW), A (e i)⟫_ℂ)) := by
  have hsharp := sLocalTraceSharpMass_asymptotic (F := F) (S := S)
    φ hPic hRamified hOutside f hLift
  obtain ⟨pa, pb, N, hpa, hpb, hsumN, hN⟩ := hsharp
  refine ⟨pa, pb, hpa, hpb, ?_⟩
  have heq : N =ᶠ[atTop] M := by
    filter_upwards [hsumN, hSum] with R h₁ h₂ using h₁.unique h₂
  have hM : Tendsto (fun R ↦ M R - (volume₁ : ℂ) * φ.val 1 * (Real.log R : ℂ))
      atTop (𝓝 ((volume₁ : ℂ) * principalValues(pa, pb))) :=
    hN.congr' (heq.mono fun R h ↦ by simp only [h])
  have hp : Tendsto (fun p : ℝ × ℝ ↦ p.1 * p.2) (atTop ×ˢ atTop) atTop :=
    tendsto_fst.atTop_mul_atTop₀ tendsto_snd
  have hlev := tendsto_hilbertTrace_nuclearCompress_sub T _ _
    (sLocalPWSobolev_polarComplement hs ha ω Λ).1 e A (fun p ↦ M (p.1 * p.2)) hFull hDiag
  have h := hlev.add (hM.comp hp)
  rw [neg_add_eq_sub] at h
  refine h.congr fun p ↦ ?_
  simp only [Function.comp_apply]
  ring

/-- Paper: Theorem 12.4.1.1, Step III, p. 517, for every number field.
Reconstruction: under the hypotheses `hFull` and `hDiag` of
`sLocalLevel_trace_asymptotic_of_full_comparison`, if the polar term is not zero, the traces
compressed to the polar-free level do not agree with the summed sharp masses up to `o(1)`. So the
comparison of Step III, as printed, holds on the level only when the polar term vanishes. -/
theorem sLocalLevel_comparison_not_tendsto_zero (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a)
    (ω : PontryaginDual J₁) (Λ : ℝ) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ ↥(fullB(hs, ha, ω, Λ) ⊓ (levelV(hs, ha, ω, Λ))ᗮ))
    (T : ℝ × ℝ → nuclearEndomorphisms LocalW) (A : LocalW →L[ℂ] LocalW) (M : ℝ → ℂ)
    (hFull : Tendsto (fun p : ℝ × ℝ ↦
        hilbertTrace (nuclearCompress (fullB(hs, ha, ω, Λ)).starProjection (T p)) -
          M (p.1 * p.2)) (atTop ×ˢ atTop) (𝓝 0))
    (hDiag : ∀ i, Tendsto (fun p ↦ ⟪(e i : LocalW), (T p).val (e i)⟫_ℂ) (atTop ×ˢ atTop)
      (𝓝 ⟪(e i : LocalW), A (e i)⟫_ℂ))
    (hpolar : ∑ i, ⟪(e i : LocalW), A (e i)⟫_ℂ ≠ 0) :
    ¬ Tendsto (fun p : ℝ × ℝ ↦
        hilbertTrace (nuclearCompress (levelV(hs, ha, ω, Λ)).starProjection (T p)) -
          M (p.1 * p.2)) (atTop ×ˢ atTop) (𝓝 0) := by
  intro h0
  have hlev := tendsto_hilbertTrace_nuclearCompress_sub T _ _
    (sLocalPWSobolev_polarComplement hs ha ω Λ).1 e A (fun p ↦ M (p.1 * p.2)) hFull hDiag
  exact hpolar (neg_eq_zero.mp (tendsto_nhds_unique hlev h0))

/-- Paper: Theorem 12.4.1.1, p. 514, with Step III, p. 517, for every number field and a
nontrivial norm-one character.
Reconstruction: for `ω ≠ 1` the polar complement is zero (`sLocalFullPWSobolev_eq_of_ne_one`).
So if the traces compressed to the full band agree with the summed sharp masses up to `o(1)`,
the traces compressed to the polar-free level satisfy the conclusion of Theorem 12.4.1.1 as
printed, with no polar term.
Deviation: The comparison on the full band is a hypothesis. The bandwidth `Λ` is fixed. -/
theorem sLocalLevel_trace_asymptotic_of_ne_one
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)))
    (hRamified : ∀ v : HeightOneSpectrum (𝓞 F), differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (hω : ω ≠ 1) (Λ : ℝ)
    (T : ℝ × ℝ → nuclearEndomorphisms LocalW) (M : ℝ → ℂ)
    (hSum : ∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (M R))
    (hFull : Tendsto (fun p : ℝ × ℝ ↦
        hilbertTrace (nuclearCompress (fullB(hs, ha, ω, Λ)).starProjection (T p)) -
          M (p.1 * p.2)) (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ (pa : archTest) (pb : finiteTest),
      (∀ (w : InfinitePlace F) (x : w.Completionˣ), (pa w).val x = φ.val (archClass(w) x)) ∧
      (∀ (v : S) (x : (v.val.adicCompletion F)ˣ), (pb v).val x = φ.val (finiteClass(v.val) x)) ∧
      Tendsto (fun p : ℝ × ℝ ↦
          hilbertTrace (nuclearCompress (levelV(hs, ha, ω, Λ)).starProjection (T p)) -
            (volume₁ : ℂ) * φ.val 1 * (Real.log (p.1 * p.2) : ℂ)) (atTop ×ˢ atTop)
        (𝓝 ((volume₁ : ℂ) * principalValues(pa, pb))) := by
  have := (sLocalPWSobolev_polarComplement hs ha ω Λ).2.2.1
  let e := stdOrthonormalBasis ℂ ↥(fullB(hs, ha, ω, Λ) ⊓ (levelV(hs, ha, ω, Λ))ᗮ)
  have key : ∀ x : LocalW, x ∈ fullB(hs, ha, ω, Λ) → x ∈ (levelV(hs, ha, ω, Λ))ᗮ → x = 0 := by
    intro x h1 h2
    rw [sLocalFullPWSobolev_eq_of_ne_one hs ha ω hω Λ] at h1
    exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal h1 h2)
  have hz : ∀ i, (e i : LocalW) = 0 := fun i ↦ key _ (e i).2.1 (e i).2.2
  have hmain := sLocalLevel_trace_asymptotic_of_full_comparison φ hPic hRamified hOutside f hLift
    hs ha ω Λ e T 0 M hSum hFull (fun i ↦ by
      simp only [hz i, inner_zero_left]
      exact tendsto_const_nhds)
  obtain ⟨pa, pb, hpa, hpb, h⟩ := hmain
  refine ⟨pa, pb, hpa, hpb, ?_⟩
  have hsum0 : ∑ i, ⟪(e i : LocalW), (0 : LocalW →L[ℂ] LocalW) (e i)⟫_ℂ = 0 := by simp
  rwa [hsum0, sub_zero] at h

end Assembly

end RiemannMasullo.Isolated
