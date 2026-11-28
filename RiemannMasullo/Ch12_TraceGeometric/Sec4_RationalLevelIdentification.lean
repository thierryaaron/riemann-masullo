module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalLevelPolarMellin

/-!
# Main's polar-free level for the rationals with no finite place

PLACEHOLDER
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set NumberField IsDedekindDomain
open scoped Topology NumberField ENNReal NNReal InnerProductSpace

namespace RiemannMasullo.Isolated

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

section QuotientMeasure

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "Hₛ" => sProjectedDiagonal F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S

open scoped Pointwise

attribute [-instance] Quotient.instMeasurableSpace

/-- Paper: (12.4.1.23), p. 518. The image in the S-idele quotient of multiplicative Tamagawa
measure restricted to an S-unit fundamental domain is the quotient Tamagawa measure. The same
statement as the private `sLocalTrace_fundamentalDomain_map` of `Sec4`, repeated so that `Sec4`
does not change. -/
theorem levelIdent_fundamentalDomain_map (D : Set Iₛ)
    (hD : IsFundamentalDomain Hₛ D μₛ) :
    ((μₛ).restrict D).map (QuotientGroup.mk : Iₛ → Jₛ) = μJ := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have : BorelSpace Jₛ := ⟨rfl⟩
  have : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  have : DiscreteTopology Hₛ := discreteTopology_sProjectedDiagonal
  have hcl : IsClosed (Hₛ : Set Iₛ) := isClosed_sProjectedDiagonal
  have : Countable Hₛ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let π : Iₛ → Jₛ := QuotientGroup.mk
  have hπ : Measurable π := Continuous.measurable (f := π) continuous_quotient_mk'
  let νD := ((μₛ).restrict D).map π
  -- The fundamental domain for the right action of the S-units.
  have hDop : IsFundamentalDomain (Subgroup.op (Hₛ)) D μₛ := by
    have h := hD.image_of_equiv (Equiv.refl Iₛ) (MeasureTheory.QuasiMeasurePreserving.id μₛ)
      (Subgroup.equivOp (Hₛ)).symm (fun g x ↦ ?_)
    · simpa using h
    · change ((g.1.unop : Iₛ)) * x = x * g.1.unop
      exact mul_comm _ _
  have : IsClosed (Hₛ : Set Iₛ) := hcl
  have : T2Space Iₛ := (sIdeleGroup_description F S).2.1
  have : T2Space Jₛ := inferInstance
  have : SecondCountableTopology Jₛ := inferInstance
  have : LocallyCompactSpace Jₛ := inferInstance
  -- Preimages of sets in the quotient are invariant under the S-units.
  have hinv (A : Set Jₛ) (g : Hₛ) : (fun x ↦ g • x) ⁻¹' (π ⁻¹' A) = π ⁻¹' A := by
    ext z
    change π ((g : Iₛ) * z) ∈ A ↔ π z ∈ A
    rw [show π ((g : Iₛ) * z) = π z from QuotientGroup.eq.mpr (by
      rw [mul_inv_rev, mul_assoc, mul_left_comm, inv_mul_cancel, mul_one]
      exact inv_mem g.2)]
  -- The image of a compact set has at most its mass.
  have hle (W : Set Iₛ) (hW : IsCompact W) : νD (π '' W) ≤ μₛ W := by
    have hm : MeasurableSet (π '' W) :=
      (IsCompact.image (f := π) hW continuous_quotient_mk').isClosed.measurableSet
    rw [Measure.map_apply hπ hm, Measure.restrict_apply (hπ hm),
      QuotientGroup.preimage_image_mk, iUnion_inter]
    refine (measure_iUnion_le _).trans (le_of_eq ?_)
    rw [hD.measure_eq_tsum W, ← (Equiv.inv Hₛ).tsum_eq]
    congr 1
    funext ξ
    congr 2
    ext y
    simp only [mem_preimage, Equiv.inv_apply, Set.mem_smul_set_iff_inv_smul_mem,
      Subgroup.coe_inv, Subgroup.smul_def, smul_eq_mul]
    rw [mul_comm]
  have hlocfin : IsLocallyFiniteMeasure νD := ⟨fun q ↦ by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨W, hWc, hWn⟩ := exists_compact_mem_nhds x
    exact ⟨π '' W, QuotientGroup.isOpenMap_coe.image_mem_nhds hWn,
      (hle W hWc).trans_lt hWc.measure_lt_top⟩⟩
  have hleft : νD.IsMulLeftInvariant := ⟨fun y ↦ by
    obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective y
    ext A hA
    have hA' : MeasurableSet ((fun z ↦ (QuotientGroup.mk x₁ : Jₛ) * z) ⁻¹' A) :=
      measurable_const_mul _ hA
    rw [Measure.map_apply (measurable_const_mul _) hA]
    simp only [νD, Measure.map_apply hπ hA', Measure.map_apply hπ hA,
      Measure.restrict_apply (hπ hA'), Measure.restrict_apply (hπ hA)]
    have hpre : π ⁻¹' ((fun z ↦ (QuotientGroup.mk x₁ : Jₛ) * z) ⁻¹' A) =
        (fun z ↦ x₁ * z) ⁻¹' (π ⁻¹' A) := rfl
    have hD1 : IsFundamentalDomain Hₛ (x₁ • D) μₛ := hD.smul_of_comm x₁
    rw [hpre]
    calc μₛ ((fun z ↦ x₁ * z) ⁻¹' (π ⁻¹' A) ∩ D)
        = μₛ ((fun z ↦ x₁ * z) ⁻¹' (π ⁻¹' A ∩ x₁ • D)) := by
          congr 1
          ext z
          simp only [mem_inter_iff, mem_preimage]
          rw [show x₁ * z = x₁ • z from rfl, smul_mem_smul_set_iff]
      _ = μₛ (π ⁻¹' A ∩ x₁ • D) := measure_preimage_mul μₛ x₁ _
      _ = μₛ (π ⁻¹' A ∩ D) := (hD.measure_set_eq hD1 (hπ hA) (hinv A)).symm⟩
  have hopen : νD.IsOpenPosMeasure := ⟨fun U hU hne h0 ↦ by
    rw [Measure.map_apply hπ hU.measurableSet, Measure.restrict_apply (hπ hU.measurableSet)] at h0
    have h1 := hD.measure_zero_of_invariant _ (fun g ↦ by
      rw [← Set.preimage_smul_inv]; exact hinv U g⁻¹) h0
    exact (hU.preimage continuous_quotient_mk').measure_ne_zero μₛ (hne.preimage
      QuotientGroup.mk_surjective) h1⟩
  have hhaar : νD.IsHaarMeasure := { }
  have hreg : νD.Regular := by
    obtain ⟨W, hWc, hWn⟩ := exists_compact_mem_nhds (1 : Iₛ)
    exact Measure.regular_of_isMulLeftInvariant (IsCompact.image (f := π) hWc continuous_quotient_mk')
      ⟨π 1, mem_interior_iff_mem_nhds.mpr (QuotientGroup.isOpenMap_coe.image_mem_nhds hWn)⟩
      ((hle W hWc).trans_lt hWc.measure_lt_top).ne
  have hweil : ∀ f : C(Iₛ, ℂ), HasCompactSupport f →
      (∫ x, f x ∂μₛ) = ∫ q, lcaCosetIntegral Hₛ Measure.count f q ∂νD := by
    intro f hf
    have : (Measure.count : Measure Hₛ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
    have : (μₛ).IsMulRightInvariant := ⟨fun g ↦ by
      rw [show (fun x : Iₛ ↦ x * g) = fun x ↦ g * x from funext fun x ↦ mul_comm x g]
      exact map_mul_left_eq_self μₛ g⟩
    have : Countable (Subgroup.op (Hₛ)) := Countable.of_equiv _ (Subgroup.equivOp (Hₛ))
    -- Near any point only finitely many S-units move it into the support of f.
    have hfin (W : Set Iₛ) (hW : IsCompact W) :
        {γ : Hₛ | (γ : Iₛ) ∈ W⁻¹ * tsupport f}.Finite :=
      (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (hW.inv.mul hf)).finite_of_discrete
    have hzero (W : Set Iₛ) (y : Iₛ) (hy : y ∈ W) (γ : Hₛ)
        (hγ : γ ∉ {γ : Hₛ | (γ : Iₛ) ∈ W⁻¹ * tsupport f}) : f (y * γ) = 0 := by
      by_contra h
      refine hγ ⟨y⁻¹, inv_mem_inv.mpr hy, y * γ, subset_tsupport f h, ?_⟩
      simp
    have hsum (x : Iₛ) : (∑' γ : Hₛ, f (x * γ)) = ∑ γ ∈ (hfin {x} isCompact_singleton).toFinset,
        f (x * γ) :=
      tsum_eq_sum fun γ hγ ↦ hzero {x} x rfl γ (by simpa using hγ)
    have hcont : Continuous fun x : Iₛ ↦ ∑' γ : Hₛ, f (x * γ) := by
      refine continuous_iff_continuousAt.mpr fun x ↦ ?_
      obtain ⟨W, hWc, hWn⟩ := exists_compact_mem_nhds x
      have heq : (fun y : Iₛ ↦ ∑ γ ∈ (hfin W hWc).toFinset, f (y * γ)) =ᶠ[𝓝 x]
          fun y ↦ ∑' γ : Hₛ, f (y * γ) :=
        Filter.mem_of_superset hWn fun y hy ↦
          (tsum_eq_sum fun γ hγ ↦ hzero W y hy γ (by simpa using hγ)).symm
      exact ((continuous_finsetSum _ fun γ _ ↦
        f.continuous.comp (continuous_id.mul continuous_const)).continuousAt).congr heq
    have hint (x : Iₛ) : Integrable (fun γ : Hₛ ↦ f (x * γ)) Measure.count :=
      integrable_count_iff.mpr (summable_of_ne_finset_zero (s := (hfin {x} isCompact_singleton).toFinset)
        fun γ hγ ↦ by rw [hzero {x} x rfl γ (by simpa using hγ), norm_zero])
    have hcoset (x : Iₛ) : lcaCosetIntegral Hₛ Measure.count f (π x) = ∑' γ : Hₛ, f (x * γ) := by
      rw [lcaCosetIntegral_mk Hₛ Measure.count (f : Iₛ → ℂ) x (hint x), integral_countable (hint x)]
      simp [Measure.real]
    have haut : QuotientGroup.automorphize (Γ := Hₛ) (f : Iₛ → ℂ) =
        lcaCosetIntegral Hₛ Measure.count f := by
      funext q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [hcoset x]
      change ∑' γ : Subgroup.op (Hₛ), f (γ • x) = _
      rw [← (Subgroup.equivOp (Hₛ)).tsum_eq]
      rfl
    have hautc : Continuous (QuotientGroup.automorphize (Γ := Hₛ) (f : Iₛ → ℂ)) := by
      rw [haut]
      refine (isQuotientMap_quotient_mk' (s := QuotientGroup.leftRel (Hₛ))).continuous_iff.mpr ?_
      change Continuous fun x ↦ lcaCosetIntegral Hₛ Measure.count f (π x)
      simp_rw [hcoset]
      exact hcont
    rw [QuotientGroup.integral_eq_integral_automorphize hDop
      (f.continuous.integrable_of_hasCompactSupport hf) hautc.aestronglyMeasurable, haut]
  exact (sLocalQuotientTamagawaMeasure_existsUnique (F := F) (S := S)).unique
    ⟨hhaar, hreg, hweil⟩ sLocalQuotientTamagawaMeasure_isWeil

end QuotientMeasure

section RatQuotient

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instMeasurableSpaceInfiniteAdeleRing_riemannMasullo
  instRatSIdeleT2 instRatSAdeleT2

attribute [-instance] Quotient.instMeasurableSpace

local notation "Sq" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "Iq" => (SAdeleRing ℚ Sq)ˣ
local notation "Jq" => SIdeleQuotient ℚ Sq
local notation "eq" => ratRealCoordEquiv
local notation "μq" => sMultiplicativeTamagawaMeasure ℚ Sq
local notation "μJq" => sLocalQuotientTamagawaMeasure ℚ Sq

/-- The S-ideles of `ℚ` with positive real coordinate form a measurable set. -/
theorem measurableSet_ratPos : MeasurableSet {x : Iq | 0 < eq x.val} := by
  have : BorelSpace (SAdeleRing ℚ Sq) := sAdeleRing_borelSpace
  have : BorelSpace Iq := sIdeleGroup_borelSpace
  exact measurableSet_lt measurable_const
    (measurable_ratRealCoordEquiv.comp Units.continuous_val.measurable)

/-- Reconstruction: for `ℚ` with no finite place, an integral over the S-idele quotient against
`main`'s quotient Tamagawa measure is the integral over the positive reals of the class of `t`
against `dt / t`. -/
theorem ratQuotient_integral (G : Jq → ℂ) (hG : AEStronglyMeasurable G μJq) :
    ∫ c, G c ∂μJq = ∫ t in Ioi 0, G (QuotientGroup.mk (ratUnit t)) / (t : ℂ) := by
  have : BorelSpace Iq := sIdeleGroup_borelSpace
  have : BorelSpace Jq := ⟨rfl⟩
  have hπ : Measurable (QuotientGroup.mk : Iq → Jq) :=
    Continuous.measurable (f := (QuotientGroup.mk : Iq → Jq)) continuous_quotient_mk'
  rw [← levelIdent_fundamentalDomain_map _ isFundamentalDomain_ratPos] at hG ⊢
  rw [integral_map hπ.aemeasurable hG, ← integral_indicator measurableSet_ratPos,
    ratIntegral_mul, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    have hmem : ratUnit t ∈ {x : Iq | 0 < eq x.val} := by
      change 0 < eq (ratUnit t).val
      rwa [ratUnit_val ht.ne', RingEquiv.apply_symm_apply]
    rw [ratLift_of_ne ht.ne', indicator_of_mem hmem, abs_of_pos ht]
  · intro t ht
    rcases eq_or_ne t 0 with rfl | h0
    · simp [ratLift_zero]
    · have hnot : ratUnit t ∉ {x : Iq | 0 < eq x.val} := by
        change ¬ 0 < eq (ratUnit t).val
        rw [ratUnit_val h0, RingEquiv.apply_symm_apply]
        exact ht
      rw [ratLift_of_ne h0, indicator_of_notMem hnot, zero_div]

/-- The S-units of `ℚ` with no finite place. -/
local notation "Uq" => ((Sq : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)ˣ
local notation "Bq" => SchwartzBruhat (Multiplicative (SAdeleRing ℚ Sq))
local notation "volume₁" => ((sLocalNormOneQuotientMeasure ℚ Sq) univ).toReal

/-- An S-unit of `ℚ` with no finite place is `1` or `-1`. -/
theorem ratSUnit_cases (u : Uq) : u = 1 ∨ u = -1 := by
  rcases integer_empty_unit u with h | h
  · exact Or.inl (Units.ext (Subtype.ext (by simpa using h)))
  · exact Or.inr (Units.ext (Subtype.ext (by simpa using h)))

/-- The S-unit `-1` of `ℚ` is not `1`. -/
theorem ratSUnit_neg_one_ne_one : (-1 : Uq) ≠ 1 := by
  intro h
  have h' := congrArg (fun u : Uq ↦ (u.val.val : ℚ)) h
  norm_num at h'

/-- The two S-units of `ℚ` with no finite place. -/
def ratSUnitEquiv : Bool ≃ Uq where
  toFun b := if b then 1 else -1
  invFun u := decide (u = 1)
  left_inv b := by cases b <;> simp
  right_inv u := by
    rcases ratSUnit_cases u with rfl | rfl <;> simp

/-- The S-unit embedding sends `-1` to `-1`. -/
theorem ratSUnitEmbedding_neg_one : (sUnitEmbedding ℚ Sq (-1 : Uq) : SAdeleRing ℚ Sq) = -1 := by
  simp [sUnitEmbedding]

/-- Reconstruction: for `ℚ` with no finite place, `main`'s S-local theta function is the sum of
the values at `g` and `-g`. -/
theorem ratTheta_apply (f : Bq) (g : Iq) :
    sLocalAdelicTheta ℚ Sq f g =
      f (Multiplicative.ofAdd g.val) + f (Multiplicative.ofAdd (-g.val)) := by
  rw [sLocalAdelicTheta_apply]
  dsimp only
  rw [← ratSUnitEquiv.tsum_eq, tsum_fintype, Fintype.sum_bool]
  simp only [ratSUnitEquiv, Equiv.coe_fn_mk, ite_true, Bool.false_eq_true, ite_false, map_one,
    one_mul]
  rw [Units.val_mul, ratSUnitEmbedding_neg_one, neg_one_mul]

/-- For `ℚ` with no finite place, a class of norm one is trivial. -/
theorem ratNormOne_eq_one (c : (sIdeleQuotientNorm ℚ Sq).ker) : c = 1 := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  have hn : sIdeleNorm ℚ Sq g = 1 := (sIdeleQuotientNorm_mk ℚ Sq g).symm.trans hc
  have habs : |eq g.val| = 1 := by
    have h := congrArg (fun t : ℝ≥0ˣ ↦ ((t : ℝ≥0) : ℝ)) hn
    simpa [ratNormq] using h
  have hmem : g ∈ sProjectedDiagonal ℚ Sq := by
    rw [mem_ratProjectedDiagonal_iff]
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact Subtype.ext ((QuotientGroup.eq_one_iff g).2 hmem)

instance : Unique (sIdeleQuotientNorm ℚ Sq).ker where
  default := 1
  uniq c := ratNormOne_eq_one c

/-- Reconstruction: for `ℚ` with no finite place the norm-one classes are trivial, so `main`'s
homogeneous theta function, for any character `ω` of them, is `volume₁` times the sum of the values
at `g` and `-g`. -/
theorem ratHomogeneousTheta_apply (ω : PontryaginDual (sIdeleQuotientNorm ℚ Sq).ker) (f : Bq)
    (g : Iq) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ Sq ω f (QuotientGroup.mk g) =
      (volume₁ : ℂ) * (f (Multiplicative.ofAdd g.val) + f (Multiplicative.ofAdd (-g.val))) := by
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply, integral_unique]
  have h1 : (default : (sIdeleQuotientNorm ℚ Sq).ker) = 1 := rfl
  simp only [h1, OneMemClass.coe_one, mul_one, map_one, Circle.coe_one]
  rw [sLocalAdelicThetaOnClasses_mk, ratTheta_apply, Complex.real_smul, measureReal_def]

end RatQuotient

end RiemannMasullo.Isolated
