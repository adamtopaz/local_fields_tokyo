import Mathlib

-- Let K be a complete valued field.
variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsTopologicalDivisionRing K]
  [CompleteSpace K] [ValuativeTopology K]
  [ValuativeRel.IsNontrivial K]

open Topology in
theorem IsTopologicalAddGroup.locallyCompactSpace_of_nhds_zero
  (M : Type*) [AddCommGroup M] [TopologicalSpace M]
  [IsTopologicalAddGroup M]
  (h : ∀ u ∈ 𝓝 (0 : M), ∃ c ∈ 𝓝 (0 : M), c ⊆ u ∧ IsCompact c) :
  LocallyCompactSpace M := sorry

-- Condition 1: K is locally compact
def cond1 : Prop := LocallyCompactSpace K

-- Condition 2: The valuation subring is compact
def cond2 : Prop := IsCompact ((ValuativeRel.valuation K).valuationSubring : Set K)

-- Condition 3: K has discrete valuation, rank ≤ 1, is nontrivial, and has finite residue field
def cond3 : Prop :=
  (ValuativeRel.IsDiscrete K) ∧
  (ValuativeRel.IsRankLeOne K) ∧
  (ValuativeRel.IsNontrivial K) ∧
  Finite (IsLocalRing.ResidueField <|
    ValuativeRel.valuation K |>.valuationSubring)

-- cond1 → cond2
lemma locally_compact_implies_compact_valuation_subring :
    cond1 K → cond2 K := by
  sorry

open Topology Pointwise in
-- cond2 → cond1
lemma compact_valuation_subring_implies_locally_compact :
    cond2 K → cond1 K := by
  intro h
  let v := ValuativeRel.valuation K
  let Γ := ValuativeRel.ValueGroupWithZero K
  have h : IsCompact { x : K | v x ≤ 1 } := h
  dsimp [cond2, cond1] at h ⊢
  apply IsTopologicalAddGroup.locallyCompactSpace_of_nhds_zero
  intro U hU
  rw [ValuativeTopology.mem_nhds_iff] at hU
  obtain ⟨γ, hγ⟩ := hU
  have hγ : {x | v x < γ} ⊆ U := hγ
  obtain ⟨δ, hδ1, hδ2⟩ : ∃ δ : Γ, 0 < δ ∧ δ < 1 := sorry
  obtain ⟨a, ha⟩ : ∃ a : K, v a = δ := sorry
  obtain ⟨b, hb⟩ : ∃ b : K, v b = γ := sorry
  let W : Set K := (a * b) • { x : K | v x ≤ 1 }
  have hW : W = { x : K | v x ≤ δ * γ } := sorry
  have hW' : W ⊆ U := by
    intro x hx
    apply hγ
    dsimp
    rw [hW] at hx
    dsimp at hx
    suffices δ * γ < γ by exact lt_of_le_of_lt hx this
    conv =>
      enter [2]
      rw [← one_mul γ]
    push_cast
    apply mul_lt_mul
    assumption
    exact Preorder.le_refl ↑γ
    exact Units.zero_lt γ
    exact zero_le_one' Γ
  have hW'' : IsCompact W := sorry
  use W
  refine ⟨?_, hW', hW''⟩
  rw [ValuativeTopology.mem_nhds_iff, hW]
  refine ⟨Units.mk0 (δ * γ) ?_, ?_⟩
  have : (γ : Γ) ≠ 0 := Units.ne_zero γ
  · sorry
  · intro x hx
    have : v x < δ * γ := hx
    show v x ≤ δ * γ
    sorry

-- cond2 → cond3
lemma compact_valuation_subring_implies_discrete_etc :
    cond2 K → cond3 K := by
  sorry

-- cond3 → cond1
lemma discrete_etc_implies_locally_compact :
    cond3 K → cond1 K := by
  sorry

theorem main_theorem : List.TFAE [
    cond1 K,
    cond2 K,
    cond3 K
    ] := by
  tfae_have 1 → 2 :=
    locally_compact_implies_compact_valuation_subring K
  tfae_have 2 → 3 :=
    compact_valuation_subring_implies_discrete_etc K
  tfae_have 3 → 1 :=
    discrete_etc_implies_locally_compact K
  tfae_finish
