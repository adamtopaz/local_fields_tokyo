import Mathlib

-- Let K be a complete valued field.
variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsTopologicalDivisionRing K]
  [CompleteSpace K] [ValuativeTopology K]


theorem main_theorem : List.TFAE [
    LocallyCompactSpace K,
    IsCompact ((ValuativeRel.valuation K).valuationSubring : Set K),
    (ValuativeRel.IsDiscrete K) ∧
    (ValuativeRel.IsRankLeOne K) ∧
    (ValuativeRel.IsNontrivial K) ∧
    Finite (IsLocalRing.ResidueField <|
      ValuativeRel.valuation K |>.valuationSubring)
    ] :=
  sorry
