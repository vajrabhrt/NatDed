import Mathlib
import NatDed.njNorm

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option maxHeartbeats 0

namespace normAlg

open Rank
open nj
open nj.propform
open nj.njprf
open nj.proofrule
open njNorm
open njNorm.isCut
open njNorm.isNormal
open njNorm.graft
open njNorm.contract
open njNorm.oneStep

def graftum {φ ψ} (ρ : njprf φ) (π: njprf ψ) : njprf ψ :=
  match h: π with
  | .ax α => if g: α = φ then (by subst_vars; exact ρ) else ax α
  | .emp α μ => emp α (graftum ρ μ)
  | .abs α β μ => abs α β (graftum ρ μ)
  | .app α β μ ν => app α β (graftum ρ μ) (graftum ρ ν)
  | .pair α β μ ν => pair α β (graftum ρ μ) (graftum ρ ν)
  | .fst α β μ =>  fst α β (graftum ρ μ)
  | .snd α β μ =>  snd α β (graftum ρ μ)
  | .left α β μ => left α β (graftum ρ μ)
  | .right α β μ => right α β (graftum ρ μ)
  | .case α β γ χ μ ν => case α β γ (graftum ρ χ) (graftum ρ μ) (graftum ρ ν)

lemma graft_graftum : ∀ ψ φ (ρ : njprf ψ) (π ϖ : njprf φ),
      graft ρ π ϖ ↔ ϖ = graftum ρ π := by
  intro ψ φ ρ π ϖ; constructor <;> intro A
  · induction A <;> simp [graftum] <;> try grind
  · subst_vars; induction π <;> simp [graftum] <;>
      try (constructor <;> try grind)
    · rename_i α; by_cases H : α = ψ
      · rw [H]; simp; constructor
      · simp [H]; constructor; grind

def contractum {φ} (π: njprf φ) : njprf φ :=
  match h: π with
  | .emp bot μ => μ
  | .app α β (.abs _ _ μ) ν => graftum ν μ
  | .fst α β (.pair _ _ μ _) => μ
  | .snd α β (.pair _ _ _ ν) => ν
  | .case α β _ (.left _ _ χ) μ ν => graftum χ μ
  | .case α β _ (.right _ _ χ) μ ν => graftum χ ν
  | .app α β (.emp _ μ) ν => emp β μ
  | .fst α β (.emp _ μ) => emp α μ
  | .snd α β (.emp _ μ) => emp β μ
  | .case α β δ (.emp _ χ) μ ν => emp δ χ
  | .app α β (.case σ τ _ χ1 χ2 χ3) μ => case σ τ β χ1
                                          (app _ _ χ2 μ) (app _ _ χ3 μ)
  | .fst α β (.case σ τ _ χ1 χ2 χ3) => case σ τ α χ1
                                          (fst _ _ χ2) (fst _ _ χ3)
  | .snd α β (.case σ τ _ χ1 χ2 χ3)=> case σ τ β χ1
                                          (snd _ _ χ2) (snd _ _ χ3)
  | .case α β δ (.case σ τ _ χ1 χ2 χ3) μ ν => case σ τ δ χ1
                                          (case _ _ _ χ2 μ ν)
                                          (case _ _ _ χ3 μ ν)
  | ϖ@_ => ϖ

lemma contract_contractum : ∀ φ (π: njprf φ), isCut π →
    contract π (contractum π) := by
  intro φ π A; cases A <;>
    simp [contractum] <;> try constructor
  all_goals rw [graft_graftum]

def stepOne {φ} (π : njprf φ) : njprf φ :=
  match π with
  | .ax α => ax α
  | .emp α μ => if maxDeg μ = maxDeg π
                then emp α (stepOne μ)
                else contractum (emp α μ)
  | .abs α β μ => abs α β (stepOne μ)
  | .app α β μ ν => if maxDeg ν = maxDeg π
                    then app α β μ (stepOne ν)
                    else if maxDeg μ = maxDeg π ∧
                            (degree π < maxDeg π ∨ lrof μ ≠ prcase)
                          then app α β (stepOne μ) ν
                          else contractum (app α β μ ν)
  | .pair α β μ ν => if maxDeg ν = maxDeg π
                      then pair α β μ (stepOne ν)
                      else pair α β (stepOne μ) ν
  | .fst α β μ => if maxDeg μ = maxDeg π ∧
                      (degree π < maxDeg π ∨ lrof μ ≠ prcase)
                  then fst α β (stepOne μ)
                  else contractum (fst α β μ)
  | .snd α β μ => if maxDeg μ = maxDeg π ∧
                      (degree π < maxDeg π ∨ lrof μ ≠ prcase)
                  then snd α β (stepOne μ)
                  else contractum (snd α β μ)
  | .left α β μ => left α β (stepOne μ)
  | .right α β μ => right α β (stepOne μ)
  | .case α β δ χ μ ν => if maxDeg ν = maxDeg π
                        then case α β δ χ μ (stepOne ν)
                        else if maxDeg μ = maxDeg π
                            then case α β δ χ (stepOne μ) ν
                            else if maxDeg χ = maxDeg π ∧
                                    (degree π < maxDeg π ∨
                                      lrof χ ≠ prcase)
                                then case α β δ (stepOne χ) μ ν
                                else contractum (case α β δ χ μ ν)

lemma oneStep_stepOne : ∀ φ (π : njprf φ),
  maxDeg π > 0 → oneStep φ π (stepOne π) := by
  intro φ π Hmd; fun_induction stepOne
  · -- ax
    rename_i α; simp [maxDeg, cutrank, degwt] at Hmd
  · -- empStep
    rename_i α μ A ihμ; simp [A]; apply oneStep.empStep
    rfl; grind; grind
  · -- empCrit
    rename_i α μ A;
    have B1 : maxDeg μ < maxDeg (emp α μ) := by
      apply empCritCondition; rfl; grind
    simp [A]; apply oneStep.empCrit
    rfl; apply contract_contractum;
    simp [maxDeg, cutrank, pairAdd_fst] at B1
    simp [degreeOfCut, degree]; grind
    assumption
  · -- absStep
    rename_i α β μ ihμ
    have B0 : maxDeg μ = maxDeg (abs α β μ) := by simp [maxDeg, cutrank]
    apply oneStep.absStep
    rfl; grind; grind
  · -- app2Step
    rename_i β α μ ν A ihν
    simp [A]; apply oneStep.app2Step
    rfl; grind; grind
  · -- app1Step
    rename_i β α μ ν A B ihμ
    simp [A, B]
    have A' : maxDeg ν < maxDeg (app α β μ ν) := by
      apply app1StepCondition; rfl; grind
    apply oneStep.app1Step
    rfl; grind; grind; grind; grind
  · -- appCrit
    rename_i β α μ ν A B
    simp [A,B]
    have A' : maxDeg ν < maxDeg (app α β μ ν) := by
      apply app1StepCondition; rfl; grind
    apply appCritCondition at A; apply A at B
    rcases B with ⟨B1, B2⟩
    rw [←B1] at Hmd; simp [←degreeOfCut] at Hmd
    apply oneStep.appCrit
    rfl; apply contract_contractum
    assumption; assumption; assumption; assumption; rfl
  · -- pair2Step
    rename_i α β μ ν A ihν
    simp [A]; apply oneStep.pair2Step
    rfl; grind; grind
  · -- pair1Step
    rename_i α β μ ν A ihμ
    simp [A]
    have B : maxDeg ν < maxDeg (pair α β μ ν) ∧
              maxDeg μ = maxDeg (pair α β μ ν):= by
      apply pair1StepCondition; rfl; grind
    rcases B with ⟨B1, B2⟩
    apply oneStep.pair1Step; rfl; assumption; assumption; grind
  · -- fstStep
    rename_i α β μ A ihμ
    simp [A]; apply oneStep.fstStep; rfl; grind; grind; grind
  · -- fstCrit
    rename_i α β μ A
    simp [A]
    apply fstCritCondition at A
    rcases A with ⟨A1, A2⟩
    rw [←A1] at Hmd; simp [←degreeOfCut] at Hmd
    apply oneStep.fstCrit
    rfl; apply contract_contractum
    assumption; assumption; assumption; rfl
  · -- sndStep
    rename_i α β μ A ihμ
    simp [A]; apply oneStep.sndStep; rfl; grind; grind; grind
  · -- sndCrit
    rename_i α β μ A
    simp [A]
    apply sndCritCondition at A
    rcases A with ⟨A1, A2⟩
    rw [←A1] at Hmd; simp [←degreeOfCut] at Hmd
    apply oneStep.sndCrit
    rfl; apply contract_contractum
    assumption; assumption; assumption; rfl
  · -- leftStep
    rename_i α β μ ihμ
    have B0 : maxDeg μ = maxDeg (left α β μ) := by simp [maxDeg, cutrank]
    apply oneStep.leftStep
    rfl; grind; grind
  · -- rightStep
    rename_i α β μ ihμ
    have B0 : maxDeg μ = maxDeg (right α β μ) := by simp [maxDeg, cutrank]
    apply oneStep.rightStep
    rfl; grind; grind
  · -- case3Step
    rename_i δ α β χ μ ν A ihν
    simp [A]; apply oneStep.case3Step
    rfl; grind; grind
  · -- case2Step
    rename_i δ α β χ μ ν A B ihμ
    simp [A,B]
    have A' : maxDeg ν < maxDeg (case α β δ χ μ ν) := by
      apply case2StepCondition; rfl; grind
    apply oneStep.case2Step; rfl; grind; grind; grind
  · -- case1Step
    rename_i δ α β χ μ ν A B C ihχ
    have A1 : maxDeg ν < maxDeg (case α β δ χ μ ν) ∧
              maxDeg μ < maxDeg (case α β δ χ μ ν) := by
      apply case1StepCondition; rfl; grind; grind
    simp [A,B,C]; apply oneStep.case1Step
    rfl; grind; grind; grind; grind; grind
  · -- caseCrit
    rename_i δ α β χ μ ν A B C
    have A1 : maxDeg ν < maxDeg (case α β δ χ μ ν) ∧
              maxDeg μ < maxDeg (case α β δ χ μ ν) := by
      apply case1StepCondition; rfl; grind; grind
    -- rcases A1 with ⟨A1, A2⟩
    simp [A,B,C]; apply caseCritCondition at A; apply A at B; apply B at C;
    rcases C with ⟨C1, C2⟩
    rw [←C1] at Hmd; simp [←degreeOfCut] at Hmd
    apply oneStep.caseCrit
    rfl; apply contract_contractum
    assumption; assumption; assumption; grind; grind; rfl

lemma stepOne_dec : ∀ φ (π : njprf φ), maxDeg π ≠ 0 →
  cutrank (stepOne π) < cutrank π := by
  intro φ π A
  have B : oneStep φ π (stepOne π) := by apply oneStep_stepOne; grind
  apply oneStepCutRank; assumption

def normalize {φ} (π : njprf φ) : njprf φ :=
  if maxDeg π = 0 then π else
    normalize (stepOne π)
    termination_by cutrank π
    decreasing_by apply stepOne_dec; assumption

theorem norm_normal : ∀ φ (π : njprf φ), isNormal (normalize π) := by
  intro φ π; fun_induction normalize
  · rename_i μ A;
    rw [normal_cutrank]; simp [maxDeg] at A;
    rcases cutrank_goodRank _ μ with B | B <;> try grind
    ext <;> grind
  · grind

theorem norm_concAss : ∀ φ (π : njprf φ),
  hypos (normalize π) ⊆ hypos π ∧ conc (normalize π) = conc π := by
  intro φ π; fun_induction normalize
  · grind
  · rename_i μ Hmd ih
    have B : oneStep φ μ (stepOne μ) := by apply oneStep_stepOne; grind
    have C : hypos (stepOne μ) ⊆ hypos μ ∧ conc (stepOne μ) = conc μ := by
        apply oneStepConcAss; exact B
    grind

-- Can we compute normal forms? Let us see!

def α : propform := letter 0
def β : propform := letter 1
def π : njprf (impl α (impl β α)) :=
  abs α _ (abs β _ (fst α β (pair α β (ax α) (ax β))))

#eval normalize π

def μ : njprf (impl α (impl β β)) :=
  abs α (impl β β)
    (abs β β
      (app α β  (
                  case α β (impl α β) (left α β (ax α)) (abs α β (ax β)) (abs α β (ax β))
                )
                (ax α)
      )
    )

#eval normalize μ

#eval stepOne μ
#eval stepOne (stepOne μ)
#eval stepOne (stepOne (stepOne μ))
#eval stepOne (stepOne (stepOne (stepOne μ)))
#eval cutrank μ
#eval cutrank (stepOne μ)
#eval cutrank (stepOne (stepOne μ))
#eval cutrank (stepOne (stepOne (stepOne μ)))
#eval cutrank (stepOne (stepOne (stepOne (stepOne μ))))

end normAlg

-- **** Interesting developments but not needed, since our measures:
-- degree, maxDeg, degwt, cutrank etc. are computable,
-- and they can be used in algorithms. ****


-- def mainsp {α} (π : njprf α) : NJPrf :=
--   match π with
--   | .ax _ => ⟨_,π⟩
--   | .emp _ μ => ⟨_,μ⟩
--   | .abs _ _ μ =>  ⟨_,π⟩
--   | .app _ _ μ ν => ⟨_,μ⟩
--   | .pair _ _ μ ν => ⟨_,π⟩
--   | .fst _ _ μ =>  ⟨_,μ⟩
--   | .snd _ _ μ =>  ⟨_,μ⟩
--   | .left _ _ μ => ⟨_,π⟩
--   | .right _ _ μ => ⟨_,π⟩
--   | .case α β _ χ μ ν => ⟨_,χ⟩

-- def elimproof {φ} (π: njprf φ) : Prop := lrof π = prapp
--                                        ∨ lrof π = prfst ∨ lrof π = prsnd
--                                        ∨ lrof π =  prcase
-- def introproof {φ} (π : njprf φ) : Prop := lrof π = premp ∨ lrof π = prabs
--                         ∨ lrof π = prpair ∨ lrof π = prleft ∨ lrof π = prright
--                                         ∨ lrof π = prcase

-- def cut {φ} (π: njprf φ) : Prop := (lrof π = premp ∧ conc π = bot) ∨
--                                     (elimproof π ∧ introproof (mainsp π).2)

-- def normal {φ} (π : njprf φ) : Prop :=
--   match h : π with
--   | .ax α => True
--   | .emp α μ => ¬cut π ∧ normal μ
--   | .abs α β μ => normal μ
--   | .app α β μ ν => ¬cut π ∧ normal μ ∧ normal ν
--   | .pair α β μ ν => normal μ ∧ normal ν
--   | .fst α β μ =>  ¬cut π ∧ normal μ
--   | .snd α β μ =>  ¬cut π ∧ normal μ
--   | .left α β μ => normal μ
--   | .right α β μ => normal μ
--   | .case α β γ χ μ ν => ¬cut π ∧ normal χ ∧ normal μ ∧ normal ν

-- lemma cut_iff_isCut : ∀ φ (π : njprf φ), cut π ↔ isCut π := by
--   intro φ π; constructor
--   · cases π <;> simp [cut, lrof,elimproof,conc,mainsp] <;> intro A
--     · subst_vars; constructor
--     · rename_i α ν μ; cases μ <;> simp [introproof, lrof] at A <;>
--         constructor
--     · rename_i α μ; cases μ <;> simp [introproof, lrof] at A <;>
--         constructor
--     · rename_i α μ; cases μ <;> simp [introproof, lrof] at A <;>
--         constructor
--     · rename_i α β χ μ ν; cases χ <;> simp [introproof, lrof] at A <;>
--         constructor
--   · intro A; cases A <;>
--       simp [cut, lrof, elimproof, mainsp, introproof, conc]

-- lemma normal_iff_isNormal : ∀ φ (π : njprf φ), normal π ↔ isNormal π := by
--   intro φ π; constructor <;> intro A
--   · induction h : π <;> simp [h, normal, cut_iff_isCut] at A
--     · apply isNormal.axNorm; grind
--     · apply isNormal.empNorm; rfl; grind; grind
--     · apply isNormal.absNorm; rfl; grind
--     · apply isNormal.appNorm; rfl; grind; grind; grind
--     · apply isNormal.pairNorm; rfl; grind; grind
--     · apply isNormal.fstNorm; rfl; grind; grind
--     · apply isNormal.sndNorm; rfl; grind; grind
--     · apply isNormal.leftNorm; rfl; grind
--     · apply isNormal.rightNorm; rfl; grind
--     · apply isNormal.caseNorm; rfl; grind; grind; grind; grind
--   · induction A <;> subst_vars <;> simp [normal,cut_iff_isCut] <;> grind
