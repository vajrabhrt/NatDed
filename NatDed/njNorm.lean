import Mathlib
import NatDed.nj
import NatDed.Rank

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option maxHeartbeats 0

namespace njNorm
open Rank
open nj
open nj.propform
open nj.njprf
open nj.proofrule

inductive isCut : {φ : propform} → njprf φ → Prop where
| appAbs : ∀ α β μ ν, isCut (app α β (abs α β μ) ν)
| fstPair : ∀ α β μ ν, isCut (fst α β (pair α β μ ν))
| sndPair : ∀ α β μ ν, isCut (snd α β (pair α β μ ν))
| caseLeft : ∀ α β δ χ μ ν, isCut (case α β δ (left α β χ) μ ν)
| caseRight : ∀ α β δ χ μ ν, isCut (case α β δ (right α β χ) μ ν)
| empBot : ∀ μ, isCut (emp bot μ)
| appEmp : ∀ α β μ ν, isCut (app α β (emp (impl α β) μ) ν)
| fstEmp : ∀ α β μ, isCut (fst α β (emp (conj α β) μ))
| sndEmp : ∀ α β μ, isCut (snd α β (emp (conj α β) μ))
| caseEmp : ∀ α β δ χ μ ν, isCut (case α β δ (emp (disj α β) χ) μ ν)
| appCase :  ∀ α β φ ψ χ ρ υ ν, isCut (app α β (case φ ψ (impl α β) χ ρ υ) ν)
| fstCase :  ∀ α β φ ψ χ ρ υ, isCut (fst α β (case φ ψ (conj α β) χ ρ υ))
| sndCase :  ∀ α β φ ψ χ ρ υ, isCut (snd α β (case φ ψ (conj α β) χ ρ υ))
| caseCase :  ∀ α β δ φ ψ χ ρ υ μ ν, isCut (case α β δ (case φ ψ (disj α β) χ ρ υ) μ ν)

inductive isNormal : {φ : propform} → njprf φ → Prop where
| axNorm : ∀ α π, π = ax α → isNormal π
| empNorm : ∀ α μ π, π = emp α μ → isNormal μ → ¬isCut π → isNormal π
| absNorm : ∀ α β μ π, π = abs α β μ → isNormal μ → isNormal π
| appNorm : ∀ α β μ ν π, π = app α β μ ν → isNormal μ → isNormal ν →
                                      ¬isCut π → isNormal π
| pairNorm : ∀ α β μ ν π, π = pair α β μ ν → isNormal μ → isNormal ν → isNormal π
| fstNorm : ∀ α β μ π, π = fst α β μ → isNormal μ → ¬isCut π → isNormal π
| sndNorm : ∀ α β μ π, π = snd α β μ → isNormal μ → ¬isCut π → isNormal π
| leftNorm : ∀ α β μ π, π = left α β μ → isNormal μ → isNormal π
| rightNorm : ∀ α β μ π, π = right α β μ → isNormal μ → isNormal π
| caseNorm : ∀ α β δ χ μ ν π, π = case α β δ χ μ ν → isNormal χ → isNormal μ →
                          isNormal ν → ¬isCut π → isNormal π

def degwt {φ} (π: njprf φ) : Rank :=
  match π with
  | app α β (njprf.abs _ _ _) _                   => ⟨sz α + sz β + 1, 1⟩
  | fst α β (pair _ _ _ _ )                       => ⟨sz α + sz β + 1, 1⟩
  | snd α β (pair _ _ _ _ )                       => ⟨sz α + sz β + 1, 1⟩
  | case α β δ (left _ _ _) _ _                   => ⟨sz α + sz β + 1, 1⟩
  | case α β δ (right _ _ _) _ _                  => ⟨sz α + sz β + 1, 1⟩
  | emp bot _                                     => ⟨sz bot, 1⟩
  | app α β (emp _ _) _                           => ⟨sz α + sz β + 1, 1⟩
  | fst α β (emp _ _)                             => ⟨sz α + sz β + 1, 1⟩
  | snd α β (emp _ _)                             => ⟨sz α + sz β + 1, 1⟩
  | case α β δ (emp _ _) _ _                      => ⟨sz α + sz β + 1, 1⟩
  | app α β (case _ _ _ ρ σ τ) _                  => ⟨sz α + sz β + 1,
                                          prfsize ρ + prfsize σ + prfsize τ + 1⟩
  | fst α β (case _ _ _ ρ σ τ)                    => ⟨sz α + sz β + 1,
                                          prfsize ρ + prfsize σ + prfsize τ + 1⟩
  | snd α β (case _ _ _ ρ σ τ)                    => ⟨sz α + sz β + 1,
                                          prfsize ρ + prfsize σ + prfsize τ + 1⟩
  | case α β δ (case _ _ _ ρ σ τ) _ _             => ⟨sz α + sz β + 1,
                                          prfsize ρ + prfsize σ + prfsize τ + 1⟩
  | _                                             => ⟨0,0⟩

def cutrank {φ} (π: njprf φ) : Rank :=
  match π with
  | .ax _ => degwt π
  | .emp _ μ => cutrank μ * degwt π
  | .abs _ _ μ => cutrank μ
  | .app _ _ μ ν => cutrank μ * cutrank ν * degwt π
  | .pair _ _ μ ν => cutrank μ * cutrank ν
  | .fst _ _ μ =>  cutrank μ * degwt π
  | .snd _ _ μ =>  cutrank μ * degwt π
  | .left _ _ μ => cutrank μ
  | .right _ _ μ => cutrank μ
  | .case α β _ χ μ ν => cutrank χ * cutrank μ * cutrank ν * degwt π

def degree {φ} (π: njprf φ) : ℕ := (degwt π).1
def weight {φ} (π: njprf φ) : ℕ := (degwt π).2
def maxDeg {φ} (π: njprf φ) : ℕ := (cutrank π).1

@[simp]
lemma isNormal_iff : ∀ φ (π : njprf φ), isNormal π ↔ ∀ ψ ϖ, ⟨ψ, ϖ⟩ ∈ subproofs π → isNormal ϖ := by
  intro φ π; constructor <;> intro H
  · induction H <;> intro ψ ϖ G <;> subst_vars <;>
      simp [subproofs] at G
    · cases G; constructor; rfl
    · rcases G with (G | G); rcases G; apply isNormal.empNorm
      rfl; assumption; assumption; grind
    · rcases G with (G | G); rcases G; apply isNormal.absNorm
      rfl; assumption; grind
    · rcases G with ((G | G) | G); rcases G; apply isNormal.appNorm;
      rfl; assumption; assumption; assumption; grind; grind
    · rcases G with ((G | G) | G); rcases G; apply isNormal.pairNorm;
      rfl; assumption; assumption; grind; grind
    · rcases G with (G | G); rcases G; apply isNormal.fstNorm;
      rfl; assumption; assumption; grind
    · rcases G with (G | G); rcases G; apply isNormal.sndNorm;
      rfl; assumption; assumption; grind
    · rcases G with (G | G); rcases G; apply isNormal.leftNorm;
      rfl; assumption; grind
    · rcases G with (G | G); rcases G; apply isNormal.rightNorm;
      rfl; assumption; grind
    · rcases G with (((G | G) | G) | G)
      rcases G; apply isNormal.caseNorm; rfl; assumption;
        assumption; assumption; assumption
      grind; grind; grind
  · cases π <;> apply H <;> simp [subproofs] <;> grind

@[simp]
lemma degwt_goodRank : ∀ φ (π : njprf φ), goodRank (degwt π) := by
  intro φ π; cases π <;> simp [goodRank, degwt] <;> split <;> try grind
  · right; simp [sz]

@[simp]
lemma cutrank_goodRank : ∀ φ (π : njprf φ), goodRank (cutrank π) := by
  intro φ π; induction π <;> simp [cutrank]
  · apply goodRank_pairAdd; assumption; simp [degwt_goodRank]
  · assumption
  · apply goodRank_pairAdd;
    apply goodRank_pairAdd <;> assumption
    simp [degwt_goodRank]
  · apply goodRank_pairAdd <;> assumption
  · apply goodRank_pairAdd; assumption; simp [degwt_goodRank]
  · apply goodRank_pairAdd; assumption; simp [degwt_goodRank]
  · assumption
  · assumption
  · apply goodRank_pairAdd; apply goodRank_pairAdd;
    apply goodRank_pairAdd; assumption; assumption;
    assumption; simp [degwt_goodRank]

lemma cutrank_sp : ∀ φ ψ (π : njprf φ) (μ : njprf ψ),
  ⟨ψ, μ⟩ ∈ subproofs π → cutrank μ ≤ cutrank π := by
  intro φ ψ π μ H
  induction π <;> simp [subproofs] at H <;> try grind
  · rename_i α π1 ih; rcases H with H | H
    · cases H; grind
    · simp [cutrank]; apply rank_le_rank_mul; grind
  · rename_i α β π1 ih; rcases H with H | H
    · cases H; grind
    · simp [cutrank]; grind
  · rename_i α β π1 π2 ih1 ih2; rcases H with (H | H )| H
    · cases H; grind
    · simp [cutrank]; apply rank_le_rank_mul;
        apply rank_le_rank_mul; grind
    · simp [cutrank]; apply rank_le_rank_mul;
        apply rank_le_mul_rank; grind
  · rename_i α β π1 π2 ih1 ih2; rcases H with (H | H )| H
    · cases H; grind
    · simp [cutrank]; apply rank_le_rank_mul; grind
    · simp [cutrank]; apply rank_le_mul_rank; grind
  · rename_i α β π1 ih; rcases H with H | H
    · cases H; grind
    · simp [cutrank]; apply rank_le_rank_mul; grind
  · rename_i α β π1 ih; rcases H with H | H
    · cases H; grind
    · simp [cutrank]; apply rank_le_rank_mul; grind
  · rename_i α β π1 ih; rcases H with H | H
    · cases H; grind
    · simp [cutrank]; grind
  · rename_i α β π1 ih; rcases H with H | H
    · cases H; grind
    · simp [cutrank]; grind
  · rename_i α β δ π1 π2 π3 ih1 ih2 ih3; rcases H with ((H | H) | H) | H
    · cases H; grind
    · simp [cutrank]; apply rank_le_rank_mul; apply rank_le_rank_mul;
      apply rank_le_rank_mul; grind
    · simp [cutrank]; apply rank_le_rank_mul; apply rank_le_rank_mul;
      apply rank_le_mul_rank; grind
    · simp [cutrank]; apply rank_le_rank_mul; apply rank_le_mul_rank;
      grind

lemma degwt_le_cutrank : ∀ φ (π : njprf φ), degwt π ≤ cutrank π := by
  intro φ π; cases π <;> simp [cutrank]
  all_goals first
    | exact le_self_mul
    | exact le_mul_self
    | simp [degwt]

lemma deg_le_maxDeg : ∀ φ (π : njprf φ), degree π ≤ maxDeg π := by
  intros; simp [degree, maxDeg];
  apply rank_le_proj; apply degwt_le_cutrank

lemma maxDeg_sp : ∀ φ ψ (π : njprf φ) (μ : njprf ψ),
  ⟨ψ, μ⟩ ∈ subproofs π → maxDeg μ ≤ maxDeg π := by
  intros; simp [maxDeg]; apply rank_le_proj
  apply cutrank_sp; assumption

lemma deg_degwt_0 : ∀ φ (π : njprf φ), degree π = 0 ↔ degwt π = ⟨0,0⟩ := by
  intros φ π;
  rcases E : degwt π with ⟨d,w⟩
  have H : goodRank ⟨d,w⟩ := by (rw [←E]; apply degwt_goodRank)
  simp [degree, goodRank, E] at *; grind

lemma degreeOfCut : ∀ φ (π : njprf φ), isCut π ↔ degree π > 0 := by
  intros φ π; constructor
  · intro H; cases H <;> simp [degree, degwt, sz]
  · intro E; cases π <;> unfold degree at E <;> simp [degwt] at E <;>
      split at E <;> try grind
    all_goals
      rename_i eq; rw [eq]; constructor

lemma normal_cutrank : ∀ φ (π : njprf φ), isNormal π ↔ cutrank π = ⟨0,0⟩ := by
  intro φ π; constructor <;> intro H
  · induction H <;> subst_vars <;> simp [cutrank] <;> try grind
    · simp [degwt]
    · rename_i α μ E ih F; simp [ih];
      rw [←deg_degwt_0]; rw [degreeOfCut] at F; grind
    · rename_i α β μ ν E F ih1 ih2 G; simp [ih1,ih2];
      rw [←deg_degwt_0]; rw [degreeOfCut] at G; grind
    · rename_i α β μ F ih G; simp [ih]
      rw [←deg_degwt_0]; rw [degreeOfCut] at G; grind
    · rename_i α β μ F ih G; simp [ih]
      rw [←deg_degwt_0]; rw [degreeOfCut] at G; grind
    · rename_i α β δ χ μ ν E F G ihχ ihμ ihν H; simp [ihχ, ihμ, ihν]
      rw [←deg_degwt_0]; rw [degreeOfCut] at H; grind
  · induction π
    · apply isNormal.axNorm; rfl
    · rename_i α μ ihμ; simp [cutrank] at H
      rcases H with ⟨H1,H2⟩
      apply ihμ at H1
      simp [←deg_degwt_0] at H2
      apply isNormal.empNorm; rfl; assumption;
      intro A; rw [degreeOfCut] at A; grind
    · rename_i α β μ ihμ; simp [cutrank] at H
      apply ihμ at H
      apply isNormal.absNorm; rfl; assumption
    · rename_i α β μ ν ihμ ihν; simp [cutrank] at H
      rcases H with ⟨⟨H1,H2⟩,H3⟩
      apply ihμ at H1; apply ihν at H2
      simp [←deg_degwt_0] at H3
      apply isNormal.appNorm; rfl; assumption; assumption
      intro A; rw [degreeOfCut] at A; grind
    · rename_i α β μ ν ihμ ihν; simp [cutrank] at H
      rcases H with ⟨H1,H2⟩
      apply ihμ at H1; apply ihν at H2
      apply isNormal.pairNorm; rfl; assumption; assumption
    · rename_i α β μ ihμ; simp [cutrank] at H
      rcases H with ⟨H1,H2⟩
      apply ihμ at H1; simp [←deg_degwt_0] at H2
      apply isNormal.fstNorm; rfl; assumption
      intro A; rw [degreeOfCut] at A; grind
    · rename_i α β μ ihμ; simp [cutrank] at H
      rcases H with ⟨H1,H2⟩
      apply ihμ at H1; simp [←deg_degwt_0] at H2
      apply isNormal.sndNorm; rfl; assumption
      intro A; rw [degreeOfCut] at A; grind
    · rename_i α β μ ihμ; simp [cutrank] at H
      apply ihμ at H; apply isNormal.leftNorm; rfl; assumption
    · rename_i α β μ ihμ; simp [cutrank] at H
      apply ihμ at H; apply isNormal.rightNorm; rfl; assumption
    · rename_i α β δ χ μ ν ihχ ihμ ihν; simp [cutrank] at H
      rcases H with ⟨⟨⟨H1,H2⟩,H3⟩,H4⟩
      apply ihχ at H1; apply ihμ at H2; apply ihν at H3
      simp [←deg_degwt_0] at H4
      apply isNormal.caseNorm; rfl;
      assumption; assumption; assumption
      intro A; rw [degreeOfCut] at A; grind

inductive graft {φ} (ρ : njprf φ) : {ψ : propform} → njprf ψ → njprf ψ → Prop
  | axgraft_same : graft ρ (ax φ) ρ
  | axgraft_diff : ∀ ψ, ψ ≠ φ → graft ρ (ax ψ) (ax ψ)
  | empgraft : ∀ α μ μ', graft ρ μ μ' → graft ρ (emp α μ) (emp α μ')
  | absgraft : ∀ α β μ μ', graft ρ μ μ' → graft ρ (abs α β μ) (abs α β μ')
  | appgraft : ∀ α β μ μ' ν ν', graft ρ μ μ' → graft ρ ν ν' →
                            graft ρ (app α β μ ν) (app α β μ' ν')
  | pairgraft : ∀ α β μ μ' ν ν', graft ρ μ μ' → graft ρ ν ν' →
                            graft ρ (pair α β μ ν) (pair α β μ' ν')
  | fstgraft : ∀ α β μ μ', graft ρ μ μ' → graft ρ (fst α β μ) (fst α β μ')
  | sndgraft : ∀ α β μ μ', graft ρ μ μ' → graft ρ (snd α β μ) (snd α β μ')
  | leftgraft : ∀ α β μ μ', graft ρ μ μ' → graft ρ (left α β μ) (left α β μ')
  | rightgraft : ∀ α β μ μ', graft ρ μ μ' → graft ρ (right α β μ) (right α β μ')
  | casegraft : ∀ α β δ χ χ' μ μ' ν ν', graft ρ χ χ' → graft ρ μ μ' →
                  graft ρ ν ν' → graft ρ (case α β δ χ μ ν) (case α β δ χ' μ' ν')

inductive contract : {φ : propform} → njprf φ → njprf φ → Prop
  | appAbsContract : ∀ α β μ μ' ν, graft ν μ μ' →
                          contract (app α β (abs α β μ) ν) μ'
  | fstPairContract : ∀ α β μ ν,
                          contract (fst α β (pair α β μ ν)) μ
  | sndPairContract : ∀ α β μ ν,
                          contract (snd α β (pair α β μ ν)) ν
  | caseLeftContract : ∀ α β δ χ μ μ' ν, graft χ μ μ' →
                          contract (case α β δ (left α β χ) μ ν) μ'
  | caseRightContract : ∀ α β δ χ μ ν ν', graft χ ν ν' →
                          contract (case α β δ (right α β χ) μ ν) ν'
  | empBotContract : ∀ μ, contract (emp bot μ) μ
  | appEmpContract : ∀ α β μ ν,
                          contract ((app α β (emp (impl α β) μ)) ν) (emp β μ)
  | fstEmpContract : ∀ α β μ,
                          contract (fst α β (emp (conj α β) μ)) (emp α μ)
  | sndEmpContract : ∀ α β μ,
                          contract (snd α β (emp (conj α β) μ)) (emp β μ)
  | caseEmpContract : ∀ α β δ χ μ ν,
                          contract ((case α β δ (emp (disj α β) χ)) μ ν) (emp δ χ)
  | appCaseContract : ∀ α β γ δ χ ρ υ ν,
                          contract  (app α β (case γ δ (impl α β) χ ρ υ) ν)
                                    (case γ δ β χ (app α β ρ ν) (app α β υ ν))
  | fstCaseContract : ∀ α β γ δ χ ρ υ,
                          contract  (fst α β (case γ δ (conj α β) χ ρ υ))
                                    (case γ δ α χ (fst α β ρ) (fst α β υ))
  | sndCaseContract : ∀ α β γ δ χ ρ υ,
                          contract  (snd α β (case γ δ (conj α β) χ ρ υ))
                                    (case γ δ β χ (snd α β ρ) (snd α β υ))
  | caseCaseContract : ∀ α β γ δ ε χ ρ υ μ ν,
                          contract  (case α β γ (case δ ε (disj α β) χ ρ υ) μ ν)
                                    (case δ ε γ χ (case α β γ ρ μ ν) (case α β γ υ μ ν))

inductive oneStep: (φ : propform) → njprf φ → njprf φ → Prop where
| empCrit : ∀ α π ϖ μ, π = emp α μ → contract π ϖ →
                    maxDeg μ < maxDeg π →
                    oneStep α π ϖ
| empStep : ∀ α π μ μ', π = emp α μ →
                    maxDeg μ = maxDeg π →
                    oneStep bot μ μ' → oneStep α π (emp α μ')
| absStep : ∀ α β π μ μ', π = abs α β μ →
                    maxDeg μ = maxDeg π →
                    oneStep β μ μ' → oneStep (impl α β) π (abs α β μ')
| appCrit : ∀ α β π ϖ μ ν, π = app α β μ ν → contract π ϖ →
                    degree π = maxDeg π →
                    lrof μ = prcase ∨
                        lrof μ ≠ prcase ∧ maxDeg μ < maxDeg π →
                    maxDeg ν < maxDeg π →
                    oneStep β π ϖ
| app1Step : ∀ α β π μ μ' ν, π = app α β μ ν →
                    degree π < maxDeg π ∨ lrof μ ≠ prcase →
                    maxDeg ν < maxDeg π → maxDeg μ = maxDeg π →
                    oneStep (impl α β) μ μ' → oneStep β π (app α β μ' ν)
| app2Step : ∀ α β π μ ν ν', π = app α β μ ν →
                    maxDeg ν = maxDeg π →
                    oneStep α ν ν' → oneStep β π (app α β μ ν')
| pair1Step : ∀ α β π μ μ' ν, π = pair α β μ ν →
                    maxDeg ν < maxDeg π → maxDeg μ = maxDeg π →
                    oneStep α μ μ' → oneStep (conj α β) π (pair α β μ' ν)
| pair2Step : ∀ α β π μ ν ν', π = pair α β μ ν →
                    maxDeg ν = maxDeg π →
                    oneStep β ν ν' → oneStep (conj α β) π (pair α β μ ν')
| fstCrit : ∀ α β π ϖ μ, π = fst α β μ → contract π ϖ →
                    degree π = maxDeg π →
                    lrof μ = prcase ∨
                        lrof μ ≠ prcase ∧ maxDeg μ < maxDeg π →
                    oneStep α π ϖ
| fstStep : ∀ α β π μ μ', π = fst α β μ →
                    degree π < maxDeg π ∨ lrof μ ≠ prcase →
                    maxDeg μ = maxDeg π →
                    oneStep (conj α β) μ μ' → oneStep α π (fst α β μ')
| sndCrit : ∀ α β π ϖ μ, π = snd α β μ → contract π ϖ →
                    degree π = maxDeg π →
                    lrof μ = prcase ∨
                        lrof μ ≠ prcase ∧ maxDeg μ < maxDeg π →
                    oneStep β π ϖ
| sndStep : ∀ α β π μ μ', π = snd α β μ →
                    degree π < maxDeg π ∨ lrof μ ≠ prcase →
                    maxDeg μ = maxDeg π →
                    oneStep (conj α β) μ μ' → oneStep β π (snd α β μ')
| leftStep : ∀ α β π μ μ', π = left α β μ →
                    maxDeg μ = maxDeg π →
                    oneStep α μ μ' → oneStep (disj α β) π (left α β μ')
| rightStep : ∀ α β π μ μ', π = right α β μ →
                    maxDeg μ = maxDeg π →
                    oneStep β μ μ' → oneStep (disj α β) π (right α β μ')
| caseCrit : ∀ α β δ π ϖ χ μ ν, π = case α β δ χ μ ν → contract π ϖ →
                    degree π = maxDeg π →
                    lrof χ = prcase ∨
                        lrof χ ≠ prcase ∧ maxDeg χ < maxDeg π →
                    maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
                    oneStep δ π ϖ
| case1Step : ∀ α β δ π χ χ' μ ν, π = case α β δ χ μ ν →
                    degree π < maxDeg π ∨ lrof χ ≠ prcase →
                    maxDeg ν < maxDeg π → maxDeg μ < maxDeg π →
                    maxDeg χ = maxDeg π →
                    oneStep (disj α β) χ χ' → oneStep δ π (case α β δ χ' μ ν)
| case2Step : ∀ α β δ π χ μ μ' ν, π = case α β δ χ μ ν  →
                    maxDeg ν < maxDeg π → maxDeg μ = maxDeg π →
                    oneStep δ μ μ' → oneStep δ π (case α β δ χ μ' ν)
| case3Step : ∀ α β δ π χ μ ν ν', π = case α β δ χ μ ν →
                    maxDeg ν = maxDeg π  →
                    oneStep δ ν ν' → oneStep δ π (case α β δ χ μ ν')

lemma graftAssConc : ∀ φ ψ (ρ : njprf φ) (π : njprf ψ) ϖ, graft ρ π ϖ →
            hypos ϖ ⊆ (hypos π \ {φ}) ∪ hypos ρ ∧ conc ϖ = conc π := by
  intro φ ψ ρ π ϖ Hgraft; constructor
  · induction Hgraft <;> simp_all [hypos] <;> try grind
    · rename_i α β μ μ' h ih; intro x hx;
      apply ih at hx;
      by_cases f : x = α <;> simp_all
  · simp [conc]

lemma lrofGraft : ∀ φ ψ (ρ : njprf φ) (π ϖ : njprf ψ),
      graft ρ π ϖ → lrof ϖ = lrof π ∨
      (lrof π = prax ∧ φ = ψ ∧ lrof ϖ = lrof ρ) := by
  intro φ ψ ρ π ϖ Hgraft; cases Hgraft <;> simp [lrof]

lemma contractAssConc : ∀ φ (π ϖ : njprf φ),
  contract π ϖ → hypos ϖ ⊆ hypos π ∧ conc ϖ = conc π := by
  intro φ π ϖ Hcontract
  constructor
  · induction Hcontract <;> simp_all [hypos, graftAssConc] <;> try grind
    · rename_i α β δ χ μ μ' ν Hgraft
      intro x hx; apply graftAssConc at Hgraft;
      rcases Hgraft.1 hx with h|h <;> simp_all
    · rename_i α β δ χ μ μ' ν Hgraft
      intro x hx; apply graftAssConc at Hgraft;
      rcases Hgraft.1 hx with h|h <;> simp_all
  · simp [conc]

lemma oneStepConcAss : ∀ φ (π π' : njprf φ),
  oneStep _ π π' → hypos π' ⊆ hypos π ∧ conc π' = conc π := by
  intro φ ϖ ϖ' hos
  induction hos <;> clear ϖ ϖ' <;>
    subst_vars <;> simp_all [hypos, conc] <;> try grind
  · rename_i μ μ' f1 f2
    apply contractAssConc at f1
    simp [hypos, conc] at f1; assumption
  · rename_i α β π' μ ν f1 f2 f3 f4
    apply contractAssConc at f1;
    simp [hypos, conc] at f1; assumption
  · rename_i α β π' μ f1 f2 f3
    apply contractAssConc at f1;
    simp [hypos, conc] at f1; assumption
  · rename_i α β π' μ f1 f2 f3
    apply contractAssConc at f1;
    simp [hypos, conc] at f1; assumption
  · rename_i α β δ π' χ μ ν f1 f2 f3 f4 f5
    apply contractAssConc at f1;
    simp [hypos, conc] at f1; assumption

lemma lrofOneStep : ∀ φ (π π' : njprf φ),
  oneStep φ π π' →  sz (conc π) < degree π ∨
                    lrof π = lrof π' ∧ lrof π ≠ prcase ∨
                    lrof π = premp ∧ conc π = bot ∨
                    lrof π = prcase := by
  intro φ π π' H
  cases H
  · rename_i μ eq A B; subst_vars; cases B; simp [lrof,conc]
  · subst_vars; simp [lrof]
  · subst_vars; simp [lrof]
  · rename_i α ν μ eq E F G H
    subst_vars; simp [lrof]; left
    cases μ <;> simp [lrof, ←E, degree, degwt] at F <;>
    simp [conc, degree, degwt]
  · right; left; cases π <;> try grind
    simp [lrof]
  · right; left; cases π <;> try grind
    simp [lrof]
  · subst_vars; simp [lrof]
  · subst_vars; simp [lrof]
  · rename_i α μ eq E F G
    subst_vars; simp [lrof]; left
    cases μ <;> simp [lrof, ←E, degree, degwt] at F <;>
    simp [conc, degree, degwt]
  · right; left; cases π <;> try grind
    simp [lrof]
  · rename_i α μ eq E F G
    subst_vars; simp [lrof]; left
    cases μ <;> simp [lrof, ←E, degree, degwt] at F <;>
    simp [conc, degree, degwt]
  · right; left; cases π <;> try grind
    simp [lrof]
  · subst_vars; simp [lrof]
  · subst_vars; simp [lrof]
  · rename_i α β μ ν χ eq E F G H I
    right; right; right; rw [eq]; simp [lrof]
  · by_cases A : lrof π = prcase
    · simp [A]
    · right; left; constructor <;> try simp [A]
      cases π <;> try grind
      simp [lrof]
  · by_cases A : lrof π = prcase
    · simp [A]
    · right; left; constructor <;> try simp [A]
      cases π <;> try grind
      simp [lrof]
  · by_cases A : lrof π = prcase
    · simp [A]
    · right; left; constructor <;> try simp [A]
      cases π <;> try grind
      simp [lrof]

lemma degree_empGraft : ∀ φ α (ρ : njprf φ) (μ μ' : njprf bot),
  graft ρ μ μ' → degree (emp α μ) = degree (emp α μ') :=  by
  intro φ α ρ μ μ' Hgraft
  cases Hgraft
  all_goals
    by_cases F : α = bot
    · subst_vars; simp [degree, degwt]
    · simp [degree, degwt, F]

lemma degree_appGraft : ∀ φ α β (ρ : njprf φ) μ μ' ν ν',
  graft ρ μ μ' → graft ρ ν ν' →
    degree (app α β μ ν) = degree (app α β μ' ν') ∨
    degree (app α β μ' ν') = sz φ := by
  intro φ α β ρ μ μ' ν ν' Hgraftμ Hgraftν
  cases Hgraftμ <;> simp_all [degree, degwt,sz]
  · split <;> simp_all

lemma degree_fstGraft : ∀ φ α β (ρ : njprf φ) μ μ',
  graft ρ μ μ' →
    degree (fst α β μ) = degree (fst α β μ') ∨
    degree (fst α β μ') = sz φ := by
  intro φ α β ρ μ μ' Hgraft
  cases Hgraft <;> simp_all [degree, degwt, sz]
  · split <;> simp_all

lemma degree_sndGraft : ∀ φ α β (ρ : njprf φ) μ μ',
  graft ρ μ μ' →
    degree (snd α β μ) = degree (snd α β μ') ∨
    degree (snd α β μ') = sz φ := by
  intro φ α β ρ μ μ' Hgraft
  cases Hgraft <;> simp_all [degree, degwt, sz]
  · split <;> simp_all

lemma degree_caseGraft : ∀ φ α β δ (ρ : njprf φ) χ χ' μ μ' ν ν',
  graft ρ χ χ' → graft ρ μ μ' → graft ρ ν ν' →
    degree (case α β δ χ μ ν) = degree (case α β δ χ' μ' ν') ∨
    degree (case α β δ χ' μ' ν') = sz φ := by
  intro φ α β δ ρ χ χ' μ μ' ν ν' Hgraftχ Hgraftμ Hgraftν
  cases Hgraftχ <;> simp [degree, degwt, sz]
  · split <;> simp_all

lemma graftCutRank : ∀ d φ ψ (ρ : njprf φ) (π ϖ : njprf ψ), graft ρ π ϖ →
          maxDeg ρ < d → maxDeg π < d → sz φ < d →
                  maxDeg ϖ < d := by
  intro d φ ψ ρ π ϖ Hgraft H1 H2 H3
  induction Hgraft <;> clear ψ π ϖ <;>
    try simp_all [maxDeg, cutrank] <;> try grind
  · rename_i α μ μ' Hgraft ih
    simp [pairAdd_fst] at H2; simp [pairAdd_fst]
    rcases H2 with ⟨H21, H22⟩
    apply degree_empGraft (α := α) at Hgraft
    simp [degree] at *; try grind
  · rename_i α β μ μ' ν ν' Hgraftμ Hgraftν ihμ ihν
    simp [pairAdd_fst] at H2; simp [pairAdd_fst]
    rcases H2 with ⟨H21, H22⟩
    rcases degree_appGraft _ α β _ _ _ _ _ Hgraftμ Hgraftν with G | G <;>
      simp [degree] at * <;> try grind
  · rename_i α β μ μ' ν ν' Hgraftμ Hgraftν ihμ ihν
    simp [pairAdd_fst] at H2; simp [pairAdd_fst]
    rcases H2 with ⟨H21, H22⟩; grind
  · rename_i α β μ μ' Hgraftμ ihμ
    simp [pairAdd_fst] at H2; simp [pairAdd_fst]
    rcases H2 with ⟨H21, H22⟩
    rcases degree_fstGraft _ α β _ _ _  Hgraftμ with G | G <;>
      simp [degree] at * <;> try grind
  · rename_i α β μ μ' Hgraftμ ihμ
    simp [pairAdd_fst] at H2; simp [pairAdd_fst]
    rcases H2 with ⟨H21, H22⟩
    rcases degree_sndGraft _ α β _ _ _  Hgraftμ with G | G <;>
      simp [degree] at * <;> try grind
  · rename_i α β δ χ χ' μ μ' ν ν' Hgraftχ Hgraftμ Hgraftν ihχ ihμ ihν
    simp [pairAdd_fst] at H2; simp [pairAdd_fst]
    rcases H2 with ⟨H21, H22⟩
    rcases degree_caseGraft _ α β δ _ _ _ _ _ _ _ Hgraftχ Hgraftμ Hgraftν
                                                      with G | G <;>
     simp [degree] at * <;> try grind

lemma appAbsCutRank : ∀ α β π ϖ μ ν,
  π = app α β (abs α β μ) ν → contract π ϖ →
  degree π = maxDeg π → maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ μ ν eq Hcontract
  subst_vars; cases Hcontract; simp [degree, maxDeg, cutrank, degwt]
  rename_i Hgraft
  intro E F G; simp [rank_lt_rank_iff]; rw [←E] at *; clear E; left
  apply graftCutRank (sz α + sz β + 1) α β at Hgraft
  simp [maxDeg] at Hgraft; grind

lemma fstPairCutRank : ∀ α β π ϖ μ ν,
  π = fst α β (pair α β μ ν) → contract π ϖ →
  degree π = maxDeg π → maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ μ ν eq Hcontract
  subst_vars; cases Hcontract; simp [degree, maxDeg, cutrank, degwt]
  intro E F G; simp [rank_lt_rank_iff]; rw [←E] at *; clear E; left; assumption

lemma sndPairCutRank : ∀ α β π ϖ μ ν,
  π = snd α β (pair α β μ ν) → contract π ϖ →
  degree π = maxDeg π → maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ μ ν eq Hcontract
  subst_vars; cases Hcontract; simp [degree, maxDeg, cutrank, degwt]
  intro E F G; simp [rank_lt_rank_iff]; rw [←E] at *; clear E; left; assumption

lemma caseLeftCutRank : ∀ α β δ π ϖ χ μ ν,
  π = case α β δ (left α β χ) μ ν → contract π ϖ →
  degree π = maxDeg π → maxDeg χ < maxDeg π →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β δ π ϖ χ μ ν eq Hcontract
  subst_vars; cases Hcontract; simp [degree, maxDeg, cutrank, degwt]
  rename_i Hgraft
  intro E F G H; simp [rank_lt_rank_iff]; rw [←E] at *; clear E; left
  apply graftCutRank (sz α + sz β + 1) α δ at Hgraft
  simp [maxDeg] at Hgraft; grind

lemma caseRightCutRank : ∀ α β δ π ϖ χ μ ν,
  π = case α β δ (right α β χ) μ ν → contract π ϖ →
  degree π = maxDeg π → maxDeg χ < maxDeg π →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β δ π ϖ χ μ ν eq Hcontract
  subst_vars; cases Hcontract; simp [degree, maxDeg, cutrank, degwt]
  rename_i Hgraft
  intro E F G H; simp [rank_lt_rank_iff]; rw [←E] at *; clear E; left
  apply graftCutRank (sz α + sz β + 1) β δ at Hgraft
  simp [maxDeg] at Hgraft; grind

lemma appEmpCutRank : ∀ α β π ϖ μ ν,
  π = app α β (emp _ μ) ν → contract π ϖ →
  degree π = maxDeg π →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ μ ν eq Hcontract
  subst_vars; cases Hcontract; intro E F G
  conv_lhs => simp [cutrank]
  simp [rank_lt_rank_iff]; left
  constructor; apply F
  have C : sz β > 0 := by apply sz_gt_0
  have D : (degwt (emp β μ)).1 ≤ 1 := by
    simp [degwt]; split <;> simp [sz] at *
  have A : sz β + 1 ≤ (cutrank (app α β (emp (α.impl β) μ) ν)).1 := by
    simp [pairAdd_fst, cutrank, degwt]
  grind

lemma fstEmpCutRank : ∀ α β π ϖ μ,
  π = fst α β (emp _ μ) → contract π ϖ →
  degree π = maxDeg π → maxDeg μ < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ μ eq Hcontract
  subst_vars; cases Hcontract; intro E F
  conv_lhs => simp [cutrank]
  simp [rank_lt_rank_iff]; left
  constructor; apply F
  have C : sz α > 0 := by apply sz_gt_0
  have D : (degwt (emp α μ)).1 ≤ 1 := by
    simp [degwt]; split <;> simp [sz] at *
  have A : sz α + 1 ≤ (cutrank (fst α β (emp (α.conj β) μ))).1 := by
    simp [pairAdd_fst, cutrank, degwt]
  grind

lemma sndEmpCutRank : ∀ α β π ϖ μ,
  π = snd α β (emp _ μ) → contract π ϖ →
  degree π = maxDeg π → maxDeg μ < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ μ eq Hcontract
  subst_vars; cases Hcontract; intro E F
  conv_lhs => simp [cutrank]
  simp [rank_lt_rank_iff]; left
  constructor; apply F
  have C : sz β > 0 := by apply sz_gt_0
  have D : (degwt (emp β μ)).1 ≤ 1 := by
    simp [degwt]; split <;> simp [sz] at *
  have A : sz β + 1 ≤ (cutrank (snd α β (emp (α.conj β) μ))).1 := by
    simp [pairAdd_fst, cutrank, degwt]
  grind

lemma caseEmpCutRank : ∀ α β δ π ϖ χ μ ν,
  π = case α β δ (emp _ χ) μ ν → contract π ϖ →
  degree π = maxDeg π → maxDeg χ < maxDeg π →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β δ π ϖ χ μ ν eq Hcontract
  subst_vars; cases Hcontract; intro E F G H
  conv_lhs => simp [cutrank]
  simp [rank_lt_rank_iff]; left
  constructor; apply F
  have C : sz α > 0 := by apply sz_gt_0
  have D : (degwt (emp δ χ)).1 ≤ 1 := by
    simp [degwt]; split <;> simp [sz] at *
  have A : sz α + 1 ≤ (cutrank (case α β δ (emp (α.disj β) χ) μ ν)).1 := by
    simp [pairAdd_fst, cutrank, degwt]
  grind

lemma appCaseCutRank : ∀ α β γ δ π ϖ χ ρ υ ν,
  π = app α β (case γ δ _ χ ρ υ) ν → contract π ϖ →
  degree π = maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β γ δ π ϖ χ ρ υ ν eq Hcontract
  subst_vars; cases Hcontract
  set μ := case γ δ _ χ ρ υ with eq1
  set π := app α β μ ν with eq2
  set ρ' := app α β ρ ν with eq3
  set υ' := app α β υ ν with eq4
  set ϖ := case γ δ _ χ ρ' υ' with eq5
  set psx := prfsize χ with Rpsx
  set psr := prfsize ρ with Rpsr
  set psu := prfsize υ with Rpsu
  intro Hp01; simp [degree, maxDeg] at Hp01
  intro Hn; simp [maxDeg] at Hn
  have Hx : maxDeg χ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      left; right; left; left; right; simp [self_sp]
  have Hr : maxDeg ρ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      left; right; left; right; simp [self_sp]
  have Hu : maxDeg υ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      left; right; right; simp [self_sp]
  have Hm : maxDeg μ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      left; right; left; left; left; grind
  have Hp0 : degwt π = ⟨sz α + sz β + 1, 1 + psx + psr + psu⟩ := by
    simp [eq2, eq1, psx, psr, psu]; simp [degwt]; omega
  have Hr' : cutrank ρ' ≤ cutrank ρ * ⟨sz α + sz β + 1, psr⟩ := by {
    calc
      cutrank ρ' = degwt ρ' * (cutrank ρ * cutrank ν) := by
                            simp [eq3, cutrank]; ac_rfl
      _ ≤ ⟨sz α + sz β + 1, psr⟩ * (cutrank ρ * cutrank ν) := by
              apply pairAdd_left_monotone; simp [eq3, Rpsr];
              cases ρ <;> simp [degwt, rank_le_rank_iff, prfsize]
      _ = cutrank ν * (cutrank ρ * ⟨sz α + sz β + 1, psr⟩) := by ac_rfl
      _ ≤ cutrank ρ * ⟨sz α + sz β + 1, psr⟩ := by {
          apply pairAdd_left_smallerd <;> try grind
          simp [←Hp01, Hp0] at Hn; simp [pairAdd_fst]; grind
        }
  }
  have Hu' : cutrank υ' ≤ cutrank υ * ⟨sz α + sz β + 1, psu⟩ := by {
    calc
      cutrank υ' = degwt υ' * (cutrank υ * cutrank ν) := by
                            simp [eq4, cutrank]; ac_rfl
      _ ≤ ⟨sz α + sz β + 1, psu⟩ * (cutrank υ * cutrank ν) := by
              apply pairAdd_left_monotone; simp [eq4, Rpsu];
              cases υ <;> simp [degwt, rank_le_rank_iff, prfsize]
      _ = cutrank ν * (cutrank υ * ⟨sz α + sz β + 1, psu⟩) := by ac_rfl
      _ ≤ cutrank υ * ⟨sz α + sz β + 1, psu⟩ := by {
          apply pairAdd_left_smallerd <;> try grind
          simp [←Hp01, Hp0] at Hn; simp [pairAdd_fst]; grind
        }
  }
  have Hvp0 : degwt ϖ ≤ ⟨sz α + sz β + 1, psx⟩ := by {
    simp [Rpsx];
    have A : degree ϖ = 0 ∨ sz γ + sz δ ≤ sz α + sz β := by {
      by_cases D : degree ϖ = 0 <;> try grind
      rw [eq5] at D
      have A : sz γ + sz δ + 1 ≤ degree (case γ δ (α.impl β) χ ρ υ) := by {
        simp [degree]; cases χ <;> simp [degree, degwt] at D <;>
          simp [degwt]
      }
      have B : sz γ + sz δ + 1 ≤ maxDeg π := by {
        simp [degree] at A
        simp [eq2, eq1, maxDeg, cutrank, pairAdd_fst, A]
      }
      rw [maxDeg, ←Hp01, eq2, eq1] at B; simp [degwt] at B; grind
    }
    simp [degree] at A; rcases A with A | A
    · simp [rank_le_rank_iff, A]
    · rw [eq5]; cases χ <;> simp [degwt, rank_le_rank_iff, prfsize] <;> try grind
  }
  -- **** A long sequence of calculations starts. ****
  calc
    cutrank ϖ = degwt ϖ * (cutrank χ * cutrank ρ' * cutrank υ') := by
                          simp [eq5, cutrank]; ac_rfl
    _ ≤ ⟨sz α + sz β + 1, psx⟩ * (cutrank χ * cutrank ρ' * cutrank υ') := by
                                            apply pairAdd_left_monotone; assumption
    _ = cutrank ρ' * ((⟨sz α + sz β + 1, psx⟩ * (cutrank χ * cutrank υ'))) := by ac_rfl
    _ ≤ (cutrank ρ * ⟨sz α + sz β + 1, psr⟩) * (⟨sz α + sz β + 1, psx⟩ *
                                                (cutrank χ * cutrank υ')) := by
                                            apply pairAdd_left_monotone; assumption
    _ = cutrank υ' * (⟨sz α + sz β + 1, psx⟩ *
                      ⟨sz α + sz β + 1, psr⟩ * cutrank χ * cutrank ρ) := by ac_rfl
    _ ≤ (cutrank υ * ⟨sz α + sz β + 1, psu⟩) * (⟨sz α + sz β + 1, psx⟩ *
                          ⟨sz α + sz β + 1, psr⟩ * cutrank χ * cutrank ρ) := by
                                            apply pairAdd_left_monotone; assumption
    _ = (cutrank χ * cutrank ρ * cutrank υ) * (⟨sz α + sz β + 1, psu⟩ *
                          ⟨sz α + sz β + 1, psx⟩ * ⟨sz α + sz β + 1, psr⟩) := by ac_rfl
    _ = (cutrank χ * cutrank ρ * cutrank υ) * ⟨sz α + sz β + 1, psx + psr + psu⟩ := by
                                                simp [pairAdd_eq_same]; grind
    _ < (cutrank χ * cutrank ρ * cutrank υ) * ⟨sz α + sz β + 1, 1 + psx + psr + psu⟩ := by
              rw [← pairAdd_right_monotone_strict]
              · right; grind
              · simp [goodRank]
              · simp [maxDeg] at *; simp [Hp0] at Hp01; rw [←Hp01] at Hx;
                rw [←Hp01] at Hr; rw [←Hp01] at Hu; simp [pairAdd_fst]; grind
    _ ≤ (cutrank ν * degwt μ ) * ((cutrank χ * cutrank ρ * cutrank υ) *
                                ⟨sz α + sz β + 1, 1 + psx + psr + psu⟩) := by
                                                                  apply le_mul_self
    _ = cutrank π := by rw [eq2,eq1,Rpsx,Rpsr,Rpsu] at Hp0;
                        rw [eq2,eq1]; simp [cutrank, Hp0]
                        ac_rfl

lemma fstCaseCutRank : ∀ α β γ δ π ϖ χ ρ υ,
  π = fst α β (case γ δ _ χ ρ υ) → contract π ϖ →
  degree π = maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β γ δ π ϖ χ ρ υ eq Hcontract
  subst_vars; cases Hcontract
  set μ := case γ δ _ χ ρ υ with eq1
  set π := fst α β μ with eq2
  set ρ' := fst α β ρ with eq3
  set υ' := fst α β υ with eq4
  set ϖ := case γ δ _ χ ρ' υ' with eq5
  set psx := prfsize χ with Rpsx
  set psr := prfsize ρ with Rpsr
  set psu := prfsize υ with Rpsu
  intro Hp01; simp [degree, maxDeg] at Hp01
  have Hx : maxDeg χ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      right; left; left; right; simp [self_sp]
  have Hr : maxDeg ρ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      right; left; right; simp [self_sp]
  have Hu : maxDeg υ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      right; right; simp [self_sp]
  have Hm : maxDeg μ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      right; left; left; left; grind
  have Hp0 : degwt π = ⟨sz α + sz β + 1, 1 + psx + psr + psu⟩ := by
    simp [eq2, eq1, psx, psr, psu, degwt]; omega
  have Hr' : cutrank ρ' ≤ cutrank ρ * ⟨sz α + sz β + 1, psr⟩ := by {
    calc
      cutrank ρ' = degwt ρ' * cutrank ρ  := by simp [eq3, cutrank]; ac_rfl
      _ ≤ ⟨sz α + sz β + 1, psr⟩ * cutrank ρ := by
        apply pairAdd_left_monotone; simp [eq3, Rpsr];
        cases ρ <;> simp [degwt, rank_le_rank_iff, prfsize] ; omega
      _ = cutrank ρ * ⟨sz α + sz β + 1, psr⟩ := by ac_rfl
  }
  have Hu' : cutrank υ' ≤ cutrank υ * ⟨sz α + sz β + 1, psu⟩ := by {
    calc
      cutrank υ' = degwt υ' * cutrank υ  := by simp [eq4, cutrank]; ac_rfl
      _ ≤ ⟨sz α + sz β + 1, psu⟩ * cutrank υ := by
        apply pairAdd_left_monotone; simp [eq4, Rpsu];
        cases υ <;> simp [degwt, rank_le_rank_iff, prfsize] ; omega
      _ = cutrank υ  * ⟨sz α + sz β + 1, psu⟩ := by ac_rfl
  }
  have Hvp0 : degwt ϖ ≤ ⟨sz α + sz β + 1, psx⟩ := by {
    simp [Rpsx];
    have A : degree ϖ = 0 ∨ sz γ + sz δ ≤ sz α + sz β := by {
      by_cases D : degree ϖ = 0 <;> try grind
      rw [eq5] at D
      have A : sz γ + sz δ + 1 ≤ degree (case γ δ (α.conj β) χ ρ υ) := by {
        simp [degree]; cases χ <;> simp [degree, degwt] at D <;>
          simp [degwt]
      }
      have B : sz γ + sz δ + 1 ≤ maxDeg π := by {
        simp [degree] at A
        simp [eq2, eq1, maxDeg, cutrank, pairAdd_fst, A]
      }
      rw [maxDeg, ←Hp01, eq2, eq1] at B; simp [degwt] at B; grind
    }
    simp [degree] at A; rcases A with A | A
    · simp [rank_le_rank_iff, A]
    · rw [eq5]; cases χ <;> simp [degwt, rank_le_rank_iff, prfsize] <;> try grind
  }
  -- **** A long sequence of calculations starts. ****
  calc
    cutrank ϖ = degwt ϖ * (cutrank χ * cutrank ρ' * cutrank υ') := by
                                            rw [eq5]; simp [cutrank]; ac_rfl
    _ ≤ ⟨sz α + sz β + 1, psx⟩ * (cutrank χ * cutrank ρ' * cutrank υ') := by
                                          apply pairAdd_left_monotone; assumption
    _ = cutrank ρ' * (⟨sz α + sz β + 1, psx⟩ * (cutrank χ * cutrank υ')) := by ac_rfl
    _ ≤ (cutrank ρ * ⟨sz α + sz β + 1, psr⟩) *
                    (⟨sz α + sz β + 1, psx⟩ * (cutrank χ * cutrank υ')) := by
                                        apply pairAdd_left_monotone; assumption
    _ = cutrank υ' * (⟨sz α + sz β + 1, psx⟩ *
                      ⟨sz α + sz β + 1, psr⟩ * cutrank χ * cutrank ρ) := by ac_rfl
    _ ≤ (cutrank υ * ⟨sz α + sz β + 1, psu⟩) * (⟨sz α + sz β + 1, psx⟩ *
                      ⟨sz α + sz β + 1, psr⟩ * cutrank χ * cutrank ρ) := by
                                            apply pairAdd_left_monotone; assumption
    _ = cutrank χ * cutrank ρ * cutrank υ * (⟨sz α + sz β + 1, psu⟩ *
                ⟨sz α + sz β + 1, psx⟩ * ⟨sz α + sz β + 1, psr⟩) := by ac_rfl
    _ = cutrank χ * cutrank ρ * cutrank υ * ⟨sz α + sz β + 1, psx + psr + psu⟩ := by
                                                simp [pairAdd_eq_same]; grind
    _ < cutrank χ * cutrank ρ * cutrank υ * ⟨sz α + sz β + 1, 1 + psx + psr + psu⟩ := by
              rw [← pairAdd_right_monotone_strict]
              · right; grind
              · simp [goodRank]
              · simp [maxDeg] at *; simp [Hp0] at Hp01; rw [←Hp01] at Hx;
                rw [←Hp01] at Hr; rw [←Hp01] at Hu; simp [pairAdd_fst]; grind
    _ ≤ degwt μ * (cutrank χ * cutrank ρ * cutrank υ *
                  ⟨sz α + sz β + 1, 1 + psx + psr + psu⟩) := by apply le_mul_self
    _ = cutrank π := by rw [eq2,eq1] at Hp0; simp [eq2,eq1, cutrank, Hp0]; ac_rfl

lemma sndCaseCutRank : ∀ α β γ δ π ϖ χ ρ υ,
  π = snd α β (case γ δ _ χ ρ υ) → contract π ϖ →
  degree π = maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β γ δ π ϖ χ ρ υ eq Hcontract
  subst_vars; cases Hcontract
  set μ := case γ δ _ χ ρ υ with eq1
  set π := snd α β μ with eq2
  set ρ' := snd α β ρ with eq3
  set υ' := snd α β υ with eq4
  set ϖ := case γ δ _ χ ρ' υ' with eq5
  set psx := prfsize χ with Rpsx
  set psr := prfsize ρ with Rpsr
  set psu := prfsize υ with Rpsu
  intro Hp01; simp [degree, maxDeg] at Hp01
  have Hx : maxDeg χ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      right; left; left; right; simp [self_sp]
  have Hr : maxDeg ρ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      right; left; right; simp [self_sp]
  have Hu : maxDeg υ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      right; right; simp [self_sp]
  have Hm : maxDeg μ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      right; left; left; left; grind
  have Hp0 : degwt π = ⟨sz α + sz β + 1, 1 + psx + psr + psu⟩ := by
    simp [eq2, eq1, psx, psr, psu, degwt]; omega
  have Hr' : cutrank ρ' ≤ cutrank ρ * ⟨sz α + sz β + 1, psr⟩ := by {
    calc
      cutrank ρ' = degwt ρ' * cutrank ρ  := by simp [eq3, cutrank]; ac_rfl
      _ ≤ ⟨sz α + sz β + 1, psr⟩ * cutrank ρ := by
        apply pairAdd_left_monotone; simp [eq3, Rpsr];
        cases ρ <;> simp [degwt, rank_le_rank_iff, prfsize] ; omega
      _ = cutrank ρ * ⟨sz α + sz β + 1, psr⟩ := by ac_rfl
  }
  have Hu' : cutrank υ' ≤ cutrank υ * ⟨sz α + sz β + 1, psu⟩ := by {
    calc
      cutrank υ' = degwt υ' * cutrank υ  := by simp [eq4, cutrank]; ac_rfl
      _ ≤ ⟨sz α + sz β + 1, psu⟩ * cutrank υ := by
        apply pairAdd_left_monotone; simp [eq4, Rpsu];
        cases υ <;> simp [degwt, rank_le_rank_iff, prfsize] ; omega
      _ = cutrank υ  * ⟨sz α + sz β + 1, psu⟩ := by ac_rfl
  }
  have Hvp0 : degwt ϖ ≤ ⟨sz α + sz β + 1, psx⟩ := by {
    simp [Rpsx];
    have A : degree ϖ = 0 ∨ sz γ + sz δ ≤ sz α + sz β := by {
      by_cases D : degree ϖ = 0 <;> try grind
      rw [eq5] at D
      have A : sz γ + sz δ + 1 ≤ degree (case γ δ (α.conj β) χ ρ υ) := by {
        simp [degree]; cases χ <;> simp [degree, degwt] at D <;>
          simp [degwt]
      }
      have B : sz γ + sz δ + 1 ≤ maxDeg π := by {
        simp [degree] at A
        simp [eq2, eq1, maxDeg, cutrank, pairAdd_fst, A]
      }
      rw [maxDeg, ←Hp01, eq2, eq1] at B; simp [degwt] at B; grind
    }
    simp [degree] at A; rcases A with A | A
    · simp [rank_le_rank_iff, A]
    · rw [eq5]; cases χ <;> simp [degwt, rank_le_rank_iff, prfsize] <;> try grind
  }
  -- **** A long sequence of calculations starts. ****
  calc
    cutrank ϖ = degwt ϖ * (cutrank χ * cutrank ρ' * cutrank υ') := by
                                            rw [eq5]; simp [cutrank]; ac_rfl
    _ ≤ ⟨sz α + sz β + 1, psx⟩ * (cutrank χ * cutrank ρ' * cutrank υ') := by
                                          apply pairAdd_left_monotone; assumption
    _ = cutrank ρ' * (⟨sz α + sz β + 1, psx⟩ * (cutrank χ * cutrank υ')) := by ac_rfl
    _ ≤ (cutrank ρ * ⟨sz α + sz β + 1, psr⟩) *
                    (⟨sz α + sz β + 1, psx⟩ * (cutrank χ * cutrank υ')) := by
                                        apply pairAdd_left_monotone; assumption
    _ = cutrank υ' * (⟨sz α + sz β + 1, psx⟩ *
                      ⟨sz α + sz β + 1, psr⟩ * cutrank χ * cutrank ρ) := by ac_rfl
    _ ≤ (cutrank υ * ⟨sz α + sz β + 1, psu⟩) * (⟨sz α + sz β + 1, psx⟩ *
                      ⟨sz α + sz β + 1, psr⟩ * cutrank χ * cutrank ρ) := by
                                            apply pairAdd_left_monotone; assumption
    _ = cutrank χ * cutrank ρ * cutrank υ * (⟨sz α + sz β + 1, psu⟩ *
                ⟨sz α + sz β + 1, psx⟩ * ⟨sz α + sz β + 1, psr⟩) := by ac_rfl
    _ = cutrank χ * cutrank ρ * cutrank υ * ⟨sz α + sz β + 1, psx + psr + psu⟩ := by
                                                simp [pairAdd_eq_same]; grind
    _ < cutrank χ * cutrank ρ * cutrank υ * ⟨sz α + sz β + 1, 1 + psx + psr + psu⟩ := by
              rw [← pairAdd_right_monotone_strict]
              · right; grind
              · simp [goodRank]
              · simp [maxDeg] at *; simp [Hp0] at Hp01; rw [←Hp01] at Hx;
                rw [←Hp01] at Hr; rw [←Hp01] at Hu; simp [pairAdd_fst]; grind
    _ ≤ degwt μ * (cutrank χ * cutrank ρ * cutrank υ *
                  ⟨sz α + sz β + 1, 1 + psx + psr + psu⟩) := by apply le_mul_self
    _ = cutrank π := by rw [eq2,eq1] at Hp0; simp [eq2,eq1, cutrank, Hp0]; ac_rfl

lemma caseCaseCutRank : ∀ α β φ γ δ π ϖ χ ρ υ μ ν,
  π = case α β φ (case γ δ _ χ ρ υ) μ ν → contract π ϖ →
  degree π = maxDeg π → maxDeg μ < maxDeg π →
  maxDeg ν < maxDeg π → cutrank ϖ < cutrank π := by
  intro α β φ γ δ π ϖ χ ρ υ μ ν eq Hcontract
  subst_vars; cases Hcontract
  set κ := case γ δ _ χ ρ υ with eq1
  set π := case α β φ κ μ ν with eq2
  set ρ' := case α β φ ρ μ ν with eq3
  set υ' := case α β φ υ μ ν with eq4
  set ϖ := case γ δ _ χ ρ' υ' with eq5
  set psx := prfsize χ with Rpsx; set psr := prfsize ρ with Rpsr
  set psu := prfsize υ with Rpsu
  set psm := prfsize μ with Rpsm; set psn := prfsize ν with Rpsn
  intro Hp01; simp [degree, maxDeg] at Hp01
  intro Hm; simp [maxDeg] at Hm
  intro Hn; simp [maxDeg] at Hn
  have Hx : maxDeg χ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      left; left; right; left; left; right; simp [self_sp]
  have Hr : maxDeg ρ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      left; left; right; left; right; simp [self_sp]
  have Hu : maxDeg υ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      left; left; right; right; simp [self_sp]
  have Hk : maxDeg κ ≤ maxDeg π := by
    simp [eq2, eq1]; apply maxDeg_sp; simp [subproofs];
      left; left; right; left; left; left; grind
  have Hp0 : degwt π = ⟨sz α + sz β + 1, 1 + psx + psr + psu⟩ := by
    simp [eq2, eq1, psx, psr, psu, degwt]; omega
  have Hr' : cutrank ρ' ≤ cutrank ρ * ⟨sz α + sz β + 1, psr⟩ := by {
    calc
      cutrank ρ' = degwt ρ' * (cutrank ρ * cutrank μ * cutrank ν) := by
                            simp [eq3, cutrank]; ac_rfl
      _ ≤ ⟨sz α + sz β + 1, psr⟩ * (cutrank ρ * cutrank μ * cutrank ν) := by
                    apply pairAdd_left_monotone; simp [eq3, Rpsr];
                    cases ρ <;> simp [degwt, rank_le_rank_iff, prfsize]
      _ = (cutrank μ * cutrank ν) * (cutrank ρ * ⟨sz α + sz β + 1, psr⟩) := by ac_rfl
      _ ≤ cutrank ρ * ⟨sz α + sz β + 1, psr⟩ := by
                apply pairAdd_left_smallerd <;> try grind
                simp [←Hp01, Hp0] at Hm; simp [←Hp01, Hp0] at Hn;
                simp [pairAdd_fst]; grind
  }
  have Hu' : cutrank υ' ≤ cutrank υ * ⟨sz α + sz β + 1, psu⟩ := by {
    calc
      cutrank υ' = degwt υ' * (cutrank υ * cutrank μ * cutrank ν) := by
                            simp [eq4, cutrank]; ac_rfl
      _ ≤ ⟨sz α + sz β + 1, psu⟩ * (cutrank υ * cutrank μ * cutrank ν) := by
                    apply pairAdd_left_monotone; simp [eq4, Rpsu];
                    cases υ <;> simp [degwt, rank_le_rank_iff, prfsize]
      _ = (cutrank μ * cutrank ν) * (cutrank υ * ⟨sz α + sz β + 1, psu⟩) := by ac_rfl
      _ ≤ cutrank υ * ⟨sz α + sz β + 1, psu⟩ := by
                apply pairAdd_left_smallerd <;> try grind
                simp [←Hp01, Hp0] at Hm; simp [←Hp01, Hp0] at Hn;
                simp [pairAdd_fst]; grind
  }
  have Hvp0 : degwt ϖ ≤ ⟨sz α + sz β + 1, psx⟩ := by {
    simp [Rpsx];
    have A : degree ϖ = 0 ∨ sz γ + sz δ ≤ sz α + sz β := by {
      by_cases D : degree ϖ = 0 <;> try grind
      rw [eq5] at D
      have A : sz γ + sz δ + 1 ≤ degree (case γ δ (α.disj β) χ ρ υ) := by {
        simp [degree]; cases χ <;> simp [degree, degwt] at D <;>
          simp [degwt]
      }
      have B : sz γ + sz δ + 1 ≤ maxDeg π := by {
        simp [eq2, eq1];
        apply le_trans (b := maxDeg (case γ δ (α.disj β) χ ρ υ))
        apply le_trans; exact A; apply deg_le_maxDeg;
        apply maxDeg_sp; simp [subproofs]; left; left; right;
          left; left; left; grind
      }
      rw [maxDeg, ←Hp01, eq2, eq1] at B; simp [degwt] at B; grind
    }
    simp [degree] at A; rcases A with A | A
    · simp [rank_le_rank_iff, A]
    · rw [eq5]; cases χ <;> simp [degwt, rank_le_rank_iff, prfsize] <;> try grind
  }
--  **** A long sequence of calculations starts. ****
  calc
    cutrank ϖ = degwt ϖ * (cutrank χ * cutrank ρ' * cutrank υ') := by
                                              simp [eq5, cutrank]; ac_rfl
    _ ≤ ⟨sz α + sz β + 1, psx⟩ * (cutrank χ * cutrank ρ' * cutrank υ') := by
                                    apply pairAdd_left_monotone; assumption
    _ = cutrank ρ' * (⟨sz α + sz β + 1, psx⟩ * (cutrank χ * cutrank υ')) := by ac_rfl
    _ ≤ (cutrank ρ * ⟨sz α + sz β + 1, psr⟩) *
            (⟨sz α + sz β + 1, psx⟩ * (cutrank χ * cutrank υ')) := by
                                    apply pairAdd_left_monotone; assumption
    _ = cutrank υ' * (⟨sz α + sz β + 1, psx⟩ *
                  ⟨sz α + sz β + 1, psr⟩ * cutrank χ * cutrank ρ) := by ac_rfl
    _ ≤ (cutrank υ * ⟨sz α + sz β + 1, psu⟩) * (⟨sz α + sz β + 1, psx⟩ *
                  ⟨sz α + sz β + 1, psr⟩ * cutrank χ * cutrank ρ) := by
                                      apply pairAdd_left_monotone; assumption
    _ = cutrank χ * cutrank ρ * cutrank υ *
        (⟨sz α + sz β + 1, psu⟩ * ⟨sz α + sz β + 1, psx⟩ * ⟨sz α + sz β + 1, psr⟩) :=
                                                                      by ac_rfl
    _ = cutrank χ * cutrank ρ * cutrank υ * ⟨sz α + sz β + 1, psx + psr + psu⟩ := by
                                                simp [pairAdd_eq_same]; grind
    _ < cutrank χ * cutrank ρ * cutrank υ * ⟨sz α + sz β + 1, 1 + psx + psr + psu⟩ := by
              rw [← pairAdd_right_monotone_strict]
              · right; grind
              · simp [goodRank]
              · simp [maxDeg] at *; simp [Hp0] at Hp01; rw [←Hp01] at Hx;
                rw [←Hp01] at Hr; rw [←Hp01] at Hu; simp [pairAdd_fst]; grind
    _ ≤ (cutrank μ * cutrank ν * degwt κ) * (cutrank χ * cutrank ρ * cutrank υ *
                    ⟨sz α + sz β + 1, 1 + psx + psr + psu⟩) := by apply le_mul_self
    _ = cutrank π := by rw [eq2,eq1,Rpsx,Rpsr,Rpsu] at Hp0;
                        rw [eq2,eq1,Rpsx,Rpsr,Rpsu]
                        simp [cutrank, Hp0]; ac_rfl

lemma empCritCutRank : ∀ α π ϖ μ, π = emp α μ → contract π ϖ →
  maxDeg μ < maxDeg π → cutrank ϖ < cutrank π := by
  intro α π ϖ μ eq Hcontract; subst_vars; cases Hcontract
  simp [maxDeg, cutrank, rank_lt_rank_iff]; grind

lemma appCritCutRank : ∀ α β π ϖ μ ν,
  π = app α β μ ν → contract π ϖ →
  degree π = maxDeg π →
  (lrof μ = prcase ∨ lrof μ ≠ prcase ∧ maxDeg μ < maxDeg π) →
  maxDeg ν < maxDeg π → cutrank ϖ < cutrank π := by
  intro α β π ϖ μ ν eq Hcontract; subst_vars
  cases Hcontract <;> simp [lrof]
  · apply appAbsCutRank; rfl; constructor; assumption
  · intro A B C; apply appEmpCutRank; rfl; constructor; assumption
    apply lt_of_lt_of_le'; exact B;
    apply maxDeg_sp; simp [subproofs]; right; simp [self_sp]
    assumption
  · intro A B; apply appCaseCutRank; rfl; constructor; assumption; assumption

lemma fstCritCutRank : ∀ α β π ϖ μ,
  π = fst α β μ → contract π ϖ →
  degree π = maxDeg π →
  (lrof μ = prcase ∨ lrof μ ≠ prcase ∧ maxDeg μ < maxDeg π) →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ μ eq Hcontract; subst_vars
  cases Hcontract <;> simp [lrof]
  · intro A B; apply fstPairCutRank; rfl; constructor; assumption
    all_goals (
      apply lt_of_lt_of_le'
      · exact B
      · apply maxDeg_sp; simp [subproofs];
        all_goals first
        | left; right; simp [self_sp]
        | right; simp [self_sp]
    )
  · intro A B; apply fstEmpCutRank; rfl; constructor; assumption
    apply lt_of_lt_of_le'; exact B; apply maxDeg_sp; simp [subproofs];
    right; simp [self_sp]
  · intro A; apply fstCaseCutRank; rfl; constructor; assumption

lemma sndCritCutRank : ∀ α β π ϖ μ,
  π = snd α β μ → contract π ϖ →
  degree π = maxDeg π →
  (lrof μ = prcase ∨ lrof μ ≠ prcase ∧ maxDeg μ < maxDeg π) →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ μ eq Hcontract; subst_vars
  cases Hcontract <;> simp [lrof]
  · intro A B; apply sndPairCutRank; rfl; constructor; assumption
    all_goals (
      apply lt_of_lt_of_le'
      · exact B
      · apply maxDeg_sp; simp [subproofs];
        all_goals first
        | left; right; simp [self_sp]
        | right; simp [self_sp]
    )
  · intro A B; apply sndEmpCutRank; rfl; constructor; assumption
    apply lt_of_lt_of_le'; exact B; apply maxDeg_sp; simp [subproofs];
    right; simp [self_sp]
  · intro A; apply sndCaseCutRank; rfl; constructor; assumption

lemma caseCritCutRank : ∀ α β δ π ϖ χ μ ν,
  π = case α β δ χ μ ν → contract π ϖ →
  degree π = maxDeg π →
  (lrof χ = prcase ∨ lrof χ ≠ prcase ∧ maxDeg χ < maxDeg π) →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π → cutrank ϖ < cutrank π := by
  intro α β δ π ϖ χ μ ν eq Hcontract; subst_vars
  cases Hcontract <;> simp [lrof]
  · intro A B C D; apply caseLeftCutRank; rfl; constructor; assumption; assumption
    apply lt_of_lt_of_le'; exact B; apply maxDeg_sp; simp [subproofs];
    right; simp [self_sp]; assumption; assumption
  · intro A B C D; apply caseRightCutRank; rfl; constructor; assumption; assumption
    apply lt_of_lt_of_le'; exact B; apply maxDeg_sp; simp [subproofs];
    right; simp [self_sp]; assumption; assumption
  · intro A B C D; apply caseEmpCutRank; rfl; constructor; assumption
    apply lt_of_lt_of_le'; exact B; apply maxDeg_sp; simp [subproofs];
    right; simp [self_sp]; assumption; assumption
  · intro A B; apply caseCaseCutRank; rfl; constructor; assumption; assumption

lemma empStepCutRank : ∀ α π μ μ', π = emp α μ →
  maxDeg μ = maxDeg π →
  oneStep _ μ μ' → cutrank μ' < cutrank μ →
  cutrank (emp α μ') < cutrank π := by
  intro α π μ μ' eq E F G; subst_vars
  have Hμ : 1 ≤ (cutrank μ).1 ∧ 1 ≤ (cutrank μ).2 := by {
    have A : goodRank (cutrank μ) := by apply cutrank_goodRank
    rcases A with ⟨A1,A2⟩ | A <;> try grind
    simp [rank_lt_rank_iff] at G; simp [A1,A2] at G
  }
  simp [cutrank]; by_cases A : α = bot
  · subst_vars; simp [degwt,sz];
    rw [←pairAdd_lt_left_preserved] <;> try grind
  · simp [degwt, A]; rw [←pairAdd_left_monotone_strict]; assumption
    simp [cutrank_goodRank]; simp

lemma absStepCutRank : ∀ α β π μ μ', π = abs α β μ →
  maxDeg μ = maxDeg π → oneStep _ μ μ' → cutrank μ' < cutrank μ →
  cutrank (abs α β μ') < cutrank π := by
  intro α β π μ μ' eq A1 A2 A3
  simp [eq, cutrank, A3]

lemma app1StepCutRank : ∀ α β π μ μ' ν, π = app _ _ μ ν →
  degree π < maxDeg π ∨ lrof μ ≠ prcase →
  maxDeg ν < maxDeg π → maxDeg μ = maxDeg π → oneStep _ μ μ' →
  cutrank μ' < cutrank μ → cutrank (app α β μ' ν) < cutrank π := by
  intro α β π μ μ' ν eq A1 A2 A3 A4 A5; subst_vars
  set A6 := lrofOneStep _ _ _ A4
  have Hμ : 0 < (cutrank μ).1 ∧ 0 < (cutrank μ).2 := by {
    have B : goodRank (cutrank μ) := by apply cutrank_goodRank
    simp [goodRank] at B; rcases B with ⟨B1,B2⟩ | ⟨B1,B2⟩
    simp [rank_lt_rank_iff] at A5; grind; grind
  }
  have Hν : (cutrank ν).1 < (cutrank μ).1 := by {
    simp [maxDeg,cutrank] at A2
    simp [maxDeg,cutrank] at A3; rw [←A3] at A2; assumption
  }
  have A7 : cutrank ν * cutrank μ' < cutrank ν * cutrank μ := by
    rw [←pairAdd_lt_right_preserved]; assumption; grind; grind
  have A8 : degwt (app α β μ' ν) ≤ degwt (app α β μ ν) ∨
            (degwt (app α β μ' ν)).1 < (cutrank μ).1 := by {
    rcases A6 with A6 | ⟨A61,A62⟩ | ⟨A61,A62⟩ | A6
    · right; have B : conc μ' = conc μ := by apply oneStepConcAss at A4; simp [A4]
      rw [←B] at A6; apply lt_of_lt_of_le (b := degree μ)
      · cases μ' <;> simp [degwt] <;> simp [conc,sz] at A6 <;> try grind
      · apply rank_le_proj; apply degwt_le_cutrank
    · left; cases μ <;> simp [lrof] at A62 <;>
        cases μ' <;> simp [lrof] at A61 <;> simp [degwt]
    · left; simp [conc] at A62
    · simp [A6] at A1;
      simp [degree, maxDeg, cutrank] at A1;
      simp[pairAdd_fst] at A1
      have B : (degwt (app α β μ ν)).1 < (cutrank μ).1 := by
        by_cases (cutrank ν).1 ≤ (degwt (app α β μ ν)).1 <;> grind
      have C : (degwt (app α β μ' ν)).1 ≤ sz (α.impl β) := by
        cases μ' <;> simp [degwt, sz]
      have D : (degwt (app α β μ ν)).1 = sz (α.impl β) := by
        cases μ <;> simp [lrof] at A6; simp [degwt, sz]
      right; grind
  }
  have A9 : (degwt (app α β μ ν)).1 ≤ (cutrank μ).1 := by
    simp [maxDeg, cutrank] at A3; rw [A3]; simp [pairAdd_fst]
  simp [cutrank]; rcases A8 with A8 | A8
  · calc
      cutrank μ' * cutrank ν * degwt (app α β μ' ν)
      ≤ cutrank μ' * cutrank ν * degwt (app α β μ ν) := by
                              apply pairAdd_right_monotone; assumption
      _ < cutrank μ * cutrank ν * degwt (app α β μ ν) := by
                              rw [←pairAdd_left_monotone_strict];
                              rw [←pairAdd_left_monotone_strict]; assumption
                              apply cutrank_goodRank; grind;
                              apply goodRank_pairAdd <;> apply cutrank_goodRank
                              simp [pairAdd_fst]; grind
  · calc
      cutrank μ' * cutrank ν * degwt (app α β μ' ν) <
      cutrank μ * cutrank ν * degwt (app α β μ' ν) := by
                            rw [mul_assoc, mul_assoc]
                            rw [←pairAdd_left_monotone_strict]; assumption
                            apply cutrank_goodRank; simp [pairAdd_fst]; grind
      _ ≤ cutrank μ * cutrank ν := by apply pairAdd_right_smallerd;
                                      simp [pairAdd_fst]; grind; grind
      _ ≤ cutrank μ * cutrank ν * degwt (app α β μ ν) := by apply le_self_mul

lemma app2StepCutRank : ∀ α β π (μ : njprf (impl α β)) ν ν',
  π = app _ _ μ ν → maxDeg ν = maxDeg π →
  oneStep _ ν ν' → cutrank ν' < cutrank ν →
  cutrank (app α β μ ν') < cutrank π := by
  intro α β π μ ν ν' eq A1 A2 A3; subst_vars
  have B : (cutrank μ).1 ≤ (cutrank ν).1 := by {
    simp [maxDeg, cutrank] at A1;
    by_cases (cutrank μ).1 ≤ (cutrank ν).1 <;> try assumption
    rw [A1]; simp [pairAdd_fst]
  }
  have C1 : degwt (app α β μ ν) = degwt (app α β μ ν') := by
                                      cases μ <;> simp [degwt]
  have C2 : (degwt (app α β μ ν)).1 ≤ (cutrank ν).1 := by {
    simp [maxDeg, cutrank] at A1; rw [A1]; simp [pairAdd_fst]
  }
  simp [cutrank, C1];
  calc
    cutrank μ * cutrank ν' * degwt (app α β μ ν') <
    cutrank μ * cutrank ν * degwt (app α β μ ν') := by
      rw [← pairAdd_left_monotone_strict];
      rw [← pairAdd_right_monotone_strict]; assumption
      apply cutrank_goodRank; assumption
      apply goodRank_pairAdd <;> apply cutrank_goodRank
      simp_all [pairAdd_fst]

lemma pair1StepCutRank : ∀ α β (π: njprf (conj α β)) μ μ' ν,
  π = pair _ _ μ ν → maxDeg ν < maxDeg π →
  maxDeg μ = maxDeg π → oneStep _ μ μ' →
  cutrank μ' < cutrank μ → cutrank (pair α β μ' ν) < cutrank π := by
  intro α β π μ μ' ν eq A1 A2 A3 A4; subst_vars
  have Hν : (cutrank ν).1 < (cutrank μ).1 := by {
    simp [maxDeg,cutrank, pairAdd_fst] at A1; grind
  }
  simp [cutrank]; rw [←pairAdd_left_monotone_strict]; assumption
  apply cutrank_goodRank; grind

lemma pair2StepCutRank : ∀ α β (π: njprf (conj α β)) μ ν ν',
  π = pair _ _ μ ν → maxDeg ν = maxDeg π →
  oneStep _ ν ν' → cutrank ν' < cutrank ν →
  cutrank (pair α β μ ν') < cutrank π := by
  intro α β π μ ν ν' eq A1 A2 A3; subst_vars
  have Hμ : (cutrank μ).1 ≤ (cutrank ν).1 := by {
    simp [maxDeg,cutrank, pairAdd_fst] at A1; grind
  }
  simp [cutrank]; rw [←pairAdd_right_monotone_strict]; assumption
  apply cutrank_goodRank; grind

lemma fstStepCutRank : ∀ α β π μ μ', π = fst _ _ μ →
  degree π < maxDeg π ∨ lrof μ ≠ prcase →
  maxDeg μ = maxDeg π → oneStep _ μ μ' →
  cutrank μ' < cutrank μ → cutrank (fst α β μ') < cutrank π := by
  intro α β π μ μ' eq A1 A2 A3 A4; subst_vars
  set A5 := lrofOneStep _ _ _ A3
  have A6 : degwt (fst α β μ') ≤ degwt (fst α β μ) ∨
            (degwt (fst α β μ')).1 < (cutrank μ).1 := by {
    rcases A5 with A5 | ⟨A51,A52⟩ | ⟨A51,A52⟩ | A5
    · right; have B : conc μ' = conc μ := by apply oneStepConcAss at A3; simp [A3]
      rw [←B] at A5; apply lt_of_lt_of_le (b := degree μ)
      · cases μ' <;> simp [degwt] <;> simp [conc,sz] at A5 <;> try grind
      · apply rank_le_proj; apply degwt_le_cutrank
    · left; cases μ <;> simp [lrof] at A52 <;>
        cases μ' <;> simp [lrof] at A51 <;> simp [degwt]
    · left; simp [conc] at A52
    · simp [A5] at A1;
      simp [degree, maxDeg, cutrank] at A1;
      simp[pairAdd_fst] at A1;
      have C : (degwt (fst α β μ')).1 ≤ sz (α.conj β) := by
        cases μ' <;> simp [degwt, sz]
      have D : (degwt (fst α β μ)).1 = sz (α.conj β) := by
        cases μ <;> simp [lrof] at A5; simp [degwt, sz]
      right; grind
  }
  have A7 : (degwt (fst α β μ)).1 ≤ (cutrank μ).1 := by
    simp [maxDeg, cutrank] at A2; rw [A2]; simp [pairAdd_fst]
  simp [cutrank]; rcases A6 with A6 | A6
  · calc
      cutrank μ' * degwt (fst α β μ')
      ≤ cutrank μ' * degwt (fst α β μ) := by apply pairAdd_right_monotone; assumption
      _ < cutrank μ *degwt (fst α β μ) := by
                              rw [←pairAdd_left_monotone_strict]; assumption
                              apply cutrank_goodRank; assumption
  · calc
      cutrank μ' * degwt (fst α β μ') <
      cutrank μ * degwt (fst α β μ') := by
                            rw [←pairAdd_left_monotone_strict]; assumption
                            apply cutrank_goodRank; grind
      _ ≤ cutrank μ := by apply pairAdd_right_smallerd; assumption; grind
      _ ≤ cutrank μ * degwt (fst α β μ) := by apply le_self_mul

lemma sndStepCutRank : ∀ α β π μ μ', π = snd _ _ μ →
  degree π < maxDeg π ∨ lrof μ ≠ prcase →
  maxDeg μ = maxDeg π → oneStep _ μ μ' →
  cutrank μ' < cutrank μ → cutrank (snd α β μ') < cutrank π := by
  intro α β π μ μ' eq A1 A2 A3 A4; subst_vars
  set A5 := lrofOneStep _ _ _ A3
  have A6 : degwt (snd α β μ') ≤ degwt (snd α β μ) ∨
            (degwt (snd α β μ')).1 < (cutrank μ).1 := by {
    rcases A5 with A5 | ⟨A51,A52⟩ | ⟨A51,A52⟩ | A5
    · right; have B : conc μ' = conc μ := by apply oneStepConcAss at A3; simp [A3]
      rw [←B] at A5; apply lt_of_lt_of_le (b := degree μ)
      · cases μ' <;> simp [degwt] <;> simp [conc,sz] at A5 <;> try grind
      · apply rank_le_proj; apply degwt_le_cutrank
    · left; cases μ <;> simp [lrof] at A52 <;>
        cases μ' <;> simp [lrof] at A51 <;> simp [degwt]
    · left; simp [conc] at A52
    · simp [A5] at A1;
      simp [degree, maxDeg, cutrank] at A1;
      simp[pairAdd_fst] at A1;
      have C : (degwt (snd α β μ')).1 ≤ sz (α.conj β) := by
        cases μ' <;> simp [degwt, sz]
      have D : (degwt (snd α β μ)).1 = sz (α.conj β) := by
        cases μ <;> simp [lrof] at A5; simp [degwt, sz]
      right; grind
  }
  have A7 : (degwt (snd α β μ)).1 ≤ (cutrank μ).1 := by
    simp [maxDeg, cutrank] at A2; rw [A2]; simp [pairAdd_fst]
  simp [cutrank]; rcases A6 with A6 | A6
  · calc
      cutrank μ' * degwt (snd α β μ')
      ≤ cutrank μ' * degwt (snd α β μ) := by apply pairAdd_right_monotone; assumption
      _ < cutrank μ *degwt (snd α β μ) := by
                              rw [←pairAdd_left_monotone_strict]; assumption
                              apply cutrank_goodRank; assumption
  · calc
      cutrank μ' * degwt (snd α β μ') <
      cutrank μ * degwt (snd α β μ') := by
                            rw [←pairAdd_left_monotone_strict]; assumption
                            apply cutrank_goodRank; grind
      _ ≤ cutrank μ := by apply pairAdd_right_smallerd; assumption; grind
      _ ≤ cutrank μ * degwt (snd α β μ) := by apply le_self_mul


lemma leftStepCutRank : ∀ α β π μ μ', π = left α β μ →
  maxDeg μ = maxDeg π → oneStep _ μ μ' → cutrank μ' < cutrank μ →
  cutrank (left α β μ') < cutrank π := by
  intro α β π μ μ' eq A1 A2 A3
  simp [eq, cutrank, A3]

lemma rightStepCutRank : ∀ α β π μ μ', π = right α β μ →
  maxDeg μ = maxDeg π → oneStep _ μ μ' → cutrank μ' < cutrank μ →
  cutrank (right α β μ') < cutrank π := by
  intro α β π μ μ' eq A1 A2 A3
  simp [eq, cutrank, A3]

lemma case1StepCutRank : ∀ α β δ π χ χ' μ ν, π = case α β δ χ μ ν →
  degree π < maxDeg π ∨ lrof χ ≠ prcase →
  maxDeg ν < maxDeg π → maxDeg μ < maxDeg π →
  maxDeg χ = maxDeg π → oneStep _ χ χ' → cutrank χ' < cutrank χ →
  cutrank (case α β δ χ' μ ν) < cutrank π := by
  intro α β δ π χ χ' μ ν eq A1 A2 A3 A4 A5 A6; subst_vars
  set A7 := lrofOneStep _ _ _ A5
  have Hχ : 0 < (cutrank χ).1 ∧ 0 < (cutrank χ).2 := by {
    have B : goodRank (cutrank χ) := by apply cutrank_goodRank
    simp [goodRank] at B; rcases B with ⟨B1,B2⟩ | ⟨B1,B2⟩
    simp [rank_lt_rank_iff] at A6; grind; grind
  }
  have Hμ : (cutrank μ).1 < (cutrank χ).1 := by {
    simp [maxDeg,cutrank] at A3
    simp [maxDeg,cutrank] at A4; rw [←A4] at A3; assumption
  }
  have Hν : (cutrank ν).1 < (cutrank χ).1 := by {
    simp [maxDeg,cutrank] at A2
    simp [maxDeg,cutrank] at A4; rw [←A4] at A2; assumption
  }
  have A8 : cutrank ν * cutrank μ * cutrank χ' <
              cutrank ν * cutrank μ * cutrank χ := by
    rw [←pairAdd_lt_right_preserved]; assumption; grind;
    rw [pairAdd_le_rank]; grind
  have A9 : degwt (case α β δ χ' μ ν) ≤ degwt (case α β δ χ μ ν) ∨
            (degwt (case α β δ χ' μ ν)).1 < (cutrank χ).1 := by {
    rcases A7 with A7 | ⟨A71,A72⟩ | ⟨A71,A72⟩ | A7
    · right; have B : conc χ' = conc χ := by apply oneStepConcAss at A5; simp [A5]
      rw [←B] at A7; apply lt_of_lt_of_le (b := degree χ)
      · cases χ' <;> simp [degwt] <;> simp [conc,sz] at A7 <;> try grind
      · apply deg_le_maxDeg
    · left; cases χ <;> simp [lrof] at A72 <;>
        cases χ' <;> simp [lrof] at A71 <;> simp [degwt]
    · left; simp [conc] at A72
    · simp [A7] at A1;
      simp [degree, maxDeg, cutrank] at A1;
      simp[pairAdd_fst] at A1
      have B : (degwt (case α β δ χ μ ν)).1 < (cutrank χ).1 := by {
        by_cases (cutrank ν).1 ≤ (degwt (case α β δ χ μ ν)).1 <;> grind
      }
      have C : (degwt (case α β δ χ' μ ν)).1 ≤ sz (α.disj β) := by
        cases χ' <;> simp [degwt, sz]
      have D : (degwt (case α β δ χ μ ν)).1 = sz (α.disj β) := by
        cases χ <;> simp [lrof] at A7; simp [degwt, sz]
      right; grind
  }
  have A10 : (degwt (case α β δ χ μ ν)).1 ≤ (cutrank χ).1 := by
    simp [maxDeg, cutrank] at A4; rw [A4]; simp [pairAdd_fst]
  simp [cutrank]; rcases A9 with A9 | A9
  · calc
      cutrank χ' * cutrank μ * cutrank ν * degwt (case α β δ χ' μ ν)
      ≤ cutrank χ' * cutrank μ * cutrank ν * degwt (case α β δ χ μ ν) := by
                              apply pairAdd_right_monotone; assumption
      _ < cutrank χ * cutrank μ * cutrank ν * degwt (case α β δ χ μ ν) := by
                              rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc];
                              rw [←pairAdd_left_monotone_strict]; assumption
                              apply cutrank_goodRank; simp [pairAdd_fst]; grind
  · calc
      cutrank χ' * cutrank μ * cutrank ν * degwt (case α β δ χ' μ ν)
      < cutrank χ * cutrank μ * cutrank ν * degwt (case α β δ χ' μ ν):= by
                              rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc];
                              rw [←pairAdd_left_monotone_strict]; assumption
                              apply cutrank_goodRank; simp [pairAdd_fst]; grind
      _ ≤ cutrank χ * cutrank μ * cutrank ν := by
                                      apply pairAdd_right_smallerd;
                                      simp [pairAdd_fst]; grind; grind
      _ ≤ cutrank χ * cutrank μ * cutrank ν * degwt (case α β δ χ μ ν) := by
                                      apply le_self_mul

lemma case2StepCutRank : ∀ α β δ π χ μ μ' ν,
  π = case α β δ χ μ ν → maxDeg ν < maxDeg π →
  maxDeg μ  = maxDeg π → oneStep _ μ μ' →
  cutrank μ' < cutrank μ → cutrank (case α β δ χ μ' ν) < cutrank π := by
  intro α β δ π χ μ μ' ν eq A1 A2 A3 A4; subst_vars
  have B : (cutrank χ).1 ≤ (cutrank μ).1 := by {
    simp [maxDeg, cutrank] at A2;
    by_cases (cutrank χ).1 ≤ (cutrank μ).1 <;> try assumption
    rw [A2]; simp [pairAdd_fst]
  }
  have C : (cutrank ν).1 ≤ (cutrank μ).1 := by {
    simp [maxDeg, cutrank] at A2;
    by_cases (cutrank ν).1 ≤ (cutrank μ).1 <;> try assumption
    rw [A2]; simp [pairAdd_fst]
  }
  have D1 : degwt (case α β δ χ μ ν) = degwt (case α β δ χ μ' ν) := by
                                      cases χ <;> simp [degwt]
  have D2 : (degwt (case α β δ χ μ ν)).1 ≤ (cutrank μ).1 := by
    simp [maxDeg, cutrank] at A2; rw [A2]; simp [pairAdd_fst]
  simp [cutrank, D1]
  calc
    cutrank χ * cutrank μ' * cutrank ν * degwt (case α β δ χ μ' ν)
    < cutrank χ * cutrank μ * cutrank ν * degwt (case α β δ χ μ' ν) := by
      rw [← pairAdd_left_monotone_strict]; rw [← pairAdd_left_monotone_strict];
      rw [←pairAdd_right_monotone_strict]; assumption
      apply cutrank_goodRank; assumption
      apply goodRank_pairAdd <;> apply cutrank_goodRank
      simp [pairAdd_fst]; grind
      apply goodRank_pairAdd; apply goodRank_pairAdd;
      apply cutrank_goodRank; apply cutrank_goodRank; apply cutrank_goodRank
      simp_all [pairAdd_fst]

lemma case3StepCutRank : ∀ α β δ π χ μ ν ν',
  π = case α β δ χ μ ν → maxDeg ν = maxDeg π →
  oneStep _ ν ν' → cutrank ν' < cutrank ν →
  cutrank (case α β δ χ μ ν') < cutrank π := by
  intro α β δ π χ μ ν ν' eq A1 A2 A3; subst_vars
  have B : (cutrank χ).1 ≤ (cutrank ν).1 := by {
    simp [maxDeg, cutrank] at A1;
    by_cases (cutrank χ).1 ≤ (cutrank ν).1 <;> try assumption
    rw [A1]; simp [pairAdd_fst]
  }
  have C : (cutrank μ).1 ≤ (cutrank ν).1 := by {
    simp [maxDeg, cutrank] at A1;
    by_cases (cutrank μ).1 ≤ (cutrank ν).1 <;> try assumption
    rw [A1]; simp [pairAdd_fst]
  }
  have D1 : degwt (case α β δ χ μ ν) = degwt (case α β δ χ μ ν') := by
                                      cases χ <;> simp [degwt]
  have D2 : (degwt (case α β δ χ μ ν)).1 ≤ (cutrank ν).1 := by
    simp [maxDeg, cutrank] at A1; rw [A1]; simp [pairAdd_fst]
  simp [cutrank, D1]
  calc
    cutrank χ * cutrank μ * cutrank ν' * degwt (case α β δ χ μ ν') =
    degwt (case α β δ χ μ ν') * (cutrank ν' * (cutrank μ * cutrank χ)) := by ac_rfl
    _ < degwt (case α β δ χ μ ν') * (cutrank ν * (cutrank μ * cutrank χ)) := by
      rw [← pairAdd_right_monotone_strict];
      rw [← pairAdd_left_monotone_strict]; assumption
      apply cutrank_goodRank; rw [pairAdd_le_rank]; grind
      apply goodRank_pairAdd; apply cutrank_goodRank
      apply goodRank_pairAdd <;> apply cutrank_goodRank
      rw [rank_le_pairAdd, rank_le_pairAdd]; simp [←D1, D2]
    _ = cutrank χ * cutrank μ * cutrank ν * degwt (case α β δ χ μ ν') := by ac_rfl

lemma oneStepCutRank : ∀ φ (π π' : njprf φ),
  oneStep _ π π' → cutrank π' < cutrank π := by
  intro φ π π' Hone
  induction Hone
  · apply empCritCutRank <;> assumption
  · apply empStepCutRank <;> assumption
  · apply absStepCutRank <;> assumption
  · apply appCritCutRank <;> assumption
  · apply app1StepCutRank <;> assumption
  · apply app2StepCutRank <;> assumption
  · apply pair1StepCutRank <;> assumption
  · apply pair2StepCutRank <;> assumption
  · apply fstCritCutRank <;> assumption
  · apply fstStepCutRank <;> assumption
  · apply sndCritCutRank <;> assumption
  · apply sndStepCutRank <;> assumption
  · apply leftStepCutRank <;> assumption
  · apply rightStepCutRank <;> assumption
  · apply caseCritCutRank <;> assumption
  · apply case1StepCutRank <;> assumption
  · apply case2StepCutRank <;> assumption
  · apply case3StepCutRank <;> assumption

lemma graftExists : ∀ ψ (ρ : njprf ψ) φ (π : njprf φ), ∃ π', graft ρ π π' := by
  intro ψ ρ φ π; induction π
  · rename_i α; by_cases A : α = ψ
    · subst_vars; exists ρ; apply graft.axgraft_same
    · exists (ax α); apply graft.axgraft_diff; grind
  · rename_i α μ ihμ; rcases ihμ with ⟨μ', ihμ⟩
    exists (emp α μ'); apply graft.empgraft; assumption
  · rename_i α β μ ihμ; rcases ihμ with ⟨μ', ihμ⟩
    exists (abs α β μ'); apply graft.absgraft; assumption
  · rename_i α β μ ν ihμ ihν;
    rcases ihμ with ⟨μ', ihμ⟩; rcases ihν with ⟨ν',ihν⟩
    exists (app α β μ' ν'); apply graft.appgraft <;> assumption
  · rename_i α β μ ν ihμ ihν;
    rcases ihμ with ⟨μ', ihμ⟩; rcases ihν with ⟨ν',ihν⟩
    exists (pair α β μ' ν'); apply graft.pairgraft <;> assumption
  · rename_i α β μ ihμ; rcases ihμ with ⟨μ', ihμ⟩
    exists (fst α β μ'); apply graft.fstgraft; assumption
  · rename_i α β μ ihμ; rcases ihμ with ⟨μ', ihμ⟩
    exists (snd α β μ'); apply graft.sndgraft; assumption
  · rename_i α β μ ihμ; rcases ihμ with ⟨μ', ihμ⟩
    exists (left α β μ'); apply graft.leftgraft; assumption
  · rename_i α β μ ihμ; rcases ihμ with ⟨μ', ihμ⟩
    exists (right α β μ'); apply graft.rightgraft; assumption
  · rename_i α β δ χ μ ν ihχ ihμ ihν; rcases ihχ with ⟨χ', ihχ⟩;
    rcases ihμ with ⟨μ', ihμ⟩; rcases ihν with ⟨ν',ihν⟩
    exists (case α β δ χ' μ' ν'); apply graft.casegraft <;> assumption

lemma empCritExists : ∀ α π μ, π = emp α μ →
  maxDeg μ < maxDeg π → exists ϖ, contract π ϖ := by
  intro α π μ eq A; subst_vars
  by_cases B : α = bot
  · rw [B]; exists μ; apply contract.empBotContract
  · simp [maxDeg, cutrank, pairAdd_fst, degwt, B] at A

lemma appCritExists : ∀ α β π μ ν, π = app α β μ ν → degree π = maxDeg π →
  (lrof μ = prcase ∨ lrof μ ≠ prcase ∧ maxDeg μ < maxDeg π) →
  maxDeg ν < maxDeg π → exists ϖ, contract π ϖ := by
  intro α β π μ ν eq A B C; subst_vars
  cases μ <;> rw [← A] at C <;> simp [degree, degwt] at C
  · rename_i μ; exists (emp β μ); apply contract.appEmpContract
  · rename_i μ; set G := graftExists _ ν _ μ;
    rcases G with ⟨μ', G⟩;
    exists μ'; apply contract.appAbsContract; assumption
  · rename_i γ δ χ ρ υ; exists (case γ δ β χ (app α β ρ ν) (app α β υ ν))
    apply contract.appCaseContract

lemma fstCritExists : ∀ α β π μ, π = fst α β μ → degree π = maxDeg π →
  (lrof μ = prcase ∨ lrof μ ≠ prcase ∧ maxDeg μ < maxDeg π) →
  exists ϖ, contract π ϖ := by
  intro α β π μ eq A B; subst_vars
  cases μ <;> rw [← A] at B <;> simp [lrof, degree, degwt] at B
  · rename_i μ; exists (emp α μ); apply contract.fstEmpContract
  · rename_i μ ν; exists μ; apply contract.fstPairContract
  · rename_i γ δ χ ρ υ; exists (case γ δ α χ (fst α β ρ) (fst α β υ))
    apply contract.fstCaseContract

lemma sndCritExists : ∀ α β π μ, π = snd α β μ → degree π = maxDeg π →
  (lrof μ = prcase ∨ lrof μ ≠ prcase ∧ maxDeg μ < maxDeg π) →
  exists ϖ, contract π ϖ := by
  intro α β π μ eq A B; subst_vars
  cases μ <;> rw [← A] at B <;> simp [lrof, degree, degwt] at B
  · rename_i μ; exists (emp β μ); apply contract.sndEmpContract
  · rename_i μ ν; exists ν; apply contract.sndPairContract
  · rename_i γ δ χ ρ υ; exists (case γ δ β χ (snd α β ρ) (snd α β υ))
    apply contract.sndCaseContract

lemma caseCritExists : ∀ α β δ π χ μ ν, π = case α β δ χ μ ν →
  degree π = maxDeg π →
  (lrof χ = prcase ∨ lrof χ ≠ prcase ∧ maxDeg χ < maxDeg π) →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π → ∃ ϖ, contract π ϖ := by
  intro α β δ π χ μ ν eq A B C D; subst_vars
  cases χ <;> rw [← A] at C <;> simp [degree, degwt] at C
  · rename_i χ; exists (emp δ χ); apply contract.caseEmpContract
  · rename_i χ; set G := graftExists _ χ _ μ;
    rcases G with ⟨χ', G⟩;
    exists χ'; apply contract.caseLeftContract; assumption
  · rename_i χ; set G := graftExists _ χ _ ν;
    rcases G with ⟨χ', G⟩;
    exists χ'; apply contract.caseRightContract; assumption
  · rename_i γ1 γ2 χ ρ υ; exists (case γ1 γ2 δ χ (case α β δ ρ μ ν) (case α β δ υ μ ν))
    apply contract.caseCaseContract

lemma empCritCondition : ∀ α μ π, π = emp α μ →
  maxDeg μ ≠ maxDeg π → maxDeg μ < maxDeg π := by
  intro α μ π eq A
  have B : maxDeg μ ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; right; simp [self_sp]
  grind

lemma app1StepCondition : ∀ α β μ ν π, π = app α β μ ν →
  maxDeg ν ≠ maxDeg π → maxDeg ν < maxDeg π := by
  intro α β μ ν π eq A
  have B : maxDeg ν ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; right; simp [self_sp]
  grind

lemma appCritCondition : ∀ α β μ ν π, π = app α β μ ν →
  maxDeg ν ≠ maxDeg π → ¬(maxDeg μ = maxDeg π ∧
  (degree π < maxDeg π ∨ lrof μ ≠ prcase)) →
  degree π = maxDeg π ∧
  (lrof μ = prcase ∨ lrof μ ≠ prcase ∧ maxDeg μ < maxDeg π) := by
  intro α β μ ν π eq A B
  have C : maxDeg ν < maxDeg π := by apply app1StepCondition <;> assumption
  have D : maxDeg μ ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; left; right; simp [self_sp]
  have E : degree π ≤ maxDeg π := by apply deg_le_maxDeg
  by_cases F : degree π < maxDeg π
  · simp [F] at B
    simp [eq, degree, maxDeg, cutrank, pairAdd_fst] at F
    simp [eq, maxDeg, cutrank, pairAdd_fst] at C
    exfalso; apply B; simp [eq, maxDeg, cutrank, pairAdd_fst]
    rcases C with C | C <;> rcases F with F | F <;> try grind
  · constructor <;> try grind

lemma pair1StepCondition : ∀ α β μ ν π, π = pair α β μ ν →
  maxDeg ν ≠ maxDeg π → maxDeg ν < maxDeg π ∧ maxDeg μ = maxDeg π := by
  intro α β μ ν π eq A
  have B : maxDeg ν ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; right; simp [self_sp]
  have C : maxDeg ν < maxDeg π := by grind
  simp [C]; simp [maxDeg] at *
  simp [eq, cutrank, pairAdd_fst] at C
  simp [eq, cutrank, C]

lemma fstCritCondition : ∀ α β μ π, π = fst α β μ →
 ¬(maxDeg μ = maxDeg π ∧ (degree π < maxDeg π ∨ lrof μ ≠ prcase)) →
  degree π = maxDeg π ∧ (lrof μ = prcase ∨
                          lrof μ ≠ prcase ∧ maxDeg μ < maxDeg π) := by
  intro α β μ π eq A
  have B : maxDeg μ ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; right; simp [self_sp]
  have C : degree π ≤ maxDeg π := by apply deg_le_maxDeg
  by_cases D : degree π < maxDeg π
  · simp [D] at A
    simp [eq, degree, maxDeg, cutrank, pairAdd_fst] at D
    exfalso; apply A; simp [eq, maxDeg, cutrank, pairAdd_fst]; grind
  · constructor <;> try grind

lemma sndCritCondition : ∀ α β μ π, π = snd α β μ →
 ¬(maxDeg μ = maxDeg π ∧ (degree π < maxDeg π ∨ lrof μ ≠ prcase)) →
  degree π = maxDeg π ∧ (lrof μ = prcase ∨
                          lrof μ ≠ prcase ∧ maxDeg μ < maxDeg π) := by
  intro α β μ π eq A
  have B : maxDeg μ ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; right; simp [self_sp]
  have C : degree π ≤ maxDeg π := by apply deg_le_maxDeg
  by_cases D : degree π < maxDeg π
  · simp [D] at A
    simp [eq, degree, maxDeg, cutrank, pairAdd_fst] at D
    exfalso; apply A; simp [eq, maxDeg, cutrank, pairAdd_fst]; grind
  · constructor <;> try grind

lemma case2StepCondition : ∀ α β δ χ μ ν π, π = case α β δ χ μ ν →
  maxDeg ν ≠ maxDeg π → maxDeg ν < maxDeg π := by
  intro α β δ χ μ ν π eq A
  have B : maxDeg ν ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; right; simp [self_sp]
  grind

lemma case1StepCondition : ∀ α β δ χ μ ν π, π = case α β δ χ μ ν →
  maxDeg ν ≠ maxDeg π → maxDeg μ ≠ maxDeg π →
  maxDeg ν < maxDeg π ∧ maxDeg μ < maxDeg π := by
  intro α β δ χ μ ν π eq A B
  constructor
  · apply case2StepCondition <;> assumption
  · have C : maxDeg μ ≤ maxDeg π := by
      apply maxDeg_sp; simp [eq, subproofs]; left; right; simp [self_sp]
    grind

lemma caseCritCondition : ∀ α β δ χ μ ν π, π = case α β δ χ μ ν →
  maxDeg ν ≠ maxDeg π → maxDeg μ ≠ maxDeg π →
  ¬(maxDeg χ = maxDeg π ∧ (degree π < maxDeg π ∨ lrof χ ≠ prcase)) →
  degree π = maxDeg π ∧
  (lrof χ = prcase ∨ lrof χ ≠ prcase ∧ maxDeg χ < maxDeg π) := by
  intro α β δ χ μ ν π eq A B C
  have D : maxDeg ν < maxDeg π ∧ maxDeg μ < maxDeg π := by
          apply case1StepCondition <;> assumption
  rcases D with ⟨D1, D2⟩
  have E : maxDeg χ ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; left; left; right; simp [self_sp]
  have F : degree π ≤ maxDeg π := by apply deg_le_maxDeg
  by_cases G : degree π < maxDeg π
  · simp [G] at C
    simp [eq, degree, maxDeg, cutrank, pairAdd_fst] at G
    simp [eq, maxDeg, cutrank, pairAdd_fst] at D1
    simp [eq, maxDeg, cutrank, pairAdd_fst] at D2
    exfalso; apply C; simp [eq, maxDeg, cutrank, pairAdd_fst]
    simp [maxDeg] at *
    rcases D1 with D1 | D1 | D1 <;> rcases D2 with D2 | D2 <;>
      rcases G with G | G | G  <;> try grind
  · constructor <;> try grind

lemma oneStepExists : ∀ φ (π : njprf φ),
  maxDeg π > 0 → ∃ π', oneStep _ π π' := by
  intro φ π
  induction π <;> clear φ <;> intro Hmd
  · -- ax
    rename_i α; simp [maxDeg, cutrank, degwt] at Hmd
  · -- emp
    rename_i α μ ihμ
    by_cases B0 : maxDeg μ = maxDeg (emp α μ)
    · rw [←B0] at Hmd; rcases ihμ Hmd with ⟨μ', Hstep⟩
      exists (emp α μ'); apply oneStep.empStep
      rfl; grind; grind
    · have B1 : maxDeg μ < maxDeg (emp α μ) := by
        apply empCritCondition; rfl; grind
      have B2 : ∃ ϖ, contract (emp α μ) ϖ := by
        apply empCritExists; rfl; exact B1
      rcases B2 with ⟨ϖ, cont⟩
      exists ϖ; apply oneStep.empCrit; rfl; exact cont; assumption
  · -- abs
    rename_i α β μ ihμ
    have B0 : maxDeg μ = maxDeg (abs α β μ) := by simp [maxDeg, cutrank]
    rcases ihμ Hmd with ⟨μ', step⟩
    exists (abs α β μ'); apply oneStep.absStep
    rfl; grind; grind
  · -- app
    rename_i α β μ ν ihμ ihν
    by_cases B0 : maxDeg ν = maxDeg (app α β μ ν)
    · rw [←B0] at Hmd; rcases ihν Hmd with ⟨ν', step⟩
      exists (app α β μ ν'); apply oneStep.app2Step
      rfl; assumption; assumption
    · have B1 : maxDeg ν < maxDeg (app α β μ ν) := by
        apply app1StepCondition; rfl; grind
      by_cases B2 : maxDeg μ = maxDeg (app α β μ ν) ∧
        (degree (app α β μ ν) < maxDeg (app α β μ ν) ∨ lrof μ ≠ prcase)
      · rw [←B2.1] at Hmd; rcases ihμ Hmd with ⟨μ', step⟩
        exists (app α β μ' ν); apply oneStep.app1Step
        rfl; grind; grind; grind; grind
      · have B3 : degree (app α β μ ν) = maxDeg (app α β μ ν) ∧
            (lrof μ = prcase ∨ lrof μ ≠ prcase ∧ maxDeg μ < maxDeg (app α β μ ν))  := by
          apply appCritCondition; rfl; grind; assumption
        have cont : ∃ ϖ, contract (app α β μ ν) ϖ := by
            apply appCritExists; rfl; grind; grind; grind
        rcases cont with ⟨ϖ, cont⟩; exists ϖ; apply oneStep.appCrit
        rfl; assumption; grind; grind; grind
  · -- pair
    rename_i α β μ ν ihμ ihν
    by_cases B0 : maxDeg ν = maxDeg (pair α β μ ν)
    · rw [←B0] at Hmd; rcases ihν Hmd with ⟨ν', step⟩
      exists (pair α β μ ν'); apply oneStep.pair2Step
      rfl; grind; grind
    · have B1 : maxDeg ν < maxDeg (pair α β μ ν) ∧
                maxDeg μ = maxDeg (pair α β μ ν) := by
        apply pair1StepCondition; rfl; grind
      rcases B1 with ⟨B11, B12⟩
      rw [←B12] at Hmd; rcases ihμ Hmd with ⟨μ',step⟩
      exists (pair α β μ' ν); apply oneStep.pair1Step
      rfl; grind; grind; grind
  · -- fst
    rename_i α β μ ihμ
    by_cases B0 : maxDeg μ = maxDeg (fst α β μ) ∧
      (degree (fst α β μ) < maxDeg (fst α β μ) ∨ lrof μ ≠ prcase)
    · rw [←B0.1] at Hmd; rcases ihμ Hmd with ⟨μ', step⟩
      exists (fst α β μ'); apply oneStep.fstStep
      rfl; grind; grind; grind
    · have B1 : degree (fst α β μ) = maxDeg (fst α β μ) ∧
        (lrof μ = prcase ∨ lrof μ ≠ prcase ∧ maxDeg μ < maxDeg (fst α β μ))  := by
        apply fstCritCondition; rfl; grind
      have cont : ∃ ϖ, contract (fst α β μ) ϖ := by
        apply fstCritExists; rfl; grind; grind
      rcases cont with ⟨ϖ, cont⟩; exists ϖ; apply oneStep.fstCrit
      rfl; assumption; grind; grind
  · -- snd
    rename_i α β μ ihμ
    by_cases B0 : maxDeg μ = maxDeg (snd α β μ) ∧
      (degree (snd α β μ) < maxDeg (snd α β μ) ∨ lrof μ ≠ prcase)
    · rw [←B0.1] at Hmd; rcases ihμ Hmd with ⟨μ', step⟩
      exists (snd α β μ'); apply oneStep.sndStep
      rfl; grind; grind; grind
    · have B1 : degree (snd α β μ) = maxDeg (snd α β μ) ∧
        (lrof μ = prcase ∨ lrof μ ≠ prcase ∧ maxDeg μ < maxDeg (snd α β μ))  := by
        apply sndCritCondition; rfl; grind
      have cont : ∃ ϖ, contract (snd α β μ) ϖ := by
        apply sndCritExists; rfl; grind; grind
      rcases cont with ⟨ϖ, cont⟩; exists ϖ; apply oneStep.sndCrit
      rfl; assumption; grind; grind
  · -- left
    rename_i α β μ ihμ
    have B0 : maxDeg μ = maxDeg (left α β μ) := by simp [maxDeg, cutrank]
    rcases ihμ Hmd with ⟨μ', step⟩
    exists (left α β μ'); apply oneStep.leftStep
    rfl; grind; grind
  · -- right
    rename_i α β μ ihμ
    have B0 : maxDeg μ = maxDeg (right α β μ) := by simp [maxDeg, cutrank]
    rcases ihμ Hmd with ⟨μ', step⟩
    exists (right α β μ'); apply oneStep.rightStep
    rfl; grind; grind
  · -- case
    rename_i α β δ χ μ ν ihχ ihμ ihν
    by_cases B0 : maxDeg ν = maxDeg (case α β δ χ μ ν)
    · rw [←B0] at Hmd; rcases ihν Hmd with ⟨ν', step⟩
      exists (case α β δ χ μ ν'); apply oneStep.case3Step
      rfl; assumption; assumption
    · have B1 : maxDeg ν < maxDeg (case α β δ χ μ ν) := by
        apply case2StepCondition; rfl; grind
      by_cases B2 : maxDeg μ = maxDeg (case α β δ χ μ ν)
      · rw [←B2] at Hmd; rcases ihμ Hmd with ⟨μ', step⟩
        exists (case α β δ χ μ' ν); apply oneStep.case2Step
        rfl; assumption; assumption; assumption
      · have B3 : maxDeg μ < maxDeg (case α β δ χ μ ν) := by
          apply And.right; apply case1StepCondition; rfl; grind; grind
        by_cases B4 : maxDeg χ = maxDeg (case α β δ χ μ ν) ∧
          (degree (case α β δ χ μ ν) < maxDeg (case α β δ χ μ ν)
                    ∨ lrof χ ≠ prcase)
        · rw [←B4.1] at Hmd; rcases ihχ Hmd with ⟨χ', step⟩
          exists (case α β δ χ' μ ν); apply oneStep.case1Step
          rfl; grind; grind; grind; grind; grind
        · have B5 : degree (case α β δ χ μ ν) = maxDeg (case α β δ χ μ ν) ∧
              (lrof χ = prcase ∨
                lrof χ ≠ prcase ∧ maxDeg χ < maxDeg (case α β δ χ μ ν))  := by
            apply caseCritCondition; rfl; grind; assumption; grind
          have cont : ∃ ϖ, contract (case α β δ χ μ ν) ϖ := by
              apply caseCritExists; rfl; grind; grind; grind; grind
          rcases cont with ⟨ϖ, cont⟩; exists ϖ; apply oneStep.caseCrit
          rfl; assumption; grind; grind; grind; grind

lemma cr_wf {φ : propform} : WellFounded
  (fun (ϖ π : njprf φ) ↦ cutrank ϖ < cutrank π) := by
  exact InvImage.wf cutrank (WellFoundedRelation.wf)

theorem normalization : ∀ φ (π : njprf φ), ∃ (ϖ : njprf φ),
  isNormal ϖ ∧ hypos ϖ ⊆ hypos π ∧ conc ϖ = conc π := by
  intro φ υ
  apply WellFounded.induction (cr_wf)
    (C := fun π : njprf φ => ∃ (ϖ : njprf φ),
        isNormal ϖ ∧ hypos ϖ ⊆ hypos π ∧ conc ϖ = conc π)
  clear υ; intro π
  by_cases d : isNormal π
  · intros; exists π
  · have e : maxDeg π > 0  := by {
      rw [normal_cutrank] at d
      have e : ¬maxDeg π = 0 := by
        simp [maxDeg]; intro A; apply d;
        rcases cutrank_goodRank _ π with f | f
        · ext <;> grind
        · grind
      grind
    }
    have g : ∃ χ, oneStep _ π χ := by {
      exact oneStepExists _ π e
    }
    rcases g with ⟨χ, g⟩
    let f := oneStepConcAss _ π χ g
    rcases f with ⟨f1, f2⟩
    let e := oneStepCutRank _ π χ g
    intro ih; apply ih χ at e
    rcases e with ⟨ϖ, e1, e2, e3⟩
    exists ϖ; grind

end njNorm
