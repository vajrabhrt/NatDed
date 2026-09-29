import Mathlib
import NatDed.nk
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

namespace nkNorm
open Rank
open nk
open nk.propform
open nk.nkprf
open nk.proofrule

inductive isCut : {φ : propform} → nkprf φ → Prop where
| appAbs : ∀ α β μ ν, isCut (app α β (abs α β μ) ν)
| fstPair : ∀ α β μ ν, isCut (fst α β (pair α β μ ν))
| sndPair : ∀ α β μ ν, isCut (snd α β (pair α β μ ν))
| caseLeft : ∀ α β χ μ ν, isCut (case α β (left α β χ) μ ν)
| caseRight : ∀ α β χ μ ν, isCut (case α β (right α β χ) μ ν)
| raaBot : ∀ μ, isCut (raa bot μ)
| raaNeg : ∀ α μ, isCut (raa (neg α) μ)
| appRaa : ∀ α β μ ν, isCut (app α β (raa (impl α β) μ) ν)
| fstRaa : ∀ α β μ, isCut (fst α β (raa (conj α β) μ))
| sndRaa : ∀ α β μ, isCut (snd α β (raa (conj α β) μ))
| caseRaa : ∀ α β χ μ ν, isCut (case α β (raa (disj α β) χ) μ ν)

inductive isNormal : {φ : propform} → nkprf φ → Prop where
| axNorm : ∀ α π, π = ax α → isNormal π
| raaNorm : ∀ α μ π, π = raa α μ → isNormal μ → ¬isCut π → isNormal π
| absNorm : ∀ α β μ π, π = abs α β μ → isNormal μ → isNormal π
| appNorm : ∀ α β μ ν π, π = app α β μ ν → isNormal μ → isNormal ν →
                                      ¬isCut π → isNormal π
| pairNorm : ∀ α β μ ν π, π = pair α β μ ν → isNormal μ → isNormal ν → isNormal π
| fstNorm : ∀ α β μ π, π = fst α β μ → isNormal μ → ¬isCut π → isNormal π
| sndNorm : ∀ α β μ π, π = snd α β μ → isNormal μ → ¬isCut π → isNormal π
| leftNorm : ∀ α β μ π, π = left α β μ → isNormal μ → isNormal π
| rightNorm : ∀ α β μ π, π = right α β μ → isNormal μ → isNormal π
| caseNorm : ∀ α β χ μ ν π, π = case α β χ μ ν → isNormal χ → isNormal μ →
                          isNormal ν → ¬isCut π → isNormal π

def degwt {φ} (π: nkprf φ) : Rank :=
  match π with
  | app α β (nkprf.abs _ _ _) _                   => ⟨sz α + sz β + 1, 1⟩
  | fst α β (pair _ _ _ _ )                       => ⟨sz α + sz β + 1, 1⟩
  | snd α β (pair _ _ _ _ )                       => ⟨sz α + sz β + 1, 1⟩
  | case α β (left _ _ _) _ _                     => ⟨sz α + sz β + 1, 1⟩
  | case α β (right _ _ _) _ _                    => ⟨sz α + sz β + 1, 1⟩
  | raa bot _                                     => ⟨2, 1⟩
  | raa (impl α bot) _                            => ⟨sz α + 4, 1⟩
  | app α β (raa _ _) _                           => ⟨sz α + sz β + 2, 1⟩
  | fst α β (raa _ _)                             => ⟨sz α + sz β + 2, 1⟩
  | snd α β (raa _ _)                             => ⟨sz α + sz β + 2, 1⟩
  | case α β (raa _ _) _ _                        => ⟨sz α + sz β + 2, 1⟩
  | _                                             => ⟨0, 0⟩
def cutrank {φ} (π: nkprf φ) : Rank :=
  match π with
  | .ax _ => degwt π
  | .raa _ μ => cutrank μ * degwt π
  | .abs _ _ μ => cutrank μ
  | .app _ _ μ ν => cutrank μ * cutrank ν * degwt π
  | .pair _ _ μ ν => cutrank μ * cutrank ν
  | .fst _ _ μ =>  cutrank μ * degwt π
  | .snd _ _ μ =>  cutrank μ * degwt π
  | .left _ _ μ => cutrank μ
  | .right _ _ μ => cutrank μ
  | .case α β χ μ ν => cutrank χ * cutrank μ * cutrank ν * degwt π

def degree {φ} (π: nkprf φ) : ℕ := (degwt π).1
def weight {φ} (π: nkprf φ) : ℕ := (degwt π).2
def maxDeg {φ} (π: nkprf φ) : ℕ := (cutrank π).1

@[simp]
lemma isNormal_iff : ∀ φ (π : nkprf φ), isNormal π ↔ ∀ ψ ϖ, ⟨ψ, ϖ⟩ ∈ subproofs π → isNormal ϖ := by
  intro φ π; constructor <;> intro H
  · induction H <;> intro ψ ϖ G <;> subst_vars <;>
      simp [subproofs] at G
    · cases G; constructor; rfl
    · rcases G with (G | G); rcases G; apply isNormal.raaNorm
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
lemma degwt_goodRank : ∀ φ (π : nkprf φ), goodRank (degwt π) := by
  intro φ π; cases π <;> simp [goodRank, degwt] <;> split <;> try grind

@[simp]
lemma cutrank_goodRank : ∀ φ (π : nkprf φ), goodRank (cutrank π) := by
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

lemma cutrank_sp : ∀ φ ψ (π : nkprf φ) (μ : nkprf ψ),
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
  · rename_i α β π1 π2 π3 ih1 ih2 ih3; rcases H with ((H | H) | H) | H
    · cases H; grind
    · simp [cutrank]; apply rank_le_rank_mul; apply rank_le_rank_mul;
      apply rank_le_rank_mul; grind
    · simp [cutrank]; apply rank_le_rank_mul; apply rank_le_rank_mul;
      apply rank_le_mul_rank; grind
    · simp [cutrank]; apply rank_le_rank_mul; apply rank_le_mul_rank;
      grind

lemma degwt_le_cutrank : ∀ φ (π : nkprf φ), degwt π ≤ cutrank π := by
  intro φ π; cases π <;> simp [cutrank]
  all_goals first
    | exact le_self_mul
    | exact le_mul_self
    | simp [degwt]

lemma deg_le_maxDeg : ∀ φ (π : nkprf φ), degree π ≤ maxDeg π := by
  intros; simp [degree, maxDeg];
  apply rank_le_proj; apply degwt_le_cutrank

lemma maxDeg_sp : ∀ φ ψ (π : nkprf φ) (μ : nkprf ψ),
  ⟨ψ, μ⟩ ∈ subproofs π → maxDeg μ ≤ maxDeg π := by
  intros; simp [maxDeg]; apply rank_le_proj
  apply cutrank_sp; assumption

lemma deg_degwt_0 : ∀ φ (π : nkprf φ), degree π = 0 ↔ degwt π = ⟨0,0⟩ := by
  intros φ π;
  rcases E : degwt π with ⟨d,w⟩
  have H : goodRank ⟨d,w⟩ := by (rw [←E]; apply degwt_goodRank)
  simp [degree, goodRank, E] at *; grind

lemma degreeOfCut : ∀ φ (π : nkprf φ), isCut π ↔ degree π > 0 := by
  intros φ π; constructor
  · intro H; cases H <;> simp [degree, degwt,neg]
  · intro E; cases π <;> unfold degree at E <;> simp [degwt] at E <;>
      split at E <;> try grind
    all_goals
      rename_i eq; rw [eq]; constructor

lemma normal_cutrank : ∀ φ (π : nkprf φ), isNormal π ↔ cutrank π = ⟨0,0⟩ := by
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
    · rename_i α β χ μ ν E F G ihχ ihμ ihν H; simp [ihχ, ihμ, ihν]
      rw [←deg_degwt_0]; rw [degreeOfCut] at H; grind
  · induction π
    · apply isNormal.axNorm; rfl
    · rename_i α μ ihμ; simp [cutrank] at H
      rcases H with ⟨H1,H2⟩
      apply ihμ at H1
      simp [←deg_degwt_0] at H2
      apply isNormal.raaNorm; rfl; assumption;
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
    · rename_i α β χ μ ν ihχ ihμ ihν; simp [cutrank] at H
      rcases H with ⟨⟨⟨H1,H2⟩,H3⟩,H4⟩
      apply ihχ at H1; apply ihμ at H2; apply ihν at H3
      simp [←deg_degwt_0] at H4
      apply isNormal.caseNorm; rfl;
      assumption; assumption; assumption
      intro A; rw [degreeOfCut] at A; grind

inductive graft {φ} (ρ : nkprf φ) : {ψ : propform} → nkprf ψ → nkprf ψ → Prop
  | axgraft_same : graft ρ (ax φ) ρ
  | axgraft_diff : ∀ ψ, ψ ≠ φ → graft ρ (ax ψ) (ax ψ)
  | raagraft : ∀ α μ μ', graft ρ μ μ' → graft ρ (raa α μ) (raa α μ')
  | absgraft : ∀ α β μ μ', graft ρ μ μ' → graft ρ (abs α β μ) (abs α β μ')
  | appgraft : ∀ α β μ μ' ν ν', graft ρ μ μ' → graft ρ ν ν' →
                            graft ρ (app α β μ ν) (app α β μ' ν')
  | pairgraft : ∀ α β μ μ' ν ν', graft ρ μ μ' → graft ρ ν ν' →
                            graft ρ (pair α β μ ν) (pair α β μ' ν')
  | fstgraft : ∀ α β μ μ', graft ρ μ μ' →
                            graft ρ (fst α β μ) (fst α β μ')
  | sndgraft : ∀ α β μ μ', graft ρ μ μ' →
                            graft ρ (snd α β μ) (snd α β μ')
  | leftgraft : ∀ α β μ μ', graft ρ μ μ' → graft ρ (left α β μ) (left α β μ')
  | rightgraft : ∀ α β μ μ', graft ρ μ μ' → graft ρ (right α β μ) (right α β μ')
  | casegraft : ∀ α β χ χ' μ μ' ν ν', graft ρ χ χ' →
                  graft ρ μ μ' → graft ρ ν ν' →
                  graft ρ (case α β χ μ ν) (case α β χ' μ' ν')

inductive elimBot : {σ : propform} →  nkprf σ → nkprf σ → Prop
| ax1_eb        : elimBot (ax (neg bot)) (abs bot _ (ax bot))
| ax2_eb        : ∀ α, α ≠ neg bot → elimBot (ax α) (ax α)
| raa_eb        : ∀ α μ μ', elimBot μ μ' → elimBot (raa α μ) (raa α μ')
| abs_eb        : ∀ α β μ μ', elimBot μ μ' → elimBot (abs α β μ) (abs α β μ')
| app_axraa_eb  : ∀ μ μ', elimBot μ μ' → elimBot
                              (app _ _ (ax (neg bot)) (raa _ μ)) μ'
| app_ax_eb     : ∀ μ μ', lrof μ ≠ prraa → elimBot μ μ' → elimBot
                              (app _ _ (ax (neg bot)) μ) μ'
| app_eb        : ∀ α β μ ν μ' ν', lrof μ ≠ prax ∨ conc μ ≠ neg bot →
                              elimBot μ μ' → elimBot ν ν' →
                              elimBot (app α β μ ν) (app α β μ' ν')
| pair_eb       : ∀ α β μ ν μ' ν', elimBot μ μ' → elimBot ν ν' →
                              elimBot (pair α β μ ν) (pair α β μ' ν')
| fst_eb        : ∀ α β μ μ', elimBot μ μ' → elimBot (fst α β μ) (fst α β μ')
| snd_eb        : ∀ α β μ μ', elimBot μ μ' → elimBot (snd α β μ) (snd α β μ')
| left_eb       : ∀ α β μ μ', elimBot μ μ' → elimBot (left α β μ) (left α β μ')
| right_eb      : ∀ α β μ μ', elimBot μ μ' → elimBot (right α β μ) (right α β μ')
| case_eb       : ∀ α β χ μ ν χ' μ' ν',
                              elimBot χ χ' → elimBot μ μ' → elimBot ν ν' →
                              elimBot (case α β χ μ ν) (case α β χ' μ' ν')

inductive elimNeg (φ : propform): {σ : propform} →  nkprf σ → nkprf σ → Prop
| ax1_en        : elimNeg φ (ax (neg (φ.impl bot)))
                          (abs (neg φ) bot (app _ _ (ax (neg φ)) (ax φ)))
| ax2_en        : ∀ α, α ≠ neg (φ.impl bot) → elimNeg φ (ax α) (ax α)
| raa_en        : ∀ α μ μ', elimNeg φ μ μ' → elimNeg φ (raa α μ) (raa α μ')
| abs_en        : ∀ α β μ μ', elimNeg φ μ μ' → elimNeg φ (abs α β μ) (abs α β μ')
| app_axraa_en  : ∀ μ μ', elimNeg φ μ μ' → elimNeg φ
                              (app _ _ (ax (neg (φ.impl bot))) (raa _ μ)) μ'
| app_ax_en     : ∀ μ μ', lrof μ ≠ prraa → elimNeg φ μ μ' → elimNeg φ
                              (app _ _ (ax (neg (φ.impl bot))) μ)
                              (app _ _ μ' (ax φ))
| app_en        : ∀ α β μ ν μ' ν', lrof μ ≠ prax ∨ conc μ ≠ neg (φ.impl bot) →
                              elimNeg φ μ μ' → elimNeg φ ν ν' →
                              elimNeg φ (app α β μ ν) (app α β μ' ν')
| pair_en       : ∀ α β μ ν μ' ν', elimNeg φ μ μ' → elimNeg φ ν ν' →
                              elimNeg φ (pair α β μ ν) (pair α β μ' ν')
| fst_en        : ∀ α β μ μ', elimNeg φ μ μ' →
                              elimNeg φ (fst α β μ) (fst α β μ')
| snd_en        : ∀ α β μ μ', elimNeg φ μ μ' →
                              elimNeg φ (snd α β μ) (snd α β μ')
| left_en       : ∀ α β μ μ', elimNeg φ μ μ' →
                              elimNeg φ (left α β μ) (left α β μ')
| right_en      : ∀ α β μ μ', elimNeg φ μ μ' →
                              elimNeg φ (right α β μ) (right α β μ')
| case_en       : ∀ α β χ μ ν χ' μ' ν',
                              elimNeg φ χ χ' → elimNeg φ μ μ' →
                              elimNeg φ ν ν' →
                              elimNeg φ (case α β χ μ ν) (case α β χ' μ' ν')

inductive elimApp (φ ψ : propform) (υ : nkprf φ) :
                              {σ : propform} →  nkprf σ → nkprf σ → Prop
| ax1_ea        : elimApp φ ψ υ (ax (neg (φ.impl ψ)))
                          (abs (φ.impl ψ) _ (app _ _ (ax (neg ψ))
                                    (app _ _ (ax (φ.impl ψ)) υ)))
| ax2_ea        : ∀ α, α ≠ neg (φ.impl ψ) → elimApp φ ψ υ (ax α) (ax α)
| raa_ea        : ∀ α μ μ', elimApp φ ψ υ μ μ' →
                                elimApp φ ψ υ (raa α μ) (raa α μ')
| abs_ea        : ∀ α β μ μ', elimApp φ ψ υ μ μ' →
                                elimApp φ ψ υ (abs α β μ) (abs α β μ')
| app_axraa_ea  : ∀ μ μ', elimApp φ ψ υ μ μ' →
                                elimApp φ ψ υ
                                (app _ _ (ax (neg (φ.impl ψ))) (raa _ μ))
                                μ'
| app_ax_ea     : ∀ μ μ', lrof μ ≠ prraa → elimApp φ ψ υ μ μ' →
                                elimApp φ ψ υ
                                (app _ _ (ax (neg (φ.impl ψ))) μ)
                                (app _ _ (ax (neg ψ)) (app _ _ μ' υ))
| app_ea        : ∀ α β μ ν μ' ν', lrof μ ≠ prax ∨ conc μ ≠ neg (φ.impl ψ) →
                              elimApp φ ψ υ μ μ' → elimApp φ ψ υ ν ν' →
                              elimApp φ ψ υ (app α β μ ν) (app α β μ' ν')
| pair_ea       : ∀ α β μ ν μ' ν', elimApp φ ψ υ μ μ' → elimApp φ ψ υ ν ν' →
                              elimApp φ ψ υ (pair α β μ ν) (pair α β μ' ν')
| fst_ea        : ∀ α β μ μ', elimApp φ ψ υ μ μ' →
                              elimApp φ ψ υ (fst α β μ) (fst α β μ')
| snd_ea        : ∀ α β μ μ', elimApp φ ψ υ μ μ' →
                              elimApp φ ψ υ (snd α β μ) (snd α β μ')
| left_ea       : ∀ α β μ μ', elimApp φ ψ υ μ μ' →
                              elimApp φ ψ υ (left α β μ) (left α β μ')
| right_ea      : ∀ α β μ μ', elimApp φ ψ υ μ μ' →
                              elimApp φ ψ υ (right α β μ) (right α β μ')
| case_ea       : ∀ α β χ μ ν χ' μ' ν',
                              elimApp φ ψ υ χ χ' → elimApp φ ψ υ μ μ' →
                              elimApp φ ψ υ ν ν' →
                              elimApp φ ψ υ (case α β χ μ ν) (case α β χ' μ' ν')

inductive elimFst (φ ψ : propform) :
                              {σ : propform} →  nkprf σ → nkprf σ → Prop
| ax1_ef        : elimFst φ ψ (ax (neg (φ.conj ψ)))
                          (abs (φ.conj ψ) _ (app _ _ (ax (neg φ))
                                    (fst _ _ (ax (φ.conj ψ)))))
| ax2_ef        : ∀ α, α ≠ neg (φ.conj ψ) → elimFst φ ψ (ax α) (ax α)
| raa_ef        : ∀ α μ μ', elimFst φ ψ μ μ' →
                                elimFst φ ψ (raa α μ) (raa α μ')
| abs_ef        : ∀ α β μ μ', elimFst φ ψ μ μ' →
                                elimFst φ ψ (abs α β μ) (abs α β μ')
| app_axraa_ef  : ∀ μ μ', elimFst φ ψ μ μ' →
                                elimFst φ ψ
                                (app _ _ (ax (neg (φ.conj ψ))) (raa _ μ))
                                μ'
| app_ax_ef     : ∀ μ μ', lrof μ ≠ prraa → elimFst φ ψ μ μ' →
                                elimFst φ ψ
                                (app _ _ (ax (neg (φ.conj ψ))) μ)
                                (app _ _ (ax (neg φ)) (fst _ _ μ'))
| app_ef        : ∀ α β μ ν μ' ν', lrof μ ≠ prax ∨ conc μ ≠ neg (φ.conj ψ) →
                              elimFst φ ψ μ μ' → elimFst φ ψ ν ν' →
                              elimFst φ ψ (app α β μ ν) (app α β μ' ν')
| pair_ef       : ∀ α β μ ν μ' ν', elimFst φ ψ μ μ' → elimFst φ ψ ν ν' →
                              elimFst φ ψ (pair α β μ ν) (pair α β μ' ν')
| fst_ef        : ∀ α β μ μ', elimFst φ ψ μ μ' →
                              elimFst φ ψ (fst α β μ) (fst α β μ')
| snd_ef        : ∀ α β μ μ', elimFst φ ψ μ μ' →
                              elimFst φ ψ (snd α β μ) (snd α β μ')
| left_ef       : ∀ α β μ μ', elimFst φ ψ μ μ' →
                              elimFst φ ψ (left α β μ) (left α β μ')
| right_ef       : ∀ α β μ μ', elimFst φ ψ μ μ' →
                              elimFst φ ψ (right α β μ) (right α β μ')
| case_ef       : ∀ α β χ μ ν χ' μ' ν',
                              elimFst φ ψ χ χ' → elimFst φ ψ μ μ' →
                              elimFst φ ψ ν ν' →
                              elimFst φ ψ (case α β χ μ ν) (case α β χ' μ' ν')

inductive elimSnd (φ ψ : propform) :
                              {σ : propform} →  nkprf σ → nkprf σ → Prop
| ax1_es        : elimSnd φ ψ (ax (neg (φ.conj ψ)))
                          (abs (φ.conj ψ) _ (app _ _ (ax (neg ψ))
                                    (snd _ _ (ax (φ.conj ψ)))))
| ax2_es        : ∀ α, α ≠ neg (φ.conj ψ) → elimSnd φ ψ (ax α) (ax α)
| raa_es        : ∀ α μ μ', elimSnd φ ψ μ μ' →
                                elimSnd φ ψ (raa α μ) (raa α μ')
| abs_es        : ∀ α β μ μ', elimSnd φ ψ μ μ' →
                                elimSnd φ ψ (abs α β μ) (abs α β μ')
| app_axraa_es  : ∀ μ μ', elimSnd φ ψ μ μ' →
                                elimSnd φ ψ
                                (app _ _ (ax (neg (φ.conj ψ))) (raa _ μ))
                                μ'
| app_ax_es     : ∀ μ μ', lrof μ ≠ prraa → elimSnd φ ψ μ μ' →
                                elimSnd φ ψ
                                (app _ _ (ax (neg (φ.conj ψ))) μ)
                                (app _ _ (ax (neg ψ)) (snd _ _ μ'))
| app_es        : ∀ α β μ ν μ' ν', lrof μ ≠ prax ∨ conc μ ≠ neg (φ.conj ψ) →
                              elimSnd φ ψ μ μ' → elimSnd φ ψ ν ν' →
                              elimSnd φ ψ (app α β μ ν) (app α β μ' ν')
| pair_es       : ∀ α β μ ν μ' ν', elimSnd φ ψ μ μ' → elimSnd φ ψ ν ν' →
                              elimSnd φ ψ (pair α β μ ν) (pair α β μ' ν')
| fst_es        : ∀ α β μ μ', elimSnd φ ψ μ μ' →
                              elimSnd φ ψ (fst α β μ) (fst α β μ')
| snd_es        : ∀ α β μ μ', elimSnd φ ψ μ μ' →
                              elimSnd φ ψ (snd α β μ) (snd α β μ')
| left_es       : ∀ α β μ μ', elimSnd φ ψ μ μ' →
                              elimSnd φ ψ (left α β μ) (left α β μ')
| right_es       : ∀ α β μ μ', elimSnd φ ψ μ μ' →
                              elimSnd φ ψ (right α β μ) (right α β μ')
| case_es       : ∀ α β χ μ ν χ' μ' ν',
                              elimSnd φ ψ χ χ' → elimSnd φ ψ μ μ' →
                              elimSnd φ ψ ν ν' →
                              elimSnd φ ψ (case α β χ μ ν) (case α β χ' μ' ν')

inductive elimCase (φ ψ : propform) (ρ υ : nkprf bot) :
                              {σ : propform} →  nkprf σ → nkprf σ → Prop
| ax1_ec        : elimCase φ ψ ρ υ (ax (neg (φ.disj ψ)))
                          (abs (φ.disj ψ) _ (case _ _ (ax (φ.disj ψ)) ρ υ))
| ax2_ec        : ∀ α, α ≠ neg (φ.disj ψ) → elimCase φ ψ ρ υ (ax α) (ax α)
| raa_ec        : ∀ α μ μ', elimCase φ ψ ρ υ μ μ' →
                                elimCase φ ψ ρ υ (raa α μ) (raa α μ')
| abs_ec        : ∀ α β μ μ', elimCase φ ψ ρ υ μ μ' →
                                elimCase φ ψ ρ υ (abs α β μ) (abs α β μ')
| app_axraa_ec  : ∀ μ μ', elimCase φ ψ ρ υ μ μ' →
                                elimCase φ ψ ρ υ
                                (app _ _ (ax (neg (φ.disj ψ))) (raa _ μ))
                                μ'
| app_ax_ec     : ∀ μ μ', lrof μ ≠ prraa → elimCase φ ψ ρ υ μ μ' →
                                elimCase φ ψ ρ υ
                                (app _ _ (ax (neg (φ.disj ψ))) μ)
                                (case _ _ μ' ρ υ)
| app_ec        : ∀ α β μ ν μ' ν', lrof μ ≠ prax ∨ conc μ ≠ neg (φ.disj ψ) →
                              elimCase φ ψ ρ υ μ μ' → elimCase φ ψ ρ υ ν ν' →
                              elimCase φ ψ ρ υ (app α β μ ν) (app α β μ' ν')
| pair_ec       : ∀ α β μ ν μ' ν', elimCase φ ψ ρ υ μ μ' → elimCase φ ψ ρ υ ν ν' →
                              elimCase φ ψ ρ υ (pair α β μ ν) (pair α β μ' ν')
| fst_ec        : ∀ α β μ μ', elimCase φ ψ ρ υ μ μ' →
                              elimCase φ ψ ρ υ (fst α β μ) (fst α β μ')
| snd_ec        : ∀ α β μ μ', elimCase φ ψ ρ υ μ μ' →
                              elimCase φ ψ ρ υ (snd α β μ) (snd α β μ')
| left_ec       : ∀ α β μ μ', elimCase φ ψ ρ υ μ μ' →
                              elimCase φ ψ ρ υ (left α β μ) (left α β μ')
| right_ec      : ∀ α β μ μ', elimCase φ ψ ρ υ μ μ' →
                              elimCase φ ψ ρ υ (right α β μ) (right α β μ')
| case_ec       : ∀ α β χ μ ν χ' μ' ν',
                              elimCase φ ψ ρ υ χ χ' → elimCase φ ψ ρ υ μ μ' →
                              elimCase φ ψ ρ υ ν ν' →
                              elimCase φ ψ ρ υ (case α β χ μ ν) (case α β χ' μ' ν')

inductive contract : {φ : propform} → nkprf φ → nkprf φ → Prop
  | appAbsContract : ∀ α β μ μ' ν, graft ν μ μ' →
                          contract (app α β (abs α β μ) ν) μ'
  | fstPairContract : ∀ α β μ ν,
                          contract (fst α β (pair α β μ ν)) μ
  | sndPairContract : ∀ α β μ ν,
                          contract (snd α β (pair α β μ ν)) ν
  | caseLeftContract : ∀ α β χ μ μ' ν, graft χ μ μ' →
                          contract (case α β (left α β χ) μ ν) μ'
  | caseRightContract : ∀ α β χ μ ν ν', graft χ ν ν' →
                          contract (case α β (right α β χ) μ ν) ν'
  | raaBotContract : ∀ μ μ', elimBot μ μ' → contract (raa bot μ) μ'
  | raaNegContract : ∀ α μ μ', elimNeg α μ μ' →
                          contract (raa (neg α) μ) (abs α bot μ')
  | appRaaContract : ∀ α β μ ν μ', elimApp α β ν μ μ' →
                          contract ((app α β (raa (impl α β) μ)) ν) (raa β μ')
  | fstRaaContract : ∀ α β μ μ', elimFst α β μ μ' →
                          contract (fst α β (raa (conj α β) μ)) (raa α μ')
  | sndRaaContract : ∀ α β μ μ', elimSnd α β μ μ' →
                          contract (snd α β (raa (conj α β) μ)) (raa β μ')
  | caseRaaContract : ∀ α β χ μ ν χ', elimCase α β μ ν χ χ' →
                      contract ((case α β (raa (disj α β) χ)) μ ν) χ'

inductive oneStep: (φ : propform) → nkprf φ → nkprf φ → Prop where
| raaCrit : ∀ α π ϖ μ, π = raa α μ → contract π ϖ →
                    maxDeg μ < maxDeg π → oneStep α π ϖ
| raaStep : ∀ α π μ μ', π = raa α μ → maxDeg μ = maxDeg π →
                    oneStep bot μ μ' → oneStep α π (raa α μ')
| absStep : ∀ α β π μ μ', π = abs α β μ → maxDeg μ = maxDeg π →
                    oneStep β μ μ' → oneStep (impl α β) π (abs α β μ')
| appCrit : ∀ α β π ϖ μ ν, π = app α β μ ν → contract π ϖ →
                    degree π = maxDeg π → maxDeg μ < maxDeg π →
                    maxDeg ν < maxDeg π → oneStep β π ϖ
| app1Step : ∀ α β π μ μ' ν, π = app α β μ ν →
                    maxDeg ν < maxDeg π → maxDeg μ = maxDeg π →
                    oneStep (impl α β) μ μ' → oneStep β π (app α β μ' ν)
| app2Step : ∀ α β π μ ν ν', π = app α β μ ν → maxDeg ν = maxDeg π →
                    oneStep α ν ν' → oneStep β π (app α β μ ν')
| pair1Step : ∀ α β π μ μ' ν, π = pair α β μ ν →
                    maxDeg ν < maxDeg π → maxDeg μ = maxDeg π →
                    oneStep α μ μ' → oneStep (conj α β) π (pair α β μ' ν)
| pair2Step : ∀ α β π μ ν ν', π = pair α β μ ν → maxDeg ν = maxDeg π →
                    oneStep β ν ν' → oneStep (conj α β) π (pair α β μ ν')
| fstCrit : ∀ α β π ϖ μ, π = fst α β μ → contract π ϖ →
                    degree π = maxDeg π → maxDeg μ < maxDeg π →
                    oneStep α π ϖ
| fstStep : ∀ α β π μ μ', π = fst α β μ → maxDeg μ = maxDeg π →
                    oneStep (conj α β) μ μ' → oneStep α π (fst α β μ')
| sndCrit : ∀ α β π ϖ μ, π = snd α β μ → contract π ϖ →
                    degree π = maxDeg π → maxDeg μ < maxDeg π →
                    oneStep β π ϖ
| sndStep : ∀ α β π μ μ', π = snd α β μ → maxDeg μ = maxDeg π →
                    oneStep (conj α β) μ μ' → oneStep β π (snd α β μ')
| leftStep : ∀ α β π μ μ', π = left α β μ → maxDeg μ = maxDeg π →
                    oneStep α μ μ' → oneStep (disj α β) π (left α β μ')
| rightStep : ∀ α β π μ μ', π = right α β μ → maxDeg μ = maxDeg π →
                    oneStep β μ μ' → oneStep (disj α β) π (right α β μ')
| caseCrit : ∀ α β π ϖ χ μ ν, π = case α β χ μ ν → contract π ϖ →
                    degree π = maxDeg π → maxDeg χ < maxDeg π →
                    maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
                    oneStep bot π ϖ
| case1Step : ∀ α β π χ χ' μ ν, π = case α β χ μ ν →
                    maxDeg ν < maxDeg π → maxDeg μ < maxDeg π →
                    maxDeg χ = maxDeg π → oneStep (disj α β) χ χ' →
                    oneStep bot π (case α β χ' μ ν)
| case2Step : ∀ α β π χ μ μ' ν, π = case α β χ μ ν  →
                    maxDeg ν < maxDeg π → maxDeg μ = maxDeg π →
                    oneStep bot μ μ' → oneStep bot π (case α β χ μ' ν)
| case3Step : ∀ α β π χ μ ν ν', π = case α β χ μ ν →
                    maxDeg ν = maxDeg π  →
                    oneStep bot ν ν' → oneStep bot π (case α β χ μ ν')

lemma lrofGraft : ∀ φ ψ (ρ : nkprf φ) (π ϖ : nkprf ψ),
      graft ρ π ϖ → lrof ϖ = lrof π ∨
      (lrof π = prax ∧ φ = ψ ∧ lrof ϖ = lrof ρ) := by
  intro φ ψ ρ π ϖ Hgraft; induction Hgraft <;> simp [lrof]

lemma graftAssConc : ∀ φ ψ (ρ : nkprf φ) (π : nkprf ψ) ϖ, graft ρ π ϖ →
            hypos ϖ ⊆ (hypos π \ {φ}) ∪ hypos ρ ∧ conc ϖ = conc π := by
  intro φ ψ ρ π ϖ Hgraft; constructor
  · induction Hgraft <;> simp_all [hypos] <;> try grind
    · rename_i α μ μ' G H;
      intro x F; by_cases E : x = neg α
      · simp [E]
      · rcases H F with D | D
        · right; left; grind
        · right; right; exact D
    · rename_i α β μ μ' G H;
      intro x F; by_cases E : x = α
      · simp [E]
      · rcases H F with D | D
        · right; left; grind
        · right; right; exact D
  · simp [conc]

lemma degree_raaGraft : ∀ φ α (ρ : nkprf φ) μ μ',
  graft ρ μ μ' → degree (raa α μ) = degree (raa α μ') :=  by
  intro φ α ρ μ μ' Hgraft
  cases α
  · simp [degree, degwt]
  · simp [degree, degwt]
  · rename_i β γ; cases γ <;> try simp [degree, degwt]
  · simp [degree, degwt]
  · simp [degree, degwt]

lemma degree_appGraft : ∀ d φ α β (ρ : nkprf φ) μ μ' ν ν',
  sz φ + 2 ≤ d → graft ρ μ μ' → graft ρ ν ν' →
  degree (app α β μ ν) < d → degree (app α β μ' ν') < d := by
  intro d φ α β ρ μ μ' ν ν' Hsz Hgraftμ Hgraftν
  cases Hgraftμ <;> simp_all [degree, degwt,sz]
  split <;> try grind

lemma degree_fstGraft : ∀ d φ α β (ρ : nkprf φ) μ μ',
  sz φ + 2 ≤ d → graft ρ μ μ' →
  degree (fst α β μ) < d →  degree (fst α β μ') < d := by
  intro d φ α β ρ μ μ' Hsz Hgraft
  cases Hgraft <;> simp_all [degree, degwt, sz]
  split <;> try grind

lemma degree_sndGraft : ∀ d φ α β (ρ : nkprf φ) μ μ',
  sz φ + 2 ≤ d → graft ρ μ μ' →
  degree (snd α β μ) < d →  degree (snd α β μ') < d := by
  intro d φ α β ρ μ μ' Hsz Hgraft
  cases Hgraft <;> simp_all [degree, degwt, sz]
  split <;> try grind

lemma degree_caseGraft : ∀ d φ α β (ρ : nkprf φ) χ χ' μ μ' ν ν',
  sz φ + 2 ≤ d → graft ρ χ χ' → graft ρ μ μ' → graft ρ ν ν' →
  degree (case α β χ μ ν) < d →  degree (case α β χ' μ' ν') < d := by
  intro d φ α β ρ χ χ' μ μ' ν ν' Hsz Hgraftχ Hgraftμ Hgraftν
  cases Hgraftχ <;> simp_all [degree, degwt, sz]
  split <;> try grind

lemma graftCutRank : ∀ d φ ψ (ρ : nkprf φ) (π ϖ : nkprf ψ), graft ρ π ϖ →
          maxDeg ρ < d → maxDeg π < d → sz φ + 2 ≤ d → maxDeg ϖ < d := by
  intro d φ ψ ρ π ϖ Hgraft H1 H2 H3
  induction Hgraft <;> clear ψ π ϖ <;>
    try simp_all [maxDeg, cutrank] <;> try grind
  · rename_i α μ μ' Hgraft ih
    simp [pairAdd_fst] at H2; simp [pairAdd_fst]
    apply degree_raaGraft (α := α) at Hgraft
    simp [degree] at *; try grind
  · rename_i α β μ μ' ν ν' Hgraftμ Hgraftν ihμ ihν
    simp [pairAdd_fst] at H2; simp [pairAdd_fst]
    simp [ihμ H2.1, ihν H2.2.1]
    apply degree_appGraft (φ := φ)
    exact H3; exact Hgraftμ; exact Hgraftν; exact H2.2.2
  · rename_i α β μ μ' ν ν' Hgraftμ Hgraftν ihμ ihν
    simp [pairAdd_fst] at H2; simp [pairAdd_fst]
    rcases H2 with ⟨H21, H22⟩; grind
  · rename_i α β μ μ' Hgraftμ ihμ
    simp [pairAdd_fst] at H2; simp [pairAdd_fst]
    simp [ihμ H2.1]
    apply degree_fstGraft (φ := φ)
    exact H3; exact Hgraftμ; exact H2.2
  · rename_i α β μ μ' Hgraftμ ihμ
    simp [pairAdd_fst] at H2; simp [pairAdd_fst]
    simp [ihμ H2.1]
    apply degree_sndGraft (φ := φ)
    exact H3; exact Hgraftμ; exact H2.2
  · rename_i α β χ χ' μ μ' ν ν' Hgraftχ Hgraftμ Hgraftν ihχ ihμ ihν
    simp [pairAdd_fst] at H2; simp [pairAdd_fst]
    simp [ihχ H2.1, ihμ H2.2.1, ihν H2.2.2.1]
    apply degree_caseGraft (φ := φ)
    exact H3; exact Hgraftχ; exact Hgraftμ; exact Hgraftν; exact H2.2.2.2

lemma lrofelimBot : ∀ σ (π π' : nkprf σ), elimBot π π' →
  lrof π' = lrof π ∨
  σ = neg bot ∧ lrof π = prax ∧ lrof π' = prabs ∨
  σ = bot := by
  intro α π π' Helim; induction Helim <;> simp [lrof, neg]

lemma elimBotConc : ∀ σ (π π': nkprf σ), elimBot π π' →
  conc π' = conc π := by simp [conc];

lemma elimBotAss : ∀ σ (π π' : nkprf σ), elimBot π π' →
  hypos π' ⊆ hypos π \ {neg bot} := by
  intro σ π π' Helim; induction Helim <;> simp [hypos] <;>
    simp [neg] at * <;> try grind

lemma elimBotCutRank : ∀ σ (π π' : nkprf σ), elimBot π π' →
  maxDeg π < 2 → maxDeg π' < 2 := by
  intro σ π π' Helim Hdegπ
  induction Helim
  · simp [maxDeg, cutrank, degwt] at *
  · simp [maxDeg, cutrank, degwt]
  · rename_i α μ μ' G ih; simp [maxDeg, cutrank] at *
    cases α <;> simp [degwt, pairAdd_fst] at * <;> try grind
    · rename_i β γ; cases γ <;> try grind
  · simp [maxDeg, cutrank] at *; grind
  · rename_i μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [degwt, G, pairAdd_fst] at *
  · rename_i μ μ' G H ih; simp [maxDeg, cutrank] at *
    cases H <;> simp [degwt, pairAdd_fst] at * <;> try grind
  · rename_i α β μ ν μ' ν' F G H ihμ ihν;
    simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ihμ Hdegπ.1, ihν Hdegπ.2.1]
    cases G <;> simp [degwt] at * <;> try grind
    simp [lrof, conc, neg] at F
  · simp [maxDeg, cutrank, pairAdd_fst] at *; grind
  · rename_i α β μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ih Hdegπ.1]
    cases G <;> simp [degwt] at *;  try grind
  · rename_i α β μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ih Hdegπ.1]
    cases G <;> simp [degwt] at *; try grind
  · simp [maxDeg, cutrank] at *; grind
  · simp [maxDeg, cutrank] at *; grind
  · rename_i α β χ μ ν χ' μ' ν' F G H ihχ ihμ ihν
    simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *
    simp [ihχ Hdegπ.1, ihμ Hdegπ.2.1, ihν Hdegπ.2.2.1]
    cases F <;> simp [degwt] at * <;> try grind

lemma lrofelimNeg : ∀ φ σ (π π' : nkprf σ), elimNeg φ π π' →
  lrof π' = lrof π ∨
  σ = neg (neg φ) ∧ lrof π = prax ∧ lrof π' = prabs ∨
  σ = bot := by
  intro φ σ π π' Helim; induction Helim <;> simp [neg, lrof]

lemma elimNegConc : ∀ φ σ (π π': nkprf σ), elimNeg φ π π' →
  conc π' = conc π := by simp [conc]

lemma elimNegAss : ∀ φ σ (π π' : nkprf σ), elimNeg φ π π' →
    hypos π' ⊆ (hypos π \ {neg (neg φ)}) ∪ {φ} := by
  intro φ σ π π' Helim
  induction Helim <;> simp [hypos] <;> simp [neg] at *
      <;> try grind
  · rename_i α μ μ' G ih; intro x F; apply ih at F
    simp at *; grind
  · rename_i α β μ μ' ν ih; intro x F; apply ih at F;
    simp at *; grind

lemma elimNegCutRank : ∀ d φ σ (π π' : nkprf σ), elimNeg φ π π' →
  maxDeg π < d → sz (φ.impl bot) < d → maxDeg π' < d := by
  intro d φ σ π π' Helim Hdegπ Hsz; simp [sz] at Hsz
  induction Helim
  · simp [maxDeg, cutrank, degwt] at *; grind
  · simp [maxDeg, cutrank, degwt]; grind
  · rename_i α μ μ' G ih; simp [maxDeg, cutrank] at *
    cases α <;> simp [degwt, pairAdd_fst] at * <;> try grind
    · rename_i β γ; cases γ <;> try grind
  · simp [maxDeg, cutrank] at *; grind
  · rename_i μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [degwt, G, pairAdd_fst] at *; grind
  · rename_i μ μ' G H ih; simp [maxDeg, cutrank] at *
    cases H <;> simp [degwt, pairAdd_fst, sz] at * <;> try grind
    simp [lrof] at G
  · rename_i α β μ ν μ' ν' F G H ihμ ihν;
    simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ihμ Hdegπ.1, ihν Hdegπ.2.1]
    cases G <;> simp [degwt] at * <;> try grind
    simp [lrof, conc, neg] at F
  · simp [maxDeg, cutrank, pairAdd_fst] at *; grind
  · rename_i α β μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ih Hdegπ.1]
    cases G <;> simp [degwt] at * <;> try grind
  · rename_i α β μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ih Hdegπ.1]
    cases G <;> simp [degwt] at * <;> try grind
  · simp [maxDeg, cutrank] at *; grind
  · simp [maxDeg, cutrank] at *; grind
  · rename_i α β χ μ ν χ' μ' ν' F G H ihχ ihμ ihν
    simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *
    simp [ihχ Hdegπ.1, ihμ Hdegπ.2.1, ihν Hdegπ.2.2.1]
    cases F <;> simp [degwt] at * <;> try grind

lemma lrofelimApp : ∀ φ ψ υ σ (π π' : nkprf σ), elimApp φ ψ υ π π' →
  lrof π' = lrof π ∨
  σ = neg (impl φ ψ) ∧ lrof π = prax ∧ lrof π' = prabs ∨
  σ = bot := by
  intro φ ψ υ σ π π' Helim; induction Helim <;> simp [lrof]

lemma elimAppConc : ∀ φ ψ υ σ (π π': nkprf σ), elimApp φ ψ υ π π' →
  conc π' = conc π := by simp [conc]

lemma elimAppAss : ∀ φ ψ υ σ (π π' : nkprf σ), elimApp φ ψ υ π π' →
    hypos π' ⊆ (hypos π \ {neg (φ.impl ψ)}) ∪ hypos υ ∪ {neg ψ} := by
  intro φ ψ υ σ π π' Helim
  induction Helim <;> simp [hypos] <;> simp [neg] at *
      <;> try grind
  · rename_i α μ μ' G ih; intro x F; apply ih at F
    simp at *; grind
  · rename_i α β μ μ' ν ih; intro x F; apply ih at F;
    simp at *; grind
  · rename_i α β χ μ ν χ' μ' ν' A B C ihχ ihμ ihν;
    constructor
    · constructor
      · intro x F; apply ihχ at F; simp at *; grind
      · intro x F; apply ihμ at F; simp at *; grind
    · intro x F; apply ihν at F; simp at *; grind

lemma elimAppCutRank : ∀ d φ ψ υ σ (π π' : nkprf σ), elimApp φ ψ υ π π' →
  maxDeg υ < d → maxDeg π < d → sz (φ.impl ψ) < d → maxDeg π' < d := by
  intro d φ ψ υ σ π π' Helim Hdegυ Hdegπ Hsz; simp [sz] at Hsz
  induction Helim
  · simp [maxDeg, cutrank, degwt, pairAdd_fst] at *; grind
  · simp [maxDeg, cutrank, degwt]; grind
  · rename_i α μ μ' G ih; simp [maxDeg, cutrank] at *
    cases α <;> simp [degwt, pairAdd_fst] at * <;> try grind
    · rename_i β γ; cases γ <;> try grind
  · simp [maxDeg, cutrank] at *; grind
  · rename_i μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [degwt, G, pairAdd_fst] at *; grind
  · rename_i μ μ' G H ih; simp [maxDeg, cutrank] at *
    cases H <;> simp [degwt, pairAdd_fst] at * <;> try grind
    simp [lrof] at G
  · rename_i α β μ ν μ' ν' F G H ihμ ihν;
    simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ihμ Hdegπ.1, ihν Hdegπ.2.1]
    cases G <;> simp [degwt] at * <;> try grind
    simp [lrof, conc, neg] at F
  · simp [maxDeg, cutrank, pairAdd_fst] at *; grind
  · rename_i α β μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ih Hdegπ.1]
    cases G <;> simp [degwt] at * <;> try grind
  · rename_i α β μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ih Hdegπ.1]
    cases G <;> simp [degwt] at * <;> try grind
  · simp [maxDeg, cutrank] at *; grind
  · simp [maxDeg, cutrank] at *; grind
  · rename_i α β χ μ ν χ' μ' ν' F G H ihχ ihμ ihν
    simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *
    simp [ihχ Hdegπ.1, ihμ Hdegπ.2.1, ihν Hdegπ.2.2.1]
    cases F <;> simp [degwt] at * <;> try grind

lemma lrofelimFst : ∀ φ ψ σ (π π' : nkprf σ), elimFst φ ψ π π' →
  lrof π' = lrof π ∨
  σ = neg (conj φ ψ) ∧ lrof π = prax ∧ lrof π' = prabs ∨
  σ = bot := by
  intro φ ψ σ π π' Helim; induction Helim <;> simp [lrof]

lemma elimFstConc : ∀ φ ψ σ (π π' : nkprf σ), elimFst φ ψ π π' →
    conc π' = conc π := by simp [conc]

lemma elimFstAss : ∀ φ ψ σ (π π' : nkprf σ), elimFst φ ψ π π' →
    hypos π' ⊆ (hypos π \ {neg (φ.conj ψ)}) ∪ {neg φ} := by
  intro φ ψ σ π π' Helim
  induction Helim <;> simp [hypos] <;> simp [neg] at *
      <;> try grind
  · rename_i α μ ih; intro x F; apply ih at F;
    simp at *; grind
  · rename_i α β μ ih; intro x F; apply ih at F;
    simp at *; grind

lemma elimFstCutRank : ∀ d φ ψ σ (π π' : nkprf σ), elimFst φ ψ π π' →
  maxDeg π < d → sz (φ.conj ψ) < d → maxDeg π' < d := by
  intro d φ ψ σ π π' Helim Hdegπ Hsz; simp [sz] at Hsz
  induction Helim
  · simp [maxDeg, cutrank, degwt] at *; grind
  · simp [maxDeg, cutrank, degwt]; grind
  · rename_i α μ μ' G ih; simp [maxDeg, cutrank] at *
    cases α <;> simp [degwt, pairAdd_fst] at * <;> try grind
    · rename_i β γ; cases γ <;> try grind
  · simp [maxDeg, cutrank] at *; grind
  · rename_i μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [degwt, G, pairAdd_fst] at *; grind
  · rename_i μ μ' G H ih; simp [maxDeg, cutrank] at *
    cases H <;> simp [degwt, pairAdd_fst] at * <;> try grind
    simp [lrof] at G
  · rename_i α β μ ν μ' ν' F G H ihμ ihν;
    simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ihμ Hdegπ.1, ihν Hdegπ.2.1]
    cases G <;> simp [degwt] at * <;> try grind
    simp [lrof, conc, neg] at F
  · simp [maxDeg, cutrank, pairAdd_fst] at *; grind
  · rename_i α β μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ih Hdegπ.1]
    cases G <;> simp [degwt] at * <;> try grind
  · rename_i α β μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ih Hdegπ.1]
    cases G <;> simp [degwt] at * <;> try grind
  · simp [maxDeg, cutrank] at *; grind
  · simp [maxDeg, cutrank] at *; grind
  · rename_i α β χ μ ν χ' μ' ν' F G H ihχ ihμ ihν
    simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *
    simp [ihχ Hdegπ.1, ihμ Hdegπ.2.1, ihν Hdegπ.2.2.1]
    cases F <;> simp [degwt] at * <;> try grind

lemma lrofelimSnd : ∀ φ ψ σ (π π' : nkprf σ), elimSnd φ ψ π π' →
  lrof π' = lrof π ∨
  σ = neg (conj φ ψ) ∧ lrof π = prax ∧ lrof π' = prabs ∨
  σ = bot := by
  intro φ ψ σ π π' Helim; induction Helim <;> simp [lrof]

lemma elimSndConc : ∀ φ ψ σ (π π' : nkprf σ), elimSnd φ ψ π π' →
    conc π' = conc π := by simp [conc]

lemma elimSndAss : ∀ φ ψ σ (π π' : nkprf σ), elimSnd φ ψ π π' →
    hypos π' ⊆ (hypos π \ {neg (φ.conj ψ)}) ∪ {neg ψ} := by
  intro φ ψ σ π π' Helim
  induction Helim <;> simp [hypos] <;> simp [neg] at *
      <;> try grind
  · rename_i α μ ih; intro x F; apply ih at F;
    simp at *; grind
  · rename_i α β μ ih; intro x F; apply ih at F;
    simp at *; grind

lemma elimSndCutRank : ∀ d φ ψ σ (π π' : nkprf σ), elimSnd φ ψ π π' →
  maxDeg π < d → sz (φ.conj ψ) < d → maxDeg π' < d := by
  intro d φ ψ σ π π' Helim Hdegπ Hsz; simp [sz] at Hsz
  induction Helim
  · simp [maxDeg, cutrank, degwt] at *; grind
  · simp [maxDeg, cutrank, degwt]; grind
  · rename_i α μ μ' G ih; simp [maxDeg, cutrank] at *
    cases α <;> simp [degwt, pairAdd_fst] at * <;> try grind
    · rename_i β γ; cases γ <;> try grind
  · simp [maxDeg, cutrank] at *; grind
  · rename_i μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [degwt, G, pairAdd_fst] at *; grind
  · rename_i μ μ' G H ih; simp [maxDeg, cutrank] at *
    cases H <;> simp [degwt, pairAdd_fst] at * <;> try grind
    simp [lrof] at G
  · rename_i α β μ ν μ' ν' F G H ihμ ihν;
    simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ihμ Hdegπ.1, ihν Hdegπ.2.1]
    cases G <;> simp [degwt] at * <;> try grind
    simp [lrof, conc, neg] at F
  · simp [maxDeg, cutrank, pairAdd_fst] at *; grind
  · rename_i α β μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ih Hdegπ.1]
    cases G <;> simp [degwt] at * <;> try grind
  · rename_i α β μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ih Hdegπ.1]
    cases G <;> simp [degwt] at * <;> try grind
  · simp [maxDeg, cutrank] at *; grind
  · simp [maxDeg, cutrank] at *; grind
  · rename_i α β χ μ ν χ' μ' ν' F G H ihχ ihμ ihν
    simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *
    simp [ihχ Hdegπ.1, ihμ Hdegπ.2.1, ihν Hdegπ.2.2.1]
    cases F <;> simp [degwt] at * <;> try grind

lemma lrofelimCase : ∀ φ ψ ρ υ σ (π π' : nkprf σ), elimCase φ ψ ρ υ π π' →
  lrof π' = lrof π ∨
  σ = neg (disj φ ψ) ∧ lrof π = prax ∧ lrof π' = prabs ∨
  σ = bot := by
  intro φ ψ ρ υ σ π π' Helim; induction Helim <;> simp [lrof]

lemma elimCaseConc : ∀ φ ψ ρ υ σ (π π' : nkprf σ), elimCase φ ψ ρ υ π π' →
    conc π' = conc π := by simp [conc]

lemma elimCaseAss : ∀ φ ψ ρ υ σ (π π' : nkprf σ), elimCase φ ψ ρ υ π π' →
  hypos π' ⊆ (hypos π \ {neg (φ.disj ψ)}) ∪ (hypos ρ \ {φ}) ∪
                          (hypos υ \ {ψ}) := by
  intro φ ψ ρ υ σ π π' Helim
  induction Helim <;> simp [hypos] <;> try grind
  rename_i α β χ μ ν χ' μ' ν' A B C ihχ ihμ ihν
  constructor; constructor
  · intro x hx; apply ihχ at hx; try grind
  · intro x hx; apply ihμ at hx; try grind
  · intro x hx; apply ihν at hx; try grind

lemma elimCaseCutRank : ∀ d φ ψ ρ υ σ (π π' : nkprf σ),
  elimCase φ ψ ρ υ π π' → maxDeg ρ < d →
  maxDeg υ < d → maxDeg π < d → sz (φ.disj ψ) < d → maxDeg π' < d := by
  intro d φ ψ ρ υ σ π π' Helim Hdegρ Hdegυ Hdegπ Hsz
  simp [sz] at Hsz
  induction Helim
  · simp [maxDeg, cutrank, degwt, pairAdd_fst] at *; grind
  · simp [maxDeg, cutrank, degwt]; grind
  · rename_i α μ μ' G ih; simp [maxDeg, cutrank] at *
    cases α <;> simp [degwt, pairAdd_fst] at * <;> try grind
    · rename_i β γ; cases γ <;> try grind
  · simp [maxDeg, cutrank] at *; grind
  · rename_i μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [degwt, G, pairAdd_fst] at *; grind
  · rename_i μ μ' G H ih; simp [maxDeg, cutrank] at *
    cases H <;> simp [degwt, pairAdd_fst] at * <;> try grind
    simp [lrof] at G
  · rename_i α β μ ν μ' ν' F G H ihμ ihν;
    simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ihμ Hdegπ.1, ihν Hdegπ.2.1]
    cases G <;> simp [degwt] at * <;> try grind
    simp [lrof, conc, neg] at F
  · simp [maxDeg, cutrank, pairAdd_fst] at *; grind
  · rename_i α β μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ih Hdegπ.1]
    cases G <;> simp [degwt] at * <;> try grind
  · rename_i α β μ μ' G ih; simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *; simp [ih Hdegπ.1]
    cases G <;> simp [degwt] at * <;> try grind
  · simp [maxDeg, cutrank] at *; grind
  · simp [maxDeg, cutrank] at *; grind
  · rename_i α β χ μ ν χ' μ' ν' F G H ihχ ihμ ihν
    simp [maxDeg, cutrank] at *
    simp [pairAdd_fst] at *
    simp [ihχ Hdegπ.1, ihμ Hdegπ.2.1, ihν Hdegπ.2.2.1]
    cases F <;> simp [degwt] at * <;> try grind

lemma contractAssConc : ∀ φ (π ϖ : nkprf φ),
  contract π ϖ → hypos ϖ ⊆ hypos π ∧ conc ϖ = conc π := by
  intro φ π ϖ Hcontract
  constructor
  · induction Hcontract <;> simp_all [hypos, graftAssConc] <;> try grind
    · rename_i α β χ μ μ' ν Hgraft
      intro x hx; apply graftAssConc at Hgraft;
      rcases Hgraft.1 hx with h|h <;> simp_all
    · rename_i α β χ μ μ' ν Hgraft
      intro x hx; apply graftAssConc at Hgraft;
      rcases Hgraft.1 hx with h|h <;> simp_all
    · rename_i μ μ' G; apply elimBotAss; exact G
    · rename_i α μ μ' G;
      intro x F; apply elimNegAss α bot μ μ' at F <;> try grind
    · rename_i α β μ ν μ' G;
      intro x F; apply elimAppAss α β ν _ μ at F <;> try grind
    · rename_i α β μ μ' G;
      intro x F; apply elimFstAss α β _ μ at F <;> try grind
    · rename_i α β μ μ' G;
      intro x F; apply elimSndAss α β _ μ at F <;> try grind
    · rename_i α β χ μ ν χ' G;
      intro x F; apply elimCaseAss α β μ ν _ χ at F <;> try grind
  · simp [conc]

lemma oneStepConcAss : ∀ φ (π π' : nkprf φ),
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
  · rename_i α β π' χ μ ν f1 f2 f3 f4 f5
    apply contractAssConc at f1;
    simp [hypos, conc] at f1; assumption

lemma lrofOneStep : ∀ φ (π π' : nkprf φ),
  oneStep φ π π' →  sz (conc π) + 1 < degree π ∨
    lrof π = lrof π' ∨ lrof π = prraa := by
  intro φ π π' H
  cases H
  · subst_vars; simp [lrof]
  · subst_vars; simp [lrof]
  · subst_vars; simp [lrof]
  · rename_i α ν μ eq E F G H
    subst_vars; simp [lrof]; left
    cases μ <;> simp [←E, degree, degwt] at F <;>
    simp [conc, degree, degwt]; try grind
    apply sz_gt_0
  · right; left; cases π <;> try grind
    simp [lrof]
  · right; left; cases π <;> try grind
    simp [lrof]
  · subst_vars; simp [lrof]
  · subst_vars; simp [lrof]
  · rename_i α μ eq E F G
    subst_vars; simp [lrof]; left
    cases μ <;> simp [←E, degree, degwt] at F <;>
    simp [conc, degree, degwt]; try grind
    apply sz_gt_0
  · right; left; cases π <;> try grind
    simp [lrof]
  · rename_i α μ eq E F G
    subst_vars; simp [lrof]; left
    cases μ <;> simp [←E, degree, degwt] at F <;>
    simp [conc, degree, degwt]; try grind
    apply sz_gt_0
  · right; left; cases π <;> try grind
    simp [lrof]
  · subst_vars; simp [lrof]
  · subst_vars; simp [lrof]
  · rename_i α β π ϖ χ μ ν eq E F G H I
    left; simp [conc,sz]
    simp [eq, degree] at *
    cases χ <;> simp [degwt] at * <;> try grind
    · left; apply sz_gt_0
    · have X : sz α > 0 := by apply sz_gt_0
      have Y : sz β > 0 := by apply sz_gt_0
      grind
    · have X : sz α > 0 := by apply sz_gt_0
      have Y : sz β > 0 := by apply sz_gt_0
      grind
  · subst_vars; simp [lrof]
  · subst_vars; simp [lrof]
  · subst_vars; simp [lrof]

lemma appAbsCutRank : ∀ α β π ϖ μ ν,
  π = app α β (abs α β μ) ν → contract π ϖ →
  degree π = maxDeg π → maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ μ ν eq Hcontract
  subst_vars; cases Hcontract; simp [degree, maxDeg, cutrank, degwt]
  rename_i Hgraft
  intro E F G; simp [rank_lt_rank_iff]; rw [←E] at *; clear E; left
  apply graftCutRank (sz α + sz β + 1) α β at Hgraft
  simp [maxDeg] at Hgraft;
  have E : sz β > 0 := by apply sz_gt_0
  grind

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

lemma caseLeftCutRank : ∀ α β π ϖ χ μ ν,
  π = case α β (left α β χ) μ ν → contract π ϖ →
  degree π = maxDeg π → maxDeg χ < maxDeg π →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ χ μ ν eq Hcontract
  subst_vars; cases Hcontract; simp [degree, maxDeg, cutrank, degwt]
  rename_i Hgraft
  intro E F G H; simp [rank_lt_rank_iff]; rw [←E] at *; clear E; left
  apply graftCutRank (sz α + sz β + 1) α at Hgraft
  simp [maxDeg] at Hgraft;
  have E : sz β > 0 := by apply sz_gt_0
  grind

lemma caseRightCutRank : ∀ α β π ϖ χ μ ν,
  π = case α β (right α β χ) μ ν → contract π ϖ →
  degree π = maxDeg π → maxDeg χ < maxDeg π →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ χ μ ν eq Hcontract
  subst_vars; cases Hcontract; simp [degree, maxDeg, cutrank, degwt]
  rename_i Hgraft
  intro E F G H; simp [rank_lt_rank_iff]; rw [←E] at *; clear E; left
  apply graftCutRank (sz α + sz β + 1) β at Hgraft
  simp [maxDeg] at Hgraft;
  have E : sz α > 0 := by apply sz_gt_0
  grind

lemma appRaaCutRank : ∀ α β π ϖ μ ν,
  π = app α β (raa _ μ) ν → contract π ϖ →
  degree π = maxDeg π →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ μ ν eq Hcontract
  subst_vars; cases Hcontract; rename_i μ' D;
  intro E F G
  conv_lhs => simp [cutrank]
  simp [rank_lt_rank_iff]; left;
  simp [degree, degwt] at E
  apply elimAppCutRank (d := sz α + sz β + 2) at D
  simp [maxDeg] at *
  rw [← E] at *; clear E;
  set H := D G F (by simp [sz]); simp [H]
  simp [degwt]; split <;> simp [sz] at *
  have X : sz α > 0 := by apply sz_gt_0
  grind

lemma fstRaaCutRank : ∀ α β π ϖ μ,
  π = fst α β (raa _ μ) → contract π ϖ →
  degree π = maxDeg π →
  maxDeg μ < maxDeg π → cutrank ϖ < cutrank π := by
  intro α β π ϖ μ eq Hcontract
  subst_vars; cases Hcontract; rename_i μ' D;
  intro E F
  conv_lhs => simp [cutrank]
  simp [rank_lt_rank_iff]; left;
  simp [degree, degwt] at E
  apply elimFstCutRank (d := sz α + sz β + 2) at D
  simp [maxDeg] at *
  rw [← E] at *; clear E;
  set H := D F (by simp [sz]); simp [H]
  simp [degwt]; split <;> simp [sz] at *
  have X : sz β > 0 := by apply sz_gt_0
  grind

lemma sndRaaCutRank : ∀ α β π ϖ μ,
  π = snd α β (raa _ μ) → contract π ϖ →
  degree π = maxDeg π →
  maxDeg μ < maxDeg π → cutrank ϖ < cutrank π := by
  intro α β π ϖ μ eq Hcontract
  subst_vars; cases Hcontract; rename_i μ' D;
  intro E F
  conv_lhs => simp [cutrank]
  simp [rank_lt_rank_iff]; left;
  simp [degree, degwt] at E
  apply elimSndCutRank (d := sz α + sz β + 2) at D
  simp [maxDeg] at *
  rw [← E] at *; clear E;
  set H := D F (by simp [sz]); simp [H]
  simp [degwt]; split <;> simp [sz] at *
  have X : sz α > 0 := by apply sz_gt_0
  grind

lemma caseRaaCutRank : ∀ α β π ϖ χ μ ν,
  π = case α β (raa _ χ) μ ν → contract π ϖ →
  degree π = maxDeg π → maxDeg χ < maxDeg π →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ χ μ ν eq Hcontract
  subst_vars; cases Hcontract; rename_i D
  intro E F G H
  simp [rank_lt_rank_iff]; left;
  simp [degree, degwt] at E
  apply elimCaseCutRank (d := sz α + sz β + 2) at D
  simp [maxDeg] at *
  rw [← E] at *; clear E;
  set J := D G H F (by simp [sz]); simp [J]

lemma raaCritCutRank : ∀ α π ϖ μ, π = raa α μ → contract π ϖ →
  maxDeg μ < maxDeg π → cutrank ϖ < cutrank π := by
  intro α π ϖ μ eq Hcontract Hdeg; subst_vars; cases Hcontract
  · rename_i μ' H;
    simp [maxDeg, cutrank, degwt] at *
    apply elimBotCutRank at H
    simp [rank_lt_rank_iff]; left
    simp [maxDeg, pairAdd_fst] at *; right; grind
  · rename_i α μ' H; simp [maxDeg, cutrank] at *
    apply elimNegCutRank (d := sz α + 4) at H
    simp [sz] at *; simp [neg, degwt] at *
    simp [rank_lt_rank_iff]; left
    simp [maxDeg, pairAdd_fst] at *; right; grind

lemma appCritCutRank : ∀ α β π ϖ μ ν,
  π = app α β μ ν → contract π ϖ →
  degree π = maxDeg π → maxDeg μ < maxDeg π →
  maxDeg ν < maxDeg π → cutrank ϖ < cutrank π := by
  intro α β π ϖ μ ν eq Hcontract; subst_vars
  cases Hcontract
  · apply appAbsCutRank; rfl; constructor; assumption
  · intro A B C; apply appRaaCutRank; rfl;
    constructor; assumption; assumption
    apply lt_of_lt_of_le'; exact B;
    apply maxDeg_sp; simp [subproofs]; right; simp [self_sp]
    assumption

lemma fstCritCutRank : ∀ α β π ϖ μ,
  π = fst α β μ → contract π ϖ →
  degree π = maxDeg π → maxDeg μ < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ μ eq Hcontract; subst_vars
  cases Hcontract
  · intro A B; apply fstPairCutRank; rfl; constructor; assumption
    all_goals (
      apply lt_of_lt_of_le'
      · exact B
      · apply maxDeg_sp; simp [subproofs];
        all_goals first
        | left; right; simp [self_sp]
        | right; simp [self_sp]
    )
  · intro A B; apply fstRaaCutRank; rfl
    constructor; assumption; assumption
    apply lt_of_lt_of_le'; exact B; apply maxDeg_sp; simp [subproofs];
    right; simp [self_sp]

lemma sndCritCutRank : ∀ α β π ϖ μ,
  π = snd α β μ → contract π ϖ →
  degree π = maxDeg π → maxDeg μ < maxDeg π →
  cutrank ϖ < cutrank π := by
  intro α β π ϖ μ eq Hcontract; subst_vars
  cases Hcontract
  · intro A B; apply sndPairCutRank; rfl; constructor; assumption
    all_goals (
      apply lt_of_lt_of_le'
      · exact B
      · apply maxDeg_sp; simp [subproofs];
        all_goals first
        | left; right; simp [self_sp]
        | right; simp [self_sp]
    )
  · intro A B; apply sndRaaCutRank; rfl
    constructor; assumption; assumption
    apply lt_of_lt_of_le'; exact B; apply maxDeg_sp; simp [subproofs];
    right; simp [self_sp]

lemma caseCritCutRank : ∀ α β π ϖ χ μ ν,
  π = case α β χ μ ν → contract π ϖ →
  degree π = maxDeg π → maxDeg χ < maxDeg π →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π → cutrank ϖ < cutrank π := by
  intro α β π ϖ χ μ ν eq Hcontract; subst_vars
  cases Hcontract
  · intro A B C D; apply caseLeftCutRank; rfl; constructor; assumption; assumption
    apply lt_of_lt_of_le'; exact B; apply maxDeg_sp; simp [subproofs];
    right; simp [self_sp]; assumption; assumption
  · intro A B C D; apply caseRightCutRank; rfl; constructor; assumption; assumption
    apply lt_of_lt_of_le'; exact B; apply maxDeg_sp; simp [subproofs];
    right; simp [self_sp]; assumption; assumption
  · intro A B C D; apply caseRaaCutRank; rfl
    constructor; assumption; assumption
    apply lt_of_lt_of_le'; exact B; apply maxDeg_sp; simp [subproofs];
    right; simp [self_sp]; assumption; assumption

lemma raaStepCutRank : ∀ α π μ μ', π = raa α μ →
  maxDeg μ = maxDeg π →
  oneStep _ μ μ' → cutrank μ' < cutrank μ →
  cutrank (raa α μ') < cutrank π := by
  intro α π μ μ' eq E F G; subst_vars
  have Hμ : 1 ≤ (cutrank μ).1 ∧ 1 ≤ (cutrank μ).2 := by {
    have A : goodRank (cutrank μ) := by apply cutrank_goodRank
    rcases A with ⟨A1,A2⟩ | A <;> try grind
    simp [rank_lt_rank_iff] at G; simp [A1,A2] at G
  }
  simp [maxDeg, cutrank] at *; cases α
  · simp [degwt, pairAdd_fst] at *
    · rw [←pairAdd_left_monotone_strict]
      assumption; apply cutrank_goodRank; simp [E]
  · simp [degwt]; rw [←pairAdd_left_monotone_strict];
    assumption; apply cutrank_goodRank; simp
  · rename_i β γ; cases γ
    · simp [degwt] at *; rw [←pairAdd_left_monotone_strict];
      assumption; apply cutrank_goodRank
      simp [pairAdd_fst] at E; simp [E]
    all_goals (
      simp [degwt]; rw [←pairAdd_left_monotone_strict];
      assumption; apply cutrank_goodRank; simp
    )
  all_goals (
    simp [degwt]; rw [←pairAdd_left_monotone_strict];
    assumption; apply cutrank_goodRank; simp
  )

lemma absStepCutRank : ∀ α β π μ μ', π = abs α β μ →
  maxDeg μ = maxDeg π → oneStep _ μ μ' → cutrank μ' < cutrank μ →
  cutrank (abs α β μ') < cutrank π := by
  intro α β π μ μ' eq A1 A2 A3
  simp [eq, cutrank, A3]

lemma app1StepCutRank : ∀ α β π μ μ' ν, π = app _ _ μ ν →
  maxDeg ν < maxDeg π →
  maxDeg μ = maxDeg π → oneStep _ μ μ' →
  cutrank μ' < cutrank μ → cutrank (app α β μ' ν) < cutrank π := by
  intro α β π μ μ' ν eq A1 A2 A3 A4; subst_vars
  set A5 := lrofOneStep _ _ _ A3
  have Hμ : 0 < (cutrank μ).1 ∧ 0 < (cutrank μ).2 := by {
    have B : goodRank (cutrank μ) := by apply cutrank_goodRank
    simp [goodRank] at B; rcases B with ⟨B1,B2⟩ | ⟨B1,B2⟩
    simp [rank_lt_rank_iff] at A4; grind; grind
  }
  have Hν : (cutrank ν).1 < (cutrank μ).1 := by {
    simp [maxDeg,cutrank] at A1
    simp [maxDeg,cutrank] at A2; rw [←A2] at A1; assumption
  }
  have A6 : cutrank μ' * cutrank ν < cutrank μ * cutrank ν := by
    rw [←pairAdd_lt_left_preserved]; assumption; grind; grind
  have A7 : degwt (app α β μ' ν) ≤ degwt (app α β μ ν) ∨
            (degwt (app α β μ' ν)).1 < (cutrank μ).1 := by {
    rcases A5 with A5 | A5 | A5
    · right; have B : conc μ' = conc μ := by apply oneStepConcAss at A3; simp [A3]
      rw [←B] at A5; apply lt_of_lt_of_le (b := degree μ)
      · cases μ' <;> simp [degwt] <;> simp [conc,sz] at A5 <;> try grind
      · apply rank_le_proj; apply degwt_le_cutrank
    · left; cases μ <;>
        cases μ' <;> simp [lrof] at A5 <;> simp [degwt]
    · left; cases μ <;> cases μ' <;> simp [lrof] at A5 <;>
        simp [degwt]; try grind
      left; left; grind
  }
  have A8 : (degwt (app α β μ ν)).1 ≤ (cutrank μ).1 := by
    simp [maxDeg, cutrank] at A2; rw [A2]; simp [pairAdd_fst]
  simp [cutrank]; rcases A7 with A7 | A7
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

lemma app2StepCutRank : ∀ α β π μ ν ν',
  π = app α β μ ν → maxDeg ν = maxDeg π →
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

lemma pair1StepCutRank : ∀ α β π μ μ' ν,
  π = pair α β μ ν → maxDeg ν < maxDeg π →
  maxDeg μ = maxDeg π → oneStep _ μ μ' →
  cutrank μ' < cutrank μ → cutrank (pair α β μ' ν) < cutrank π := by
  intro α β π μ μ' ν eq A1 A2 A3 A4; subst_vars
  have Hν : (cutrank ν).1 < (cutrank μ).1 := by {
    simp [maxDeg,cutrank, pairAdd_fst] at A1; grind
  }
  simp [cutrank]; rw [←pairAdd_left_monotone_strict]; assumption
  apply cutrank_goodRank; grind

lemma pair2StepCutRank : ∀ α β π μ ν ν',
  π = pair α β μ ν → maxDeg ν = maxDeg π →
  oneStep _ ν ν' → cutrank ν' < cutrank ν →
  cutrank (pair α β μ ν') < cutrank π := by
  intro α β π μ ν ν' eq A1 A2 A3; subst_vars
  have Hμ : (cutrank μ).1 ≤ (cutrank ν).1 := by {
    simp [maxDeg,cutrank, pairAdd_fst] at A1; grind
  }
  simp [cutrank]; rw [←pairAdd_right_monotone_strict]; assumption
  apply cutrank_goodRank; grind

lemma fstStepCutRank : ∀ α β π μ μ', π = fst α β μ →
  maxDeg μ = maxDeg π → oneStep _ μ μ' →
  cutrank μ' < cutrank μ → cutrank (fst α β μ') < cutrank π := by
  intro α β π μ μ' eq A1 A2 A3; subst_vars
  set A6 := lrofOneStep _ _ _ A2
  have Hμ : 0 < (cutrank μ).1 ∧ 0 < (cutrank μ).2 := by {
    have B : goodRank (cutrank μ) := by apply cutrank_goodRank
    simp [goodRank] at B; rcases B with ⟨B1,B2⟩ | ⟨B1,B2⟩
    simp [rank_lt_rank_iff] at A3; grind; grind
  }
  have A4 : degwt (fst α β μ') ≤ degwt (fst α β μ) ∨
            (degwt (fst α β μ')).1 < (cutrank μ).1 := by {
    rcases A6 with A6 | A6 | A6
    · right; have B : conc μ' = conc μ := by apply oneStepConcAss at A2; simp [A2]
      rw [←B] at A6; apply lt_of_lt_of_le (b := degree μ)
      · cases μ' <;> simp [degwt] <;> simp [conc,sz] at A6 <;> try grind
      · apply rank_le_proj; apply degwt_le_cutrank
    · left; cases μ <;>
        cases μ' <;> simp [lrof] at A6 <;> simp [degwt]
    · left; cases μ <;> cases μ' <;> simp [lrof] at A6 <;>
        simp [degwt]; try grind
      left; left; grind
  }
  have A5 : (degwt (fst α β μ)).1 ≤ (cutrank μ).1 := by
    simp [maxDeg, cutrank] at A1; rw [A1]; simp [pairAdd_fst]
  simp [cutrank]; rcases A4 with A4 | A4
  · calc
      cutrank μ' * degwt (fst α β μ')
      ≤ cutrank μ' * degwt (fst α β μ) := by
                              apply pairAdd_right_monotone; assumption
      _ < cutrank μ * degwt (fst α β μ) := by
                              rw [←pairAdd_left_monotone_strict]; assumption
                              apply cutrank_goodRank; grind;
  · calc
      cutrank μ' * degwt (fst α β μ') <
      cutrank μ * degwt (fst α β μ') := by
                            rw [←pairAdd_left_monotone_strict]; assumption
                            apply cutrank_goodRank; grind
      _ ≤ cutrank μ := by apply pairAdd_right_smallerd <;> grind
      _ ≤ cutrank μ * degwt (fst α β μ) := by apply le_self_mul

lemma sndStepCutRank : ∀ α β π μ μ', π = snd α β μ →
  maxDeg μ = maxDeg π → oneStep _ μ μ' →
  cutrank μ' < cutrank μ → cutrank (snd α β μ') < cutrank π := by
  intro α β π μ μ' eq A1 A2 A3; subst_vars
  set A6 := lrofOneStep _ _ _ A2
  have Hμ : 0 < (cutrank μ).1 ∧ 0 < (cutrank μ).2 := by {
    have B : goodRank (cutrank μ) := by apply cutrank_goodRank
    simp [goodRank] at B; rcases B with ⟨B1,B2⟩ | ⟨B1,B2⟩
    simp [rank_lt_rank_iff] at A3; grind; grind
  }
  have A4 : degwt (snd α β μ') ≤ degwt (snd α β μ) ∨
            (degwt (snd α β μ')).1 < (cutrank μ).1 := by {
    rcases A6 with A6 | A6 | A6
    · right; have B : conc μ' = conc μ := by apply oneStepConcAss at A2; simp [A2]
      rw [←B] at A6; apply lt_of_lt_of_le (b := degree μ)
      · cases μ' <;> simp [degwt] <;> simp [conc,sz] at A6 <;> try grind
      · apply rank_le_proj; apply degwt_le_cutrank
    · left; cases μ <;>
        cases μ' <;> simp [lrof] at A6 <;> simp [degwt]
    · left; cases μ <;> cases μ' <;> simp [lrof] at A6 <;>
        simp [degwt]; try grind
      left; left; grind
  }
  have A5 : (degwt (snd α β μ)).1 ≤ (cutrank μ).1 := by
    simp [maxDeg, cutrank] at A1; rw [A1]; simp [pairAdd_fst]
  simp [cutrank]; rcases A4 with A4 | A4
  · calc
      cutrank μ' * degwt (snd α β μ')
      ≤ cutrank μ' * degwt (snd α β μ) := by
                              apply pairAdd_right_monotone; assumption
      _ < cutrank μ * degwt (snd α β μ) := by
                              rw [←pairAdd_left_monotone_strict]; assumption
                              apply cutrank_goodRank; grind;
  · calc
      cutrank μ' * degwt (snd α β μ') <
      cutrank μ * degwt (snd α β μ') := by
                            rw [←pairAdd_left_monotone_strict]; assumption
                            apply cutrank_goodRank; grind
      _ ≤ cutrank μ := by apply pairAdd_right_smallerd <;> grind
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

lemma case1StepCutRank : ∀ α β π χ χ' μ ν, π = case α β χ μ ν →
  maxDeg ν < maxDeg π → maxDeg μ < maxDeg π → maxDeg χ = maxDeg π →
  oneStep _ χ χ' → cutrank χ' < cutrank χ →
  cutrank (case α β χ' μ ν) < cutrank π := by
  intro α β π χ χ' μ ν eq A1 A2 A3 A4 A5; subst_vars
  set A6 := lrofOneStep _ _ _ A4
  have Hχ : 0 < (cutrank χ).1 ∧ 0 < (cutrank χ).2 := by {
    have B : goodRank (cutrank χ) := by apply cutrank_goodRank
    simp [goodRank] at B; rcases B with ⟨B1,B2⟩ | B
    · rw [←A3] at A2; simp [maxDeg] at A2; grind
    · assumption
  }
  have Hμ : (cutrank μ).1 < (cutrank χ).1 := by {
    simp [maxDeg,cutrank] at A2
    simp [maxDeg,cutrank] at A3; rw [←A3] at A2; assumption
  }
  have Hν : (cutrank ν).1 < (cutrank χ).1 := by {
    simp [maxDeg,cutrank] at A1
    simp [maxDeg,cutrank] at A3; rw [←A3] at A1; assumption
  }
  have A7 : cutrank χ' * cutrank μ * cutrank ν <
              cutrank χ * cutrank μ * cutrank ν  := by
    rw [mul_assoc, mul_assoc, ←pairAdd_lt_left_preserved]
    assumption; grind; rw [←A3] at A1; rw [←A3] at A2;
    simp [maxDeg] at *; grind
  have A8 : degwt (case α β χ' μ ν) ≤ degwt (case α β χ μ ν) ∨
            (degwt (case α β χ' μ ν)).1 < (cutrank χ).1 := by {
    rcases A6 with A6 | A6 | A6
    · right; have B : conc χ' = conc χ := by apply oneStepConcAss at A4; simp [A4]
      rw [←B] at A6; apply lt_of_lt_of_le (b := degree χ)
      · cases χ' <;> simp [degwt] <;> simp [conc,sz] at A6 <;> try grind
      · apply rank_le_proj; apply degwt_le_cutrank
    · left; cases χ <;>
        cases χ' <;> simp [lrof] at A6 <;> simp [degwt]
    · left; cases χ <;> cases χ' <;> simp [lrof] at A6 <;>
        simp [degwt, rank_le_rank_iff]
  }
  have A9 : (degwt (case α β χ μ ν)).1 ≤ (cutrank χ).1 := by
    simp [maxDeg, cutrank] at A3; rw [A3]; simp [pairAdd_fst]
  simp [cutrank]; rcases A8 with A8 | A8
  · calc
      cutrank χ' * cutrank μ * cutrank ν * degwt (case α β χ' μ ν)
      ≤ cutrank χ' * cutrank μ * cutrank ν * degwt (case α β χ μ ν) := by
                              apply pairAdd_right_monotone; assumption
      _ < cutrank χ * cutrank μ * cutrank ν * degwt (case α β χ μ ν) := by
                              rw [←pairAdd_left_monotone_strict]; assumption
                              apply goodRank_pairAdd; apply goodRank_pairAdd;
                              apply cutrank_goodRank; apply cutrank_goodRank
                              apply cutrank_goodRank
                              simp [pairAdd_fst]; grind
  · calc
      cutrank χ' * cutrank μ * cutrank ν * degwt (case α β χ' μ ν)
      < cutrank χ * cutrank μ * cutrank ν * degwt (case α β χ' μ ν) := by
                              rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
                              rw [←pairAdd_left_monotone_strict]; assumption
                              apply cutrank_goodRank
                              simp [pairAdd_fst]; grind
      _ ≤ cutrank χ * cutrank μ * cutrank ν := by
                              apply pairAdd_right_smallerd
                              simp [pairAdd_fst]; grind; grind
      _ ≤ cutrank χ * cutrank μ * cutrank ν * degwt (case α β χ μ ν) := by
                              apply le_self_mul

lemma case2StepCutRank : ∀ α β π χ μ μ' ν,
  π = case α β χ μ ν → maxDeg ν < maxDeg π →
  maxDeg μ = maxDeg π → oneStep _ μ μ' →
  cutrank μ' < cutrank μ → cutrank (case α β χ μ' ν) < cutrank π := by
  intro α β π χ μ μ' ν eq A1 A2 A3 A4; subst_vars
  have A : (cutrank χ).1 ≤ (cutrank μ).1 := by {
    simp [maxDeg, cutrank] at A2;
    by_cases (cutrank χ).1 ≤ (cutrank μ).1 <;> try assumption
    rw [A2]; simp [pairAdd_fst]
  }
  have B : (cutrank ν).1 < (cutrank μ).1 := by rw [←A2] at A1; assumption
  have C1 : degwt (case α β χ μ ν) = degwt (case α β χ μ' ν) := by
                                      cases χ <;> simp [degwt]
  have C2 : (degwt (case α β χ μ ν)).1 ≤ (cutrank μ).1 := by
    simp [maxDeg, cutrank] at A2; rw [A2]; simp [pairAdd_fst]
  simp [cutrank, C1];
  calc
    cutrank χ * cutrank μ' * cutrank ν * degwt (case α β χ μ' ν) <
    cutrank χ * cutrank μ * cutrank ν * degwt (case α β χ μ' ν) := by
      rw [← pairAdd_left_monotone_strict];
      rw [← pairAdd_left_monotone_strict];
      rw [← pairAdd_right_monotone_strict]; assumption
      apply cutrank_goodRank; assumption
      apply goodRank_pairAdd <;> apply cutrank_goodRank
      simp_all [pairAdd_fst]; grind
      apply goodRank_pairAdd; apply goodRank_pairAdd
      apply cutrank_goodRank; apply cutrank_goodRank
      apply cutrank_goodRank
      simp [pairAdd_fst]; right; left; simp [←C1, C2]

lemma case3StepCutRank : ∀ α β π χ μ ν ν',
  π = case α β χ μ ν → maxDeg ν = maxDeg π →
  oneStep _ ν ν' → cutrank ν' < cutrank ν →
  cutrank (case α β χ μ ν') < cutrank π := by
  intro α β π χ μ ν ν' eq A1 A2 A3; subst_vars
  have A : (cutrank χ).1 ≤ (cutrank ν).1 := by {
    simp [maxDeg, cutrank] at A1;
    by_cases (cutrank χ).1 ≤ (cutrank ν).1 <;> try assumption
    rw [A1]; simp [pairAdd_fst]
  }
  have B : (cutrank μ).1 ≤ (cutrank ν).1 := by {
    simp [maxDeg, cutrank] at A1;
    by_cases (cutrank μ).1 ≤ (cutrank ν).1 <;> try assumption
    rw [A1]; simp [pairAdd_fst]
  }
  have C1 : degwt (case α β χ μ ν) = degwt (case α β χ μ ν') := by
                                      cases χ <;> simp [degwt]
  have C2 : (degwt (case α β χ μ ν)).1 ≤ (cutrank ν).1 := by
    simp [maxDeg, cutrank] at A1; rw [A1]; simp [pairAdd_fst]
  simp [cutrank, C1];
  calc
    cutrank χ * cutrank μ * cutrank ν' * degwt (case α β χ μ ν') <
    cutrank χ * cutrank μ * cutrank ν * degwt (case α β χ μ ν') := by
      rw [← pairAdd_left_monotone_strict];
      rw [← pairAdd_right_monotone_strict]; assumption
      apply cutrank_goodRank; simp [pairAdd_fst] at *; grind
      apply goodRank_pairAdd; apply goodRank_pairAdd
      apply cutrank_goodRank; apply cutrank_goodRank
      apply cutrank_goodRank
      simp [pairAdd_fst]; right; right; simp [←C1, C2]

lemma oneStepCutRank : ∀ φ (π π' : nkprf φ),
  oneStep _ π π' → cutrank π' < cutrank π := by
  intro φ π π' Hone
  induction Hone
  · apply raaCritCutRank <;> assumption
  · apply raaStepCutRank <;> assumption
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

lemma graftExists : ∀ ψ (ρ : nkprf ψ) φ (π : nkprf φ), ∃ π', graft ρ π π' := by
  intro ψ ρ φ π; induction π
  · rename_i α; by_cases A : α = ψ
    · subst_vars; exists ρ; apply graft.axgraft_same
    · exists (ax α); apply graft.axgraft_diff; grind
  · rename_i α μ ihμ; rcases ihμ with ⟨μ', ihμ⟩
    exists (raa α μ'); apply graft.raagraft; assumption
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
  · rename_i α β χ μ ν ihχ ihμ ihν; rcases ihχ with ⟨χ', ihχ⟩;
    rcases ihμ with ⟨μ', ihμ⟩; rcases ihν with ⟨ν',ihν⟩
    exists (case α β χ' μ' ν'); apply graft.casegraft <;> assumption

lemma elimBotExists : ∀ σ (π : nkprf σ), ∃ π', elimBot π π' := by
  have X : ∀ d σ (π : nkprf σ), prfsize π < d → ∃ π', elimBot π π' := by {
  intro d; induction d
  · intros ; grind
  · rename_i n ihn; intro σ π Hn; cases π
    · by_cases A : σ = neg bot
      · subst_vars; exists abs bot bot (ax bot); apply elimBot.ax1_eb
      · exists ax σ; apply elimBot.ax2_eb; exact A
    · rename_i μ;
      have A : ∃ μ', elimBot μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases A with ⟨μ', A⟩
      exists raa σ μ'; apply elimBot.raa_eb; assumption
    · rename_i α β μ;
      have A : ∃ μ', elimBot μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases A with ⟨μ', A⟩
      exists abs α β μ'; apply elimBot.abs_eb; assumption
    · rename_i β ν μ
      by_cases A : lrof μ = prax ∧ σ = bot ∧ β = bot
      · rcases A with ⟨A,A1,A2⟩; subst_vars
        cases μ <;> simp [lrof] at A; try grind
        clear A; by_cases B : lrof ν = prraa
        · cases ν <;> simp [lrof] at B
          clear B; rename_i μ
          have B : ∃ μ', elimBot μ μ' := by apply ihn; simp [prfsize] at *; grind
          rcases B with ⟨μ', B⟩
          exists μ'; apply elimBot.app_axraa_eb; try grind
        · have C : ∃ ν', elimBot ν ν' := by apply ihn; simp [prfsize] at *; grind
          rcases C with ⟨ν', C⟩
          exists ν'; apply elimBot.app_ax_eb <;> try grind
      · have B : ∃ μ', elimBot μ μ' := by apply ihn; simp [prfsize] at *; grind
        rcases B with ⟨μ', B⟩
        have C : ∃ ν', elimBot ν ν' := by apply ihn; simp [prfsize] at *; grind
        rcases C with ⟨ν', C⟩
        exists app β σ μ' ν'; apply elimBot.app_eb <;> try grind
        by_cases D : lrof μ = prax <;> try grind
        simp [D] at A; simp [conc,neg]; grind
    · rename_i α β μ ν
      have B : ∃ μ', elimBot μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      have C : ∃ ν', elimBot ν ν' := by apply ihn; simp [prfsize] at *; grind
      rcases C with ⟨ν', C⟩
      exists (pair α β μ' ν')
      apply elimBot.pair_eb <;> assumption
    · rename_i β μ
      have B : ∃ μ', elimBot μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (fst σ β μ')
      apply elimBot.fst_eb; assumption
    · rename_i β μ
      have B : ∃ μ', elimBot μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (snd β σ μ')
      apply elimBot.snd_eb; assumption
    · rename_i α β μ
      have B : ∃ μ', elimBot μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (left α β μ')
      apply elimBot.left_eb; assumption
    · rename_i α β μ
      have B : ∃ μ', elimBot μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (right α β μ')
      apply elimBot.right_eb; assumption
    · rename_i α β χ μ ν
      have B : ∃ χ', elimBot χ χ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨χ', B⟩
      have C : ∃ μ', elimBot μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases C with ⟨μ', C⟩
      have D : ∃ ν', elimBot ν ν' := by apply ihn; simp [prfsize] at *; grind
      rcases D with ⟨ν', D⟩
      exists (case α β χ' μ' ν')
      apply elimBot.case_eb <;> assumption
  }
  intro σ π; apply X (prfsize π + 1) σ π; grind

lemma elimNegExists : ∀ φ σ (π : nkprf σ), ∃ π', elimNeg φ π π' := by
  intro φ
  have X : ∀ d σ (π : nkprf σ), prfsize π < d → ∃ π', elimNeg φ π π' := by {
  intro d; induction d
  · intros ; grind
  · rename_i n ihn; intro σ π Hn; cases π
    · by_cases A : σ = neg (impl φ bot)
      · subst_vars;
        exists abs (neg φ) _ (app _ _ (ax (neg φ)) (ax φ));
        apply elimNeg.ax1_en
      · exists ax σ; apply elimNeg.ax2_en; exact A
    · rename_i μ;
      have A : ∃ μ', elimNeg φ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases A with ⟨μ', A⟩
      exists raa σ μ'; apply elimNeg.raa_en; assumption
    · rename_i α β μ;
      have A : ∃ μ', elimNeg φ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases A with ⟨μ', A⟩
      exists abs α β μ'; apply elimNeg.abs_en; assumption
    · rename_i β ν μ
      by_cases A : lrof μ = prax ∧ β = neg φ ∧ σ = bot
      · rcases A with ⟨A,A1,A2⟩; subst_vars
        cases μ <;> simp [lrof] at A; try grind
        clear A; by_cases B : lrof ν = prraa
        · cases ν <;> simp [lrof] at B
          clear B; rename_i μ
          have B : ∃ μ', elimNeg φ μ μ' := by apply ihn; simp [prfsize] at *; grind
          rcases B with ⟨μ', B⟩
          exists μ'; apply elimNeg.app_axraa_en; try grind
        · have C : ∃ ν', elimNeg φ ν ν' := by apply ihn; simp [prfsize] at *; grind
          rcases C with ⟨ν', C⟩
          exists (app _ _ ν' (ax φ));
          apply elimNeg.app_ax_en <;> try grind
          assumption; assumption
      · have B : ∃ μ', elimNeg φ μ μ' := by apply ihn; simp [prfsize] at *; grind
        rcases B with ⟨μ', B⟩
        have C : ∃ ν', elimNeg φ ν ν' := by apply ihn; simp [prfsize] at *; grind
        rcases C with ⟨ν', C⟩
        exists app β σ μ' ν'; apply elimNeg.app_en <;> try grind
        by_cases D : lrof μ = prax <;> try grind
        simp [D] at A; simp [conc,neg] at *; grind
    · rename_i α β μ ν
      have B : ∃ μ', elimNeg φ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      have C : ∃ ν', elimNeg φ ν ν' := by apply ihn; simp [prfsize] at *; grind
      rcases C with ⟨ν', C⟩
      exists (pair α β μ' ν')
      apply elimNeg.pair_en <;> assumption
    · rename_i β μ
      have B : ∃ μ', elimNeg φ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (fst σ β μ')
      apply elimNeg.fst_en; assumption
    · rename_i β μ
      have B : ∃ μ', elimNeg φ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (snd β σ μ')
      apply elimNeg.snd_en; assumption
    · rename_i α β μ
      have B : ∃ μ', elimNeg φ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (left α β μ')
      apply elimNeg.left_en; assumption
    · rename_i α β μ
      have B : ∃ μ', elimNeg φ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (right α β μ')
      apply elimNeg.right_en; assumption
    · rename_i α β χ μ ν
      have B : ∃ χ', elimNeg φ χ χ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨χ', B⟩
      have C : ∃ μ', elimNeg φ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases C with ⟨μ', C⟩
      have D : ∃ ν', elimNeg φ ν ν' := by apply ihn; simp [prfsize] at *; grind
      rcases D with ⟨ν', D⟩
      exists (case α β χ' μ' ν')
      apply elimNeg.case_en <;> assumption
  }
  intro σ π; apply X (prfsize π + 1) σ π; grind

lemma elimAppExists : ∀ φ ψ υ σ (π : nkprf σ), ∃ π', elimApp φ ψ υ π π' := by
  intro φ ψ υ
  have X : ∀ d σ (π : nkprf σ), prfsize π < d → ∃ π', elimApp φ ψ υ π π' := by {
  intro d; induction d
  · intros ; grind
  · rename_i n ihn; intro σ π Hn; cases π
    · by_cases A : σ = neg (impl φ ψ)
      · subst_vars;
        exists abs (φ.impl ψ) _ (app _ _ (ax (neg ψ)) (app _ _ (ax (φ.impl ψ)) υ));
        apply elimApp.ax1_ea
      · exists ax σ; apply elimApp.ax2_ea; exact A
    · rename_i μ;
      have A : ∃ μ', elimApp φ ψ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases A with ⟨μ', A⟩
      exists raa σ μ'; apply elimApp.raa_ea; assumption
    · rename_i α β μ;
      have A : ∃ μ', elimApp φ ψ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases A with ⟨μ', A⟩
      exists abs α β μ'; apply elimApp.abs_ea; assumption
    · rename_i β ν μ
      by_cases A : lrof μ = prax ∧ β = φ.impl ψ ∧ σ = bot
      · rcases A with ⟨A,A1,A2⟩; subst_vars
        cases μ <;> simp [lrof] at A; try grind
        clear A; by_cases B : lrof ν = prraa
        · cases ν <;> simp [lrof] at B
          clear B; rename_i μ
          have B : ∃ μ', elimApp φ ψ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
          rcases B with ⟨μ', B⟩
          exists μ'; apply elimApp.app_axraa_ea; try grind
        · have C : ∃ ν', elimApp φ ψ υ ν ν' := by apply ihn; simp [prfsize] at *; grind
          rcases C with ⟨ν', C⟩
          exists (app _ _ (ax (neg ψ)) (app _ _ ν' υ));
          apply elimApp.app_ax_ea <;> try grind
      · have B : ∃ μ', elimApp φ ψ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
        rcases B with ⟨μ', B⟩
        have C : ∃ ν', elimApp φ ψ υ ν ν' := by apply ihn; simp [prfsize] at *; grind
        rcases C with ⟨ν', C⟩
        exists app β σ μ' ν'; apply elimApp.app_ea <;> try grind
        by_cases D : lrof μ = prax <;> try grind
        simp [D] at A; simp [conc,neg]; grind
    · rename_i α β μ ν
      have B : ∃ μ', elimApp φ ψ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      have C : ∃ ν', elimApp φ ψ υ ν ν' := by apply ihn; simp [prfsize] at *; grind
      rcases C with ⟨ν', C⟩
      exists (pair α β μ' ν')
      apply elimApp.pair_ea <;> assumption
    · rename_i β μ
      have B : ∃ μ', elimApp φ ψ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (fst σ β μ')
      apply elimApp.fst_ea; assumption
    · rename_i β μ
      have B : ∃ μ', elimApp φ ψ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (snd β σ μ')
      apply elimApp.snd_ea; assumption
    · rename_i α β μ
      have B : ∃ μ', elimApp φ ψ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (left α β μ')
      apply elimApp.left_ea; assumption
    · rename_i α β μ
      have B : ∃ μ', elimApp φ ψ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (right α β μ')
      apply elimApp.right_ea; assumption
    · rename_i α β χ μ ν
      have B : ∃ χ', elimApp φ ψ υ χ χ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨χ', B⟩
      have C : ∃ μ', elimApp φ ψ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases C with ⟨μ', C⟩
      have D : ∃ ν', elimApp φ ψ υ ν ν' := by apply ihn; simp [prfsize] at *; grind
      rcases D with ⟨ν', D⟩
      exists (case α β χ' μ' ν')
      apply elimApp.case_ea <;> assumption
  }
  intro σ π; apply X (prfsize π + 1) σ π; grind

lemma elimFstExists : ∀ φ ψ σ (π : nkprf σ), ∃ π', elimFst φ ψ π π' := by
  intro φ ψ
  have X : ∀ d σ (π : nkprf σ), prfsize π < d → ∃ π', elimFst φ ψ π π' := by {
  intro d; induction d
  · intros ; grind
  · rename_i n ihn; intro σ π Hn; cases π
    · by_cases A : σ = neg (conj φ ψ)
      · subst_vars;
        exists abs (conj φ ψ) _ (app _ _ (ax (neg φ)) (fst _ _ (ax (conj φ ψ))));
        apply elimFst.ax1_ef
      · exists ax σ; apply elimFst.ax2_ef; exact A
    · rename_i μ;
      have A : ∃ μ', elimFst φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases A with ⟨μ', A⟩
      exists raa σ μ'; apply elimFst.raa_ef; assumption
    · rename_i α β μ;
      have A : ∃ μ', elimFst φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases A with ⟨μ', A⟩
      exists abs α β μ'; apply elimFst.abs_ef; assumption
    · rename_i β ν μ
      by_cases A : lrof μ = prax ∧ β = conj φ ψ ∧ σ = bot
      · rcases A with ⟨A,A1,A2⟩; subst_vars
        cases μ <;> simp [lrof] at A; try grind
        clear A; by_cases B : lrof ν = prraa
        · cases ν <;> simp [lrof] at B
          clear B; rename_i μ
          have B : ∃ μ', elimFst φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
          rcases B with ⟨μ', B⟩
          exists μ'; apply elimFst.app_axraa_ef; try grind
        · have C : ∃ ν', elimFst φ ψ ν ν' := by apply ihn; simp [prfsize] at *; grind
          rcases C with ⟨ν', C⟩
          exists app _ _ (ax (neg φ)) (fst _ _ ν');
          apply elimFst.app_ax_ef <;> try grind
      · have B : ∃ μ', elimFst φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
        rcases B with ⟨μ', B⟩
        have C : ∃ ν', elimFst φ ψ ν ν' := by apply ihn; simp [prfsize] at *; grind
        rcases C with ⟨ν', C⟩
        exists app β σ μ' ν'; apply elimFst.app_ef <;> try grind
        by_cases D : lrof μ = prax <;> try grind
        simp [D] at A; simp [conc,neg] at *; grind
    · rename_i α β μ ν
      have B : ∃ μ', elimFst φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      have C : ∃ ν', elimFst φ ψ ν ν' := by apply ihn; simp [prfsize] at *; grind
      rcases C with ⟨ν', C⟩
      exists (pair α β μ' ν')
      apply elimFst.pair_ef <;> assumption
    · rename_i β μ
      have B : ∃ μ', elimFst φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (fst σ β μ')
      apply elimFst.fst_ef; assumption
    · rename_i β μ
      have B : ∃ μ', elimFst φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (snd β σ μ')
      apply elimFst.snd_ef; assumption
    · rename_i α β μ
      have B : ∃ μ', elimFst φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (left α β μ')
      apply elimFst.left_ef; assumption
    · rename_i α β μ
      have B : ∃ μ', elimFst φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (right α β μ')
      apply elimFst.right_ef; assumption
    · rename_i α β χ μ ν
      have B : ∃ χ', elimFst φ ψ χ χ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨χ', B⟩
      have C : ∃ μ', elimFst φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases C with ⟨μ', C⟩
      have D : ∃ ν', elimFst φ ψ ν ν' := by apply ihn; simp [prfsize] at *; grind
      rcases D with ⟨ν', D⟩
      exists (case α β χ' μ' ν')
      apply elimFst.case_ef <;> assumption
  }
  intro σ π; apply X (prfsize π + 1) σ π; grind

lemma elimSndExists : ∀ φ ψ σ (π : nkprf σ), ∃ π', elimSnd φ ψ π π' := by
  intro φ ψ
  have X : ∀ d σ (π : nkprf σ), prfsize π < d → ∃ π', elimSnd φ ψ π π' := by {
  intro d; induction d
  · intros ; grind
  · rename_i n ihn; intro σ π Hn; cases π
    · by_cases A : σ = neg (conj φ ψ)
      · subst_vars;
        exists abs (conj φ ψ) _ (app _ _ (ax (neg ψ)) (snd _ _ (ax (conj φ ψ))));
        apply elimSnd.ax1_es
      · exists ax σ; apply elimSnd.ax2_es; exact A
    · rename_i μ;
      have A : ∃ μ', elimSnd φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases A with ⟨μ', A⟩
      exists raa σ μ'; apply elimSnd.raa_es; assumption
    · rename_i α β μ;
      have A : ∃ μ', elimSnd φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases A with ⟨μ', A⟩
      exists abs α β μ'; apply elimSnd.abs_es; assumption
    · rename_i β ν μ
      by_cases A : lrof μ = prax ∧ β = conj φ ψ ∧ σ = bot
      · rcases A with ⟨A,A1,A2⟩; subst_vars
        cases μ <;> simp [lrof] at A; try grind
        clear A; by_cases B : lrof ν = prraa
        · cases ν <;> simp [lrof] at B
          clear B; rename_i μ
          have B : ∃ μ', elimSnd φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
          rcases B with ⟨μ', B⟩
          exists μ'; apply elimSnd.app_axraa_es; try grind
        · have C : ∃ ν', elimSnd φ ψ ν ν' := by apply ihn; simp [prfsize] at *; grind
          rcases C with ⟨ν', C⟩
          exists app _ _ (ax (neg ψ)) (snd _ _ ν');
          apply elimSnd.app_ax_es <;> try grind
      · have B : ∃ μ', elimSnd φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
        rcases B with ⟨μ', B⟩
        have C : ∃ ν', elimSnd φ ψ ν ν' := by apply ihn; simp [prfsize] at *; grind
        rcases C with ⟨ν', C⟩
        exists app β σ μ' ν'; apply elimSnd.app_es <;> try grind
        by_cases D : lrof μ = prax <;> try grind
        simp [D] at A; simp [conc,neg] at *; grind
    · rename_i α β μ ν
      have B : ∃ μ', elimSnd φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      have C : ∃ ν', elimSnd φ ψ ν ν' := by apply ihn; simp [prfsize] at *; grind
      rcases C with ⟨ν', C⟩
      exists (pair α β μ' ν')
      apply elimSnd.pair_es <;> assumption
    · rename_i β μ
      have B : ∃ μ', elimSnd φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (fst σ β μ')
      apply elimSnd.fst_es; assumption
    · rename_i β μ
      have B : ∃ μ', elimSnd φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (snd β σ μ')
      apply elimSnd.snd_es; assumption
    · rename_i α β μ
      have B : ∃ μ', elimSnd φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (left α β μ')
      apply elimSnd.left_es; assumption
    · rename_i α β μ
      have B : ∃ μ', elimSnd φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (right α β μ')
      apply elimSnd.right_es; assumption
    · rename_i α β χ μ ν
      have B : ∃ χ', elimSnd φ ψ χ χ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨χ', B⟩
      have C : ∃ μ', elimSnd φ ψ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases C with ⟨μ', C⟩
      have D : ∃ ν', elimSnd φ ψ ν ν' := by apply ihn; simp [prfsize] at *; grind
      rcases D with ⟨ν', D⟩
      exists (case α β χ' μ' ν')
      apply elimSnd.case_es <;> assumption
  }
  intro σ π; apply X (prfsize π + 1) σ π; grind

lemma elimCaseExists : ∀ φ ψ ρ υ σ (π : nkprf σ), ∃ π', elimCase φ ψ ρ υ π π' := by
  intro φ ψ ρ υ
  have X : ∀ d σ (π : nkprf σ), prfsize π < d → ∃ π', elimCase φ ψ ρ υ π π' := by {
  intro d; induction d
  · intros ; grind
  · rename_i n ihn; intro σ π Hn; cases π
    · by_cases A : σ = neg (disj φ ψ)
      · subst_vars;
        exists abs (φ.disj ψ) _ (case _ _ (ax (φ.disj ψ)) ρ υ);
        apply elimCase.ax1_ec
      · exists ax σ; apply elimCase.ax2_ec; exact A
    · rename_i μ;
      have A : ∃ μ', elimCase φ ψ ρ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases A with ⟨μ', A⟩
      exists raa σ μ'; apply elimCase.raa_ec; assumption
    · rename_i α β μ;
      have A : ∃ μ', elimCase φ ψ ρ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases A with ⟨μ', A⟩
      exists abs α β μ'; apply elimCase.abs_ec; assumption
    · rename_i β ν μ
      by_cases A : lrof μ = prax ∧ β = φ.disj ψ ∧ σ = bot
      · rcases A with ⟨A,A1,A2⟩; subst_vars
        cases μ <;> simp [lrof] at A; try grind
        clear A; by_cases B : lrof ν = prraa
        · cases ν <;> simp [lrof] at B
          clear B; rename_i μ
          have B : ∃ μ', elimCase φ ψ ρ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
          rcases B with ⟨μ', B⟩
          exists μ'; apply elimCase.app_axraa_ec; try grind
        · have C : ∃ ν', elimCase φ ψ ρ υ ν ν' := by apply ihn; simp [prfsize] at *; grind
          rcases C with ⟨ν', C⟩
          exists (case _ _ ν' ρ υ);
          apply elimCase.app_ax_ec <;> try grind
      · have B : ∃ μ', elimCase φ ψ ρ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
        rcases B with ⟨μ', B⟩
        have C : ∃ ν', elimCase φ ψ ρ υ ν ν' := by apply ihn; simp [prfsize] at *; grind
        rcases C with ⟨ν', C⟩
        exists app β σ μ' ν'; apply elimCase.app_ec <;> try grind
        by_cases D : lrof μ = prax <;> try grind
        simp [D] at A; simp [conc,neg]; grind
    · rename_i α β μ ν
      have B : ∃ μ', elimCase φ ψ ρ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      have C : ∃ ν', elimCase φ ψ ρ υ ν ν' := by apply ihn; simp [prfsize] at *; grind
      rcases C with ⟨ν', C⟩
      exists (pair α β μ' ν')
      apply elimCase.pair_ec <;> assumption
    · rename_i β μ
      have B : ∃ μ', elimCase φ ψ ρ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (fst σ β μ')
      apply elimCase.fst_ec; assumption
    · rename_i β μ
      have B : ∃ μ', elimCase φ ψ ρ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (snd β σ μ')
      apply elimCase.snd_ec; assumption
    · rename_i α β μ
      have B : ∃ μ', elimCase φ ψ ρ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (left α β μ')
      apply elimCase.left_ec; assumption
    · rename_i α β μ
      have B : ∃ μ', elimCase φ ψ ρ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨μ', B⟩
      exists (right α β μ')
      apply elimCase.right_ec; assumption
    · rename_i α β χ μ ν
      have B : ∃ χ', elimCase φ ψ ρ υ χ χ' := by apply ihn; simp [prfsize] at *; grind
      rcases B with ⟨χ', B⟩
      have C : ∃ μ', elimCase φ ψ ρ υ μ μ' := by apply ihn; simp [prfsize] at *; grind
      rcases C with ⟨μ', C⟩
      have D : ∃ ν', elimCase φ ψ ρ υ ν ν' := by apply ihn; simp [prfsize] at *; grind
      rcases D with ⟨ν', D⟩
      exists (case α β χ' μ' ν')
      apply elimCase.case_ec <;> assumption
  }
  intro σ π; apply X (prfsize π + 1) σ π; grind

lemma raaCritExists : ∀ α π μ, π = raa α μ →
  maxDeg μ < maxDeg π → exists ϖ, contract π ϖ := by
  intro α π μ eq A; subst_vars
  cases B : α
  · subst_vars; rcases elimBotExists _ μ with ⟨μ',C⟩;
    exists μ'; apply contract.raaBotContract; assumption
  · subst_vars; simp [maxDeg, cutrank, pairAdd_fst, degwt] at A
  · rename_i β γ; cases C : γ
    · subst_vars; rcases elimNegExists β _ μ with ⟨μ',C⟩
      exists abs β bot μ'; apply contract.raaNegContract; assumption
    all_goals (
      subst_vars; simp [maxDeg, cutrank, pairAdd_fst, degwt] at A
    )
  · subst_vars; simp [maxDeg, cutrank, pairAdd_fst, degwt] at A
  · subst_vars; simp [maxDeg, cutrank, pairAdd_fst, degwt] at A

lemma raaCritCondition : ∀ α μ π, π = raa α μ →
  maxDeg μ ≠ maxDeg π → maxDeg μ < maxDeg π := by
  intro α μ π eq A
  have B : maxDeg μ ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; right; simp [self_sp]
  grind

lemma appCritExists : ∀ α β π μ ν, π = app α β μ ν → degree π = maxDeg π →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π → exists ϖ, contract π ϖ := by
  intro α β π μ ν eq A B C; subst_vars
  cases μ <;> rw [← A] at C <;> simp [degree, degwt] at C
  · rename_i μ
    have X : exists μ', elimApp α β ν μ μ' := by apply elimAppExists
    rcases X with ⟨μ', X⟩; exists (raa β μ')
    apply contract.appRaaContract; assumption
  · rename_i μ; set G := graftExists _ ν _ μ;
    rcases G with ⟨μ', G⟩;
    exists μ'; apply contract.appAbsContract; assumption

lemma app1StepCondition : ∀ α β μ ν π, π = app α β μ ν →
  maxDeg ν ≠ maxDeg π → maxDeg ν < maxDeg π := by
  intro α β μ ν π eq A
  have B : maxDeg ν ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; right; simp [self_sp]
  grind

lemma appCritCondition : ∀ α β μ ν π, π = app α β μ ν →
  maxDeg ν ≠ maxDeg π → maxDeg μ ≠ maxDeg π →
  degree π = maxDeg π ∧ maxDeg μ < maxDeg π := by
  intro α β μ ν π eq A B
  have C : maxDeg ν < maxDeg π := by apply app1StepCondition <;> assumption
  have D : maxDeg μ ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; left; right; simp [self_sp]
  have E : degree π ≤ maxDeg π := by apply deg_le_maxDeg
  by_cases F : degree π < maxDeg π
  · simp [eq, degree, maxDeg, cutrank, pairAdd_fst] at F
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

lemma fstCritExists : ∀ α β π μ, π = fst α β μ → degree π = maxDeg π →
  maxDeg μ < maxDeg π → exists ϖ, contract π ϖ := by
  intro α β π μ eq A B; subst_vars
  cases μ <;> rw [← A] at B <;> simp [degree, degwt] at B
  · rename_i μ
    have X : exists μ', elimFst α β μ μ' := by apply elimFstExists
    rcases X with ⟨μ', X⟩; exists (raa α μ')
    apply contract.fstRaaContract; assumption
  · rename_i μ ν;
    exists μ; apply contract.fstPairContract

lemma fstCritCondition : ∀ α β μ π, π = fst α β μ →
  maxDeg μ ≠ maxDeg π → degree π = maxDeg π ∧ maxDeg μ < maxDeg π := by
  intro α β μ π eq A
  have B : maxDeg μ ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; right; simp [self_sp]
  have C : degree π ≤ maxDeg π := by apply deg_le_maxDeg
  by_cases D : degree π < maxDeg π
  · simp [eq, degree, maxDeg, cutrank, pairAdd_fst] at D
    exfalso; apply A; simp [eq, maxDeg, cutrank, pairAdd_fst]; grind
  · constructor <;> try grind

lemma sndCritExists : ∀ α β π μ, π = snd α β μ → degree π = maxDeg π →
  maxDeg μ < maxDeg π → exists ϖ, contract π ϖ := by
  intro α β π μ eq A B; subst_vars
  cases μ <;> rw [← A] at B <;> simp [degree, degwt] at B
  · rename_i μ
    have X : exists μ', elimSnd α β μ μ' := by apply elimSndExists
    rcases X with ⟨μ', X⟩; exists (raa β μ')
    apply contract.sndRaaContract; assumption
  · rename_i μ ν;
    exists ν; apply contract.sndPairContract

lemma sndCritCondition : ∀ α β μ π, π = snd α β μ →
  maxDeg μ ≠ maxDeg π → degree π = maxDeg π ∧ maxDeg μ < maxDeg π := by
  intro α β μ π eq A
  have B : maxDeg μ ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; right; simp [self_sp]
  have C : degree π ≤ maxDeg π := by apply deg_le_maxDeg
  by_cases D : degree π < maxDeg π
  · simp [eq, degree, maxDeg, cutrank, pairAdd_fst] at D
    exfalso; apply A; simp [eq, maxDeg, cutrank, pairAdd_fst]; grind
  · constructor <;> try grind

lemma caseCritExists : ∀ α β π χ μ ν, π = case α β χ μ ν →
  degree π = maxDeg π → maxDeg χ < maxDeg π →
  maxDeg μ < maxDeg π → maxDeg ν < maxDeg π →
  exists ϖ, contract π ϖ := by
  intro α β π χ μ ν eq A B C D; subst_vars
  cases χ <;> rw [← A] at B <;> simp [degree, degwt] at B
  · rename_i χ
    have X : exists χ', elimCase α β μ ν χ χ' := by
        apply elimCaseExists
    rcases X with ⟨χ', X⟩; exists χ'
    apply contract.caseRaaContract; assumption
  · rename_i χ; set G := graftExists _ χ _ μ;
    rcases G with ⟨μ', G⟩;
    exists μ'; apply contract.caseLeftContract; assumption
  · rename_i χ; set G := graftExists _ χ _ ν;
    rcases G with ⟨ν', G⟩;
    exists ν'; apply contract.caseRightContract; assumption

lemma case2StepCondition : ∀ α β χ μ ν π, π = case α β χ μ ν →
  maxDeg ν ≠ maxDeg π → maxDeg ν < maxDeg π := by
  intro α β χ μ ν π eq A
  have B : maxDeg ν ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; right; simp [self_sp]
  grind

lemma case1StepCondition : ∀ α β χ μ ν π, π = case α β χ μ ν →
  maxDeg ν ≠ maxDeg π → maxDeg μ ≠ maxDeg π → maxDeg μ < maxDeg π := by
  intro α β χ μ ν π eq A B
  · have C : maxDeg μ ≤ maxDeg π := by
      apply maxDeg_sp; simp [eq, subproofs]; left; right; simp [self_sp]
    grind

lemma caseCritCondition : ∀ α β χ μ ν π, π = case α β χ μ ν →
  maxDeg ν ≠ maxDeg π → maxDeg μ ≠ maxDeg π → maxDeg χ ≠ maxDeg π →
  degree π = maxDeg π ∧ maxDeg χ < maxDeg π := by
  intro α β χ μ ν π eq A B C
  have D : maxDeg ν < maxDeg π ∧ maxDeg μ < maxDeg π := by
    constructor
    · apply case2StepCondition <;> assumption
    · apply case1StepCondition <;> assumption
  rcases D with ⟨D1, D2⟩
  have E : maxDeg χ ≤ maxDeg π := by
    apply maxDeg_sp; simp [eq, subproofs]; left; left; right; simp [self_sp]
  have F : degree π ≤ maxDeg π := by apply deg_le_maxDeg
  by_cases G : degree π < maxDeg π
  · simp [eq, degree, maxDeg, cutrank, pairAdd_fst] at G
    simp [eq, maxDeg, cutrank, pairAdd_fst] at D1
    simp [eq, maxDeg, cutrank, pairAdd_fst] at D2
    exfalso; apply C; simp [eq, maxDeg, cutrank, pairAdd_fst]
    simp [maxDeg] at *
    rcases D1 with D1 | D1 | D1 <;> rcases D2 with D2 | D2 <;>
      rcases G with G | G | G  <;> try grind
  · constructor <;> try grind

lemma oneStepExists : ∀ φ (π : nkprf φ),
  maxDeg π > 0 → ∃ π', oneStep _ π π' := by
  intro φ π
  induction π <;> clear φ <;> intro Hmd
  · -- ax
    rename_i α; simp [maxDeg, cutrank, degwt] at Hmd
  · -- raa
    rename_i α μ ihμ
    by_cases B0 : maxDeg μ = maxDeg (raa α μ)
    · rw [←B0] at Hmd; rcases ihμ Hmd with ⟨μ', Hstep⟩
      exists (raa α μ'); apply oneStep.raaStep
      rfl; grind; grind
    · have B1 : maxDeg μ < maxDeg (raa α μ) := by
        apply raaCritCondition; rfl; grind
      have B2 : ∃ ϖ, contract (raa α μ) ϖ := by
        apply raaCritExists; rfl; exact B1
      rcases B2 with ⟨ϖ, cont⟩
      exists ϖ; apply oneStep.raaCrit; rfl; exact cont; assumption
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
      by_cases B2 : maxDeg μ = maxDeg (app α β μ ν)
      · rw [←B2] at Hmd; rcases ihμ Hmd with ⟨μ', step⟩
        exists (app α β μ' ν); apply oneStep.app1Step
        rfl; grind; grind; grind
      · have B3 : degree (app α β μ ν) = maxDeg (app α β μ ν)
            ∧ maxDeg μ < maxDeg (app α β μ ν) := by
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
    by_cases B0 : maxDeg μ = maxDeg (fst α β μ)
    · rw [←B0] at Hmd; rcases ihμ Hmd with ⟨μ', step⟩
      exists (fst α β μ'); apply oneStep.fstStep
      rfl; grind; grind
    · have B1 : degree (fst α β μ) = maxDeg (fst α β μ) ∧
                maxDeg μ < maxDeg (fst α β μ) := by
        apply fstCritCondition; rfl; grind
      have cont : ∃ ϖ, contract (fst α β μ) ϖ := by
        apply fstCritExists; rfl; grind; grind
      rcases cont with ⟨ϖ, cont⟩; exists ϖ; apply oneStep.fstCrit
      rfl; assumption; grind; grind
  · -- snd
    rename_i α β μ ihμ
    by_cases B0 : maxDeg μ = maxDeg (snd α β μ)
    · rw [←B0] at Hmd; rcases ihμ Hmd with ⟨μ', step⟩
      exists (snd α β μ'); apply oneStep.sndStep
      rfl; grind; grind;
    · have B1 : degree (snd α β μ) = maxDeg (snd α β μ) ∧
                maxDeg μ < maxDeg (snd α β μ)  := by
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
    rename_i α β χ μ ν ihχ ihμ ihν
    by_cases B0 : maxDeg ν = maxDeg (case α β χ μ ν)
    · rw [←B0] at Hmd; rcases ihν Hmd with ⟨ν', step⟩
      exists (case α β χ μ ν'); apply oneStep.case3Step
      rfl; assumption; assumption
    · have B1 : maxDeg ν < maxDeg (case α β χ μ ν) := by
        apply case2StepCondition; rfl; grind
      by_cases B2 : maxDeg μ = maxDeg (case α β χ μ ν)
      · rw [←B2] at Hmd; rcases ihμ Hmd with ⟨μ', step⟩
        exists (case α β χ μ' ν); apply oneStep.case2Step
        rfl; assumption; assumption; assumption
      · have B3 : maxDeg μ < maxDeg (case α β χ μ ν) := by
          apply case1StepCondition; rfl; grind; grind
        by_cases B4 : maxDeg χ = maxDeg (case α β χ μ ν)
        · rw [←B4] at Hmd; rcases ihχ Hmd with ⟨χ', step⟩
          exists (case α β χ' μ ν); apply oneStep.case1Step
          rfl; grind; grind; grind; grind
        · have B5 : degree (case α β χ μ ν) = maxDeg (case α β χ μ ν) ∧
                  maxDeg χ < maxDeg (case α β χ μ ν)  := by
            apply caseCritCondition; rfl; grind; assumption; grind
          have cont : ∃ ϖ, contract (case α β χ μ ν) ϖ := by
              apply caseCritExists; rfl; grind; grind; grind; grind
          rcases cont with ⟨ϖ, cont⟩; exists ϖ; apply oneStep.caseCrit
          rfl; assumption; grind; grind; grind; grind

lemma cr_wf {φ : propform} : WellFounded
  (fun (ϖ π : nkprf φ) ↦ cutrank ϖ < cutrank π) := by
  exact InvImage.wf cutrank (WellFoundedRelation.wf)

theorem normalization : ∀ φ (π : nkprf φ), ∃ (ϖ : nkprf φ),
  isNormal ϖ ∧ hypos ϖ ⊆ hypos π ∧ conc ϖ = conc π := by
  intro φ υ
  apply WellFounded.induction (cr_wf)
    (C := fun π : nkprf φ => ∃ (ϖ : nkprf φ),
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

end nkNorm
