import Mathlib

import NatDed.nk
import NatDed.Rank
import NatDed.nkNorm

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.style.multiGoal false

namespace subform
open Rank
open nk
open nk.propform
open nk.nkprf
open nk.proofrule
open nkNorm

inductive isNeutral : {φ : propform} → nkprf φ → Prop where
| axNeut : ∀ α π, π = ax α → isNeutral π
| appNeut : ∀ α β μ ν π, π = app α β μ ν → isNormal π → isNeutral π
| fstNeut : ∀ α β μ π, π = fst α β μ → isNormal π → isNeutral π
| sndNeut : ∀ α β μ π, π = snd α β μ → isNormal π → isNeutral π
| caseNeut : ∀ α β χ μ ν π, π = case α β χ μ ν → isNormal π → isNeutral π

lemma neutral_normal : ∀ φ (π : nkprf φ), isNeutral π → isNormal π := by
  intro φ π Hneut; cases Hneut <;> subst_vars <;> try grind
  apply isNormal.axNorm; rfl

lemma normal_sp : ∀ φ ψ (π : nkprf φ) (π' : nkprf ψ),
  ⟨ψ, π'⟩ ∈ subproofs π → isNormal π → isNormal π' := by
  intro φ ψ π π' Hsp Hnorm; induction Hnorm
  · rename_i α μ eq; subst_vars; simp [subproofs] at Hsp
    cases Hsp; apply isNormal.axNorm; grind
  · rename_i α ν μ A B C ih; subst_vars;
    simp [subproofs] at Hsp; rcases Hsp with H | H
    · cases H; cases ψ
      · exfalso; apply C; apply isCut.raaBot
      · apply isNormal.raaNorm; rfl; assumption; assumption
      · rename_i α β; cases β
        · exfalso; apply C; apply isCut.raaNeg
        all_goals (apply isNormal.raaNorm; rfl; assumption; assumption)
      · apply isNormal.raaNorm; rfl; assumption; assumption
      · apply isNormal.raaNorm; rfl; assumption; assumption
    · grind
  · rename_i α β ν μ A B ih; subst_vars; simp [subproofs] at Hsp
    rcases Hsp with H | H
    · cases H; apply isNormal.absNorm; rfl; assumption
    · grind
  · rename_i α β μ ν χ eq A B C ihμ ihν
    subst_vars; simp [subproofs] at Hsp
    rcases Hsp with (H | H) | H
    · cases H; apply isNormal.appNorm; rfl;
      assumption; assumption; assumption
    · grind
    · grind
  · rename_i α β μ ν χ eq A B ihμ ihν
    subst_vars; simp [subproofs] at Hsp
    rcases Hsp with (H | H) | H
    · cases H; apply isNormal.pairNorm; rfl;
      assumption; assumption
    · grind
    · grind
  · rename_i α β μ χ eq A B ihμ
    subst_vars; simp [subproofs] at Hsp
    rcases Hsp with H | H
    · cases H; apply isNormal.fstNorm; rfl;
      assumption; assumption
    · grind
  · rename_i α β μ χ eq A B ihμ
    subst_vars; simp [subproofs] at Hsp
    rcases Hsp with H | H
    · cases H; apply isNormal.sndNorm; rfl;
      assumption; assumption
    · grind
  · rename_i α β μ χ eq A ihμ
    subst_vars; simp [subproofs] at Hsp
    rcases Hsp with H | H
    · cases H; apply isNormal.leftNorm; rfl; assumption
    · grind
  · rename_i α β μ χ eq A ihμ
    subst_vars; simp [subproofs] at Hsp
    rcases Hsp with H | H
    · cases H; apply isNormal.rightNorm; rfl; assumption
    · grind
  · rename_i α β χ μ ν ϖ eq A B C D ihχ ihμ ihν
    subst_vars; simp [subproofs] at Hsp
    rcases Hsp with ((H | H) | H) | H
    · cases H; apply isNormal.caseNorm; rfl;
      assumption; assumption; assumption; assumption
    · grind
    · grind
    · grind

lemma botNeutral : ∀ α (μ : nkprf α), α = bot → isNormal μ → isNeutral μ := by
  intro α μ eq Hnorm; induction Hnorm <;> subst_vars <;> try grind
  · apply isNeutral.axNeut; rfl
  · rename_i ν A B C; exfalso; apply C; apply isCut.raaBot
  · apply isNeutral.appNeut; rfl; apply isNormal.appNorm;
    rfl; assumption; assumption; assumption
  · apply isNeutral.fstNeut; rfl; apply isNormal.fstNorm;
    rfl; assumption; assumption
  · apply isNeutral.sndNeut; rfl; apply isNormal.sndNorm;
    rfl; assumption; assumption
  · apply isNeutral.caseNeut; rfl; apply isNormal.caseNorm;
    rfl; assumption; assumption; assumption; assumption

lemma raaNormal_msp  : ∀ α μ, isNormal (raa α μ) → isNeutral μ := by
  intro α μ Hnorm; apply botNeutral; rfl
  apply normal_sp (π := raa α μ); simp [subproofs]; right;
  apply self_sp; assumption

lemma appNormal_msp : ∀ α β μ ν, isNormal (app α β μ ν) → isNeutral μ := by
  intro α β μ ν Hnorm; cases Hnorm <;> try grind
  rename_i σ υ A ρ B C D; cases C
  cases μ
  · apply isNeutral.axNeut; rfl
  · exfalso; apply D; apply isCut.appRaa
  · exfalso; apply D; apply isCut.appAbs
  · apply isNeutral.appNeut; rfl; assumption
  · apply isNeutral.fstNeut; rfl; assumption
  · apply isNeutral.sndNeut; rfl; assumption

lemma fstNormal_msp : ∀ α β μ, isNormal (fst α β μ) → isNeutral μ := by
  intro α β μ Hnorm; cases Hnorm <;> try grind
  rename_i σ υ A B C; cases B
  cases μ
  · apply isNeutral.axNeut; rfl
  · exfalso; apply C; apply isCut.fstRaa
  · apply isNeutral.appNeut; rfl; assumption
  · exfalso; apply C; apply isCut.fstPair
  · apply isNeutral.fstNeut; rfl; assumption
  · apply isNeutral.sndNeut; rfl; assumption

lemma sndNormal_msp : ∀ α β μ, isNormal (snd α β μ) → isNeutral μ := by
  intro α β μ Hnorm; cases Hnorm <;> try grind
  rename_i σ υ A B C; cases B
  cases μ
  · apply isNeutral.axNeut; rfl
  · exfalso; apply C; apply isCut.sndRaa
  · apply isNeutral.appNeut; rfl; assumption
  · exfalso; apply C; apply isCut.sndPair
  · apply isNeutral.fstNeut; rfl; assumption
  · apply isNeutral.sndNeut; rfl; assumption

lemma caseNormal_msp : ∀ α β χ μ ν, isNormal (case α β χ μ ν) → isNeutral χ := by
  intro α β χ μ ν Hnorm; cases Hnorm <;> try grind
  rename_i σ τ ρ1 E ρ2 ρ3 F G H I; cases H
  cases χ
  · apply isNeutral.axNeut; rfl
  · exfalso; apply I; apply isCut.caseRaa
  · apply isNeutral.appNeut; rfl; assumption
  · apply isNeutral.fstNeut; rfl; assumption
  · apply isNeutral.sndNeut; rfl; assumption
  · exfalso; apply I; apply isCut.caseLeft
  · exfalso; apply I; apply isCut.caseRight

lemma cl_neg : ∀ α μ, isNormal (raa α μ) → cl (neg α) = cl α := by
  intro α μ Hnorm; cases Hnorm <;> try grind
  rename_i ν G eq F; cases eq
  have X : ∀ β, α ≠ impl β bot := by
    intro β Y; subst_vars;
    set F' := isCut.raaNeg β μ; exact F F'
  cases α
  · simp [neg, cl, bar]; grind
  · simp [neg, cl, bar]; grind
  · rename_i γ δ;
    have A: bar (γ.impl δ) = neg (γ.impl δ) := by simp [bar, neg]
    rw [←A, ←impl_cl]; intro Z; subst_vars; apply X; rfl
  · rename_i γ δ;
    have A : bar (γ.conj δ) = neg (γ.conj δ) := by simp [bar, neg]
    rw [←A, ←conj_cl]
  · rename_i γ δ;
    have A : bar (γ.disj δ) = neg (γ.disj δ) := by simp [bar, neg]
    rw [←A, ←disj_cl]

lemma formsin_normal : ∀ φ (π : nkprf φ),
  (isNormal π → formsin π ⊆ CL (hypos π ∪ {conc π})) ∧
  (isNeutral π → formsin π ⊆ CL (hypos π)) := by
  intro φ π
  induction π
  · -- ax
    constructor <;> intro H <;> simp [formsin, conc, hypos, CL, self_cl]
  · -- raa
    rename_i α μ ihμ
    constructor
    · intro Hnorm x H; simp [formsin] at H; rcases H with H | H
      · simp [H, CL, conc, self_cl]
      · apply ihμ.2 (raaNormal_msp _ _ Hnorm) at H
        simp [CL, hypos, conc]; simp [CL] at H;
        rcases H with ⟨φ, H1, H2⟩
        by_cases A : φ = neg α
        · subst_vars; rw [cl_neg α μ] at H2 <;> grind
        · right; exists φ
    · intro H; cases H <;> try grind
  · -- abs
    rename_i α β μ ihμ
    constructor
    · intro Hnorm x H; simp [formsin] at H; rcases H with H | H
      · simp [H, CL, conc, self_cl]
      · apply ihμ.1 at H
        · simp [CL, conc] at H; simp [CL]; rcases H with H | ⟨σ, H⟩
          · simp [conc, cl, H]
          · simp [hypos]
            by_cases G : x ∈ cl α
            · simp [conc, cl, G]
            · right; exists σ; simp [H]; intro C; subst_vars; grind
        · apply normal_sp _ _ (abs α β μ);
          simp [subproofs]; right; simp [self_sp]; assumption
    · intro H; cases H <;> try grind
  · -- app
    rename_i α β μ ν ihμ ihν
    have A :  isNormal (app α β μ ν) →
          formsin (app α β μ ν) ⊆ CL (hypos (app α β μ ν)) := by {
      intro Hnorm x H;
      have F : α.impl β ∈ CL (hypos μ) := by {
        have F : α.impl β ∈ formsin μ := by apply conc_in_forms
        apply ihμ.2 (appNormal_msp _ _ _ _ Hnorm) at F; assumption
      }
      simp [formsin] at H; rcases H with (H | H) | H
      · simp [H, CL, hypos]; simp [CL] at F; rcases F with ⟨τ, ⟨F1,F2⟩⟩
        exists τ; simp [F1]; apply cl_trans (ψ := α.impl β)
        simp [cl, self_cl]; exact F2
      · apply ihμ.1 at H
        · simp [CL, conc] at H; simp [CL]; rcases H with H | ⟨σ, ⟨H1,H2⟩⟩
          · simp [CL] at F; rcases F with ⟨τ,⟨F1,F2⟩⟩
            set X := cl_trans _ _ _ H F2;
            exists τ; simp [X]; simp [hypos, F1]
          · exists σ; simp [H2]; simp [hypos,H1]
        · cases Hnorm <;> try grind
      · apply ihν.1 at H
        · simp [CL, conc] at H; simp [CL]; rcases H with H | ⟨σ, ⟨H1,H2⟩⟩
          · simp [CL] at F; rcases F with ⟨τ,⟨F1,F2⟩⟩
            have X : x ∈ cl τ := by {
              apply cl_trans (ψ := α.impl β);
              apply cl_trans; exact H; simp [cl, self_cl]; exact F2
            }
            exists τ; simp [X]; simp [hypos, F1]
          · exists σ; simp [H2]; simp [hypos,H1]
        · cases Hnorm <;> try grind
    }
    constructor
    · intro H x G; apply A H at G; simp [CL]; simp [CL] at G; simp [G]
    · intro H; apply A; apply neutral_normal; assumption
  · -- pair
    rename_i α β μ ν ihμ ihν
    constructor
    · intro Hnorm x H; simp [formsin] at H; rcases H with (H | H) | H
      · simp [H, CL, conc, self_cl]
      · apply ihμ.1 at H
        · simp [CL, conc] at H; simp [CL]; rcases H with H | ⟨σ, H⟩
          · simp [conc, cl, H]
          · simp [hypos]
            by_cases G : x ∈ cl α
            · simp [conc, cl, G]
            · right; exists σ; simp [H]
        · apply normal_sp _ _ (pair α β μ ν);
          simp [subproofs]; left; right; simp [self_sp];
          assumption
      · apply ihν.1 at H
        · simp [CL, conc] at H; simp [CL]; rcases H with H | ⟨σ, H⟩
          · simp [conc, cl, H]
          · simp [hypos]
            by_cases G : x ∈ cl α
            · simp [conc, cl, G]
            · right; exists σ; simp [H]
        · apply normal_sp _ _ (pair α β μ ν);
          simp [subproofs]; right; simp [self_sp];
          assumption
    · intro H; cases H <;> try grind
  · -- fst
    rename_i α β μ ihμ
    have A : isNormal (fst α β μ) →
          formsin (fst α β μ) ⊆ CL (hypos (fst α β μ)) := by {
      intro Hnorm x H;
      have F : α.conj β ∈ CL (hypos μ) := by {
        have F : α.conj β ∈ formsin μ := by apply conc_in_forms
        apply ihμ.2 (fstNormal_msp _ _ _ Hnorm) at F; assumption
      }
      simp [formsin] at H; rcases H with H | H
      · simp [H, CL, hypos]; simp [CL] at F; rcases F with ⟨τ, ⟨F1,F2⟩⟩
        exists τ; simp [F1]; apply cl_trans (ψ := α.conj β)
        simp [cl, self_cl]; exact F2
      · apply ihμ.1 at H
        · simp [CL, conc] at H; simp [CL]; rcases H with H | ⟨σ, ⟨H1,H2⟩⟩
          · simp [CL] at F; rcases F with ⟨τ,⟨F1,F2⟩⟩
            set X := cl_trans _ _ _ H F2;
            exists τ
          · exists σ
        · cases Hnorm <;> try grind
    }
    constructor
    · intro H x G; apply A H at G; simp [CL]; simp [CL] at G; simp [G]
    · intro H; apply A; apply neutral_normal; assumption
  · -- snd
    rename_i α β μ ihμ
    have A :  isNormal (snd α β μ) →
          formsin (snd α β μ) ⊆ CL (hypos (snd α β μ)) := by {
      intro Hnorm x H;
      have F : α.conj β ∈ CL (hypos μ) := by {
        have F : α.conj β ∈ formsin μ := by apply conc_in_forms
        apply ihμ.2 (sndNormal_msp _ _ _ Hnorm) at F; assumption
      }
      simp [formsin] at H; rcases H with H | H
      · simp [H, CL, hypos]; simp [CL] at F; rcases F with ⟨τ, ⟨F1,F2⟩⟩
        exists τ; simp [F1]; apply cl_trans (ψ := α.conj β)
        simp [cl, self_cl]; exact F2
      · apply ihμ.1 at H
        · simp [CL, conc] at H; simp [CL]; rcases H with H | ⟨σ, ⟨H1,H2⟩⟩
          · simp [CL] at F; rcases F with ⟨τ,⟨F1,F2⟩⟩
            set X := cl_trans _ _ _ H F2;
            exists τ
          · exists σ
        · cases Hnorm <;> try grind
    }
    constructor
    · intro H x G; apply A H at G; simp [CL]; simp [CL] at G; simp [G]
    · intro H; apply A; apply neutral_normal; assumption
  · -- left
    rename_i α β μ ihμ
    constructor
    · intro Hnorm x H; simp [formsin] at H; rcases H with H | H
      · simp [H, CL, conc, self_cl]
      · apply ihμ.1 at H
        · simp [CL, conc] at H; simp [CL]; rcases H with H | ⟨σ, H⟩
          · simp [conc, cl, H]
          · simp [hypos]
            by_cases G : x ∈ cl α
            · simp [conc, cl, G]
            · right; exists σ
        · apply normal_sp _ _ (left α β μ);
          simp [subproofs]; right; simp [self_sp]; assumption
    · intro H; cases H <;> try grind
  · -- right
    rename_i α β μ ihμ
    constructor
    · intro Hnorm x H; simp [formsin] at H; rcases H with H | H
      · simp [H, CL, conc, self_cl]
      · apply ihμ.1 at H
        · simp [CL, conc] at H; simp [CL]; rcases H with H | ⟨σ, H⟩
          · simp [conc, cl, H]
          · simp [hypos]
            by_cases G : x ∈ cl α
            · simp [conc, cl, G]
            · right; exists σ
        · apply normal_sp _ _ (right α β μ);
          simp [subproofs]; right; simp [self_sp]; assumption
    · intro H; cases H <;> try grind
  · -- case
    rename_i α β χ μ ν ihχ ihμ ihν
    have A :  isNormal (case α β χ μ ν) →
          formsin (case α β χ μ ν) ⊆ CL (hypos (case α β χ μ ν)) := by {
      intro Hnorm x H;
      have C' : isNeutral χ := by apply caseNormal_msp; assumption
      have C : isNormal χ := by apply neutral_normal; assumption
      have D : isNormal μ := by
        apply normal_sp (π := case α β χ μ ν); simp [subproofs];
        left; right; simp [self_sp]; assumption
      have D' : isNeutral μ := by apply botNeutral; rfl; assumption
      have E : isNormal ν := by
        apply normal_sp (π := case α β χ μ ν); simp [subproofs];
        right; simp [self_sp]; assumption
      have E' : isNeutral ν := by apply botNeutral; rfl; assumption
      have F : α.disj β ∈ CL (hypos χ) := by {
        have F : α.disj β ∈ formsin χ := by apply conc_in_forms
        grind
      }
      simp [formsin] at H; rcases H with (H | H) | H
      · apply ihχ.2 at H; apply CL_cong (hypos χ); simp [hypos]
        grind; grind; grind
      · apply ihμ.2 at H
        · by_cases G : x ∈ cl α
          · simp [CL] at F; rcases F with ⟨τ, ⟨F1,F2⟩⟩
            have X : x ∈ cl τ := by {
              apply cl_trans (ψ := α.disj β)
              apply cl_trans; exact G; simp [cl, self_cl]; exact F2
            }
            apply CL_cong (hypos χ); simp [hypos]; grind;
            simp [CL]; exists τ
          · simp [CL] at H; rcases H with ⟨τ, H1, H2⟩
            simp [CL]; exists τ; simp [hypos, H2]
            left; right; simp [H1]; intro Z; subst_vars; grind
        · assumption
      · apply ihν.2 at H
        · by_cases G : x ∈ cl β
          · simp [CL] at F; rcases F with ⟨τ, ⟨F1,F2⟩⟩
            have X : x ∈ cl τ := by {
              apply cl_trans (ψ := α.disj β)
              apply cl_trans; exact G; simp [cl, self_cl]; exact F2
            }
            apply CL_cong (hypos χ); simp [hypos]; grind;
            simp [CL]; exists τ
          · simp [CL] at H; rcases H with ⟨τ, H1, H2⟩
            simp [CL]; exists τ; simp [hypos, H2]
            right; simp [H1]; intro Z; subst_vars; grind
        · assumption
    }
    constructor
    · intro Hnorm; apply A at Hnorm; intro x Hx; apply Hnorm at Hx;
      apply CL_cong (hypos (case α β χ μ ν)); grind; assumption
    · intro Hneut; apply A; apply neutral_normal; assumption

theorem subformula : ∀ φ (π : nkprf φ), ∃ (ϖ : nkprf φ),
  hypos ϖ ⊆ hypos π ∧ conc ϖ = conc π
      ∧ formsin ϖ ⊆ CL (hypos ϖ ∪ {conc ϖ}) := by
  intro φ π
  let h := normalization _ π
  rcases h with ⟨ϖ, h1, h2, h3⟩
  exists ϖ; simp [h2, h3]; apply (formsin_normal _ ϖ).1 at h1
  rw [← h3]; simp at h1; assumption

end subform
