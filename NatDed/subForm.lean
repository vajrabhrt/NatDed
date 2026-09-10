import Mathlib

import NatDed.nj
import NatDed.Rank
import NatDed.njNorm

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.style.multiGoal false

namespace subform
open Rank
open nj
open nj.propform
open nj.njprf
open nj.proofrule
open njNorm

inductive isNeutral : {φ : propform} → njprf φ → Prop where
| axNeut : ∀ α π, π = ax α → isNeutral π
| appNeut : ∀ α β μ ν π, π = app α β μ ν → isNormal π → isNeutral π
| fstNeut : ∀ α β μ π, π = fst α β μ → isNormal π → isNeutral π
| sndNeut : ∀ α β μ π, π = snd α β μ → isNormal π → isNeutral π
| caseNeut : ∀ α β χ μ ν π, π = case α β bot χ μ ν → isNormal π → isNeutral π

lemma neutral_normal : ∀ φ (π : njprf φ), isNeutral π → isNormal π := by
  intro φ π Hneut; cases Hneut <;> subst_vars <;> try grind
  apply isNormal.axNorm; rfl

lemma normal_sp : ∀ φ ψ (π : njprf φ) (π' : njprf ψ),
  ⟨ψ, π'⟩ ∈ subproofs π → isNormal π → isNormal π' := by
  unhygienic
  intro φ ψ π π' Hsp Hnorm; induction Hnorm <;>
    subst_vars <;> simp [subproofs] at Hsp <;> try grind
  · cases Hsp; apply isNormal.axNorm; rfl
  · cases Hsp <;> try grind
    cases h; by_cases  ψ = bot
    subst_vars; exfalso; apply a_2; apply isCut.empBot
    apply isNormal.empNorm; rfl; grind; grind
  · cases Hsp <;> try grind
    cases h; apply isNormal.absNorm; rfl; grind
  · cases Hsp <;> try grind
    cases h <;> try grind
    cases h_1; apply isNormal.appNorm; rfl; grind; grind; grind
  · cases Hsp <;> try grind
    cases h <;> try grind
    cases h_1; apply isNormal.pairNorm; rfl; grind; grind
  · cases Hsp <;> try grind
    cases h; apply isNormal.fstNorm; rfl; grind; grind
  · cases Hsp <;> try grind
    cases h; apply isNormal.sndNorm; rfl; grind; grind
  · cases Hsp <;> try grind
    cases h; apply isNormal.leftNorm; rfl; grind
  · cases Hsp <;> try grind
    cases h; apply isNormal.rightNorm; rfl; grind
  · cases Hsp <;> try grind
    cases h <;> try grind
    cases h_1 <;> try grind
    cases h; apply isNormal.caseNorm; rfl; grind; grind; grind; grind

lemma empNormal_msp : ∀ α μ, isNormal (emp α μ) → isNeutral μ := by
  intro α μ Hnorm; cases Hnorm <;> try grind
  rename_i ν A B C; cases B
  by_cases X:  α = bot
  · subst_vars; exfalso; apply C; apply isCut.empBot
  · clear X; cases μ
    · apply isNeutral.axNeut; rfl
    · exfalso; cases A <;> try grind
      rename_i D; apply D; apply isCut.empBot
    · apply isNeutral.appNeut; rfl; assumption
    · apply isNeutral.fstNeut; rfl; assumption
    · apply isNeutral.sndNeut; rfl; assumption
    · apply isNeutral.caseNeut; rfl; assumption

lemma appNormal_msp : ∀ α β μ ν, isNormal (app α β μ ν) → isNeutral μ := by
  intro α β μ ν Hnorm; cases Hnorm <;> try grind
  rename_i σ υ A ρ B C D; cases C
  cases μ
  · apply isNeutral.axNeut; rfl
  · exfalso; apply D; apply isCut.appEmp
  · exfalso; apply D; apply isCut.appAbs
  · apply isNeutral.appNeut; rfl; assumption
  · apply isNeutral.fstNeut; rfl; assumption
  · apply isNeutral.sndNeut; rfl; assumption
  · exfalso; apply D; apply isCut.appCase

lemma fstNormal_msp : ∀ α β μ, isNormal (fst α β μ) → isNeutral μ := by
  intro α β μ Hnorm; cases Hnorm <;> try grind
  rename_i σ υ A B C; cases B
  cases μ
  · apply isNeutral.axNeut; rfl
  · exfalso; apply C; apply isCut.fstEmp
  · apply isNeutral.appNeut; rfl; assumption
  · exfalso; apply C; apply isCut.fstPair
  · apply isNeutral.fstNeut; rfl; assumption
  · apply isNeutral.sndNeut; rfl; assumption
  · exfalso; apply C; apply isCut.fstCase

lemma sndNormal_msp : ∀ α β μ, isNormal (snd α β μ) → isNeutral μ := by
  intro α β μ Hnorm; cases Hnorm <;> try grind
  rename_i σ υ A B C; cases B
  cases μ
  · apply isNeutral.axNeut; rfl
  · exfalso; apply C; apply isCut.sndEmp
  · apply isNeutral.appNeut; rfl; assumption
  · exfalso; apply C; apply isCut.sndPair
  · apply isNeutral.fstNeut; rfl; assumption
  · apply isNeutral.sndNeut; rfl; assumption
  · exfalso; apply C; apply isCut.sndCase

lemma caseNormal_msp : ∀ α β δ χ μ ν, isNormal (case α β δ χ μ ν) → isNeutral χ := by
  intro α β δ χ μ ν Hnorm; cases Hnorm <;> try grind
  rename_i σ τ ρ1 E ρ2 ρ3 F G H I; cases H
  cases χ
  · apply isNeutral.axNeut; rfl
  · exfalso; apply I; apply isCut.caseEmp
  · apply isNeutral.appNeut; rfl; assumption
  · apply isNeutral.fstNeut; rfl; assumption
  · apply isNeutral.sndNeut; rfl; assumption
  · exfalso; apply I; apply isCut.caseLeft
  · exfalso; apply I; apply isCut.caseRight
  · exfalso; apply I; apply isCut.caseCase

lemma caseNeutral_ssp : ∀ α β δ χ μ ν, isNeutral (case α β δ χ μ ν) → isNeutral μ := by
  intro α β δ χ μ ν Hnorm; cases Hnorm <;> try grind
  rename_i σ τ ρ1 ρ2 ρ3 E F; cases E
  cases ρ2
  · apply isNeutral.axNeut; rfl
  · rename_i μ3
    have C : isNormal (emp bot μ3) := by {
      apply normal_sp _ _ (case α β bot χ (emp bot μ3) ρ3)
      simp [subproofs]; grind; grind
    }
    cases C <;> try grind
    rename_i C; exfalso; apply C; apply isCut.empBot
  · rename_i σ υ1 υ2; apply isNeutral.appNeut; rfl;
    apply normal_sp _ _ (case α β bot χ (app σ bot υ2 υ1) ρ3)
    simp [subproofs]; grind; grind
  · rename_i σ υ; apply isNeutral.fstNeut; rfl;
    apply normal_sp _ _ (case α β bot χ (fst bot σ υ) ρ3)
    simp [subproofs]; grind; grind
  · rename_i σ υ; apply isNeutral.sndNeut; rfl;
    apply normal_sp _ _ (case α β bot χ (snd σ bot υ) ρ3)
    simp [subproofs]; grind; grind
  · rename_i σ τ υ1 υ2; apply isNeutral.caseNeut; rfl
    rename_i γ; apply normal_sp _ _ (case α β bot χ (case γ σ bot τ υ1 υ2) ρ3)
    simp [subproofs]; left; grind; grind

lemma formsin_normal : ∀ φ (π : njprf φ),
  (isNormal π → formsin π ⊆ SF (hypos π ∪ {conc π})) ∧
  (isNeutral π → formsin π ⊆ SF (hypos π)) := by
  intro φ π
  induction π
  · -- ax
    constructor <;> intro H <;> simp [formsin, conc, hypos, SF, self_sf]
  · -- emp
    rename_i α μ ihμ
    constructor
    · intro Hnorm x H; simp [formsin] at H; rcases H with H | H
      · simp [H, SF, conc, self_sf]
      · apply ihμ.2 (empNormal_msp _ _ Hnorm) at H
        simp [SF, hypos]; right; assumption
    · intro H; cases H <;> try grind
  · -- abs
    rename_i α β μ ihμ
    constructor
    · intro Hnorm x H; simp [formsin] at H; rcases H with H | H
      · simp [H, SF, conc, self_sf]
      · apply ihμ.1 at H
        · simp [SF, conc] at H; simp [SF]; rcases H with H | ⟨σ, H⟩
          · simp [conc, sf, H]
          · simp [hypos]
            by_cases G : x ∈ sf α
            · simp [conc, sf, G]
            · right; exists σ; simp [H]; intro C; subst_vars; grind
        · apply normal_sp _ _ (abs α β μ);
          simp [subproofs]; right; simp [self_sp]; assumption
    · intro H; cases H <;> try grind
  · -- app
    rename_i α β μ ν ihμ ihν
    have A :  isNormal (app α β μ ν) →
          formsin (app α β μ ν) ⊆ SF (hypos (app α β μ ν)) := by {
      intro Hnorm x H;
      have F : α.impl β ∈ SF (hypos μ) := by {
        have F : α.impl β ∈ formsin μ := by apply conc_in_forms
        apply ihμ.2 (appNormal_msp _ _ _ _ Hnorm) at F; assumption
      }
      simp [formsin] at H; rcases H with (H | H) | H
      · simp [H, SF, hypos]; simp [SF] at F; rcases F with ⟨τ, ⟨F1,F2⟩⟩
        exists τ; simp [F1]; apply sf_trans (ψ := α.impl β)
        simp [sf, self_sf]; exact F2
      · apply ihμ.1 at H
        · simp [SF, conc] at H; simp [SF]; rcases H with H | ⟨σ, ⟨H1,H2⟩⟩
          · simp [SF] at F; rcases F with ⟨τ,⟨F1,F2⟩⟩
            set X := sf_trans _ _ _ H F2;
            exists τ; simp [X]; simp [hypos, F1]
          · exists σ; simp [H2]; simp [hypos,H1]
        · cases Hnorm <;> try grind
      · apply ihν.1 at H
        · simp [SF, conc] at H; simp [SF]; rcases H with H | ⟨σ, ⟨H1,H2⟩⟩
          · simp [SF] at F; rcases F with ⟨τ,⟨F1,F2⟩⟩
            have X : x ∈ sf τ := by {
              apply sf_trans (ψ := α.impl β);
              apply sf_trans; exact H; simp [sf, self_sf]; exact F2
            }
            exists τ; simp [X]; simp [hypos, F1]
          · exists σ; simp [H2]; simp [hypos,H1]
        · cases Hnorm <;> try grind
    }
    constructor
    · intro H x G; apply A H at G; simp [SF]; simp [SF] at G; simp [G]
    · intro H; apply A; apply neutral_normal; assumption
  · -- pair
    rename_i α β μ ν ihμ ihν
    constructor
    · intro Hnorm x H; simp [formsin] at H; rcases H with (H | H) | H
      · simp [H, SF, conc, self_sf]
      · apply ihμ.1 at H
        · simp [SF, conc] at H; simp [SF]; rcases H with H | ⟨σ, H⟩
          · simp [conc, sf, H]
          · simp [hypos]
            by_cases G : x ∈ sf α
            · simp [conc, sf, G]
            · right; exists σ; simp [H]
        · apply normal_sp _ _ (pair α β μ ν);
          simp [subproofs]; left; right; simp [self_sp];
          assumption
      · apply ihν.1 at H
        · simp [SF, conc] at H; simp [SF]; rcases H with H | ⟨σ, H⟩
          · simp [conc, sf, H]
          · simp [hypos]
            by_cases G : x ∈ sf α
            · simp [conc, sf, G]
            · right; exists σ; simp [H]
        · apply normal_sp _ _ (pair α β μ ν);
          simp [subproofs]; right; simp [self_sp];
          assumption
    · intro H; cases H <;> try grind
  · -- fst
    rename_i α β μ ihμ
    have A : isNormal (fst α β μ) →
          formsin (fst α β μ) ⊆ SF (hypos (fst α β μ)) := by {
      intro Hnorm x H;
      have F : α.conj β ∈ SF (hypos μ) := by {
        have F : α.conj β ∈ formsin μ := by apply conc_in_forms
        apply ihμ.2 (fstNormal_msp _ _ _ Hnorm) at F; assumption
      }
      simp [formsin] at H; rcases H with H | H
      · simp [H, SF, hypos]; simp [SF] at F; rcases F with ⟨τ, ⟨F1,F2⟩⟩
        exists τ; simp [F1]; apply sf_trans (ψ := α.conj β)
        simp [sf, self_sf]; exact F2
      · apply ihμ.1 at H
        · simp [SF, conc] at H; simp [SF]; rcases H with H | ⟨σ, ⟨H1,H2⟩⟩
          · simp [SF] at F; rcases F with ⟨τ,⟨F1,F2⟩⟩
            set X := sf_trans _ _ _ H F2;
            exists τ
          · exists σ
        · cases Hnorm <;> try grind
    }
    constructor
    · intro H x G; apply A H at G; simp [SF]; simp [SF] at G; simp [G]
    · intro H; apply A; apply neutral_normal; assumption
  · -- snd
    rename_i α β μ ihμ
    have A :  isNormal (snd α β μ) →
          formsin (snd α β μ) ⊆ SF (hypos (snd α β μ)) := by {
      intro Hnorm x H;
      have F : α.conj β ∈ SF (hypos μ) := by {
        have F : α.conj β ∈ formsin μ := by apply conc_in_forms
        apply ihμ.2 (sndNormal_msp _ _ _ Hnorm) at F; assumption
      }
      simp [formsin] at H; rcases H with H | H
      · simp [H, SF, hypos]; simp [SF] at F; rcases F with ⟨τ, ⟨F1,F2⟩⟩
        exists τ; simp [F1]; apply sf_trans (ψ := α.conj β)
        simp [sf, self_sf]; exact F2
      · apply ihμ.1 at H
        · simp [SF, conc] at H; simp [SF]; rcases H with H | ⟨σ, ⟨H1,H2⟩⟩
          · simp [SF] at F; rcases F with ⟨τ,⟨F1,F2⟩⟩
            set X := sf_trans _ _ _ H F2;
            exists τ
          · exists σ
        · cases Hnorm <;> try grind
    }
    constructor
    · intro H x G; apply A H at G; simp [SF]; simp [SF] at G; simp [G]
    · intro H; apply A; apply neutral_normal; assumption
  · -- left
    rename_i α β μ ihμ
    constructor
    · intro Hnorm x H; simp [formsin] at H; rcases H with H | H
      · simp [H, SF, conc, self_sf]
      · apply ihμ.1 at H
        · simp [SF, conc] at H; simp [SF]; rcases H with H | ⟨σ, H⟩
          · simp [conc, sf, H]
          · simp [hypos]
            by_cases G : x ∈ sf α
            · simp [conc, sf, G]
            · right; exists σ
        · apply normal_sp _ _ (left α β μ);
          simp [subproofs]; right; simp [self_sp]; assumption
    · intro H; cases H <;> try grind
  · -- right
    rename_i α β μ ihμ
    constructor
    · intro Hnorm x H; simp [formsin] at H; rcases H with H | H
      · simp [H, SF, conc, self_sf]
      · apply ihμ.1 at H
        · simp [SF, conc] at H; simp [SF]; rcases H with H | ⟨σ, H⟩
          · simp [conc, sf, H]
          · simp [hypos]
            by_cases G : x ∈ sf α
            · simp [conc, sf, G]
            · right; exists σ
        · apply normal_sp _ _ (right α β μ);
          simp [subproofs]; right; simp [self_sp]; assumption
    · intro H; cases H <;> try grind
  · -- case
    rename_i α β δ χ μ ν ihχ ihμ ihν
    have A :  isNormal (case α β δ χ μ ν) →
          formsin (case α β δ χ μ ν) ⊆ SF (hypos (case α β δ χ μ ν) ∪ {δ}) := by {
      intro Hnorm x H;
      have F : α.disj β ∈ SF (hypos χ) := by {
        have F : α.disj β ∈ formsin χ := by apply conc_in_forms
        apply ihχ.2 (caseNormal_msp _ _ _ _ _ _ Hnorm) at F; assumption
      }
      simp [formsin] at H; rcases H with (H | H) | H
      · apply ihχ.1 at H
        · simp [SF, conc] at H; simp [SF]; rcases H with H | ⟨σ, ⟨H1,H2⟩⟩
          · simp [SF] at F; rcases F with ⟨τ,⟨F1,F2⟩⟩
            set X := sf_trans _ _ _ H F2;
            right; exists τ; simp [X, hypos, F1]
          · right; exists σ; simp [H2,hypos,H1]
        · cases Hnorm <;> try grind
      · apply ihμ.1 at H
        · simp [SF, conc] at H; simp [SF]; rcases H with H | ⟨σ, ⟨H1,H2⟩⟩
          · simp [hypos, H]
          · by_cases G : x ∈ sf α
            · simp [SF] at F; rcases F with ⟨τ, ⟨F1,F2⟩⟩
              have X : x ∈ sf τ := by {
                apply sf_trans (ψ := α.disj β)
                apply sf_trans; exact G; simp [sf, self_sf]; exact F2
              }
              right; exists τ; simp [hypos,X,F1]
            · right; exists σ; simp [H2, hypos]; left; right;
              simp [H1]; intro C; grind
        · cases Hnorm <;> try grind
      · apply ihν.1 at H
        · simp [SF, conc] at H; simp [SF]; rcases H with H | ⟨σ, ⟨H1,H2⟩⟩
          · simp [hypos, H]
          · by_cases G : x ∈ sf β
            · simp [SF] at F; rcases F with ⟨τ, ⟨F1,F2⟩⟩
              have X : x ∈ sf τ := by {
                apply sf_trans (ψ := α.disj β)
                apply sf_trans; exact G; simp [sf, self_sf]; exact F2
              }
              right; exists τ; simp [hypos,X,F1]
            · right; exists σ; simp [H2, hypos]; right;
              simp [H1]; intro C; grind
        · cases Hnorm <;> try grind
    }
    constructor
    · exact A
    · intro Hneut; set H := Hneut
      cases Hneut <;> try grind
      have B : isNeutral μ := by apply caseNeutral_ssp; apply H
      apply ihμ.2 at B
      have C : bot ∈ formsin μ := by apply conc_in_forms
      apply B at C; rename_i D; apply A at D
      intro x G; apply D at G; simp [SF, sf] at G; simp [SF]
      have F : α.disj β ∈ SF (hypos χ) := by {
        have F : α.disj β ∈ formsin χ := by apply conc_in_forms
        apply ihχ.2 (caseNormal_msp _ _ _ _ _ _ (neutral_normal _ _ H)) at F
        assumption
      }
      rcases G with (G | ⟨σ, ⟨G1,G2⟩⟩)
      · subst_vars; simp [SF] at C; rcases C with ⟨τ, ⟨C1,C2⟩⟩
        · by_cases X : bot ∈ sf α
          · simp [SF] at F; rcases F with ⟨σ, ⟨F1,F2⟩⟩
            have Y : bot ∈ sf σ := by {
              apply sf_trans (ψ := α.disj β)
              apply sf_trans; exact X; simp [sf, self_sf]; exact F2
            }
            exists σ; simp [Y,hypos,F1]
          · exists τ; simp [C2,hypos,C1]; left; right; intro Z
            subst_vars; grind
      · exists σ

theorem subformula : ∀ φ (π : njprf φ), ∃ (ϖ : njprf φ),
  hypos ϖ ⊆ hypos π ∧ conc ϖ = conc π
      ∧ formsin ϖ ⊆ SF (hypos ϖ ∪ {conc ϖ}) := by
  intro φ π
  let h := normalization _ π
  rcases h with ⟨ϖ, h1, h2, h3⟩
  exists ϖ; simp [h2, h3]; apply (formsin_normal _ ϖ).1 at h1
  rw [← h3]; simp at h1; assumption

end subform
