import Mathlib
import NatDed.nkNorm

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option maxHeartbeats 0

namespace nkNormAlg

open Rank
open nk
open nk.propform
open nk.nkprf
open nk.proofrule
open nkNorm
open nkNorm.isCut
open nkNorm.isNormal
open nkNorm.graft
open nkNorm.contract
open nkNorm.oneStep

def graftFn {φ ψ} (ρ : nkprf φ) (π: nkprf ψ) : nkprf ψ :=
  match h: π with
  | .ax α => if g: α = φ then (by subst_vars; exact ρ) else ax α
  | .raa α μ => raa α (graftFn ρ μ)
  | .abs α β μ => abs α β (graftFn ρ μ)
  | .app α β μ ν => app α β (graftFn ρ μ) (graftFn ρ ν)
  | .pair α β μ ν => pair α β (graftFn ρ μ) (graftFn ρ ν)
  | .fst α β μ =>  fst α β (graftFn ρ μ)
  | .snd α β μ =>  snd α β (graftFn ρ μ)
  | .left α β μ => left α β (graftFn ρ μ)
  | .right α β μ => right α β (graftFn ρ μ)
  | .case α β χ μ ν => case α β (graftFn ρ χ) (graftFn ρ μ) (graftFn ρ ν)

def elimBotFn {σ : propform} : nkprf σ → nkprf σ
  | ax α =>
      if f : α = impl bot bot
      then (by rw [f]; exact abs bot bot (ax bot))
      else ax α
  | raa α μ => raa α (elimBotFn μ)
  | .abs α β μ => abs α β (elimBotFn μ)
  | app α β μ ν =>
      if f1 : α = bot
      then
        if f2 : β = bot
        then
          if f3 : lrof μ = prax
          then
            if g : lrof ν = prraa
            then by {
              cases h : ν <;>
              simp [h, lrof] at g
              rename_i ν'; rw [f2]
              exact elimBotFn ν'
            }
            else by {
              rw [f2, ←f1]
              exact elimBotFn ν
            }
          else app α β (elimBotFn μ) (elimBotFn ν)
        else app α β (elimBotFn μ) (elimBotFn ν)
      else app α β (elimBotFn μ) (elimBotFn ν)
  | pair α β μ ν => pair α β (elimBotFn μ) (elimBotFn ν)
  | fst α β μ => fst α β (elimBotFn μ)
  | snd α β μ => snd α β (elimBotFn μ)
  | left α β μ => left α β (elimBotFn μ)
  | right α β μ => right α β (elimBotFn μ)
  | case α β χ μ ν => case α β (elimBotFn χ) (elimBotFn μ) (elimBotFn ν)
  termination_by prf => prfsize prf
  decreasing_by
    all_goals (subst_vars; simp [prfsize]; try grind)

def elimNegFn {σ : propform} (φ : propform)  : nkprf σ → nkprf σ
  | ax α =>
      if f : α = impl (impl φ bot) bot
      then by {
        rw [f]
        exact (abs (neg φ) bot (app _ _ (ax (neg φ)) (ax φ)))
      }
      else ax α
  | raa α μ => raa α (elimNegFn φ μ)
  | .abs α β μ => abs α β (elimNegFn φ μ)
  | app α β μ ν =>
      if f1 : α = impl φ bot
      then
        if f2 : β = bot
        then
          if f3 : lrof μ = prax
          then
            if g : lrof ν = prraa
            then by {
              cases h : ν <;> simp [h, lrof] at g
              rename_i ν'; rw [f2]; exact elimNegFn φ ν'
            }
            else by {
              rw [f1] at ν; rw [f2]
              exact (app _ _ (elimNegFn φ ν) (ax φ))
            }
          else app α β (elimNegFn φ μ) (elimNegFn φ ν)
        else app α β (elimNegFn φ μ) (elimNegFn φ ν)
      else app α β (elimNegFn φ μ) (elimNegFn φ ν)
  | pair α β μ ν => pair α β (elimNegFn φ μ) (elimNegFn φ ν)
  | fst α β μ => fst α β (elimNegFn φ μ)
  | snd α β μ => snd α β (elimNegFn φ μ)
  | left α β μ => left α β (elimNegFn φ μ)
  | right α β μ => right α β (elimNegFn φ μ)
  | case α β χ μ ν => case α β (elimNegFn φ χ) (elimNegFn φ μ) (elimNegFn φ ν)
  termination_by prf => prfsize prf
  decreasing_by
    all_goals (subst_vars; simp [prfsize]; try grind)

def elimAppFn {σ : propform} (φ ψ : propform) (υ : nkprf φ) : nkprf σ → nkprf σ
  | ax α =>
      if f : α = impl (impl φ ψ) bot
      then by {
        rw [f]
        exact abs (φ.impl ψ) bot (app ψ bot (ax (neg ψ))
                  (app φ ψ (ax (φ.impl ψ)) υ))
      }
      else ax α
  | raa α μ => raa α (elimAppFn φ ψ υ μ)
  | .abs α β μ => abs α β (elimAppFn φ ψ υ μ)
  | app α β μ ν =>
      if f1 : α = impl φ ψ
      then
        if f2 : β = bot
        then
          if f3 : lrof μ = prax
          then
            if g : lrof ν = prraa
            then by {
              cases h : ν <;> simp [h, lrof] at g
              rename_i ν'; rw [f2]; exact elimAppFn φ ψ υ ν'
            }
            else by {
              rw [f1] at ν
              exact (app _ _ (ax (impl ψ β))
                    (app _ _ (elimAppFn φ ψ υ ν) υ))
            }
          else app α β (elimAppFn φ ψ υ μ) (elimAppFn φ ψ υ ν)
        else app α β (elimAppFn φ ψ υ μ) (elimAppFn φ ψ υ ν)
      else app α β (elimAppFn φ ψ υ μ) (elimAppFn φ ψ υ ν)
  | pair α β μ ν => pair α β (elimAppFn φ ψ υ μ) (elimAppFn φ ψ υ ν)
  | fst α β μ => fst α β (elimAppFn φ ψ υ μ)
  | snd α β μ => snd α β (elimAppFn φ ψ υ μ)
  | left α β μ => left α β (elimAppFn φ ψ υ μ)
  | right α β μ => right α β (elimAppFn φ ψ υ μ)
  | case α β χ μ ν => case α β (elimAppFn φ ψ υ χ) (elimAppFn φ ψ υ μ) (elimAppFn φ ψ υ ν)
  termination_by prf => prfsize prf
  decreasing_by
    all_goals (subst_vars; simp [prfsize]; try grind)

def elimFstFn {σ : propform} (φ ψ : propform) : nkprf σ → nkprf σ
  | ax α =>
      if f : α = impl (conj φ ψ) bot
      then by {
        rw [f]
        exact abs (φ.conj ψ) bot (app φ bot (ax (neg φ))
                  (fst φ ψ (ax (φ.conj ψ))))
      }
      else ax α
  | raa α μ => raa α (elimFstFn φ ψ μ)
  | .abs α β μ => abs α β (elimFstFn φ ψ μ)
  | app α β μ ν =>
      if f1 : α = conj φ ψ
      then
        if f2 : β = bot
        then
          if f3 : lrof μ = prax
          then
            if g : lrof ν = prraa
            then by {
              cases h : ν <;> simp [h, lrof] at g
              rename_i ν'; rw [f2]; exact elimFstFn φ ψ ν'
            }
            else by {
              rw [f1] at ν; rw [f2]
              exact (app _ _ (ax (neg φ))
                    (fst _ _ (elimFstFn φ ψ ν)))
            }
          else app α β (elimFstFn φ ψ μ) (elimFstFn φ ψ ν)
        else app α β (elimFstFn φ ψ μ) (elimFstFn φ ψ ν)
      else app α β (elimFstFn φ ψ μ) (elimFstFn φ ψ ν)
  | pair α β μ ν => pair α β (elimFstFn φ ψ μ) (elimFstFn φ ψ ν)
  | fst α β μ => fst α β (elimFstFn φ ψ μ)
  | snd α β μ => snd α β (elimFstFn φ ψ μ)
  | left α β μ => left α β (elimFstFn φ ψ μ)
  | right α β μ => right α β (elimFstFn φ ψ μ)
  | case α β χ μ ν => case α β (elimFstFn φ ψ χ) (elimFstFn φ ψ μ) (elimFstFn φ ψ ν)
  termination_by prf => prfsize prf
  decreasing_by
    all_goals (subst_vars; simp [prfsize]; try grind)

def elimSndFn {σ : propform} (φ ψ : propform) : nkprf σ → nkprf σ
  | ax α =>
      if f : α = impl (conj φ ψ) bot
      then by {
        rw [f]
        exact abs (φ.conj ψ) bot (app ψ bot (ax (neg ψ))
                  (snd φ ψ (ax (φ.conj ψ))))
      }
      else ax α
  | raa α μ => raa α (elimSndFn φ ψ μ)
  | .abs α β μ => abs α β (elimSndFn φ ψ μ)
  | app α β μ ν =>
      if f1 : α = conj φ ψ
      then
        if f2 : β = bot
        then
          if f3 : lrof μ = prax
          then
            if g : lrof ν = prraa
            then by {
              cases h : ν <;> simp [h, lrof] at g
              rename_i ν'; rw [f2]; exact elimSndFn φ ψ ν'
            }
            else by {
              rw [f1] at ν; rw [f2]
              exact (app _ _ (ax (neg ψ))
                    (snd _ _ (elimSndFn φ ψ ν)))
            }
          else app α β (elimSndFn φ ψ μ) (elimSndFn φ ψ ν)
        else app α β (elimSndFn φ ψ μ) (elimSndFn φ ψ ν)
      else app α β (elimSndFn φ ψ μ) (elimSndFn φ ψ ν)
  | pair α β μ ν => pair α β (elimSndFn φ ψ μ) (elimSndFn φ ψ ν)
  | fst α β μ => fst α β (elimSndFn φ ψ μ)
  | snd α β μ => snd α β (elimSndFn φ ψ μ)
  | left α β μ => left α β (elimSndFn φ ψ μ)
  | right α β μ => right α β (elimSndFn φ ψ μ)
  | case α β χ μ ν => case α β (elimSndFn φ ψ χ) (elimSndFn φ ψ μ) (elimSndFn φ ψ ν)
  termination_by prf => prfsize prf
  decreasing_by
    all_goals (subst_vars; simp [prfsize]; try grind)

def elimCaseFn {σ : propform} (φ ψ : propform) (ρ υ : nkprf bot) : nkprf σ → nkprf σ
  | ax α =>
      if f : α = impl (disj φ ψ) bot
      then by {
        rw [f]
        exact abs (φ.disj ψ) _ (case φ ψ (ax (φ.disj ψ)) ρ υ)
      }
      else ax α
  | raa α μ => raa α (elimCaseFn φ ψ ρ υ μ)
  | .abs α β μ => abs α β (elimCaseFn φ ψ ρ υ μ)
  | app α β μ ν =>
      if f1 : α = disj φ ψ
      then
        if f2 : β = bot
        then
          if f3 : lrof μ = prax
          then
            if g : lrof ν = prraa
            then by {
              cases h : ν <;> simp [h, lrof] at g
              rename_i ν'; rw [f2]; exact elimCaseFn φ ψ ρ υ ν'
            }
            else by {
              rw [f1] at ν; rw [f2]
              exact case _ _ (elimCaseFn φ ψ ρ υ ν) ρ υ
            }
          else app α β (elimCaseFn φ ψ ρ υ μ) (elimCaseFn φ ψ ρ υ ν)
        else app α β (elimCaseFn φ ψ ρ υ μ) (elimCaseFn φ ψ ρ υ ν)
      else app α β (elimCaseFn φ ψ ρ υ μ) (elimCaseFn φ ψ ρ υ ν)
  | pair α β μ ν => pair α β (elimCaseFn φ ψ ρ υ μ) (elimCaseFn φ ψ ρ υ ν)
  | fst α β μ => fst α β (elimCaseFn φ ψ ρ υ μ)
  | snd α β μ => snd α β (elimCaseFn φ ψ ρ υ μ)
  | left α β μ => left α β (elimCaseFn φ ψ ρ υ μ)
  | right α β μ => right α β (elimCaseFn φ ψ ρ υ μ)
  | case α β χ μ ν => case α β (elimCaseFn φ ψ ρ υ χ)
                      (elimCaseFn φ ψ ρ υ μ) (elimCaseFn φ ψ ρ υ ν)
  termination_by prf => prfsize prf
  decreasing_by
    all_goals (subst_vars; simp [prfsize]; try grind)

def contractFn {φ} (π: nkprf φ) : nkprf φ :=
  match h: π with
  | .app α β (.abs _ _ μ) ν => graftFn ν μ
  | .fst α β (.pair _ _ μ ν) => μ
  | .snd α β (.pair _ _ μ ν) => ν
  | .case α β (.left _ _ χ) μ ν => graftFn χ μ
  | .case α β (.right _ _ χ) μ ν => graftFn χ ν
  | .raa bot μ => elimBotFn μ
  | .raa (impl α bot) μ => abs α _ (elimNegFn α μ)
  | .app α β (.raa _ μ) ν => raa β (elimAppFn α β ν μ)
  | .fst α β (.raa _ μ)=> raa α (elimFstFn α β μ)
  | .snd α β (.raa _ μ) => raa β (elimSndFn α β μ)
  | .case α β (.raa _ χ) μ ν => elimCaseFn α β μ ν χ
  | ϖ@_ => ϖ

def stepOne {φ} (π : nkprf φ) : nkprf φ :=
  match π with
  | .ax α => ax α
  | .raa α μ => if maxDeg μ = maxDeg π
                then raa α (stepOne μ)
                else contractFn (raa α μ)
  | .abs α β μ => abs α β (stepOne μ)
  | .app α β μ ν => if maxDeg ν = maxDeg π
                    then app α β μ (stepOne ν)
                    else if maxDeg μ = maxDeg π
                          then app α β (stepOne μ) ν
                          else contractFn (app α β μ ν)
  | .pair α β μ ν => if maxDeg ν = maxDeg π
                      then pair α β μ (stepOne ν)
                      else pair α β (stepOne μ) ν
  | .fst α β μ => if maxDeg μ = maxDeg π
                  then fst α β (stepOne μ)
                  else contractFn (fst α β μ)
  | .snd α β μ => if maxDeg μ = maxDeg π
                  then snd α β (stepOne μ)
                  else contractFn (snd α β μ)
  | .left α β μ => left α β (stepOne μ)
  | .right α β μ => right α β (stepOne μ)
  | .case α β χ μ ν => if maxDeg ν = maxDeg π
                        then case α β χ μ (stepOne ν)
                        else if maxDeg μ = maxDeg π
                            then case α β χ (stepOne μ) ν
                            else if maxDeg χ = maxDeg π
                                then case α β (stepOne χ) μ ν
                                else contractFn (case α β χ μ ν)

lemma graft_graftFn : ∀ ψ φ (ρ : nkprf ψ) (π ϖ : nkprf φ),
      graft ρ π ϖ ↔ ϖ = graftFn ρ π := by
  intro ψ φ ρ π ϖ; constructor <;> intro A
  · induction A <;> simp [graftFn] <;> try grind
  · subst_vars; induction π <;> simp [graftFn] <;>
      try (constructor <;> try grind)
    · rename_i α; by_cases H : α = ψ
      · rw [H]; simp; constructor
      · simp [H]; constructor; grind

lemma elimBot_elimBotFn : ∀ σ (π π' : nkprf σ),
  elimBot π π' ↔ elimBotFn π = π' := by
  intro σ π π'
  constructor <;> intro H
  · induction H
    all_goals try (simp [elimBotFn]; grind)
    · simp [neg, elimBotFn]
    · rename_i α G; simp [neg] at G;
      unfold elimBotFn; simp [G]
    · rename_i μ μ' F ih; simp [neg, elimBotFn, lrof, ih]
    · rename_i μ μ' F G H; simp [neg]
      unfold elimBotFn; simp [F];
      split_ifs <;> simp [lrof] at * ; try grind
    · rename_i α β μ ν μ' ν' F Gμ Gν Hμ Hν
      rcases F with F | F
      · unfold elimBotFn; simp [F]; grind
      · simp [neg] at *
        have G : ¬ α = bot ∨ ¬ β = bot := by {
          by_cases G1 : α = bot
          · simp [conc] at F; grind
          · grind
        }
        rcases G with G | G <;>
          (unfold elimBotFn; simp [G]; grind)
  · subst H
    induction π
    · rename_i α
      by_cases A : α = bot.impl bot
      · subst_vars; simp [elimBotFn]; apply elimBot.ax1_eb
      · simp [elimBotFn, A]; apply elimBot.ax2_eb ; simp [neg]; grind
    · rename_i α μ ih
      simp [elimBotFn]
      exact elimBot.raa_eb α μ (elimBotFn μ) ih
    · rename_i α β μ ih
      simp [elimBotFn]
      exact elimBot.abs_eb α β μ (elimBotFn μ) ih
    · rename_i α β μ ν ihμ ihν
      by_cases A : α = bot ∧ β = bot ∧ μ = ax (α.impl β)
      · rcases A with ⟨A1,A2,A3⟩;
        subst_vars
        cases ν <;> simp [elimBotFn] at * <;>
          constructor <;> try simp [lrof] at *
        all_goals try assumption
        · cases ihν; assumption
      · have B : ¬α = bot ∨ ¬β = bot ∨ ¬μ = ax (α.impl β) := by grind
        rcases B with B | B | B <;> unfold elimBotFn <;> simp [B]
        · apply elimBot.app_eb <;> try assumption
          simp [neg, conc]; grind
        · apply elimBot.app_eb <;> try assumption
          simp [neg, conc]; grind
        · cases μ <;> simp [lrof] at * <;> try grind
          all_goals
            (simp [elimBotFn] at * ; constructor <;>
              try (simp [lrof])) <;> try grind
    all_goals (simp [elimBotFn] at *; constructor <;>
                  try (simp [lrof])) <;> try grind

lemma elimNeg_elimNegFn : ∀ φ σ (π π' : nkprf σ),
  elimNeg φ π π' ↔ elimNegFn φ π = π' := by
  intro φ σ π π'
  constructor <;> intro H
  · induction H
    all_goals try (simp [elimNegFn]; grind)
    · simp [neg, elimNegFn]
    · rename_i α G; simp [neg] at G;
      unfold elimNegFn; simp [G]
    · rename_i μ μ' F ih; simp [neg, elimNegFn, lrof, ih]
    · rename_i μ μ' F G H; simp [neg]
      unfold elimNegFn; simp [F];
      split_ifs <;> simp [lrof] at * ; try grind
    · rename_i α β μ ν μ' ν' F Gμ Gν Hμ Hν
      rcases F with F | F
      · unfold elimNegFn; simp [F]; grind
      · simp [neg] at *
        have G : ¬ α = φ.impl bot ∨ ¬ β = bot := by {
          by_cases G1 : α = φ.impl bot
          · simp [conc] at F; grind
          · grind
        }
        rcases G with G | G <;>
          (unfold elimNegFn; simp [G]; grind)
  · subst H
    induction π
    · rename_i α
      by_cases A : α = (φ.impl bot).impl bot
      · subst_vars; simp [elimNegFn]; apply elimNeg.ax1_en
      · simp [elimNegFn, A]; apply elimNeg.ax2_en; simp [neg]; grind
    · rename_i α μ ih
      simp [elimNegFn]
      exact elimNeg.raa_en α μ (elimNegFn φ μ) ih
    · rename_i α β μ ih
      simp [elimNegFn]
      exact elimNeg.abs_en α β μ (elimNegFn φ μ) ih
    · rename_i α β μ ν ihμ ihν
      by_cases A : α = φ.impl bot ∧ β = bot ∧ μ = ax (α.impl β)
      · rcases A with ⟨A1,A2,A3⟩;
        subst_vars
        cases ν <;> simp [elimNegFn] at * <;>
          constructor <;> try simp [lrof] at *
        all_goals try assumption
        · cases ihν; assumption
      · have B : ¬α = φ.impl bot ∨ ¬β = bot ∨ ¬μ = ax (α.impl β) := by grind
        rcases B with B | B | B <;> unfold elimNegFn <;> simp [B]
        · apply elimNeg.app_en <;> try assumption
          simp [neg, conc]; grind
        · apply elimNeg.app_en <;> try assumption
          simp [neg, conc]; grind
        · cases μ <;> simp [lrof] at * <;> try grind
          all_goals
            (simp [elimNegFn] at * ; constructor <;>
              try (simp [lrof])) <;> try grind
    all_goals (simp [elimNegFn] at *; constructor <;>
                  try (simp [lrof])) <;> try grind

lemma elimApp_elimAppFn : ∀ φ ψ υ σ (π π' : nkprf σ),
  elimApp φ ψ υ π π' ↔ elimAppFn φ ψ υ π = π' := by
  intro φ ψ υ σ π π'
  constructor <;> intro H
  · induction H
    all_goals try (simp [elimAppFn]; grind)
    · simp [neg, elimAppFn]
    · rename_i α G; simp [neg] at G;
      unfold elimAppFn; simp [G]
    · rename_i μ μ' F ih; simp [neg, elimAppFn, lrof, ih]
    · rename_i μ μ' F G H; simp [neg]
      unfold elimAppFn; simp [F];
      split_ifs <;> simp [lrof] at * ; try grind
    · rename_i α β μ ν μ' ν' F Gμ Gν Hμ Hν
      rcases F with F | F
      · unfold elimAppFn; simp [F]; grind
      · simp [neg] at *
        have G : ¬ α = φ.impl ψ ∨ ¬ β = bot := by {
          by_cases G1 : α = φ.impl ψ
          · simp [conc] at F; grind
          · grind
        }
        rcases G with G | G <;>
          (unfold elimAppFn; simp [G]; grind)
  · subst H
    induction π
    · rename_i α
      by_cases A : α = (φ.impl ψ).impl bot
      · subst_vars; simp [elimAppFn]; apply elimApp.ax1_ea
      · simp [elimAppFn, A]; apply elimApp.ax2_ea ; simp [neg]; grind
    · rename_i α μ ih
      simp [elimAppFn]
      exact elimApp.raa_ea α μ (elimAppFn φ ψ υ μ) ih
    · rename_i α β μ ih
      simp [elimAppFn]
      exact elimApp.abs_ea α β μ (elimAppFn φ ψ υ μ) ih
    · rename_i α β μ ν ihμ ihν
      by_cases A : α = φ.impl ψ ∧ β = bot ∧ μ = ax (α.impl β)
      · rcases A with ⟨A1,A2,A3⟩;
        subst_vars
        cases ν <;> simp [elimAppFn] at * <;>
          constructor <;> try simp [lrof] at *
        all_goals try assumption
        · cases ihν; assumption
      · have B : ¬α = φ.impl ψ ∨ ¬β = bot ∨ ¬μ = ax (α.impl β) := by grind
        rcases B with B | B | B <;> unfold elimAppFn <;> simp [B]
        · apply elimApp.app_ea <;> try assumption
          simp [neg, conc]; grind
        · apply elimApp.app_ea <;> try assumption
          simp [neg, conc]; grind
        · cases μ <;> simp [lrof] at * <;> try grind
          all_goals
            (simp [elimAppFn] at * ; constructor <;>
              try (simp [lrof])) <;> try grind
    all_goals (simp [elimAppFn] at *; constructor <;>
                  try (simp [lrof])) <;> try grind

lemma elimFst_elimFstFn : ∀ φ ψ σ (π π' : nkprf σ),
  elimFst φ ψ π π' ↔ elimFstFn φ ψ π = π' := by
  intro φ ψ σ π π'
  constructor <;> intro H
  · induction H
    all_goals try (simp [elimFstFn]; grind)
    · simp [neg, elimFstFn]
    · rename_i α G; simp [neg] at G;
      unfold elimFstFn; simp [G]
    · rename_i μ μ' F ih; simp [neg, elimFstFn, lrof, ih]
    · rename_i μ μ' F G H; simp [neg]
      unfold elimFstFn; simp [F];
      split_ifs <;> simp [lrof, neg] at *; try grind
    · rename_i α β μ ν μ' ν' F Gμ Gν Hμ Hν
      rcases F with F | F
      · unfold elimFstFn; simp [F]; grind
      · simp [neg] at *
        have G : ¬ α = φ.conj ψ ∨ ¬ β = bot := by {
          by_cases G1 : α = φ.conj ψ
          · simp [conc] at F; grind
          · grind
        }
        rcases G with G | G <;>
          (unfold elimFstFn; simp [G]; grind)
  · subst H
    induction π
    · rename_i α
      by_cases A : α = (φ.conj ψ).impl bot
      · subst_vars; simp [elimFstFn]; apply elimFst.ax1_ef
      · simp [elimFstFn, A]; apply elimFst.ax2_ef ; simp [neg]; grind
    · rename_i α μ ih
      simp [elimFstFn]
      exact elimFst.raa_ef α μ (elimFstFn φ ψ μ) ih
    · rename_i α β μ ih
      simp [elimFstFn]
      exact elimFst.abs_ef α β μ (elimFstFn φ ψ μ) ih
    · rename_i α β μ ν ihμ ihν
      by_cases A : α = φ.conj ψ ∧ β = bot ∧ μ = ax (α.impl β)
      · rcases A with ⟨A1,A2,A3⟩;
        subst_vars
        cases ν <;> simp [elimFstFn] at * <;>
          constructor <;> try simp [lrof] at *
        all_goals try assumption
        · cases ihν; assumption
      · have B : ¬α = φ.conj ψ ∨ ¬β = bot ∨ ¬μ = ax (α.impl β) := by grind
        rcases B with B | B | B <;> unfold elimFstFn <;> simp [B]
        · apply elimFst.app_ef <;> try assumption
          simp [neg, conc]; grind
        · apply elimFst.app_ef <;> try assumption
          simp [neg, conc]; grind
        · cases μ <;> simp [lrof] at * <;> try grind
          all_goals
            (simp [elimFstFn] at * ; constructor <;>
              try (simp [lrof])) <;> try grind
    all_goals (simp [elimFstFn] at *; constructor <;>
                  try (simp [lrof])) <;> try grind

lemma elimSnd_elimSndFn : ∀ φ ψ σ (π π' : nkprf σ),
  elimSnd φ ψ π π' ↔ elimSndFn φ ψ π = π' := by
  intro φ ψ σ π π'
  constructor <;> intro H
  · induction H
    all_goals try (simp [elimSndFn]; grind)
    · simp [neg, elimSndFn]
    · rename_i α G; simp [neg] at G;
      unfold elimSndFn; simp [G]
    · rename_i μ μ' F ih; simp [neg, elimSndFn, lrof, ih]
    · rename_i μ μ' F G H; simp [neg]
      unfold elimSndFn; simp [F];
      split_ifs <;> simp [lrof, neg] at *; try grind
    · rename_i α β μ ν μ' ν' F Gμ Gν Hμ Hν
      rcases F with F | F
      · unfold elimSndFn; simp [F]; grind
      · simp [neg] at *
        have G : ¬ α = φ.conj ψ ∨ ¬ β = bot := by {
          by_cases G1 : α = φ.conj ψ
          · simp [conc] at F; grind
          · grind
        }
        rcases G with G | G <;>
          (unfold elimSndFn; simp [G]; grind)
  · subst H
    induction π
    · rename_i α
      by_cases A : α = (φ.conj ψ).impl bot
      · subst_vars; simp [elimSndFn]; apply elimSnd.ax1_es
      · simp [elimSndFn, A]; apply elimSnd.ax2_es ; simp [neg]; grind
    · rename_i α μ ih
      simp [elimSndFn]
      exact elimSnd.raa_es α μ (elimSndFn φ ψ μ) ih
    · rename_i α β μ ih
      simp [elimSndFn]
      exact elimSnd.abs_es α β μ (elimSndFn φ ψ μ) ih
    · rename_i α β μ ν ihμ ihν
      by_cases A : α = φ.conj ψ ∧ β = bot ∧ μ = ax (α.impl β)
      · rcases A with ⟨A1,A2,A3⟩;
        subst_vars
        cases ν <;> simp [elimSndFn] at * <;>
          constructor <;> try simp [lrof] at *
        all_goals try assumption
        · cases ihν; assumption
      · have B : ¬α = φ.conj ψ ∨ ¬β = bot ∨ ¬μ = ax (α.impl β) := by grind
        rcases B with B | B | B <;> unfold elimSndFn <;> simp [B]
        · apply elimSnd.app_es <;> try assumption
          simp [neg, conc]; grind
        · apply elimSnd.app_es <;> try assumption
          simp [neg, conc]; grind
        · cases μ <;> simp [lrof] at * <;> try grind
          all_goals
            (simp [elimSndFn] at * ; constructor <;>
              try (simp [lrof])) <;> try grind
    all_goals (simp [elimSndFn] at *; constructor <;>
                  try (simp [lrof])) <;> try grind

lemma elimCase_elimCaseFn : ∀ φ ψ ρ υ σ (π π' : nkprf σ),
  elimCase φ ψ ρ υ π π' ↔ elimCaseFn φ ψ ρ υ π = π' := by
  intro φ ψ ρ υ σ π π'
  constructor <;> intro H
  · induction H
    all_goals try (simp [elimCaseFn]; grind)
    · simp [neg, elimCaseFn]
    · rename_i α G; simp [neg] at G;
      unfold elimCaseFn; simp [G]
    · rename_i μ μ' F ih; simp [neg, elimCaseFn, lrof, ih]
    · rename_i μ μ' F G H; simp [neg]
      unfold elimCaseFn; simp [F];
      split_ifs <;> simp [lrof] at * ; try grind
    · rename_i α β μ ν μ' ν' F Gμ Gν Hμ Hν
      rcases F with F | F
      · unfold elimCaseFn; simp [F]; grind
      · simp [neg] at *
        have G : ¬ α = φ.disj ψ ∨ ¬ β = bot := by {
          by_cases G1 : α = φ.disj ψ
          · simp [conc] at F; grind
          · grind
        }
        rcases G with G | G <;>
          (unfold elimCaseFn; simp [G]; grind)
  · subst H
    induction π
    · rename_i α
      by_cases A : α = (φ.disj ψ).impl bot
      · subst_vars; simp [elimCaseFn]; apply elimCase.ax1_ec
      · simp [elimCaseFn, A]; apply elimCase.ax2_ec ; simp [neg]; grind
    · rename_i α μ ih
      simp [elimCaseFn]
      exact elimCase.raa_ec α μ (elimCaseFn φ ψ ρ υ μ) ih
    · rename_i α β μ ih
      simp [elimCaseFn]
      exact elimCase.abs_ec α β μ (elimCaseFn φ ψ ρ υ μ) ih
    · rename_i α β μ ν ihμ ihν
      by_cases A : α = φ.disj ψ ∧ β = bot ∧ μ = ax (α.impl β)
      · rcases A with ⟨A1,A2,A3⟩;
        subst_vars
        cases ν <;> simp [elimCaseFn] at * <;>
          constructor <;> try simp [lrof] at *
        all_goals try assumption
        · cases ihν; assumption
      · have B : ¬α = φ.disj ψ ∨ ¬β = bot ∨ ¬μ = ax (α.impl β) := by grind
        rcases B with B | B | B <;> unfold elimCaseFn <;> simp [B]
        · apply elimCase.app_ec <;> try assumption
          simp [neg, conc]; grind
        · apply elimCase.app_ec <;> try assumption
          simp [neg, conc]; grind
        · cases μ <;> simp [lrof] at * <;> try grind
          all_goals
            (simp [elimCaseFn] at * ; constructor <;>
              try (simp [lrof])) <;> try grind
    all_goals (simp [elimCaseFn] at *; constructor <;>
                  try (simp [lrof])) <;> try grind


lemma contract_contractFn : ∀ φ (π: nkprf φ), isCut π →
    contract π (contractFn π) := by
  intro φ π A; cases A <;>
    simp [contractFn]
  · apply contract.appAbsContract; rw [graft_graftFn]
  · apply contract.fstPairContract
  · apply contract.sndPairContract
  · apply contract.caseLeftContract; rw [graft_graftFn]
  · apply contract.caseRightContract; rw [graft_graftFn]
  · apply contract.raaBotContract; rw [elimBot_elimBotFn]
  · apply contract.raaNegContract; rw [elimNeg_elimNegFn]
  · apply contract.appRaaContract; rw [elimApp_elimAppFn]
  · apply contract.fstRaaContract; rw [elimFst_elimFstFn]
  · apply contract.sndRaaContract; rw [elimSnd_elimSndFn]
  · apply contract.caseRaaContract; rw [elimCase_elimCaseFn]

lemma oneStep_stepOne : ∀ σ (π : nkprf σ),
  maxDeg π > 0 → oneStep σ π (stepOne π) := by
  intro σ π Hmd; fun_induction stepOne
  · -- ax
    rename_i α; simp [maxDeg, cutrank, degwt] at Hmd
  · -- raaStep
    rename_i α μ A ihμ; simp [A]; apply oneStep.raaStep
    rfl; grind; grind
  · -- raaCrit
    rename_i α μ A;
    have B1 : maxDeg μ < maxDeg (raa α μ) := by
      apply raaCritCondition; rfl; grind
    simp [A]; apply oneStep.raaCrit
    rfl; apply contract_contractFn;
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
    rfl; grind; grind; grind
  · -- appCrit
    rename_i β α μ ν A B
    simp [A,B]
    have A' : maxDeg ν < maxDeg (app α β μ ν) := by
      apply app1StepCondition; rfl; grind
    apply appCritCondition at A; apply A at B
    rcases B with ⟨B1, B2⟩
    rw [←B1] at Hmd; simp [←degreeOfCut] at Hmd
    apply oneStep.appCrit
    rfl; apply contract_contractFn
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
    simp [A]; apply oneStep.fstStep; rfl; grind; grind
  · -- fstCrit
    rename_i α β μ A
    simp [A]
    apply fstCritCondition at A
    rcases A with ⟨A1, A2⟩
    rw [←A1] at Hmd; simp [←degreeOfCut] at Hmd
    apply oneStep.fstCrit
    rfl; apply contract_contractFn
    assumption; assumption; assumption; rfl
  · -- sndStep
    rename_i α β μ A ihμ
    simp [A]; apply oneStep.sndStep; rfl; grind; grind
  · -- sndCrit
    rename_i α β μ A
    simp [A]
    apply sndCritCondition at A
    rcases A with ⟨A1, A2⟩
    rw [←A1] at Hmd; simp [←degreeOfCut] at Hmd
    apply oneStep.sndCrit
    rfl; apply contract_contractFn
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
    rename_i α β χ μ ν A ihν
    simp [A]; apply oneStep.case3Step
    rfl; grind; grind
  · -- case2Step
    rename_i α β χ μ ν A B ihμ
    simp [A,B]
    have A' : maxDeg ν < maxDeg (case α β χ μ ν) := by
      apply case2StepCondition; rfl; grind
    apply oneStep.case2Step; rfl; grind; grind; grind
  · -- case1Step
    rename_i α β χ μ ν A B C ihχ
    have A1 : maxDeg ν < maxDeg (case α β χ μ ν) ∧
              maxDeg μ < maxDeg (case α β χ μ ν) := by
      constructor
      · apply case2StepCondition; rfl; grind
      · apply case1StepCondition; rfl; grind; grind
    simp [A,B,C]; apply oneStep.case1Step
    rfl; grind; grind; grind; grind
  · -- caseCrit
    rename_i α β χ μ ν A B C
    have A1 : maxDeg ν < maxDeg (case α β χ μ ν) ∧
              maxDeg μ < maxDeg (case α β χ μ ν) := by
      constructor
      · apply case2StepCondition; rfl; grind
      · apply case1StepCondition; rfl; grind; grind
    -- rcases A1 with ⟨A1, A2⟩
    simp [A,B,C]; apply caseCritCondition at A; apply A at B; apply B at C;
    rcases C with ⟨C1, C2⟩
    rw [←C1] at Hmd; simp [←degreeOfCut] at Hmd
    apply oneStep.caseCrit
    rfl; apply contract_contractFn
    assumption; assumption; assumption; grind; grind; rfl

lemma stepOne_dec : ∀ φ (π : nkprf φ), maxDeg π ≠ 0 →
  cutrank (stepOne π) < cutrank π := by
  intro φ π A
  have B : oneStep φ π (stepOne π) := by apply oneStep_stepOne; grind
  apply oneStepCutRank; assumption

def normalize {φ} (π : nkprf φ) : nkprf φ :=
  if maxDeg π = 0 then π else
    normalize (stepOne π)
    termination_by cutrank π
    decreasing_by apply stepOne_dec; assumption

theorem norm_normal : ∀ φ (π : nkprf φ), isNormal (normalize π) := by
  intro φ π; fun_induction normalize
  · rename_i μ A;
    rw [normal_cutrank]; simp [maxDeg] at A;
    rcases cutrank_goodRank _ μ with B | B <;> try grind
    ext <;> grind
  · grind

theorem norm_concAss : ∀ φ (π : nkprf φ),
  hypos (normalize π) ⊆ hypos π ∧ conc (normalize π) = conc π := by
  intro φ π; fun_induction normalize
  · grind
  · rename_i μ Hmd ih
    have B : oneStep φ μ (stepOne μ) := by apply oneStep_stepOne; grind
    have C : hypos (stepOne μ) ⊆ hypos μ ∧ conc (stepOne μ) = conc μ := by
        apply oneStepConcAss; exact B
    grind

def α : propform := letter 0
def β : propform := letter 1

def μ : nkprf (impl α (impl β β)) :=
  abs α (impl β β)
    (abs β β
      (app α β  (raa _
                  (case α β (left α β (ax α))
                        (app _ _ (ax (neg (impl α β))) (abs α β (ax β)))
                        (app _ _ (ax (neg (impl α β))) (abs α β (ax β)))
                  )
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

end nkNormAlg
