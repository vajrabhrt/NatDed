import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.style.multiGoal false

namespace nk
-- Syntax of classical propositional logic

inductive propform where
| bot : propform
| letter : ℕ → propform
| impl : propform → propform → propform
| conj : propform → propform → propform
| disj : propform → propform → propform
deriving Repr, DecidableEq

def neg (α : propform) : propform := .impl α .bot

open propform

def bar : propform → propform
  | impl α bot => α
  | α => impl α bot

def sz : propform → ℕ
| .bot => 1
| .letter _ => 1
| .impl α β => sz α + sz β + 1
| .conj α β => sz α + sz β + 1
| .disj α β => sz α + sz β + 1

lemma sz_gt_0 : ∀ α, sz α > 0 := by
  intro α; cases α <;> simp [sz]

def cl : propform → Set propform
| .bot => {bot, bar bot}
| .letter n => {bot, bar bot, letter n, bar (letter n)}
| .impl α β => {impl α β, bar (impl α β)} ∪ cl α ∪ cl β
| .conj α β => {conj α β, bar (conj α β)} ∪ cl α ∪ cl β
| .disj α β => {disj α β, bar (disj α β)} ∪ cl α ∪ cl β

lemma self_cl : ∀ α, α ∈ cl α := by
  intro α; cases α <;> simp [cl]

lemma bot_cl : ∀ α, bot ∈ cl α := by
  intro α; induction α <;> simp [cl] <;> grind

lemma barbot_cl : ∀ α, bot.impl bot ∈ cl α := by
  intro α; induction α <;> simp [cl, bar] at * <;> grind

lemma impl_cl : ∀ α β, β ≠ bot → cl (impl α β) = cl (bar (impl α β)) := by
  intro α β H; simp [bar, cl, H, bot_cl, barbot_cl]; grind

lemma conj_cl : ∀ α β, cl (conj α β) = cl (bar (conj α β)) := by
  intro α β; simp [bar, cl, bot_cl, barbot_cl]; grind

lemma disj_cl : ∀ α β, cl (disj α β) = cl (bar (disj α β)) := by
  intro α β; simp [bar, cl, bot_cl, barbot_cl]; grind

lemma cl_trans : ∀ θ ψ φ : propform, θ ∈ cl ψ → ψ ∈ cl φ → θ ∈ cl φ := by
    intro θ ψ φ; induction φ generalizing ψ
    · simp [cl]; intro f g; simp [bar] at *;
      rcases g with g | g <;> subst_vars <;> simp [cl, bar] at * <;> grind
    · simp [cl]; intro f g; simp [bar] at *;
      rcases g with g | g | g | g <;> subst_vars <;>
        simp [cl,bar] at * <;> grind
    · rename_i α β ihα ihβ; intro A;
      set Hα := ihα _ A; set Hβ := ihβ _ A;
      intro F; simp [cl] at F
      rcases F with ((F | F) | F) | F <;> subst_vars
      · simp [cl, bar] at A; simp [cl, bar]; grind
      · by_cases B : β = bot
        · subst_vars
          simp [bar] at A; simp [cl]; simp [bar]; grind
        · rw [impl_cl] <;> grind
      · simp [cl]; grind
      · simp [cl]; grind
    · rename_i α β ihα ihβ; intro A;
      set Hα := ihα _ A; set Hβ := ihβ _ A;
      intro F; simp [cl] at F
      rcases F with ((F | F) | F) | F <;> subst_vars
      · simp [cl, bar] at A; simp [cl, bar]; grind
      · rw [conj_cl]; grind
      · simp [cl]; grind
      · simp [cl]; grind
    · rename_i α β ihα ihβ; intro A;
      set Hα := ihα _ A; set Hβ := ihβ _ A;
      intro F; simp [cl] at F
      rcases F with ((F | F) | F) | F <;> subst_vars
      · simp [cl, bar] at A; simp [cl, bar]; grind
      · rw [disj_cl]; grind
      · simp [cl]; grind
      · simp [cl]; grind

def CL (X: Set propform) : Set propform := {α | ∃ φ ∈ X, α ∈ cl φ}

lemma CL_cong : ∀ X Y : Set propform, X ⊆ Y → CL X ⊆ CL Y := by
    intro X Y hss
    simp [CL]; intro a x xinX aincl
    exists x; grind

-- Defining Natural Deduction proofs for classical propositional logic
-- The System NK

inductive nkprf : propform → Type
| ax :  ∀ α, nkprf α
| raa : ∀ α , nkprf bot → nkprf α
| abs : ∀ α β, nkprf β → nkprf (impl α β)
| app: ∀ α β, nkprf (impl α β) → nkprf α → nkprf β
| pair : ∀ α β, nkprf α → nkprf β → nkprf (conj α β)
| fst : ∀ α β, nkprf (conj α β) → nkprf α
| snd : ∀ α β, nkprf (conj α β) → nkprf β
| left : ∀ α β, nkprf α → nkprf (disj α β)
| right : ∀ α β, nkprf β → nkprf (disj α β)
| case : ∀ α β, nkprf (disj α β) → nkprf bot → nkprf bot → nkprf bot
deriving Repr, DecidableEq

def hypos {α : propform} : (π: nkprf α) → Set propform
| .ax β =>  {β}
| .raa α μ => hypos μ \ {neg α}
| .abs α _ μ =>  hypos μ \ {α}
| .app _ _ μ ν => hypos μ ∪ hypos ν
| .pair _ _ μ ν => hypos μ ∪ hypos ν
| .fst _ _ μ =>  hypos μ
| .snd _ _ μ =>  hypos μ
| .left _ _ μ => hypos μ
| .right _ _ μ => hypos μ
| .case α β χ μ ν => hypos χ ∪ (hypos μ \ {α}) ∪ (hypos ν \ {β})

def conc {α : propform} (π: nkprf α) : propform := α

def NKPrf := Σ (α : propform), nkprf α

def Conc (prf: NKPrf) : propform := prf.1

def Hypos (prf: NKPrf) : Set propform := hypos prf.2

inductive proofrule where
| prax
| prraa
| prabs
| prapp
| prpair
| prfst
| prsnd
| prleft
| prright
| prcase
deriving Repr , DecidableEq

open nkprf
open proofrule

def lrof {α} (π : nkprf α) : proofrule :=
match π with
| .ax _ =>  prax
| .raa _ _ => prraa
| .abs _ _ _ =>  prabs
| .app _ _ _ _ => prapp
| .pair _ _ _ _ => prpair
| .fst _ _ _ =>  prfst
| .snd _ _ _ =>  prsnd
| .left _ _ _ => prleft
| .right _ _ _ => prright
| .case _ _ _ _ _ => prcase

def formsin {α} (π: nkprf α) : Set propform :=
  match π with
  | .ax α => {α}
  | .raa α μ => {α} ∪ formsin μ
  | .abs α β μ =>  {impl α β} ∪ formsin μ
  | .app _ β μ ν => {β} ∪ formsin μ ∪ formsin ν
  | .pair α β μ ν => {conj α β} ∪ formsin μ  ∪ formsin ν
  | .fst α _ μ =>  {α} ∪ formsin μ
  | .snd _ β μ =>  {β} ∪ formsin μ
  | .left α β μ => {disj α β} ∪ formsin μ
  | .right α β μ => {disj α β} ∪ formsin μ
  | .case _ _ χ μ ν => formsin χ ∪ formsin μ ∪ formsin ν

lemma conc_in_forms : ∀ φ (π : nkprf φ), φ ∈ formsin π := by
    intro φ π; induction  π <;> simp [formsin]; grind

def prfsize {α} (π: nkprf α) : ℕ :=
  match π with
  | .ax _ => 1
  | .raa _ μ => 1 + prfsize μ
  | .abs _ _ μ =>  1 + prfsize μ
  | .app _ _ μ ν => 1 + prfsize μ + prfsize ν
  | .pair _ _ μ ν => 1 + prfsize μ + prfsize ν
  | .fst _ _ μ =>  1 + prfsize μ
  | .snd _ _ μ =>  1 + prfsize μ
  | .left _ _ μ => 1 + prfsize μ
  | .right _ _ μ => 1 + prfsize μ
  | .case α β χ μ ν => 1 + prfsize χ + prfsize μ + prfsize ν

lemma prfsize_gt_0 : ∀ φ (π : nkprf φ), prfsize π > 0 := by
  intro φ π; cases π <;> simp [prfsize]

def subproofs {α} (π: nkprf α) : Set NKPrf :=
  match π with
  | .ax _ => {⟨_,π⟩}
  | .raa _ μ => {⟨_, π⟩} ∪ subproofs μ
  | .abs _ _ μ =>  {⟨_, π⟩} ∪ subproofs μ
  | .app _ _ μ ν => {⟨_, π⟩} ∪ subproofs μ ∪ subproofs ν
  | .pair _ _ μ ν => {⟨_, π⟩} ∪ subproofs μ  ∪ subproofs ν
  | .fst _ _ μ =>  {⟨_, π⟩} ∪ subproofs μ
  | .snd _ _ μ =>  {⟨_, π⟩} ∪ subproofs μ
  | .left _ _ μ => {⟨_, π⟩} ∪ subproofs μ
  | .right _ _ μ => {⟨_, π⟩} ∪ subproofs μ
  | .case α β χ μ ν => {⟨_, π⟩} ∪ subproofs χ ∪ subproofs μ ∪ subproofs ν

@[simp]
lemma self_sp : ∀ φ (π : nkprf φ), ⟨φ,π⟩ ∈ subproofs π := by
  intro φ π; rcases π <;> simp [subproofs] <;> grind

lemma sp_trans : ∀ φ ψ θ (π : nkprf φ) (ϖ : nkprf ψ) (υ : nkprf θ),
  ⟨ψ, ϖ⟩ ∈ subproofs π → ⟨θ, υ⟩ ∈ subproofs ϖ →
  ⟨θ, υ⟩ ∈ subproofs π := by
  intro φ ψ θ π ϖ υ
  induction π generalizing ψ ϖ <;>
    intro fsp gsp <;> simp [subproofs] at *
  · cases fsp; simp [subproofs] at *; assumption
  · rename_i α μ ihμ
    rcases fsp with fsp | fsp
    · cases fsp; simp [subproofs] at *; assumption
    · right; apply ihμ; exact fsp; exact gsp
  · rename_i α β μ ihμ
    rcases fsp with fsp | fsp
    · cases fsp; simp [subproofs] at *; assumption
    · right; apply ihμ; exact fsp; exact gsp
  · rename_i α β μ ν ihμ ihν
    rcases fsp with (fsp | fsp) | fsp
    · cases fsp; simp [subproofs] at *; assumption
    · left; right; apply ihμ; exact fsp; exact gsp
    · right; apply ihν; exact fsp; exact gsp
  · rename_i α β μ ν ihμ ihν
    rcases fsp with (fsp | fsp) | fsp
    · cases fsp; simp [subproofs] at *; assumption
    · left; right; apply ihμ; exact fsp; exact gsp
    · right; apply ihν; exact fsp; exact gsp
  · rename_i α β μ ihμ
    rcases fsp with fsp | fsp
    · cases fsp; simp [subproofs] at *; assumption
    · right; apply ihμ; exact fsp; exact gsp
  · rename_i α β μ ihμ
    rcases fsp with fsp | fsp
    · cases fsp; simp [subproofs] at *; assumption
    · right; apply ihμ; exact fsp; exact gsp
  · rename_i α β μ ihμ
    rcases fsp with fsp | fsp
    · cases fsp; simp [subproofs] at *; assumption
    · right; apply ihμ; exact fsp; exact gsp
  · rename_i α β μ ihμ
    rcases fsp with fsp | fsp
    · cases fsp; simp [subproofs] at *; assumption
    · right; apply ihμ; exact fsp; exact gsp
  · rename_i α β χ μ ν ihχ ihμ ihν
    rcases fsp with ((fsp | fsp) | fsp) | fsp
    · cases fsp; simp [subproofs] at *; assumption
    · left; left; right; apply ihχ; exact fsp; exact gsp
    · left; right; apply ihμ; exact fsp; exact gsp
    · right; apply ihν; exact fsp; exact gsp

def Deducible (X : Set propform) (α : propform) : Prop :=
  ∃ (π: nkprf α), hypos π ⊆ X

def Provable (α : propform) : Prop := Deducible ∅ α

theorem ex1 : ∀ (α β : propform),
  Provable (impl α (impl (impl α β) β)) := by
  intro α β
  exists (abs _ _ (abs _ _ (app _ _ (ax (impl α β)) (ax α))))
  simp [hypos]; grind

theorem ex2 : ∀ (α : propform),
  Provable (neg (neg (disj α (neg α)))) := by
  intro α
  exists (abs _ _
            (app _ _ (ax (neg (disj α (neg α))))
                (right _ _ (abs _ _
                              (app _ _ (ax (neg (disj α (neg α))))
                                  (left _ _ (ax α))
                              )
                            )
                )
            )
          )
  simp [hypos, neg]

end nk
