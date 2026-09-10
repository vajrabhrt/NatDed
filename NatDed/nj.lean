import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.lambdaSyntax false
set_option linter.style.longLine false
set_option linter.style.multiGoal false

namespace nj
-- Syntax of intuitionistic propositional logic

inductive propform where
| bot : propform
| letter : ℕ → propform
| impl : propform → propform → propform
| conj : propform → propform → propform
| disj : propform → propform → propform
deriving Repr, DecidableEq

def neg (α : propform) : propform := .impl α .bot

open propform

def sz : propform → ℕ
| .bot => 1
| .letter _ => 1
| .impl α β => sz α + sz β + 1
| .conj α β => sz α + sz β + 1
| .disj α β => sz α + sz β + 1

lemma sz_gt_0 : ∀ α, sz α > 0 := by
  intro α; cases α <;> simp [sz]

def sf : propform → Set propform
| .bot => {bot}
| .letter n => {letter n}
| .impl α β => {impl α β} ∪ sf α ∪ sf β
| .conj α β => {conj α β} ∪ sf α ∪ sf β
| .disj α β => {disj α β} ∪ sf α ∪ sf β

lemma self_sf : ∀ α, α ∈ sf α := by
  intro α; cases α <;> simp [sf]

def SF (X: Set propform) : Set propform := {α | ∃ φ ∈ X, α ∈ sf φ}

lemma sf_trans : ∀ θ ψ φ : propform, θ ∈ sf ψ → ψ ∈ sf φ → θ ∈ sf φ := by
    intro θ ψ φ; induction φ generalizing ψ
    · simp [sf]; intro f g; subst_vars; rfl
    · simp [sf]; intro f g; subst_vars; rfl
    · rename_i α β ihα ihβ; simp [sf]
      rintro f ((g|g)|g)
      · subst_vars; simp [sf] at f; assumption
      · left; right; apply ihα ψ f g
      · right; apply ihβ ψ f g
    · rename_i α β ihα ihβ; simp [sf]
      rintro f ((g|g)|g)
      · subst_vars; simp [sf] at f; assumption
      · left; right; apply ihα ψ f g
      · right; apply ihβ ψ f g
    · rename_i α β ihα ihβ; simp [sf]
      rintro f ((g|g)|g)
      · subst_vars; simp [sf] at f; assumption
      · left; right; apply ihα ψ f g
      · right; apply ihβ ψ f g

lemma SF_cong : ∀ X Y : Set propform, X ⊆ Y → SF X ⊆ SF Y := by
    intro X Y hss
    simp [SF]; intro a x xinX ainsf
    exists x; grind

-- Defining Natural Deduction proofs for intuitionistic propositional logic
-- The System NJ

inductive njprf : propform → Type
| ax :  ∀ α, njprf α
| emp : ∀ α , njprf bot → njprf α
| abs : ∀ α β, njprf β → njprf (impl α β)
| app: ∀ α β, njprf (impl α β) → njprf α → njprf β
| pair : ∀ α β, njprf α → njprf β → njprf (conj α β)
| fst : ∀ α β, njprf (conj α β) → njprf α
| snd : ∀ α β, njprf (conj α β) → njprf β
| left : ∀ α β, njprf α → njprf (disj α β)
| right : ∀ α β, njprf β → njprf (disj α β)
| case : ∀ α β δ, njprf (disj α β) → njprf δ → njprf δ → njprf δ
deriving Repr, DecidableEq

def hypos {α : propform} : (π: njprf α) → Set propform
| .ax β =>  {β}
| .emp _ μ => hypos μ
| .abs α _ μ =>  hypos μ \ {α}
| .app _ _ μ ν => hypos μ ∪ hypos ν
| .pair _ _ μ ν => hypos μ ∪ hypos ν
| .fst _ _ μ =>  hypos μ
| .snd _ _ μ =>  hypos μ
| .left _ _ μ => hypos μ
| .right _ _ μ => hypos μ
| .case α β _ χ μ ν => hypos χ ∪ (hypos μ \ {α}) ∪ (hypos ν \ {β})

def conc {α : propform} (π: njprf α) : propform := α

def NJPrf := Σ (α : propform), njprf α

def Conc (prf: NJPrf) : propform := prf.1

def Hypos (prf: NJPrf) : Set propform := hypos prf.2

inductive proofrule where
| prax
| premp
| prabs
| prapp
| prpair
| prfst
| prsnd
| prleft
| prright
| prcase
deriving Repr , DecidableEq

open njprf
open proofrule

def lrof {α} (π : njprf α) : proofrule :=
match π with
| .ax _ =>  prax
| .emp _ _ => premp
| .abs _ _ _ =>  prabs
| .app _ _ _ _ => prapp
| .pair _ _ _ _ => prpair
| .fst _ _ _ =>  prfst
| .snd _ _ _ =>  prsnd
| .left _ _ _ => prleft
| .right _ _ _ => prright
| .case _ _ _ _ _ _ => prcase

def formsin {α} (π: njprf α) : Set propform :=
  match π with
  | .ax α => {α}
  | .emp α μ => {α} ∪ formsin μ
  | .abs α β μ =>  {impl α β} ∪ formsin μ
  | .app _ β μ ν => {β} ∪ formsin μ ∪ formsin ν
  | .pair α β μ ν => {conj α β} ∪ formsin μ  ∪ formsin ν
  | .fst α _ μ =>  {α} ∪ formsin μ
  | .snd _ β μ =>  {β} ∪ formsin μ
  | .left α β μ => {disj α β} ∪ formsin μ
  | .right α β μ => {disj α β} ∪ formsin μ
  | .case _ _ _ χ μ ν => formsin χ ∪ formsin μ ∪ formsin ν

lemma conc_in_forms : ∀ φ (π : njprf φ), φ ∈ formsin π := by
    intro φ π; induction  π <;> simp [formsin]; grind

def prfsize {α} (π: njprf α) : ℕ :=
  match π with
  | .ax _ => 1
  | .emp _ μ => 1 + prfsize μ
  | .abs _ _ μ =>  1 + prfsize μ
  | .app _ _ μ ν => 1 + prfsize μ + prfsize ν
  | .pair _ _ μ ν => 1 + prfsize μ + prfsize ν
  | .fst _ _ μ =>  1 + prfsize μ
  | .snd _ _ μ =>  1 + prfsize μ
  | .left _ _ μ => 1 + prfsize μ
  | .right _ _ μ => 1 + prfsize μ
  | .case α β _ χ μ ν => 1 + prfsize χ + prfsize μ + prfsize ν

lemma prfsize_gt_0 : ∀ φ (π : njprf φ), prfsize π > 0 := by
  intro φ π; cases π <;> simp [prfsize]

def subproofs {α} (π: njprf α) : Set NJPrf :=
  match π with
  | .ax _ => {⟨_,π⟩}
  | .emp _ μ => {⟨_, π⟩} ∪ subproofs μ
  | .abs _ _ μ =>  {⟨_, π⟩} ∪ subproofs μ
  | .app _ _ μ ν => {⟨_, π⟩} ∪ subproofs μ ∪ subproofs ν
  | .pair _ _ μ ν => {⟨_, π⟩} ∪ subproofs μ  ∪ subproofs ν
  | .fst _ _ μ =>  {⟨_, π⟩} ∪ subproofs μ
  | .snd _ _ μ =>  {⟨_, π⟩} ∪ subproofs μ
  | .left _ _ μ => {⟨_, π⟩} ∪ subproofs μ
  | .right _ _ μ => {⟨_, π⟩} ∪ subproofs μ
  | .case α β _ χ μ ν => {⟨_, π⟩} ∪ subproofs χ ∪ subproofs μ ∪ subproofs ν

@[simp]
lemma self_sp : ∀ φ (π : njprf φ), ⟨φ,π⟩ ∈ subproofs π := by
  intro φ π; rcases π <;> simp [subproofs] <;> grind

lemma sp_trans : ∀ φ ψ θ (π : njprf φ) (ϖ : njprf ψ) (υ : njprf θ),
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
  · rename_i α β δ χ μ ν ihχ ihμ ihν
    rcases fsp with ((fsp | fsp) | fsp) | fsp
    · cases fsp; simp [subproofs] at *; assumption
    · left; left; right; apply ihχ; exact fsp; exact gsp
    · left; right; apply ihμ; exact fsp; exact gsp
    · right; apply ihν; exact fsp; exact gsp

def Deducible (X : Set propform) (α : propform) : Prop :=
  ∃ (π: njprf α), hypos π ⊆ X

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

end nj
