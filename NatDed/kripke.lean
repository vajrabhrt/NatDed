import Mathlib

import NatDed.nj

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.lambdaSyntax false

-- Kripke semantics for intuitionistic logic and soundness of NJ
namespace Kripke
open nj
open nj.propform
open nj.njprf

structure KripkeModel where
  World : Type
  [instPreorder : Preorder World]
  Val : ℕ → World → Prop
  monotone : ∀ n c c', c ≤ c' →
      Val n c → Val n c'
attribute [instance] KripkeModel.instPreorder

def Forces {M : KripkeModel} :
    M.World → propform → Prop
| c, .bot       => False
| c, .letter n  => M.Val n c
| c, .impl α β  => ∀ d, c ≤ d →
                  Forces d α → Forces d β
| c, .conj α β  => Forces c α ∧ Forces c β
| c, .disj α β  => Forces c α ∨ Forces c β

def Entails (X: Set propform) (α : propform) : Prop :=
  ∀ (M : KripkeModel) (c : M.World), (∀ β, β ∈ X → Forces c β) → Forces c α

lemma forces_monotone : ∀ (M : KripkeModel)
    (c c' : M.World) (α : propform),
    c ≤ c' → Forces c α → Forces c' α := by
  intro M c c' α h
  induction α generalizing c c'
  · intro hbot
    cases hbot
  · rename_i x
    intro hx
    exact M.monotone x c c' h hx
  · rename_i α β ihα ihβ
    intro hImp d hc'd hdα
    apply hImp <;> grind
  · rename_i α β ihα ihβ
    rintro ⟨hα,hβ⟩
    constructor
    · apply ihα c c' h hα
    · apply ihβ c c' h hβ
  · rename_i α β ihα ihβ
    rintro (hα | hβ)
    · left; apply ihα c c' h hα
    · right; apply ihβ c c' h hβ

lemma soundness' : ∀ (α : propform) (π: njprf α), Entails (hypos π) α := by
  intro φ π
  induction π <;> intro M c fhπ
  · rename_i α
    simp [hypos] at fhπ; grind
  · rename_i α μ ihμ
    simp [hypos] at fhπ; apply ihμ at fhπ
    cases fhπ
  · rename_i α β μ ihμ
    intro d cled fdα
    simp [hypos] at fhπ;
    apply ihμ; intro γ hγ
    have H: γ = α ∨ ¬γ = α := by grind
    rcases H with (H | H)
    · grind
    · apply forces_monotone (c := c)
      · assumption
      · grind
  · rename_i α β μ ν ihμ ihν
    have himp : Forces c (α.impl β) := by {
      apply ihμ; intro γ hγ; apply fhπ
      simp [hypos]; grind
    }
    have hα : Forces c α := by {
      apply ihν; intro γ hγ; apply fhπ
      simp [hypos]; grind
    }
    apply himp <;> grind
  · rename_i α β μ ν ihμ ihν
    have hα : Forces c α := by {
      apply ihμ; intro γ hγ; apply fhπ
      simp [hypos]; grind
    }
    have hβ : Forces c β := by {
      apply ihν; intro γ hγ; apply fhπ
      simp [hypos]; grind
    }
    constructor <;> assumption
  · rename_i α β μ ihμ
    let fαβ := ihμ M c fhπ
    cases fαβ; grind
  · rename_i α β μ ihμ
    let fαβ := ihμ M c fhπ
    cases fαβ; grind
  · rename_i α β μ ihμ
    let fα := ihμ M c fhπ
    left; assumption
  · rename_i α β μ ihμ
    let fβ := ihμ M c fhπ
    right; assumption
  · rename_i α β δ χ μ ν ihχ ihμ ihν
    simp [hypos] at fhπ
    have hdisj : Forces c (disj α β) := by {
      apply ihχ; intro γ hγ
      apply fhπ; grind
    }
    rcases hdisj with (H | H)
    · apply ihμ; intro γ hγ
      have G : γ = α ∨ ¬γ = α := by grind
      rcases G with (G | G)
      · grind
      · apply fhπ; grind
    · apply ihν; intro γ hγ
      have G : γ = β ∨ ¬γ = β := by grind
      rcases G with (G | G)
      · grind
      · apply fhπ; grind

theorem soundness : ∀ (X: Set propform) (α : propform),
  Deducible X α → Entails X α := by
  rintro X φ ⟨π, hπ⟩
  intro M c fX
  apply soundness' _ π
  intro δ δinhπ
  apply fX; grind

end Kripke
