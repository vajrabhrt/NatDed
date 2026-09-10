import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.style.lambdaSyntax false
set_option linter.dupNamespace false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option warn.classDefReducibility false

namespace Rank

inductive Rank where
  | mk : ℕ → ℕ → Rank
deriving DecidableEq

@[ext]
lemma rank_ext : ∀ (r s : Rank), r.1 = s.1 → r.2 = s.2 → r = s := by
  intro r s; intros
  cases r
  cases s
  simp_all

instance : LT Rank where
lt
| ⟨d1, w1⟩, ⟨d2, w2⟩ => d1 < d2 ∨ d1 = d2 ∧ w1 < w2

instance : LE Rank where
le
| r1, r2 => r1 < r2 ∨ r1 = r2

lemma rank_lt_rank_iff : ∀ (r s: Rank),
  r < s ↔ r.1 < s.1 ∨ r.1 = s.1 ∧ r.2 < s.2 := by
  intro r s; rfl

lemma rank_lt_rankd0_iff : ∀ (r s : Rank),
  s.2 = 0 → (r < s ↔ r.1 < s.1) := by
  intro r s H; rw [rank_lt_rank_iff]; grind

lemma rank_lt_rank0w_iff : ∀ (r s : Rank),
  s.1 = 0 → (r < s ↔ r.1 = 0 ∧ r.2 < s.2) := by
  intro r s H; simp [rank_lt_rank_iff, H]

lemma rank_le_rank_iff : ∀ (r s: Rank),
  r ≤ s ↔ r.1 < s.1 ∨ r.1 = s.1 ∧ r.2 ≤ s.2 := by
  intro ⟨dr,wr⟩ ⟨ds,ws⟩; constructor
  · rintro ((H | ⟨G,H⟩ ) | ⟨G,H⟩ ) <;> simp
    · left; assumption
    · right; constructor <;> grind
  · simp; rintro (H | ⟨G,H⟩)
    · left; left; assumption
    · have F : wr < ws ∨ wr = ws := by grind
      rcases F with F | F
      · left; right; constructor <;> assumption
      · right; ext <;> simpa

lemma rank_le_rank0w_iff : ∀ (r s : Rank),
  s.1 = 0 → (r ≤ s ↔ r.1 = 0 ∧ r.2 ≤ s.2) := by
  intro r s H; simp [rank_le_rank_iff, H]

@[simp]
lemma rank_le_proj : ∀ (r s : Rank),
  r ≤ s → r.1 ≤  s.1 := by
  intro r s; rw [rank_le_rank_iff]; grind

@[simp]
lemma rank_00_least : ∀ r, Rank.mk 0 0 ≤ r := by
  intros; simp [rank_le_rank_iff]; grind

instance : OrderBot Rank where
  bot := Rank.mk 0 0
  bot_le := by intro ⟨d,w⟩; simp [rank_le_rank_iff]; grind

def dec_rank_le : ∀ r1 r2 : Rank, Decidable (r1 ≤ r2) := by
  intro ⟨d1,w1⟩ ⟨d2,w2⟩
  if f: d1 < d2 then
    apply isTrue (by simp [rank_le_rank_iff]; grind)
  else if g: d1 > d2 then
    apply isFalse (by simp [rank_le_rank_iff]; grind)
    else if h : w1 < w2 then
      apply isTrue (by simp [rank_le_rank_iff]; grind)
      else if e : w1 > w2 then
        apply isFalse (by simp [rank_le_rank_iff]; grind)
        else apply isTrue (by simp [rank_le_rank_iff]; grind)

instance : DecidableRel (LE.le : Rank → Rank → Prop) := dec_rank_le

instance : LinearOrder Rank where
  le_refl := by {
    simp [rank_le_rank_iff]
  }

  le_trans := by {
    intros; simp [rank_le_rank_iff] at *; grind
  }

  le_antisymm := by {
    intros; simp [rank_le_rank_iff] at *; ext <;> grind
  }

  le_total := by {
    intros; simp [rank_le_rank_iff] at *; grind
  }

  toDecidableLE := λ r1 r2 ↦ dec_rank_le r1 r2

  lt_iff_le_not_ge := by {
    intros; simp [rank_lt_rank_iff, rank_le_rank_iff] at *; grind
  }

instance: WellFoundedRelation Rank where
  rel := LT.lt
  wf := by {
    constructor; intro ⟨ad,aw⟩;
    induction ad generalizing aw
    · induction aw
      · constructor; intros; simp [rank_lt_rank_iff] at *
      · rename_i n ih
        constructor; simp [rank_lt_rank0w_iff]
        intro y f g; change Acc LT.lt (Rank.mk y.1 y.2);
        simp [f] at *; clear f
        by_cases h : y.2 = n
        · subst_vars; assumption
        · cases ih; rename_i ih; apply ih
          simp [rank_lt_rank0w_iff]; grind
    · rename_i ad ih; induction aw
      · constructor; rintro ⟨yd,yw⟩ (h | ⟨h1,h2⟩) <;> try grind
        by_cases g: yd < ad
        · cases ih yw; rename_i e; apply e; left; assumption
        · have f: yd = ad := by grind
          subst_vars; apply ih
      · rename_i aw ihw
        constructor; rintro ⟨zd,zw⟩ (h | ⟨h1,h2⟩) <;> try grind
        · by_cases g: zd = ad
          · subst_vars; apply ih
          · have g' : zd < ad := by grind
            cases ih zw; rename_i f; apply f; left; assumption
        · subst_vars; by_cases f: zw = aw
          · subst_vars; assumption
          · have e : zw < aw := by grind
            cases ihw; rename_i g; apply g
            right; grind
  }

def pairAdd (r1 r2 : Rank) : Rank :=
  match r1, r2 with
  | ⟨d1, w1⟩, ⟨d2, w2⟩ =>
    if d1 = d2 then ⟨d1, w1+w2⟩ else if d1 < d2 then r2 else r1

@[simp]
lemma pairAdd_comm : ∀ (r1 r2 : Rank), pairAdd r1 r2 = pairAdd r2 r1 := by
  intros; simp [pairAdd]; split_ifs <;> grind

@[simp]
lemma pairAdd_assoc : ∀ r1 r2 r3,
  pairAdd (pairAdd r1 r2) r3 = pairAdd r1 (pairAdd r2 r3) := by
  intros; simp [pairAdd]; split_ifs <;> grind

instance : Std.Associative pairAdd := ⟨pairAdd_assoc⟩
instance : Std.Commutative pairAdd := ⟨pairAdd_comm⟩

@[simp]
lemma leftId_00 : ∀ r : Rank, pairAdd ⟨0, 0⟩ r = r := by
  intros; simp [pairAdd]; split_ifs <;> ext <;> try grind

@[simp]
lemma rightId_00 : ∀ r : Rank, pairAdd r ⟨0,0⟩ = r := by
  intros; simp [pairAdd]

def rankCommMonoid : CommMonoid Rank where
  mul := pairAdd
  one := Rank.mk 0 0
  mul_assoc := pairAdd_assoc
  one_mul := leftId_00
  mul_one := rightId_00
  mul_comm := pairAdd_comm

instance : CommMonoid Rank := rankCommMonoid
@[simp]
lemma rank_one_def : (1 : Rank) = Rank.mk 0 0 := by rfl

lemma rank_mul_def : ∀ (r s: Rank), r * s = pairAdd r s := by intros; rfl

@[simp]
lemma pairAdd_eq_mul : ∀ (r s : Rank), pairAdd r s = r * s := by
  intro r s; rw [←rank_mul_def]

@[simp]
lemma pairAdd_eq_left : ∀ (r s : Rank), r.1 > s.1 → r * s = r := by
  intro r s H; cases r; cases s;
  rw [rank_mul_def]; simp [pairAdd]; grind


@[simp]
lemma pairAdd_eq_right : ∀ (r s : Rank), r.1 < s.1 → r * s = s := by
  intro r s H; cases r; cases s;
  rw [rank_mul_def]; simp [pairAdd]; grind

@[simp]
lemma pairAdd_eq_same : ∀ (r s : Rank), r.1 = s.1 → r * s = ⟨r.1, r.2+s.2⟩ := by
  intro r s H; cases r; cases s;
  rw [rank_mul_def]; simp [pairAdd]; grind

@[simp]
lemma mul_eq_id_iff : ∀ r s : Rank, r * s = 1 ↔ r = 1 ∧ s = 1 := by
  intro ⟨dr,wr⟩ ⟨ds,ws⟩;
  have A : (1 : Rank) = Rank.mk 0 0 := by rfl
  rw [A]; clear A; rw [rank_mul_def]; simp [pairAdd]; grind

@[simp]
lemma pairAdd_left_monotone : ∀ r r1 r2 : Rank, r1 ≤ r2 → r1 * r ≤ r2 * r := by
  rintro ⟨d,w⟩ ⟨d1,w1⟩ ⟨d2,w2⟩ ((h | ⟨h1,h2⟩) | ⟨h1,h2⟩) <;>
    rw [rank_mul_def] <;> rw [rank_mul_def] <;>
    simp [pairAdd] <;> split_ifs <;>
    rw [rank_le_rank_iff] <;> try grind

@[simp]
lemma pairAdd_right_monotone : ∀ r r1 r2 : Rank, r1 ≤ r2 → r * r1 ≤ r * r2 := by
  intro r r1 r2; rw [mul_comm]; nth_rewrite 2 [mul_comm]
  apply pairAdd_left_monotone

@[simp]
lemma rank_left_pairAdd : ∀ (r s : Rank), r ≤ r * s := by
  intro r s
  calc
    r = r * ⟨0,0⟩     := by rw [rank_mul_def, rightId_00]
    _ ≤ r * s         := by apply pairAdd_right_monotone; simp

@[simp]
lemma rank_right_pairAdd : ∀ (r s: Rank), r ≤ s * r := by
  intro r s; rw [mul_comm]; apply rank_left_pairAdd

@[simp]
lemma rank_le_mul_rank : ∀ (p q r : Rank), p ≤ r → p ≤ q * r := by
  intro p q r H; apply le_trans; exact H; apply rank_right_pairAdd

@[simp]
lemma rank_le_rank_mul : ∀ (p q r : Rank), p ≤ q → p ≤ q * r := by
  intro p q r H; apply le_trans; exact H; apply rank_left_pairAdd

instance: CanonicallyOrderedMul Rank where
  exists_mul_of_le := by
    rintro ⟨da,wa⟩ ⟨db,wb⟩ ((H | ⟨H1,H2⟩) | ⟨H1,H1⟩)
    · exists ⟨db,wb⟩; rw [rank_mul_def];
        simp [pairAdd]; split_ifs <;> grind
    · exists ⟨da, wb-wa⟩; rw [rank_mul_def];
        simp [pairAdd]; grind
    · exists ⟨0,0⟩; rw [rank_mul_def];
        simp [pairAdd]
  le_mul_self := by apply rank_right_pairAdd
  le_self_mul := by apply rank_left_pairAdd

instance : MulLeftMono Rank  := ⟨λ r a b h ↦ pairAdd_right_monotone r a b h⟩

instance : MulRightMono Rank := ⟨λ r a b h ↦ pairAdd_left_monotone r a b h⟩

lemma pairAdd_fst : ∀ (r1 r2 : Rank), (r1 * r2).1 = max r1.1 r2.1 := by
  intro ⟨d1, w1⟩ ⟨d2, w2⟩
  rw [rank_mul_def]; simp [pairAdd]; split_ifs <;> try grind

@[simp]
lemma left_pairAdd_consumed : ∀ (r s : Rank), r.1 < (r * s).1 → r * s = s := by
  intro ⟨dr,wr⟩ ⟨ds,ws⟩; simp;
  rw [rank_mul_def]; simp [pairAdd]; split_ifs <;> try grind

@[simp]
lemma right_pairAdd_consumed : ∀ (r s : Rank), r.1 < (s * r).1 → s * r = s := by
  intro ⟨dr,wr⟩ ⟨ds,ws⟩;
  rw [rank_mul_def]; simp [pairAdd]; split_ifs <;> try grind

@[simp]
lemma pairAdd_lt_rank : ∀ (p q r : Rank), (p * q).1 < r.1 ↔ p.1 < r.1 ∧ q.1 < r.1 := by
  intro p q r; rw [rank_mul_def]; simp [pairAdd] at *;
  split_ifs at * <;> grind

@[simp]
lemma pairAdd_le_rank : ∀ (p q r : Rank), (p * q).1 ≤ r.1 ↔ p.1 ≤ r.1 ∧ q.1 ≤ r.1 := by
  intro p q r; rw [rank_mul_def]; simp [pairAdd];
    split_ifs <;> grind

@[simp]
lemma rank_le_pairAdd : ∀ (p q r : Rank), r.1 ≤ (p * q).1 ↔ r.1 ≤ p.1 ∨ r.1 ≤ q.1 := by
  intro p q r; rw [rank_mul_def];
    simp [pairAdd]; split_ifs <;> grind

@[simp]
lemma pairAdd_le_Cong : ∀ r1 r2 r3 r4 : Rank,
  r1 ≤ r2 → r3 ≤ r4 → r1 * r3 ≤ r2 * r4 := by
  intro r1 r2 r3 r4 E F
  calc
    r1 * r3 ≤ r2 * r3   := by apply pairAdd_left_monotone; simp [E]
    _ ≤ r2 * r4         := by apply pairAdd_right_monotone; simp [F]

@[simp]
lemma pairAdd_left_smallerd : ∀ r1 r2 r3 : Rank,
  r1.1 < r3.1 → r2 ≤ r3 → r1 * r2 ≤ r3 := by
  intro r1 r2 r3 E F
  calc
    r1 * r2 ≤ r1 * r3 := by apply pairAdd_right_monotone; simp [F]
    _ = r3            := by simp [E]

@[simp]
lemma pairAdd_right_smallerd : ∀ r1 r2 r3 : Rank,
  r2.1 < r3.1 → r1 ≤ r3 → r1 * r2 ≤ r3 := by
  intro r1 r2 r3; rw [mul_comm]; apply pairAdd_left_smallerd

@[simp]
lemma pairAdd_eq_00 : ∀ r s : Rank,
  r * s = ⟨0,0⟩ ↔ r = ⟨0,0⟩ ∧ s = ⟨0,0⟩ := by
  intro r s; rw [rank_mul_def];
    simp [pairAdd]; split_ifs <;>
    constructor <;> intros <;> subst_vars <;>
      try grind
  · rename_i eq1 eq2; simp at *;
    constructor <;> ext <;> grind
  · rename_i eq1 eq2; cases eq2;
    subst_vars; simp

@[simp]
lemma pairAdd_lt_left_preserved : ∀ r s t : Rank, 0 < s.2 → t.1 ≤ s.1 → (r < s ↔ r * t < s * t) := by
  intro r s t A B; simp [rank_lt_rank_iff]; constructor
  · rintro (A | ⟨A1,A2⟩)
    · rw [rank_mul_def]; rw [rank_mul_def]
      simp [pairAdd]; split_ifs <;> try grind
    · by_cases D: t.1 < s.1 <;>
      rw [rank_mul_def] <;> rw [rank_mul_def] <;>
      simp [pairAdd] <;> split_ifs <;> grind
  · rw [rank_mul_def]; rw [rank_mul_def];
    simp [pairAdd]; split_ifs <;> intros <;>  try grind


@[simp]
lemma pairAdd_lt_right_preserved : ∀ r s t : Rank, 0 < s.2 → t.1 ≤ s.1 → (r < s ↔ t * r < t * s) := by
  intro r s t; simp [mul_comm]; apply pairAdd_lt_left_preserved

def goodRank (r : Rank) : Prop := r.1 = 0 ∧ r.2 = 0 ∨ r.1 > 0 ∧ r.2 > 0

@[simp]
lemma goodRank_pairAdd : ∀ r s, goodRank r → goodRank s → goodRank (r * s) := by
  intro r s; rw [rank_mul_def];
  simp [goodRank, pairAdd]; split_ifs <;> grind

@[simp]
lemma pairAdd_goodRank : ∀ r s, goodRank (r * s) → goodRank r ∨ goodRank s := by
  intro r s; rw [rank_mul_def];
  simp [goodRank, pairAdd]; split_ifs <;> grind

@[simp]
lemma pairAdd_left_monotone_strict : ∀ r r1 r2 : Rank,
  goodRank r2 → r.1 ≤ r2.1 → (r1 < r2 ↔ r1 * r < r2 * r) := by
  rintro ⟨d,w⟩ ⟨d1,w1⟩ ⟨d2,w2⟩ (⟨g1,g2⟩ | ⟨g1,g2⟩) f <;>
    rw [rank_mul_def] <;> rw [rank_mul_def] <;>
    simp [pairAdd] at * <;> split_ifs <;>
    simp [rank_lt_rank_iff] <;> try grind


@[simp]
lemma pairAdd_right_monotone_strict : ∀ r r1 r2 : Rank,
  goodRank r2 → r.1 ≤ r2.1 → (r1 < r2 ↔ r * r1 < r * r2) := by
  intro r r1 r2; rw [mul_comm]; nth_rewrite 2 [mul_comm];
  apply pairAdd_left_monotone_strict

end Rank
