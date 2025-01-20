import Mathlib.Tactic
/-
 a ≈ b, b ≈ c, ⬝ ≈ ⬝ → f ⬝ ≈ f ⬝
 ⊢ fa ≈ fc
-/

example {f : α → β} {sα : Setoid α} {sβ : Setoid β}
        (h1 : a ≈ b) (h2 : b ≈ c) (cong : ∀ a b, a ≈ b → f a ≈ f b)
        : f a ≈ f c :=
  by
  replace h1 := Quotient.sound h1
  replace h2 := Quotient.sound h2
  replace cong := λ a b heq => Quotient.sound $ cong a b (Quotient.exact heq)
  apply Quotient.exact
  apply cong
  rw [h1, h2]


example {x1 : α} {sα : Setoid α}
    (h1 : x1 ≈ x2)
    (h2 : x3 ≈ x2)
    (h3 : x6 ≈ x3)
    (h4 : x5 ≈ x4)
    (h5 : x5 ≈ x7)
    (h6 : x6 ≈ x5)
      : x4 ≈ x1 :=
  by
  -- "rw [← h4, ← h6, h3, h2, h1]"
  --replace h1 := Quotient.sound h1; replace h2 := Quotient.sound h2; replace h3 := Quotient.sound h3
  --replace h4 := Quotient.sound h4; replace h5 := Quotient.sound h5; replace h6 := Quotient.sound h6
  --apply Quotient.exact
  --rw [← h4, ← h6, h3, h2, h1]

  -- "rw [← h4]" v1:
  --replace h4 := Quotient.sound h4; apply Quotient.exact
  --rw [← h4]
  --replace h4 := Quotient.exact h4; apply Quotient.sound

  -- "rw [← h4]" v2:
  -- refine Setoid.trans (Setoid.symm h4) ?_
  sorry

#check Eq.mpr

example {x1 x2 : ℕ} {f : ℕ →  ℕ →  ℕ  →  ℕ  →  ℕ  → ℕ}
    (h1 : x1 = x2)
    (h2 : f = g)
    : f x1 x2 = g x2 x1 :=
  by
  show_term rewrite [h1, h2]; rfl


example {x1 x2 : ℕ} {f : ℕ →  ℕ →  ℕ  →  ℕ  →  ℕ  → ℕ}
    (h1 : x1 = x2)
    (h2 : f = g)
    : ∀ y, f x1 y = g x2 y :=
  by
  --rewrite [h1, h2]; exact fun y => rfl
  exact
    Eq.mpr (congrArg (fun _a => ∀ (y : ℕ), f _a y = g x2 y) h1)
      (Eq.mpr (congrArg (fun _a => ∀ (y : ℕ), _a x2 y = g x2 y) h2) fun y => rfl)









-- From here:
-- https://jfr.unibo.it/article/view/1574/1077
namespace Coq_examples

abbrev relation (α : Type _) := α → α → Prop

variable (Set : Type)
variable (eqset : relation Set)
variable (eqset_equiv : Equivalence eqset)

variable (empty : Set)
variable (union : Set → Set → Set)
variable (union_empty : ∀s, eqset (union s empty) s)
variable (union_idem : ∀s, eqset (union s s) s)
variable (union_compat : ∀ x x', eqset x x' → ∀ y y', eqset y y' → eqset (union x x') (union y y'))

example : ∀ s, eqset (union (union s empty) s) s :=
  by
  intro s
  -- "rewrite" not implemented for equivalence relations
  --rewrite [union_empty s, union_idem s]
  apply eqset_equiv.trans ?_ ?_
  exact union s s
  · apply union_compat
    · exact union_empty s
    · exact eqset_equiv.refl s
  · exact union_idem s

example : ∀P Q : Prop, (P ↔ Q) → (Q→P) ∧ (Q→P) :=
  by
  intro P Q H
  rewrite [H]
  exact ⟨id, id⟩




end Coq_examples


-- Proof of Confluence for STLC here (Proof uses alot of β-rewriting)?


-- Examples from https://github.com/fblanqui/color/tree/master
-- here?


-- Examples that give alot of side-conditions ?


-- All examples verbatim from https://jfr.unibo.it/article/view/1574/1077 ?


-- Any specific ugly rewriting-examples you know of?

-- Looks like Sébastien Michelland has already implemented the entirety of the "Generalized Rewriting" Coq article
-- in Lean4 here: https://github.com/lephe/lean4-rewriting/tree/main
