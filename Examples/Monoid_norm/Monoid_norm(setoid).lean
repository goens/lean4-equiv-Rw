import Mathlib.Tactic
-- From: https://cs.ioc.ee/ewscs/2009/dybjer/mainPalmse-revised.pdf

inductive Exp (α : Type)
| app : Exp α → Exp α → Exp α
| id  : Exp α
| elem : α → Exp α


inductive convr : (Exp α) → (Exp α) → Prop
| assoc {e e' e'' : Exp α} : convr ((e.app e').app e'') (e.app (e'.app e''))
| id_left {e  : Exp α}     : convr ((Exp.id).app e) (e)
| id_right {e : Exp α}     : convr (e.app Exp.id) (e)
| refl     {e : Exp α}     : convr (e) (e)
| sym      {e e' : Exp α}  : convr (e) (e') → convr (e') (e)
| trans {e e' e'' : Exp α} : convr (e) (e') → convr (e') (e'') → convr (e) (e'')
| app {a b c d : Exp α}    : convr (a) (b) → convr (c) (d) → convr (a.app c) (b.app d)





-- Setoid instance here:
instance ExpClass.Setoid : Setoid (Exp α) :=
  { r := convr
    iseqv :=
      { refl := λ _ => convr.refl
        symm := convr.sym
        trans := convr.trans
      }
  }

def ExpClass α := Quotient (@ExpClass.Setoid α)

lemma ExpClass.def {e1 e2 : Exp α} :
  convr e1 e2 ↔ (⟦e1⟧ : ExpClass α) = ⟦e2⟧ :=
  by
  apply Iff.intro
  exact fun a => Quotient.sound a
  exact fun a => Quotient.exact a

lemma ExpClass.assoc {e e' e'' : Exp α} :
  (⟦(e.app e').app e''⟧ : ExpClass α) = ⟦e.app (e'.app e'')⟧
  := ExpClass.def.mp convr.assoc

lemma ExpClass.id_left {e  : Exp α} : (⟦(Exp.id).app e⟧ : ExpClass α) = ⟦e⟧
  := ExpClass.def.mp convr.id_left

lemma ExpClass.id_right {e  : Exp α} : (⟦e.app Exp.id⟧ : ExpClass α) = ⟦e⟧
  := ExpClass.def.mp convr.id_right

-- In Sozeau's notation:
-- Proper ( ≈ ++> ≈ ++> ≈ ) app
lemma ExpClass.app {a b c d : Exp α} : (⟦a⟧ : ExpClass α) = ⟦b⟧ → (⟦c⟧ : ExpClass α) = ⟦d⟧ →  (⟦a.app c⟧ : ExpClass α) = ⟦b.app d⟧
  :=
  by
  rewrite [← ExpClass.def, ← ExpClass.def, ← ExpClass.def]
  exact fun a_1 a_2 => convr.app a_1 a_2

lemma ExpClass.app_arg {a c d : Exp α} : (⟦c⟧ : ExpClass α) = ⟦d⟧ →  (⟦a.app c⟧ : ExpClass α) = ⟦a.app d⟧
  := fun a_1 => ExpClass.app rfl a_1

lemma ExpClass.app_fun {a b c : Exp α} : (⟦a⟧ : ExpClass α) = ⟦b⟧ →  (⟦a.app c⟧ : ExpClass α) = ⟦b.app c⟧
  := fun a_1 => ExpClass.app a_1 rfl




def eval : (Exp α) → (Exp α → Exp α)
  | Exp.app a b => (λ e => eval a (eval b e))
  | Exp.id      => id
  | Exp.elem x  => (λ e => (Exp.elem x).app e)


-- ∀ b, a.app b ~ [[a]]b
lemma eval_lemma1 (a : Exp α) : ∀ b, convr (a.app b) ((eval a) b) :=
by
  induction a
  case app c d c_ih d_ih =>
    unfold eval
    intro b
    specialize d_ih b
    specialize c_ih (eval d b)
    -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧"
    (replace c_ih := ExpClass.def.mp c_ih); replace d_ih := ExpClass.def.mp d_ih
    apply ExpClass.def.mpr
    -- (c ⬝ d) ⬝ b ~ c ⬝ (d ⬝ b) ~ c ⬝ (eval d b) ~ eval c (eval d b)
    -- "rewrite [convr.assoc, d_ih, c_ih]"
    rw [ExpClass.assoc, ExpClass.app_arg d_ih, c_ih]

  case id =>
    intro b
    exact convr.id_left

  case elem =>
    intro b
    exact convr.refl

-- a ~ b  → ∀ c, [[a]]c = [[b]]c
lemma eval_lemma2 {a b : Exp α} (h : convr a b) : ∀ c : Exp α, (eval a) c = (eval b) c :=
by
  induction h

  any_goals
    intros; aesop

  case app a b c d _ _ ab_ih cd_ih =>
    clear * - ab_ih cd_ih
    intro e
    specialize cd_ih e
    specialize ab_ih ((eval d) e)
    simp only [eval]
    rw [cd_ih, ab_ih]

def reify (f : Exp α → Exp α) : (Exp α) := f Exp.id

def nbe (e : Exp α) : Exp α := reify (eval e)

-- Shows decidability of e ~ e'
theorem correctness (e e' : Exp α) : (convr (e) (e')) ↔ (nbe e = nbe e') :=
by
  apply Iff.intro
  · intro h
    induction h
    any_goals
      aesop
    case mp.app a b c d a_r_b c_r_d _ _ =>
      clear * - a_r_b c_r_d
      apply eval_lemma2 ?_ Exp.id
      -- convr-rewriting here
      exact convr.app a_r_b c_r_d

  · unfold nbe reify
    intro h0
    -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧"
    apply ExpClass.def.mpr
    -- e ~ e ⬝ id ~ nbe e = nbe e' ~ e' ⬝ id ~ e'
    -- "rewrite [← convr.id_right, eval_lemma1 e Exp.id, h0, ← eval_lemma1 e' Exp.id, convr.id_right]"
    rw [← ExpClass.id_right, ExpClass.def.mp $ eval_lemma1 e Exp.id, h0,
        ← ExpClass.def.mp $ eval_lemma1 e' Exp.id, ExpClass.id_right]

-- Python code to quickly generate examples:
/-
import random

def generate_tree(L):
    # base case
    if len(L) == 1:
        return L[0]
    split = random.randint(1, len(L)-1)
    left = L[:split]
    right = L[split:]
    # recursion
    return (generate_tree(left), generate_tree(right))


for i in range(2):
  rep0 = [0] * random.randint(0,2)
  rep1 = [0] * random.randint(0,2)
  rep2 = [0] * random.randint(0,2)
  rep3 = [0] * random.randint(0,2)
  list = rep0 + [1] + rep1 + [2] + rep2 + [3] + rep3
  print(generate_tree(list))
-/

def zero := (Exp.id : Exp ℕ)
def one  := Exp.elem 1
def two  := Exp.elem 2
def three := Exp.elem 3

-- ((1, 2), ((0, 0), 3)) ~ ((0, 0), (1, (2, (0, 3))))
#reduce nbe ( (one.app two).app  ((zero.app zero).app three) )
#reduce nbe ( (zero.app zero).app (one.app (two.app (zero.app three))))

example : convr
          ( (one.app two).app  ((zero.app zero).app three) )
          ( (zero.app zero).app (one.app (two.app (zero.app three)))) :=
  by
  -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧"
  apply ExpClass.def.mpr

  -- "rw (config := {occs := .pos [1]}) [@convr.id_left zero]"
  unfold zero
  rewrite [ExpClass.app_arg $ ExpClass.app_fun $ @ExpClass.id_left ℕ Exp.id]
  -- "rewrite [convr.assoc]"
  rewrite [ExpClass.assoc]
  -- "rewrite [← convr.id_left]"
  rewrite [← ExpClass.id_left]
  -- "rw (config := {occs := .pos [1]}) [← @convr.id_left zero]"
  rw [ExpClass.app_fun (ExpClass.id_left).symm]

-- ∀ x y, ((x, (0,0)), y) ~ (x, (y, (0,0)))
example : ∀ x y : Exp ℕ, convr ((x.app (zero.app zero)).app y) (x.app (y.app (zero.app zero))) :=
  by
  -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧"
  simp_rw [ExpClass.def]
  unfold zero
  -- ((x, (0,0)), y) ~ ((x, 0), y)
  -- "rewrite [@ExpClass.id_left ℕ Exp.id]"
  simp_rw [ExpClass.app_fun $ ExpClass.app_arg $ @ExpClass.id_left ℕ Exp.id]
  -- ((x, 0), y) ~ (x,y)
  -- "rewrite [ExpClass.id_right]"
  simp_rw [ExpClass.app_fun $ ExpClass.id_right]
  -- rhs:  (x, (y, (0,0))) ~ (x, (y,0))
  -- "rewrite [ExpClass.id_right]"
  simp_rw [ExpClass.app_arg $ ExpClass.app_arg $ ExpClass.id_right]
  -- rhs:  (x, (y,0)) ~ (x,y)
  -- "rewrite [ExpClass.id_right]"
  simp_rw [ExpClass.app_arg $ ExpClass.id_right]
  aesop
