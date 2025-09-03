import Mathlib.Tactic
-- From: https://cs.ioc.ee/ewscs/2009/dybjer/mainPalmse-revised.pdf

inductive Exp (α : Type)
| app : Exp α → Exp α → Exp α
| id  : Exp α
| elem : α → Exp α


-- Didn't declare the Setoid instance for this yet
inductive convr : (Exp α) → (Exp α) → Prop
| assoc {e e' e'' : Exp α} : convr ((e.app e').app e'') (e.app (e'.app e''))
| id_left {e  : Exp α}     : convr ((Exp.id).app e) (e)
| id_right {e : Exp α}     : convr (e.app Exp.id) (e)
| refl     {e : Exp α}     : convr (e) (e)
| sym      {e e' : Exp α}  : convr (e) (e') → convr (e') (e)
| trans {e e' e'' : Exp α} : convr (e) (e') → convr (e') (e'') → convr (e) (e'')
| app {a b c d : Exp α}    : convr (a) (b) → convr (c) (d) → convr (a.app c) (b.app d)



def eval : (Exp α) → (Exp α → Exp α)
  | Exp.app a b => (λ e => eval a (eval b e))
  | Exp.id      => id
  | Exp.elem x  => (λ e => (Exp.elem x).app e)

-- ∀ b, a.app b ~ [[a]]b
lemma eval_lemma1 (a : Exp α) : ∀ b, convr (a.app b) ((eval a) b) :=
by
  induction a
  case app c d c_ih d_ih =>
    intro b
    specialize d_ih b
    specialize c_ih (eval d b)
    -- convr-rewriting here
    have h0 : convr ((c.app d).app b) (c.app (d.app b)) := convr.assoc
    refine (convr.trans h0 ?_)
    clear h0
    have h0 : convr (c.app (d.app b)) (c.app (eval d b)) := convr.app (convr.refl) (d_ih)
    refine (convr.trans h0 ?_)
    clear h0
    exact c_ih

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
    rw [cd_ih]
    rw [ab_ih]


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
    -- convr-rewriting here
    have h1 : convr (e) (e.app Exp.id) := (convr.sym convr.id_right)
    refine (convr.trans h1 ?_)
    clear h1
    have h1 : convr (e.app Exp.id) ((eval e) Exp.id) := eval_lemma1 e Exp.id
    refine (convr.trans h1 ?_)
    clear h1
    rewrite [h0]
    clear h0
    have h0 : convr ((eval e') Exp.id) (e'.app Exp.id) := convr.sym (eval_lemma1 e' Exp.id)
    refine (convr.trans h0 ?_)
    clear h0
    exact convr.id_right

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
  have h0 : convr (zero.app zero)  zero := convr.id_left
  have h1 : convr ((zero.app zero).app three) (zero.app three) := convr.app h0 convr.refl
-- ((1, 2), ((0, 0), 3)) ~ ((1, 2), (0, 3))
  have h2 : convr ((one.app two).app ((zero.app zero).app three))
                  ((one.app two).app (zero.app three)) := convr.app convr.refl h1
-- ((1, 2), (0, 3)) ~ (1, (2, (0, 3))
  have h3 : convr ((one.app two).app (zero.app three))
                  (one.app (two.app (zero.app three))) := convr.assoc
  have h4 : convr zero (zero.app zero) := convr.sym h0
-- (1, (2, (0, 3)) ~ (0, (1, (2, (0, 3)))
  have h5 : convr (one.app (two.app (zero.app three)))
                  (zero.app (one.app (two.app (zero.app three)))) := convr.sym convr.id_left
-- (0, (1, (2, (0, 3))) ~ ((0, 0), (1, (2, (0, 3)))
  have h6 : convr (zero.app (one.app (two.app (zero.app three))))
                  ((zero.app zero).app (one.app (two.app (zero.app three)))) := convr.app h4 convr.refl
  clear h0 h1 h4
  apply convr.trans h2
  apply convr.trans h3
  apply convr.trans h5
  apply convr.trans h6
  exact convr.refl
