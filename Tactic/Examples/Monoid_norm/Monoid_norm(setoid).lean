import Tactic.setoidRw

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
instance convr_Setoid : Setoid (Exp α) :=
  { r := convr
    iseqv :=
      { refl := λ _ => convr.refl
        symm := convr.sym
        trans := convr.trans
      }
  }


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
    have convr.assoc' := @convr.assoc
    have convr.app'   := @convr.app
    translate convr convr_Setoid
    hide convr.assoc'
    hide convr.app'

    --revert c_ih d_ih  b d c α
    --generalize eq : @Exp.app = Exp.app_aux

    -- (c ⬝ d) ⬝ b ~ c ⬝ (d ⬝ b) ~ c ⬝ (eval d b) ~ eval c (eval d b)
    -- "rewrite [convr.assoc, d_ih, c_ih]"
    rw [convr.assoc', convr.app' rfl d_ih, c_ih]

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
    have convr.id_right' := @convr.id_right
    have eval_lemma1'    := @eval_lemma1
    translate convr convr_Setoid
    hide convr.id_right'
    hide eval_lemma1'
    -- e ~ e ⬝ id ~ nbe e = nbe e' ~ e' ⬝ id ~ e'
    -- "rewrite [← convr.id_right, eval_lemma1 e Exp.id, h0, ← eval_lemma1 e' Exp.id, convr.id_right]"
    rw [← convr.id_right', eval_lemma1' e Exp.id, h0, ← eval_lemma1' e' Exp.id, convr.id_right']

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
  have convr.id_left' := @convr.id_left
  have convr.assoc'   := @convr.assoc
  have convr.app'     := @convr.app
  translate convr convr_Setoid
  hide convr.id_left'
  hide convr.assoc'
  hide convr.app'
  -- "rw (config := {occs := .pos [1]}) [@convr.id_left zero]"
  unfold zero
  rewrite [convr.app' rfl (convr.app' (@convr.id_left' ℕ Exp.id) rfl)]
  -- "rewrite [convr.assoc]"
  rewrite [convr.assoc']
  -- "rewrite [← convr.id_left]"
  rewrite [← convr.id_left']
  --"rw (config := {occs := .pos [1]}) [← @convr.id_left' ℕ zero]"
  rw [convr.app' (convr.id_left').symm rfl]

-- ∀ x y, ((x, (0,0)), y) ~ (x, (y, (0,0)))
example : ∀ x y : Exp ℕ, convr ((x.app (zero.app zero)).app y) (x.app (y.app (zero.app zero))) :=
  by
  -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧"
  have convr.id_left' := @convr.id_left
  have convr.id_right':= @convr.id_right
  have convr.assoc'   := @convr.assoc
  have convr.app'     := @convr.app
  translate convr convr_Setoid
  hide convr.id_left'
  hide convr.id_right'
  hide convr.assoc'
  hide convr.app'

  unfold zero
  -- ((x, (0,0)), y) ~ ((x, 0), y)
  -- "rewrite [@ExpClass.id_left ℕ Exp.id]"
  simp_rw [convr.app' rfl (convr.app' rfl (@convr.id_left' ℕ Exp.id))]
  -- ((x, 0), y) ~ (x,y)
  -- "rewrite [ExpClass.id_right]"
  simp_rw [convr.app' rfl (convr.id_right')]
  -- rhs:  (x, (y, (0,0))) ~ (x, (y,0))
  -- "rewrite [ExpClass.id_right]"
  simp_rw [convr.app' (convr.app' rfl (convr.id_right')) rfl]
  -- rhs:  (x, (y,0)) ~ (x,y)
  -- "rewrite [ExpClass.id_right]"
  simp_rw [convr.app' (convr.id_right') rfl]
  aesop
