import Tactic.setoidRw

-- From: https://cs.ioc.ee/ewscs/2009/dybjer/mainPalmse-revised.pdf

inductive Ty : Type
| Nat : Ty
| arrow : Ty → Ty → Ty
open Ty
infixr : 100 " ⇒' " => arrow

inductive Exp : Ty → Type
| K {a b : Ty}     :  Exp (a ⇒' b ⇒' a)
| S {a b c : Ty}   :  Exp ((a ⇒' b ⇒' c) ⇒' (a ⇒' b) ⇒' (a ⇒' c))
| App {a b : Ty}   :  Exp (a ⇒' b) → Exp a → Exp b
| zero             :  Exp Nat
| succ             :  Exp (Nat ⇒' Nat)
| recN {a : Ty}    :  Exp (a ⇒' (Nat ⇒' a ⇒' a) ⇒' Nat ⇒' a)
open Exp
infixl : 100 " ⬝ " => App

inductive convr : Π {α : Ty}, (Exp α) → (Exp α) → Prop
| refl {α : Ty}{e : Exp α}
        : convr (e) (e)
| sym   {α : Ty}{e e' : Exp α}
        : convr (e) (e') → convr (e') (e)
| trans {α : Ty}{e e' e'' : Exp α}
        : convr (e) (e') → convr (e') (e'') → convr (e) (e'')
| K     {α β : Ty}{x : Exp α} {y : Exp β}
        : convr (K ⬝ x ⬝ y) (x)
| S     {α β γ: Ty}{x : Exp (γ ⇒' β ⇒' α)} {y : Exp (γ ⇒' β)} {z : Exp γ}
        : convr (S ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
| app   {α β : Ty} {a b : Exp (β ⇒' α)} {c d : Exp β}
        : convr (a) (b) → convr (c) (d) → convr (a ⬝ c) (b ⬝ d)
| recN_zero {α : Ty} {e : Exp α} {f : Exp (Nat ⇒' α ⇒' α)}
        : convr (recN ⬝ e ⬝ f ⬝ zero) (e)
| recN_succ {α : Ty} {n : Exp Nat} {e : Exp α} {f : Exp (Nat ⇒' α ⇒' α)}
        : convr (recN ⬝ e ⬝ f ⬝ (succ ⬝ n)) (f ⬝ n ⬝ (recN ⬝ e ⬝ f ⬝ n))

-- Setoid instance here:
instance convr_Setoid : Setoid (Exp α) :=
  { r := convr
    iseqv :=
      { refl := λ _ => convr.refl
        symm := convr.sym
        trans := convr.trans
      }
  }


def Ty_inter : Ty → Type
| Ty.Nat => ℕ

| arrow a b => Exp (a ⇒' b) × (Ty_inter a → Ty_inter b)



def numeral : ℕ → Exp Ty.Nat
| 0 => zero

| n+1 => succ ⬝ (numeral n)


def reify (α : Ty) (e : Ty_inter α) : Exp α :=
  match α,e with
  | Ty.Nat, e            => numeral e

  | Ty.arrow α β, (c, f) => c


def appsem {a b : Ty} (t : Ty_inter (a ⇒' b)) (e' : Ty_inter a) : Ty_inter b := (t.snd e')


def Exp_inter (a : Ty) : (e : Exp a) → Ty_inter a
| @K a b => (K,
            (λ p ↦ (K ⬝ (reify a p),
            (λ _ ↦ p))))
| @S a b c => (S,
              (λ x ↦ (S ⬝ (reify (a⇒'b⇒'c) x),
              (λ y ↦ (S ⬝ (reify (a⇒'b⇒'c) x) ⬝ (reify (a⇒'b) y),
              (λ z ↦ appsem (appsem x z) (appsem y z)))))))
| @App a b f e  => appsem (Exp_inter (a ⇒' b) f) (Exp_inter a e)
| zero          => (0 : ℕ)
| succ          => (succ,
                   (λ n : ℕ ↦ n+1) )
| @recN a       => (recN,
                   (λ p ↦ (recN ⬝ (reify a p),
                   (λ q ↦ (recN ⬝ (reify a p) ⬝ (reify (Nat⇒'a⇒'a) q),
                   (λ n0 ↦ Nat.rec p (λ n r ↦ appsem (appsem q n) r) n0))))))


def nbe (a : Ty) (e : Exp a) : (Exp a) := reify a (Exp_inter a e)


-- e ~ e'  implies [[e]]a = [[e']]a
lemma convr_lemma1 {a : Ty} {e e' : Exp a} : convr e e' → ((Exp_inter a e) = (Exp_inter a e')) :=
by
  intro h
  induction h
  any_goals aesop
  case app α β a b c d a_r_b c_r_d ab_ih cd_ih =>
    unfold Exp_inter
    rw [ab_ih, cd_ih]

-- e ~ e'  implies nbe a e = nbe a e'
lemma soundness {a : Ty} {e e' : Exp a} : convr e e' → nbe a e = nbe a e' :=
by
  unfold nbe
  intro h1
  have h2 : Exp_inter a e = Exp_inter a e' := convr_lemma1 h1
  rw [h2]


-- Tait-reducibility relation
def R : (a : Ty) → (e : Exp a) → Prop
| Ty.Nat, e       => convr e (nbe Ty.Nat e)

| Ty.arrow α β, e => convr e (nbe (α ⇒' β) e)  ∧  ∀ e', R α e' → R β (App e e')

-- R a e  implies  e ~ nbe a e
lemma R_convr_nbe (h : R a e)  : convr e (nbe a e) :=
  by
  cases a
  all_goals (unfold R at h); aesop

-- e ~ e' implies  R α e ↔ R α e'
lemma convr_R_iff : ∀ e e', convr e e' → (R α e ↔ R α e') :=
  by
  induction α
  · unfold R
    intro a b a_r_b
    apply Iff.intro
    · intro a_r_nbe
      -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧":
      have soundness' := @soundness
      translate `convr `convr_Setoid
      hide soundness'
      -- b ~ a ~ nbe a = nbe b
      -- "rewrite [← a_r_b, a_r_nbe, soundness a_r_b]"
      rw [← a_r_b, a_r_nbe, soundness' a_r_b]
    · intro b_r_nbe
      -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧":
      have soundness' := @soundness
      translate `convr `convr_Setoid
      hide soundness'
      -- a ~ b ~ nbe b = nbe a
      -- "rewrite [a_r_b, b_r_nbe, ← soundness a_r_b]"
      rw [a_r_b, b_r_nbe, ← soundness' a_r_b]

  · rename_i α β αIH βIH; clear αIH
    intros f1 f2 f1_r_f2
    apply Iff.intro
    · intro R_f1
      apply And.intro
      · have f1_r_nbe := R_convr_nbe R_f1; clear R_f1
        -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧":
        have soundness' := @soundness
        translate `convr `convr_Setoid
        hide soundness'
        -- f2 ~ f1 ~ nbe f1 = nbe f2
        -- "rewrite [← f1_r_f2, f1_r_nbe, soundness f1_r_f2]"
        rw [← f1_r_f2, f1_r_nbe, soundness' f1_r_f2]
      · intro e' Re'
        rewrite [← βIH (f1 ⬝ e') (f2 ⬝ e') (f1_r_f2.app convr.refl)]
        rcases R_f1 with ⟨_, h0⟩
        exact h0 e' Re'

    · intro R_f2
      apply And.intro
      · have f2_r_nbe := R_convr_nbe R_f2; clear R_f2
        -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧":
        have soundness' := @soundness
        translate `convr `convr_Setoid
        hide soundness'
        -- f1 ~ f2 ~ nbe f2 = nbe f1
        -- "rewrite [f1_r_f2, f2_r_nbe, ← soundness f1_r_f2]"
        rw [f1_r_f2, f2_r_nbe, ← soundness' f1_r_f2]
      · intro e' Re'
        rewrite [βIH (f1 ⬝ e') (f2 ⬝ e') (f1_r_f2.app convr.refl)]
        rcases R_f2 with ⟨_, h0⟩
        exact h0 e' Re'


lemma R_numeral : R Ty.Nat (numeral n) :=
  by
  unfold R
  induction n
  case zero => exact convr.refl

  case succ n' IH =>
    unfold numeral
    have eq : nbe Ty.Nat (succ ⬝ numeral n') = succ ⬝ (nbe Ty.Nat $ numeral n') := rfl
    -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧":
    have convr.app' := @convr.app
    translate `convr `convr_Setoid
    hide convr.app'
    -- succ ⬝ numeral n' ~ succ ⬝ nbe (numeral n') = nbe (succ ⬝ numeral n')
    -- "rewrite [IH, eq]"
    rw [convr.app' rfl IH, eq]

-- for all e, R a e
lemma all_R {e : Exp a} : R a e :=
  by
  induction e
  all_goals clear a
  case K a b =>
    apply And.intro
    · exact convr.refl
    · intro e' Re'
      apply And.intro
      · have e'_r_nbe := R_convr_nbe Re'; clear Re'
        have eq : nbe (b ⇒' a) (K ⬝ e') = K ⬝ nbe a e' := rfl
        -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧"
        have convr.app' := @convr.app
        translate `convr `convr_Setoid
        hide convr.app'
        -- K ⬝ e' ~ K ⬝ nbe e' = nbe (K ⬝ e')
        -- "rewrite [e'_r_nbe, eq]"
        rw [convr.app' rfl e'_r_nbe, eq]

      · intro e'' Re''; clear Re''
        --convr-rewriting here
        -- R (K ⬝ e' ⬝ e'') = R e'
        -- "rewrite [convr.K]"
        rewrite [convr_R_iff (K ⬝ e' ⬝ e'') e' convr.K]
        exact Re'

  case S a b c =>
    apply And.intro
    · exact convr.refl
    · intro x Rx
      apply And.intro
      · have x_r_nbe := R_convr_nbe Rx; clear Rx
        have eq : nbe ((a ⇒' b) ⇒' a ⇒' c) (S ⬝ x) = S ⬝ nbe (a ⇒' b ⇒' c)  x := rfl
        -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧"
        have convr.app' := @convr.app
        translate `convr `convr_Setoid
        hide convr.app'
        -- S ⬝ x ~ S ⬝ nbe x = nbe (S ⬝ x)
        -- "rewrite [x_r_nbe, eq]"
        rw [convr.app' rfl x_r_nbe, eq]
      · intro y Ry
        apply And.intro
        · have x_r_nbe := R_convr_nbe Rx; clear Rx; have y_r_nbe := R_convr_nbe Ry; clear Ry
          have eq : nbe (a ⇒' c) (S ⬝ x ⬝ y) = S ⬝ nbe (a ⇒' b ⇒' c) x ⬝ nbe (a ⇒' b) y := rfl
          -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧"
          have convr.app' := @convr.app
          translate `convr `convr_Setoid
          hide convr.app'
          -- S ⬝ x ⬝ y ~ S ⬝ nbe x ⬝ y ~ S ⬝ nbe x ⬝ nbe y = nbe (S ⬝ x ⬝ y)
          -- "rewrite [x_r_nbe, y_r_nbe, eq]"
          rw [convr.app' (convr.app' rfl x_r_nbe) rfl, convr.app' rfl y_r_nbe, eq]
        · intro z Rz
          -- convr-rewriting here
          -- "rewrite [convr.S]"
          rewrite [convr_R_iff (S ⬝ x ⬝ y ⬝ z) _ convr.S]
          rcases Rx with ⟨left, Rxz⟩; clear left; specialize Rxz z Rz
          rcases Ry with ⟨left, Ryz⟩; clear left; specialize Ryz z Rz
          rcases Rxz with ⟨left, Rxzyz⟩; clear left; specialize Rxzyz (y ⬝ z) Ryz
          exact Rxzyz

  case App α β f x Rf Rx =>
    rcases Rf with ⟨_, h0⟩
    exact h0 x Rx

  case zero =>
    exact convr.refl

  case succ =>
    apply And.intro
    · exact convr.refl
    · intro x Rx
      unfold R at *; rename' Rx => x_r_nbe
      have eq : nbe Ty.Nat (succ ⬝ x) = succ ⬝ (nbe Ty.Nat x) := rfl
      -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧"
      have convr.app' := @convr.app
      translate `convr `convr_Setoid
      hide convr.app'
      -- succ ⬝ x ~ succ ⬝ nbe x = nbe (succ ⬝ x)
      -- "rewrite [x_r_nbe, eq]"
      rw [convr.app' rfl x_r_nbe, eq]

  case recN α =>
    apply And.intro
    · exact convr.refl
    · intro e' Re'
      apply And.intro
      · have e'_r_nbe := R_convr_nbe Re'; clear Re'
        have eq : nbe ((Ty.Nat ⇒' α ⇒' α) ⇒' Ty.Nat ⇒' α) (recN ⬝ e') = recN ⬝ nbe α e' := rfl
        -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧"
        have convr.app' := @convr.app
        translate `convr `convr_Setoid
        hide convr.app'
        -- recN ⬝ e' ~ recN ⬝ nbe e' = nbe (recN ⬝ e')
        -- "rewrite [e'_r_nbe, eq]"
        rw [convr.app' rfl e'_r_nbe, eq]
      · intro e'' Re''
        apply And.intro
        · have e'_r_nbe := R_convr_nbe Re'; clear Re'; have e''_r_nbe := R_convr_nbe Re''; clear Re''
          have eq : nbe (Ty.Nat ⇒' α) (recN ⬝ e' ⬝ e'') = recN ⬝ nbe α e' ⬝ nbe (Ty.Nat ⇒' α ⇒' α) e'' := rfl
          -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧"
          have convr.app' := @convr.app
          translate `convr `convr_Setoid
          hide convr.app'
          -- recN ⬝ e' ⬝ e'' ~ recN ⬝ nbe e' ⬝ e'' ~ recN ⬝ nbe e' ⬝ nbe e'' = nbe (recN ⬝ e' ⬝ e'')
          -- "rewrite [e'_r_nbe, e''_r_nbe, eq]"
          rw [convr.app' (convr.app' rfl e'_r_nbe) rfl, convr.app' rfl e''_r_nbe, eq]
        · intro n Rn
          have n_r_nbe := Rn; unfold R at n_r_nbe
          -- "rewrite [n_r_nbe]"
          rewrite [convr_R_iff (recN ⬝ e' ⬝ e'' ⬝ n) (recN ⬝ e' ⬝ e'' ⬝ (nbe Ty.Nat n)) (convr.refl.app n_r_nbe)]
          unfold nbe; simp [reify]
          induction ((Exp_inter Ty.Nat n))
          · unfold numeral
            -- "rewrite [convr.recN_zero]"
            exact (convr_R_iff (recN ⬝ e' ⬝ e'' ⬝ zero) e' convr.recN_zero).mpr Re'
          · rename_i n' IH
            apply (convr_R_iff (.recN ⬝ e' ⬝ e'' ⬝ (.succ ⬝ numeral n')) (e'' ⬝ (numeral n') ⬝ (.recN ⬝ e' ⬝ e'' ⬝ (numeral n'))) convr.recN_succ).mpr
            have R_numeral_n' : R Ty.Nat (numeral n') := by exact R_numeral
            rcases Re'' with ⟨left, h0⟩; clear left
            specialize h0 (numeral n') R_numeral_n'
            rcases h0 with ⟨left, h0⟩; clear left
            exact h0 (.recN ⬝ e' ⬝ e'' ⬝ numeral n') IH


-- e ~ nbe a e
lemma convr_nbe {e : Exp a} : convr e (nbe a e) := R_convr_nbe all_R

-- nbe a e = nbe a e' implies e ~ e'
lemma completeness : nbe a e = nbe a e' → convr e e' :=
  by
  intro eq
  -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧"
  have convr_nbe' := @convr_nbe
  translate `convr `convr_Setoid
  hide convr_nbe'
  -- e ~ nbe e = nbe e' ~ e'
  -- "rewrite [convr_nbe, eq, ← convr_nbe]"
  rw [convr_nbe', eq, ← convr_nbe']

-- e ~ e' ↔ nbe a e = nbe a e'
lemma correctness {e e' : Exp a} : convr e e' ↔ nbe a e = nbe a e' := ⟨soundness, completeness⟩
