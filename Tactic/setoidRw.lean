import Lean
import Mathlib.Tactic

open Lean Elab Tactic Term Meta

--set_option pp.universes true

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

inductive convr : {α : Ty} → (Exp α) → (Exp α) → Prop
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

def ExpClass α := Quotient (@convr_Setoid α)

/-
lemma convr_eq :
  (@convr) = (λ α => λ (e1 e2 : Exp α) => ((⟦e1⟧ : ExpClass α) = ⟦e2⟧)) :=
  by
  show_term
    funext
    apply propext
    apply Iff.intro
    exact λ h => Quotient.sound h
    exact λ h => Quotient.exact h
-/

/-Prints out the current Environment.
-/
def printEnv : CoreM Unit := do
  let env ← getEnv
  for (name, info)
    in (env.constants).toList.take 150 do
        let type := info.type
        logInfo s!"{name} : {type}"
elab "printEnv" : tactic => do printEnv

/-Prints out the current Local-Context
-/
def printLocalCtxt : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let localCtxt ← getLCtx
    for localDecl in localCtxt do
        let expr := localDecl.toExpr
        let name := localDecl.userName
        let type := localDecl.type
        logInfo s!"{name} := {expr}"
        logInfo s!": {type}"
        logInfo " "
    logInfo " "
    logInfo s!"goal"
    logInfo s!": {←goal.getType}"
elab "printLocalCtxt" : tactic => do printLocalCtxt


/-
Our Grammar for Inductive setoids is:
  inductive R : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → (_ : X) → (_ : X) → Prop
    where
    · (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → (_ : X) → (_ : X) → Prop  is a telescope
    · X is our carrier-set

  instance R_Setoid : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Setoid X
                 := λ (x₁ : T₁) (x₂ : T₂) ⋯ (xₙ : Tₙ) => ⟨r := R, iseqv := ⋯⟩
-/
/-
grammar ⟨r := R, iseqv := ⋯⟩  := ⟨X⟩
-/


-- R : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → (_ : X) → (_ : X) → Prop
-- destruct R := ⟨[(x₁ : T₁), ⋯, (xₙ : Tₙ)], (_ : X) → (_ : X) → Prop⟩
def destructR (R : Name) : MetaM (Array Expr × Expr) := do
  let R := .const R []
  let RType := ← inferType R
  let n_plus_two := RType.getNumHeadForalls
  forallBoundedTelescope RType (some $ n_plus_two-2) fun xs X_X_Prop => do
    logInfo s!"{← mkForallFVars xs X_X_Prop}"
    return ⟨xs, X_X_Prop⟩
#eval destructR ``convr


-- R        : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → (_ : X) → (_ : X) → Prop
-- R_Setoid : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Setoid X

-- QuotientExpr R R_Setoid := (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Quotient X (R_Setoid x₁ ⋯ xₙ)
def QuotientExpr (R : Name) (R_Setoid : Name) : MetaM Expr := do
  let R_Setoid  := (Expr.const R_Setoid [])

  let R := .const R []
  let RType := ← inferType R
  let n_plus_two := RType.getNumHeadForalls
  forallBoundedTelescope RType (some $ n_plus_two-2) fun xs X_X_Prop => do
    let X := X_X_Prop.bindingDomain!
    let Quotient := (← mkAppOptM ``Quotient $ #[some X] ++ #[some $ mkAppN (R_Setoid) xs ])
    mkLambdaFVars xs Quotient
#eval do check $ ← QuotientExpr `convr `convr_Setoid
#eval do ppExpr $ ← QuotientExpr `convr `convr_Setoid
#eval QuotientExpr `convr `convr_Setoid
#check fun α => @Quotient (Exp α) (@convr_Setoid α)


-- R        : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → (_ : X) → (_ : X) → Prop
-- R_Setoid : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Setoid X

-- mkQuotientEq R R_Setoid := λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧
def mkQuotientEq (R : Name) (R_Setoid : Name) : MetaM Expr := do
  let R_Setoid  := (Expr.const R_Setoid [])


  let R := .const R []
  let RType := ← inferType R
  let n_plus_two := RType.getNumHeadForalls
  forallBoundedTelescope RType (some $ n_plus_two) fun xs_e1_e2 _Prop => do
    let xs := xs_e1_e2.pop.pop
    let e1 := xs_e1_e2.pop.toList.getLast!
    let e2 := xs_e1_e2.toList.getLast!
    let X := ← inferType e2
    let bb_e1_dd := (← mkAppOptM ``Quotient.mk $ #[some X] ++ #[some $ mkAppN (R_Setoid) xs, e1])
    let bb_e2_dd := (← mkAppOptM ``Quotient.mk $ #[some X] ++ #[some $ mkAppN (R_Setoid) xs, e2])
    let eq := ← mkEq bb_e1_dd bb_e2_dd
    mkLambdaFVars xs_e1_e2 eq
#eval do check $ ← mkQuotientEq `convr `convr_Setoid
#eval do ppExpr $ ← mkQuotientEq `convr `convr_Setoid
#eval mkQuotientEq `convr `convr_Setoid
#check fun α e1 e2 => (@Quotient.mk (Exp α) (@convr_Setoid α) e1) = (@Quotient.mk (Exp α) (@convr_Setoid α) e2)

-- R        : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → (_ : X) → (_ : X) → Prop
-- R_Setoid : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Setoid X

-- mkR_Eq_Quotient R R_Setoid := R = λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧
def mkR_Eq_Quotient (R : Name) (R_Setoid : Name) : MetaM Expr := do
  let QuotientEq := ← mkQuotientEq R R_Setoid
  let R := .const R []
  mkEq R QuotientEq
#eval do check $ ← mkR_Eq_Quotient `convr `convr_Setoid
#eval do ppExpr $ ← mkR_Eq_Quotient `convr `convr_Setoid
#eval mkR_Eq_Quotient ``convr ``convr_Setoid
#check @convr = fun {α} e1 e2 ↦ ⟦e1⟧ = ⟦e2⟧


-- R        : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → (_ : X) → (_ : X) → Prop
-- R_Setoid : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Setoid X

-- Adds "R_eq : R = λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧" to the environment
def addR_eq (R : Name) (R_Setoid : Name) : TermElabM Unit := do
  -- Build the type "R = λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧"
  let type := ← mkR_Eq_Quotient R R_Setoid

  -- Elaborate automated tactic proof as an expression
  -- Ensuring there are no meta-variables (so kernel doesn't complain)
  let pf := ← elabTerm (← `(by
      funext
      apply propext
      apply Iff.intro
      exact λ h => Quotient.sound h
      exact λ h => Quotient.exact h
    )) (some type)
  Term.synthesizeSyntheticMVarsNoPostponing
  let pf ← instantiateMVars pf

  -- Add "R_eq : R = λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧" to the environment
  let env              := ← getEnv
  let restrictedPrefix := env.asyncPrefix?.casesOn' ("") (λ name => name.toString ++ ".")
  let decl := Declaration.thmDecl {
    name        := (restrictedPrefix ++ R.toString ++ "_eq").toName
    levelParams := []
    type        := type
    value       := pf
  }
  addDecl decl
  compileDecl decl



elab "addR_eq" R:name R_Setoid:name : tactic => do addR_eq R.getName R_Setoid.getName


-- R        : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → (_ : X) → (_ : X) → Prop
-- R_Setoid : (x₁ : T₁) → (x₂ : T₂) → ⋯ → (xₙ : Tₙ) → Setoid X
def translate (R : Name) (R_Setoid : Name) : TacticM Unit :=
  withMainContext do
    -- Add "R_eq : R = λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧" to the environment
    let env       := ← getEnv
    let restrictedPrefix := env.asyncPrefix?.casesOn' ("") (λ name => name.toString ++ ".")
    let R_eq      := (restrictedPrefix ++ R.toString ++ "_eq").toName
    if ! env.contains R_eq
    then
      addR_eq R R_Setoid

    -- Revert all localHyps (last-to-first localHyps)
    let localHyps := (← getLocalHyps).map (λ expr => (expr.fvarId!))
    let goal      := ← getMainGoal
    let (_, goal) := ← goal.revert (preserveOrder := True) (localHyps)
    replaceMainGoal [goal]

    -- Generalize on R
    let R_Ident    := mkIdent R
    let R'_Ident   := mkIdent (R.toString ++ "'").toName
    let eq_Ident  := mkIdent ("eq").toName
    evalTactic (← `(tactic | generalize $eq_Ident:ident : (@$R_Ident:ident) = $R'_Ident:ident))

    -- Rewrite "R_eq : R = R_eq : R = (λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧)"
    -- at "eq : R = R'"
    let R_eq_Ident := mkIdent R_eq
    evalTactic (← `(tactic | rewrite [($R_eq_Ident:ident)] at ($eq_Ident:ident)))

    -- Substitute "eq : (λ x₁ ⋯ xₙ e1 e2 => ⟦e1⟧ = ⟦e2⟧)  =  R'" everywhere
    evalTactic (← `(tactic | subst ($eq_Ident:ident)))

    -- Beta-reduce the goal
    evalTactic (← `(tactic | beta_reduce))

    -- Re-intro all our localHyps (first-to-last localHyps)
    let goal      := ← getMainGoal
    let localHyps := (← localHyps.mapM (λ fvar => fvar.getUserName)).toList
    let n := localHyps.length
    let (_, goal) := ← goal.introN n (givenNames := localHyps)
    replaceMainGoal [goal]

elab "translate" R:name R_Setoid:name : tactic => do translate @R.getName @R_Setoid.getName

/-
Step 1: Revert EVERYTHING to get a single Target with an empty LocalCtxt

Step 2: Translate Target

Step 3: Intro EVERYTHING with all their original names

This avoids breaking anything due to dependent products.
This way we guarantee translating all "R"s in one single step.
-/
example {α : Ty} {a b : Exp α}
                        (f : (x y : Exp α) → (@convr α x y) → Nat)
                        (hf : (x y : Exp α) → (xRy : @convr α x y) → f x y xRy = 3)
                        (aRb : convr a b)
                        : (f a b aRb) = 3 :=
  by
  printEnv
  addR_eq `convr `convr_Setoid
  printEnv

  revert aRb hf f b a α
  generalize eq : @convr = convr'
  rewrite [convr_eq] at eq
  subst eq
  beta_reduce
  intro α a b f hf aRb

  exact hf a b aRb


example {α : Ty} {x y z : Exp α}
  (xRy : convr x y)
  (zRy : convr z y)
  : convr x z :=
  by
  translate `convr `convr_Setoid
  grind


example {α : Ty} {a b c : Exp α}
                        (f : (x y : Exp α) → (@convr α x y) → Nat)
                        (hf : (x y : Exp α) → (xRy : @convr α x y) → f x y xRy = 3)
                        (junk : convr c b)
                        (aRb : convr a b)
                        : (f a b aRb) = 3 :=
  by
  translate `convr `convr_Setoid
  exact hf a b aRb


example {α : Ty} {β : Ty} {x : Exp α} (y : Exp β)
  :  (⟦K ⬝ x ⬝ y⟧ : ExpClass α) = ⟦x⟧ :=
  by
  have convr.K' := @convr.K
  translate `convr `convr_Setoid
  exact convr.K'


example : (⟦a⟧ : ExpClass (β ⇒' α)) = ⟦b⟧ → (⟦c⟧ : ExpClass β) = ⟦d⟧ →  (⟦a ⬝ c⟧ : ExpClass α) = ⟦b ⬝ d⟧ :=
  by
  have convr.app' := @convr.app
  translate `convr `convr_Setoid
  exact fun a_1 a_2 ↦ convr.app' a_1 a_2




-- Alternate implementation idea: Have a custom typeclass "SetoidRewrite"
-- that extends "Setoid R" has an addtional "rEq" field.
-- This would also automatically add our equality lemma "R_eq" to the environment.
class SetoidRewrite (α : Sort u) extends Setoid α where
  /-- `x ≈ y` is the distinguished equivalence relation of a setoid. -/
  r := r
  /-- The relation `x ≈ y` is an equivalence relation. -/
  iseqv := iseqv

  rEq : (r) = (λ e1 => λ e2 => @Eq (@Quotient α ⟨r, iseqv⟩) (@Quotient.mk α ⟨r, iseqv⟩ e1) (@Quotient.mk α ⟨r, iseqv⟩ e2))

instance {α_Setoid : Setoid α} : SetoidRewrite α :=
  { rEq :=
      by
      funext
      apply propext
      apply Iff.intro
      exact fun a ↦ Quotient.sound a
      exact fun a ↦ Quotient.exact a
                                    }


lemma ExpClass_test :
  (λ α => @convr α) = (λ α => λ (e1 e2 : Exp α) => ((⟦e1⟧ : ExpClass α) = ⟦e2⟧)) :=
  by

  have rEq' := λ α => @SetoidRewrite.rEq (Exp α)
  show_term
    apply funext; intro α
    apply funext ; intro e1
    apply funext ; intro e2
    apply propext
    apply Iff.intro
    exact fun a => Quotient.sound a
    exact fun a => Quotient.exact a

lemma ExpClass_test2 {α} {e1 e2 : Exp α} :
  (@convr α e1 e2) = (((⟦e1⟧ : ExpClass α) = ⟦e2⟧)) :=
  by
  show_term
    apply propext
    apply Iff.intro
    exact fun a => Quotient.sound a
    exact fun a => Quotient.exact a


def Eq' : {α : Ty} → (Exp α) → (Exp α) → Prop := λ {α : Ty} (e1 e2 : Exp α) => ((⟦e1⟧ : ExpClass α) = ⟦e2⟧)


lemma ExpClass_K {α : Ty} {β : Ty} {x : Exp α} (y : Exp β) : (⟦K ⬝ x ⬝ y⟧ : ExpClass α) = ⟦x⟧ :=
  by
    have convr.K' := @convr.K
    translate `convr `convr_Setoid
    apply convr.K'

lemma ExpClass_S : (⟦S ⬝ x ⬝ y ⬝ z⟧ : ExpClass α) = ⟦x ⬝ z ⬝ (y ⬝ z)⟧ :=
  by
    have convr.S' := @convr.S
    translate `convr `convr_Setoid
    apply convr.S'

-- Congruence wrt Exp.app
lemma ExpClass_app : (⟦a⟧ : ExpClass (β ⇒' α)) = ⟦b⟧ → (⟦c⟧ : ExpClass β) = ⟦d⟧ →  (⟦a ⬝ c⟧ : ExpClass α) = ⟦b ⬝ d⟧ :=
  by
    have convr.app' := @convr.app
    translate `convr `convr_Setoid
    apply convr.app'

lemma ExpClass_app_arg : (⟦c⟧ : ExpClass β) = ⟦d⟧ →  (⟦a ⬝ c⟧ : ExpClass α) = ⟦a ⬝ d⟧
  := fun a_1 => ExpClass_app rfl a_1

lemma ExpClass_app_fun : (⟦a⟧ : ExpClass (β ⇒' α)) = ⟦b⟧ →  (⟦a ⬝ c⟧ : ExpClass α) = ⟦b ⬝ c⟧
  := fun a_1 => ExpClass_app a_1 rfl

lemma ExpClass_recN_zero : (⟦recN ⬝ e ⬝ f ⬝ zero⟧ : ExpClass α) = ⟦e⟧ :=
  by
    have convr.recN_zero' := @convr.recN_zero
    translate `convr `convr_Setoid
    apply convr.recN_zero'



lemma ExpClass_recN_succ : (⟦recN ⬝ e ⬝ f ⬝ (succ ⬝ n)⟧ : ExpClass α) = ⟦f ⬝ n ⬝ (recN ⬝ e ⬝ f ⬝ n)⟧ :=
  by
    have convr.recN_succ' := @convr.recN_succ
    translate `convr `convr_Setoid
    apply convr.recN_succ'


def Ty_inter : Ty → Type
| Ty.Nat => ℕ

| arrow a b => Exp (a ⇒' b) × (Ty_inter a → Ty_inter b)


def appsem {a b : Ty} (t : Ty_inter (a ⇒' b)) (e' : Ty_inter a) : Ty_inter b := (t.snd e')

def reify (a : Ty) (e : Ty_inter a) : Exp a :=
/-
  match a with
| Ty.Nat =>
  match e with
  | (0 : ℕ)    => zero
  | n+1         => succ ⬝ (reify Ty.Nat n)

| Ty.arrow a b =>
  match e with
  | (c, f) => c
-/
by
  cases a
  case Nat =>
    induction e
    case zero           => exact zero
    case succ _ reify_n => exact (succ ⬝ reify_n)
  case arrow a b        => exact e.fst


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
      translate `convr `convr_Setoid

      -- Add soundness Lemma
      have soundness' := @soundness
      translate `convr `convr_Setoid

      -- b ~ a ~ nbe a = nbe b
      -- "rewrite [← a_r_b, a_r_nbe, soundness a_r_b]"
      rw [← a_r_b, a_r_nbe, soundness' a_r_b]
    · intro b_r_nbe
      -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧":
      translate `convr `convr_Setoid

      -- Add soundness Lemma
      have soundness' := @soundness
      translate `convr `convr_Setoid

      -- a ~ b ~ nbe b = nbe a
      -- "rewrite [a_r_b, b_r_nbe, ← soundness a_r_b]"
      rw [a_r_b, b_r_nbe, ← soundness' a_r_b]

  · rename_i α β αIH βIH
    clear αIH
    intros f1 f2 f1_r_f2
    apply Iff.intro
    · intro R_f1
      apply And.intro
      · have f1_r_nbe := R_convr_nbe R_f1; clear R_f1
        -- Translate "convr a b" to "⟦a⟧ = ⟦b⟧":
        translate `convr `convr_Setoid

        -- Add soundness Lemma
        have soundness' := @soundness
        translate `convr `convr_Setoid

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
        translate `convr `convr_Setoid

        -- Add soundness Lemma
        have soundness' := @soundness
        translate `convr `convr_Setoid

        -- f1 ~ f2 ~ nbe f2 = nbe f1
        -- "rewrite [f1_r_f2, f2_r_nbe, ← soundness f1_r_f2]"
        rw [f1_r_f2, f2_r_nbe, ← soundness' f1_r_f2]
      · intro e' Re'
        rewrite [βIH (f1 ⬝ e') (f2 ⬝ e') (f1_r_f2.app convr.refl)]
        rcases R_f2 with ⟨_, h0⟩
        exact h0 e' Re'
