/-
Setoid (our implementation):

Wanted Features:
1. Rewriting under ∀ or Π binders:
  Yes, using "simp_rw" we can rewrite under binders.
  Not easy to use "simp_rw", but does work

2. Rewriting using congruences/selecting a specific instance:
  Yes, can do it but not pretty, needs to be cleaned up:
    f ⬝ x3 ⬝ (x2 ⬝ x3 ⬝ x4) ~ f ⬝ x3 ⬝ (x2 ⬝ x3' ⬝ x4)

    Currently: rw [.app_arg .app_fun .app_arg x3_r_x3']

    Want: "rw (config := {occs := .pos [2]}) [x3_r_x3']"

  That is, congruently-rewrite specific instances in the equivalence class
  and numerically selelcting which specific occurance.
  Should require an additional Lemma / TypeClass-instance

3. Rewriting under functions:
  Don't know, haven't tried it yet, an example would be:
    f (g x) y ~ f (g x') y'

  Would need 2 additional Lemmas / TypeClass-instances saying:
    "Proper (~ ++> ~ ++> ~) f"
    a.  ⬝~⬝ => ⬝~⬝  =>  (f ⬝ ⬝) ~ (f ⬝ ⬝)

    "Proper (~ ++> ~) g"
    b.  ⬝~⬝ => (g ⬝) ~ (g ⬝)

4. Other-features ???



-- Need, even more intense and ugly rewriting examples!!
-- They need to be as ugly and heavy-duty as possible, more intensive proofs and examples

Pros:
1. Can rewrite under binders using "simp_rw"

2. Can automatically do refl, symm, and trans stuff easily

3. Able to compress 3-4 apply lines into one "rewrite" line

4. Would be nice to extend this congruence-rewriting to certain relations.
  For example:
    R (K ⬝ e' ⬝ e'') = R e'
    Currently: rewrite [convr_R_iff (K ⬝ e' ⬝ e'') e' convr.K]
    Want: "rewrite [convr.K]"

5. Completely mimmics structure of inductive R

Cons:
1. R is not "general-rewriting", now we are just doing "setoid-rewriting" do to using
  Quotient-types

2. Ugly to do specific-instance rewrites:
    f ⬝ x3 ⬝ (x2 ⬝ x3 ⬝ x4) ~ f ⬝ x3 ⬝ (x2 ⬝ x3' ⬝ x4)
    Currently: rw [.app_arg .app_fun .app_arg x3_r_x3']
    Want: "rw (config := {occs := .pos [2]}) [x3_r_x3']"

3. Ugly "definitional-casts" required to use prev-lemmas:
    e ~ e ⬝ id ~ nbe e = nbe e' ~ e' ⬝ id ~ e'
    Currently: rw [← ExpClass.id_right, ExpClass.def.mp $ eval_lemma1 e Exp.id, h0,
                   ← ExpClass.def.mp $ eval_lemma1 e' Exp.id, ExpClass.id_right]
    Want: "rewrite [← convr.id_right, eval_lemma1 e Exp.id, h0, ← eval_lemma1 e' Exp.id, convr.id_right]"

    a ~ b ~ nbe b = nbe a
    Currently: rw [a_r_b, b_r_nbe, ← soundness $ ExpClass.def.mpr a_r_b]
    Want: "rewrite [a_r_b, b_r_nbe, ← soundness a_r_b]"

  Want these "definitional-casts" to be automatic/ "under the hood"

4. Since R is not "general", this is a special-case of Sozeau's algorithm.
  a. To do the heavy duty "congruence-rewriting" we want, need to use similar TypeClass-mechanism

  b. Difference is we would hopefully not need "all"-combinator TypeClass-instances to-do Rewriting under binders.
    Could instead potentially use "simp_rw" to do it (though this is just a guess, I have never rewritten under binders in practice)

  c. Hopefully won't have to use the "Subrel" instances, as that seems to complicate the TypeClass instances we need

5. Don't know how this would work for an R that is not Inductive or an Equiv.
-/


/-
Grewrite (Sebastian implementation based-on Sozeau's alg):

Pros:
1. More general than Setoid-approach, can work with R's that are not Equivs

2. (Mostly) nice to-do specific-instance rewrites

Cons:
1. Cannot rewrite under ∀ or Π binders! This is b/c [ARROW], [LAMBDA] and [FORALL] cases are not implemented yet.
  Not clear what is going on in Sozeau's alg with [ARROW] and [FORALL] cases, seems like they would loop-forever?
  Maybe these cases are supposed to be captured by instances involving the "all" and "impl" combinators?

2. Sebastian's partial-implementation is all I could find so-far.
  Sozeau says he implemented this in Coq 8.2 in his article, but I haven't been able to find his implementation

3. Required TypeClass instances are not always the easiest to figure out

4. Sometimes is unable to select/recognize specific rewrite-instances, as an example (could be due to missing TypeClass-instances):
  ((x, (0,0)), y) ~ ((x, 0), y)
  grewrite convr.id_left at 1
  ((x, 0), y) ~ (x,y)
  -- Can't do this step using grewrite!!!
  -- Need more Typeclass instances probably
  apply convr.trans $ convr.id_right.app convr.refl

5. Cannot work-with/recognize local hypotheses derived from tactics:
    example (finish: Pα a') : Rα a a' → Pα a := by
    intro h
    -- BAD!!:
    -- "grewrite" doesn't work with local name "h"
    --grewrite h
    sorry

  Found a "workaround" for this problem
  (i.e. copy the local-context to a comment, then create an additional lemma using this context and do grewrites in lemma)

6.

-/
