(*  Title:      LF_Examples.thy

    The proofs displayed in the paper, checked by evaluation.
*)

theory LF_Examples
  imports LF_Render
begin

section \<open>The paper's examples\<close>

abbreviation (input) "xv \<equiv> STR ''x''"
abbreviation (input) "yv \<equiv> STR ''y''"
abbreviation (input) "an \<equiv> STR ''a''"
abbreviation (input) "bn \<equiv> STR ''b''"

definition Pf :: fm where "Pf = Atom (STR ''P'') []"
definition Qf :: fm where "Qf = Atom (STR ''Q'') []"
definition Rf :: fm where "Rf = Atom (STR ''R'') []"
definition Ff :: "nm \<Rightarrow> fm" where "Ff a = Atom (STR ''F'') [namedTerm a]"
definition Gf :: "trm \<Rightarrow> fm" where "Gf t = Atom (STR ''G'') [t]"

definition allx_G :: fm where "allx_G = (\<forall>\<^sub>o xv. Gf (variableTerm xv))"
definition ally_G :: fm where "ally_G = (\<forall>\<^sub>o yv. Gf (variableTerm yv))"

subsection \<open>Section 2: the running example\<close>

definition sec2_lemmon :: lemmon_proof where
  "sec2_lemmon =
     [ \<langle>{1}, 1, Pf, Assumption\<rangle>\<^sub>L
     , \<langle>{2}, 2, Qf, Assumption\<rangle>\<^sub>L
     , \<langle>{1, 2}, 3, Pf \<and>\<^sub>o Qf, AndIntro 1 2\<rangle>\<^sub>L
     , \<langle>{1}, 4, Qf \<longrightarrow>\<^sub>o (Pf \<and>\<^sub>o Qf), CP 2 3\<rangle>\<^sub>L ]"

definition sec2_fitch :: fitch_proof where
  "sec2_fitch =
     [ \<langle>1, Pf, FPremise\<rangle>\<^sub>F
     , \<lbrakk>2 : Qf; [\<langle>3, Pf \<and>\<^sub>o Qf, FAndIntro 1 2\<rangle>\<^sub>F]\<rbrakk>\<^sub>F
     , \<langle>4, Qf \<longrightarrow>\<^sub>o (Pf \<and>\<^sub>o Qf), FCP (2, 3)\<rangle>\<^sub>F ]"

subsection \<open>Example 11: discharge order\<close>

definition ex11 :: lemmon_proof where
  "ex11 =
     [ \<langle>{1}, 1, Pf, Assumption\<rangle>\<^sub>L
     , \<langle>{2}, 2, Qf, Assumption\<rangle>\<^sub>L
     , \<langle>{1, 2}, 3, Pf \<and>\<^sub>o Qf, AndIntro 1 2\<rangle>\<^sub>L
     , \<langle>{2}, 4, Pf \<longrightarrow>\<^sub>o (Pf \<and>\<^sub>o Qf), CP 1 3\<rangle>\<^sub>L
     , \<langle>{}, 5, Qf \<longrightarrow>\<^sub>o (Pf \<longrightarrow>\<^sub>o (Pf \<and>\<^sub>o Qf)), CP 2 4\<rangle>\<^sub>L ]"

subsection \<open>Example 12: positional trapping\<close>

definition ex12 :: lemmon_proof where
  "ex12 =
     [ \<langle>{1}, 1, Pf, Assumption\<rangle>\<^sub>L
     , \<langle>{2}, 2, Qf, Assumption\<rangle>\<^sub>L
     , \<langle>{1}, 3, Pf \<or>\<^sub>o Rf, OrIntroL 1\<rangle>\<^sub>L
     , \<langle>{2}, 4, Qf \<and>\<^sub>o Qf, AndIntro 2 2\<rangle>\<^sub>L
     , \<langle>{}, 5, Qf \<longrightarrow>\<^sub>o (Qf \<and>\<^sub>o Qf), CP 2 4\<rangle>\<^sub>L
     , \<langle>{1}, 6, (Pf \<or>\<^sub>o Rf) \<and>\<^sub>o (Qf \<longrightarrow>\<^sub>o (Qf \<and>\<^sub>o Qf)), AndIntro 3 5\<rangle>\<^sub>L ]"

subsection \<open>Theorem 22: the eigenvariable proof\<close>

definition thm22_lemmon :: lemmon_proof where
  "thm22_lemmon =
     [ \<langle>{1}, 1, allx_G, Assumption\<rangle>\<^sub>L
     , \<langle>{2}, 2, Ff an, Assumption\<rangle>\<^sub>L
     , \<langle>{1}, 3, Gf (namedTerm an), ForallElim 1\<rangle>\<^sub>L
     , \<langle>{1}, 4, ally_G, ForallIntro 3\<rangle>\<^sub>L
     , \<langle>{1, 2}, 5, Ff an \<and>\<^sub>o ally_G, AndIntro 2 4\<rangle>\<^sub>L
     , \<langle>{1}, 6, Ff an \<longrightarrow>\<^sub>o (Ff an \<and>\<^sub>o ally_G), CP 2 5\<rangle>\<^sub>L ]"

text \<open>The Fitch proof the unmodified construction returns, and the one the
  renaming repair returns: only line 3 changes.\<close>

definition thm22_fitch_bad :: fitch_proof where
  "thm22_fitch_bad =
     [ \<langle>1, allx_G, FPremise\<rangle>\<^sub>F
     , \<lbrakk>2 : Ff an;
          [ \<langle>3, Gf (namedTerm an), FForallElim 1\<rangle>\<^sub>F
          , \<langle>4, ally_G, FForallIntro 3\<rangle>\<^sub>F
          , \<langle>5, Ff an \<and>\<^sub>o ally_G, FAndIntro 2 4\<rangle>\<^sub>F ]\<rbrakk>\<^sub>F
     , \<langle>6, Ff an \<longrightarrow>\<^sub>o (Ff an \<and>\<^sub>o ally_G), FCP (2, 5)\<rangle>\<^sub>F ]"

definition thm22_fitch_good :: fitch_proof where
  "thm22_fitch_good =
     [ \<langle>1, allx_G, FPremise\<rangle>\<^sub>F
     , \<lbrakk>2 : Ff an;
          [ \<langle>3, Gf (namedTerm bn), FForallElim 1\<rangle>\<^sub>F
          , \<langle>4, ally_G, FForallIntro 3\<rangle>\<^sub>F
          , \<langle>5, Ff an \<and>\<^sub>o ally_G, FAndIntro 2 4\<rangle>\<^sub>F ]\<rbrakk>\<^sub>F
     , \<langle>6, Ff an \<longrightarrow>\<^sub>o (Ff an \<and>\<^sub>o ally_G), FCP (2, 5)\<rangle>\<^sub>F ]"

subsection \<open>Corollary 6: \<open>\<delta>\<close> is not injective\<close>

text \<open>Two Fitch proofs differing only in the placement of a line within a
  subproof whose assumption it does not use.\<close>

definition cor6_wide :: fitch_proof where
  "cor6_wide =
     [ \<langle>1, Pf, FPremise\<rangle>\<^sub>F
     , \<lbrakk>2 : Qf; [\<langle>3, Pf \<or>\<^sub>o Rf, FOrIntroL 1\<rangle>\<^sub>F]\<rbrakk>\<^sub>F ]"

definition cor6_narrow :: fitch_proof where
  "cor6_narrow =
     [ \<langle>1, Pf, FPremise\<rangle>\<^sub>F
     , \<langle>2, Qf, FPremise\<rangle>\<^sub>F
     , \<langle>3, Pf \<or>\<^sub>o Rf, FOrIntroL 1\<rangle>\<^sub>F ]"

section \<open>What the examples show\<close>

text \<open>Everything below is settled by evaluating the checkers, which is what
  Section 7 of the paper reports having done in Haskell.  Here the checkers are
  the ones the theorems above are about, so the evidence and the statements
  concern the same objects.\<close>

subsection \<open>The examples are correct proofs\<close>

lemma correct_sources:
  "lemmonCorrect sec2_lemmon"
  "lemmonCorrect ex11"
  "lemmonCorrect ex12"
  "lemmonCorrect thm22_lemmon"
  "fitchCorrect sec2_fitch"
  by eval+

subsection \<open>Section 2: the two notations agree on the running example\<close>

lemma sec2_delta: "\<delta> sec2_fitch = sec2_lemmon"
  by eval

lemma sec2_roundtrip: "lemmonToFitchDirect sec2_lemmon = Inr sec2_fitch"
  by eval

subsection \<open>Theorem 10: two correct Lemmon proofs with no positional Fitch image\<close>

text \<open>Example 11: the discharges demand incompatible nestings.  Reported at
  line 4, which discharges assumption 1 while the box opened at 2 is still open.\<close>

theorem example_11_not_positional: "lemmonToFitchDirect ex11 = Inl (NotNested 4 1 [2])"
  by eval

text \<open>Example 12: line 3 is written inside the box opened at 2, which it does not
  depend on, and line 6 cites it after that box has closed.\<close>

theorem example_12_not_positional: "lemmonToFitchDirect ex12 = Inl (OutOfScope 6 3 2)"
  by eval

theorem theorem_10:
  "lemmonCorrect ex11 \<and> (\<forall>F. lemmonToFitchDirect ex11 \<noteq> Inr F)"
  "lemmonCorrect ex12 \<and> (\<forall>F. lemmonToFitchDirect ex12 \<noteq> Inr F)"
  using example_11_not_positional example_12_not_positional correct_sources by auto

subsection \<open>Corollary 6: \<open>\<delta>\<close> is not injective, and the round trip normalises\<close>

theorem corollary_6:
  "fitchCorrect cor6_wide"
  "fitchCorrect cor6_narrow"
  "cor6_wide \<noteq> cor6_narrow"
  "\<delta> cor6_wide = \<delta> cor6_narrow"
  by eval+

text \<open>Composing the other way returns a proof whose subproofs are no wider than
  they need to be.\<close>

theorem roundtrip_normalises: "lemmonToFitchDirect (\<delta> cor6_wide) = Inr cor6_narrow"
  by eval

subsection \<open>Proposition 7 on an example\<close>

lemma proposition_7_ex12: "recompute (stripDeps ex12) = ex12"
  by eval

subsection \<open>Theorem 22, and what it does to Theorem 4\<close>

text \<open>The positional translation applies to the Lemmon proof of Theorem 22 --- the
  discharges nest and nothing goes out of scope --- and returns exactly the Fitch
  proof the paper displays.\<close>

theorem theorem_22_construction: "lemmonToFitchDirect thm22_lemmon = Inr thm22_fitch_bad"
  by eval

text \<open>And that proof is not correct: line 4 generalises on @{term "STR ''a''"}
  while @{term "Ff (STR ''a'')"} stands as an undischarged assumption in its
  scope.\<close>

theorem theorem_22: "\<not> fitchCorrect thm22_fitch_bad"
  by eval

text \<open>The renaming repair of Section 5: line 3 instantiates to a name occurring
  nowhere else, and nothing moves.\<close>

theorem renaming_repair: "fitchCorrect thm22_fitch_good"
  by eval

text \<open>\bigskip
  Theorem 4 of the paper states that a Fitch proof @{term F} is correct
  \emph{if and only if} @{term "\<delta> F"} is.  The ``if'' direction fails, and
  Theorem 22 is itself the counterexample: @{term thm22_fitch_bad} is not a
  correct Fitch proof, but its image under \<open>\<delta>\<close> is the correct Lemmon proof the
  paper displays just above it.

  This is not an accident of the present formalisation.  It is the same
  phenomenon Section 6.2 identifies: at universal introduction the Fitch side
  condition speaks of scope where the Lemmon one speaks of dependency, and
  because scope may properly include the dependency set (Proposition 5), Fitch
  licenses strictly less.  A rule that licenses strictly less cannot have its
  correctness reflected by a translation that forgets scope.  The direction that
  survives is @{thm [source] theorem_4_forward}, proved in
  \<open>LF_Delta.thy\<close>: correctness transfers from Fitch to Lemmon, not back.\<close>

theorem theorem_4_backward_fails:
  "\<not> fitchCorrect thm22_fitch_bad \<and> lemmonCorrect (\<delta> thm22_fitch_bad)"
  by eval

text \<open>The image is exactly the Lemmon proof of Theorem 22, so the failure is
  visible on the very pair of proofs the paper prints.\<close>

lemma theorem_22_delta: "\<delta> thm22_fitch_bad = thm22_lemmon"
  by eval

section \<open>Proofs as objects\<close>

text \<open>A Lemmon proof is a list of @{const ProofLine} values; a Fitch proof is a
  list of @{const FLine} and @{const FSub} values.  Nothing here is notation for
  a proof: these are the proofs, and \<open>\<delta>\<close> and the two translations are ordinary
  functions on them, which the code generator runs.  What follows are
  evaluations, printed through \<open>LF_Render.thy\<close>.  Put the
  cursor on a @{command print_proof} line to see its output.\<close>

print_proof \<open>showFitch sec2_fitch\<close>
print_proof \<open>showLemmon (\<delta> sec2_fitch)\<close>
print_proof \<open>showTranslation (lemmonToFitch sec2_lemmon)\<close>
print_proof \<open>showTranslation (lemmonToFitch ex11)\<close>
print_proof \<open>showTranslation (lemmonToFitch ex12)\<close>
print_proof \<open>showTranslation (lemmonToFitchChecked thm22_lemmon)\<close>

section \<open>Section 6.3: translating through derivation trees\<close>

text \<open>``Examples 11 and 12 translate through the construction to Fitch proofs of
  five and six lines respectively --- exactly the lengths of the originals.  No
  line was duplicated in either case.  This is what one would expect if
  Conjecture 28 holds and the unfolding is simply doing more work than it needs
  to.''\<close>

theorem example_11_via_tree:
  "case lemmonToFitch ex11 of
     Inr (r, F) \<Rightarrow> r = ViaTree \<and> fitchCorrect F \<and> length (flatten F) = 5
                    \<and> fitchConclusion F = conclusion ex11
   | Inl _ \<Rightarrow> False"
  by eval

theorem example_12_via_tree:
  "case lemmonToFitch ex12 of
     Inr (r, F) \<Rightarrow> r = ViaTree \<and> fitchCorrect F \<and> length (flatten F) = 6
                    \<and> fitchConclusion F = conclusion ex12
   | Inl _ \<Rightarrow> False"
  by eval

subsection \<open>The unchecked translation takes the wrong route on Theorem 22\<close>

text \<open>@{const lemmonToFitchDirect} succeeds on the Lemmon proof of Theorem 22:
  its discharges nest, and nothing goes out of scope.  So the paper's
  @{const lemmonToFitch}, which accepts a positional image without asking the
  checker, returns an incorrect Fitch proof by the @{const Direct} route.\<close>

theorem lemmonToFitch_unchecked:
  "lemmonToFitch thm22_lemmon = Inr (Direct, thm22_fitch_bad)"
  "\<not> fitchCorrect thm22_fitch_bad"
  by eval+

text \<open>The checked variant falls back to the unfolding, and the unfolding applies
  the renaming repair of Section 5.4.  The proof it returns is the paper's, line
  for line, with a name of its own where the paper writes \<open>b\<close>.\<close>

theorem lemmonToFitchChecked_thm22:
  "case lemmonToFitchChecked thm22_lemmon of
     Inr (r, F) \<Rightarrow> r = ViaTree \<and> fitchCorrect F \<and> length (flatten F) = 6
                    \<and> fitchConclusion F = conclusion thm22_lemmon
   | Inl _ \<Rightarrow> False"
  by eval

section \<open>Existential elimination has the same defect\<close>

text \<open>Section 6.2 says that ``universal introduction alone imposes a condition on
  the assumptions''.  On the rule set of \<open>LF_Lemmon.thy\<close>
  existential elimination imposes one too: its witness must occur in no
  assumption the conclusion depends on other than the witness assumption itself.
  The argument of Section 6.2 therefore applies to it word for word, and the
  proof below is the proof of Theorem 22 with \<open>\<exists>\<close> in place of \<open>\<forall>\<close>.\<close>

definition exx_G :: fm where "exx_G = Exi xv (Gf (Vr xv))"
definition exy_G :: fm where "exy_G = Exi yv (Gf (Vr yv))"

definition exE_lemmon :: lemmon_proof where
  "exE_lemmon =
     [ ProofLine 1 exx_G Assumption {1}
     , ProofLine 2 (Ff an) Assumption {2}
     , ProofLine 3 (Gf (Nm an)) Assumption {3}
     , ProofLine 4 exy_G (ExistsIntro 3) {3}
     , ProofLine 5 exy_G (ExistsElim 1 3 4) {1}
     , ProofLine 6 (Conj (Ff an) exy_G) (AndIntro 2 5) {1, 2}
     , ProofLine 7 (Impl (Ff an) (Conj (Ff an) exy_G)) (CP 2 6) {1} ]"

text \<open>Line 5 eliminates the existential on @{term "STR ''a''"}, and
  @{term "Ff (STR ''a'')"} is not among the assumptions line 4 depends on, which
  are @{term "{3::nat}"} and are discharged by the elimination itself.  The
  Lemmon side condition is satisfied.\<close>

theorem exE_source_correct: "lemmonCorrect exE_lemmon"
  by eval

text \<open>Its positional image exists --- the boxes @{term "(3::nat, 4::nat)"} and
  @{term "(2::nat, 6::nat)"} nest, and no citation crosses a closed box --- and
  is not a correct Fitch proof: at line 5 the witness stands in
  @{term "Ff (STR ''a'')"}, which is in scope.\<close>

theorem exE_defect:
  "case lemmonToFitchDirect exE_lemmon of
     Inr F \<Rightarrow> \<not> fitchCorrect F
   | Inl _ \<Rightarrow> False"
  by eval

text \<open>So Conjecture 26, repairing only at universal introduction, would leave
  this proof untranslated.  @{const exRepair} applies the same repair at
  existential elimination, and the unfolding then returns a correct proof.\<close>

theorem exE_repair:
  "case lemmonToFitchChecked exE_lemmon of
     Inr (r, F) \<Rightarrow> r = ViaTree \<and> fitchCorrect F
                    \<and> fitchConclusion F = conclusion exE_lemmon
   | Inl _ \<Rightarrow> False"
  by eval

print_proof \<open>showLemmon exE_lemmon\<close>
print_proof \<open>showTranslation (case lemmonToFitchDirect exE_lemmon of
                          Inl e \<Rightarrow> Inl e | Inr F \<Rightarrow> Inr (Direct, F))\<close>
print_proof \<open>showTranslation (lemmonToFitchChecked exE_lemmon)\<close>

section \<open>The quantifiers and the connectives\<close>

text \<open>A correct Lemmon proof that puts every symbol on the page: \<open>\<forall>\<close> in the
  premise and in the conclusion of line 3, with universal elimination and
  universal introduction as the rules that move between them, and \<open>\<not>\<close>, \<open>\<bottom>\<close>,
  \<open>\<and>\<close>, \<open>\<or>\<close> and \<open>\<longrightarrow>\<close> along the way.  The universal introduction at line 3 is
  legitimate: line 2 rests only on the premise, in which \<open>a\<close> does not occur, and
  it stands \<^emph>\<open>before\<close> the assumption \<open>\<not>G(a)\<close> is made --- so unlike Theorem 22 this
  one survives the positional translation untouched.\<close>

definition symbols_lemmon :: lemmon_proof where
  "symbols_lemmon =
     [ ProofLine 1 allx_G Assumption {1}
     , ProofLine 2 (Gf (Nm an)) (ForallElim 1) {1}
     , ProofLine 3 ally_G (ForallIntro 2) {1}
     , ProofLine 4 (Neg (Gf (Nm an))) Assumption {4}
     , ProofLine 5 Bot (BotI 2 4) {1, 4}
     , ProofLine 6 (Neg (Neg (Gf (Nm an)))) (RAA 4 5) {1}
     , ProofLine 7 (Conj (Neg (Neg (Gf (Nm an)))) ally_G) (AndIntro 6 3) {1}
     , ProofLine 8 (Disj (Conj (Neg (Neg (Gf (Nm an)))) ally_G) (Neg ally_G))
                   (OrIntroL 7) {1}
     , ProofLine 9 (Impl (Neg (Gf (Nm an))) Bot) (CP 4 5) {1} ]"

theorem symbols_correct: "lemmonCorrect symbols_lemmon"
  by eval

theorem symbols_positional:
  "case lemmonToFitch symbols_lemmon of
     Inr (r, F) \<Rightarrow> r = Direct \<and> fitchCorrect F
                    \<and> fitchConclusion F = conclusion symbols_lemmon
   | Inl _ \<Rightarrow> False"
  by eval

print_proof \<open>showLemmon symbols_lemmon\<close>
print_proof \<open>showTranslation (lemmonToFitch symbols_lemmon)\<close>

text \<open>And the two symbols no single proof above happens to need, with the
  identity predicate:\<close>

print_proof \<open>map showFm
  [ Uni xv (Gf (Vr xv))
  , Exi xv (Gf (Vr xv))
  , Iff Pf Qf
  , Eqf (Nm an) (Nm bn)
  , Impl (Iff Pf Qf) (Disj (Neg Pf) Qf) ]\<close>


end
