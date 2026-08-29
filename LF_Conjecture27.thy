(*  Title:      LF_Conjecture27.thy

    Conjecture 27 of the paper:

      "Every correct Lemmon proof can be permuted --- preserving the requirement
       that a line follow the lines it cites --- into one with a positional Fitch
       image."

    It is false.  There is a third obstruction to positional translation, beyond
    the two of Theorem 10, and unlike those two it is invariant under permutation:
    a Lemmon proof may discharge two different assumptions at the same line.
*)

theory LF_Conjecture27
  imports LF_Positional
begin

section \<open>Definition 9, as a predicate\<close>

text \<open>``A translation from Lemmon to Fitch is positional if it preserves the
  sequence of lines: the \<open>n\<close>th line of the Lemmon proof becomes the \<open>n\<close>th line of
  the Fitch proof, with the same formula and the corresponding rule.''  So
  @{term F} is a positional image of @{term P} when flattening @{term F} recovers
  the source line for line, number, formula and rule alike.  Whether the image is
  a \emph{Fitch proof} is the separate demand @{const fitchWF}: Theorem 10 says
  there are sources for which no @{term F} meets both.\<close>

text \<open>``The corresponding rule'' is @{const toFitchRule} at every rule but one.
  The exception is @{const Assumption}: the Fitch rule set says one thing more
  than the Lemmon one, namely whether an undischarged assumption is a premise, so
  a Lemmon assumption corresponds to @{const FPremise} when it stands at the
  outermost level and to @{const FAssume} when it opens a subproof.
  @{const toFitchRule} has to pick one and picks @{const FPremise}; the
  correspondence proper admits both.  Reading Definition 9 with
  @{const toFitchRule} alone would make the notion vacuous --- no proof with a
  discharge could have an image, since a subproof's first line carries
  @{const FAssume} --- and every theorem below would be true for the wrong
  reason.  \<open>sec2_positional_image\<close> below is the check that it is not.\<close>

definition ruleMatches :: "just \<Rightarrow> fitch_rule \<Rightarrow> bool" where
  "ruleMatches j r \<longleftrightarrow>
     (if j = Assumption then r = FPremise \<or> r = FAssume else r = toFitchRule j)"

lemma ruleMatches_toFitchRule [simp]: "ruleMatches j (toFitchRule j)"
  by (cases j) (simp_all add: ruleMatches_def)

lemma ruleMatches_not_assumption:
  "j \<noteq> Assumption \<Longrightarrow> ruleMatches j r \<Longrightarrow> r = toFitchRule j"
  by (simp add: ruleMatches_def)

definition lineMatches :: "fline \<Rightarrow> pline \<Rightarrow> bool" where
  "lineMatches fl l \<longleftrightarrow>
     flNum fl = lineNumber l \<and> flFm fl = formula l
       \<and> ruleMatches (justification l) (flRule fl)"

definition positionalImage :: "fitch_proof \<Rightarrow> lemmon_proof \<Rightarrow> bool" where
  "positionalImage F P \<longleftrightarrow> list_all2 lineMatches (flatten F) P"

text \<open>Conjecture 28 asks for an image that need not be positional, so we also
  want the notion with the order forgotten: @{term F} carries exactly the lines of
  @{term P}, each with its number, its formula and the corresponding rule, but in
  whatever order the boxes require.  Adding that no line is repeated --- which,
  since the numbers are distinct on both sides, is just a count --- gives the
  image Conjecture 28 asks for.\<close>

definition fitchImage :: "fitch_proof \<Rightarrow> lemmon_proof \<Rightarrow> bool" where
  "fitchImage F P \<longleftrightarrow>
     (\<forall>l \<in> set P. \<exists>fl \<in> set (flatten F). lineMatches fl l) \<and>
     (\<forall>fl \<in> set (flatten F). \<exists>l \<in> set P. lineMatches fl l)"

definition noDuplication :: "fitch_proof \<Rightarrow> lemmon_proof \<Rightarrow> bool" where
  "noDuplication F P \<longleftrightarrow> fitchImage F P \<and> length (flatten F) = length P"

lemma list_all2_setD1: "list_all2 R xs ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>y \<in> set ys. R x y"
  by (induction xs ys rule: list_all2_induct) auto

lemma list_all2_setD2: "list_all2 R xs ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x \<in> set xs. R x y"
  by (induction xs ys rule: list_all2_induct) auto

lemma positionalImage_fitchImage: "positionalImage F P \<Longrightarrow> fitchImage F P"
  unfolding positionalImage_def fitchImage_def
  by (meson list_all2_setD1 list_all2_setD2)

lemma positionalImage_noDuplication: "positionalImage F P \<Longrightarrow> noDuplication F P"
  unfolding noDuplication_def
  using positionalImage_fitchImage positionalImage_def list_all2_lengthD by metis

lemma fitchImage_line:
  assumes "fitchImage F P" and "l \<in> set P"
  shows "\<exists>fl \<in> set (flatten F). lineMatches fl l"
  using assms unfolding fitchImage_def by blast

text \<open>The well-formedness demand is not an extra condition smuggled into the
  reading of Definition 9.  Without it every Lemmon proof would have a positional
  image and Theorem 10 would be false: laying the lines out flat, with no
  subproofs at all, matches the source line for line, number, formula and rule.
  What it fails to be is a Fitch proof.  So ``has a positional Fitch image'' must
  mean ``some \emph{Fitch proof} is a positional image'', and that is the reading
  under which Conjecture 27 is refuted below.\<close>

lemma positionalImage_flat:
  "positionalImage (map (\<lambda>l. FLine (lineNumber l) (formula l)
                                   (toFitchRule (justification l))) P) P"
  by (simp add: positionalImage_def flatten_def comp_def lineMatches_def
                list_all2_conv_all_nth)

lemma positionalImage_always: "\<exists>F. positionalImage F P"
  using positionalImage_flat by blast

text \<open>Non-vacuity.  The running example of Section 2 does have a positional Fitch
  image, and its image is a Fitch proof: the assumption discharged at line 4 opens
  a subproof, so line 2 carries @{const FAssume} where the source carries
  @{const Assumption}.  Without @{const ruleMatches} this would fail, and every
  theorem below would hold vacuously.\<close>

lemma sec2_positional_image:
  "fitchWF sec2_fitch \<and> positionalImage sec2_fitch sec2_lemmon"
  by (simp add: positionalImage_def sec2_fitch_def sec2_lemmon_def flatten_def
                lineMatches_def ruleMatches_def)
     eval

section \<open>The seven checks are sufficient, but not necessary for this predicate\<close>

text \<open>The permissive assumption clause in @{const ruleMatches} admits an
  unused subproof: an undischarged Lemmon assumption may carry @{const FAssume}
  even when no later rule cites its subproof.  Consequently the seven checks of
  @{const lemmonToFitchDirect} are sufficient for a well-formed positional
  image, by @{thm [source] lemmonToFitchDirect_fitchWF}, but they are not
  necessary for @{const positionalImage} as defined above.  The late premise
  witness is decisive: representing line 3 as a one-line unused subproof avoids
  @{const premisesFirst}, while the direct construction represents it as a late
  @{const FPremise} and correctly rejects that canonical image.\<close>

definition premLate_fitch_alt :: fitch_proof where
  "premLate_fitch_alt =
     [ FLine 1 Pf FPremise
     , FLine 2 (Disj Pf Rf) (FOrIntroL 1)
     , FSub (Subproof 3 Qf []) ]"

lemma premLate_has_positional_image:
  "fitchWF premLate_fitch_alt \<and> positionalImage premLate_fitch_alt premLate"
  by eval

theorem seven_checks_not_necessary:
  "lemmonCorrect premLate
     \<and> (\<exists>F. fitchWF F \<and> positionalImage F premLate)
     \<and> (\<nexists>F. lemmonToFitchDirect premLate = Inr F)"
  using premLate_correct premLate_has_positional_image premLate_rejected by auto

section \<open>A discharging line cites the subproof its Lemmon rule names\<close>

text \<open>The two rule maps agree on subproof references: what Lemmon writes as a
  discharge pair is exactly what Fitch writes as a subproof citation; this is
  @{thm [source] fCitedSubs_toFitchRule}.\<close>

lemma citationOK_subs:
  assumes "fitchWF F" and "fl \<in> set (flatten F)"
      and "s \<in> set (fCitedSubs (flRule fl))"
  shows "(s, flScope fl) \<in> set (subrefs F)"
proof -
  from assms(1,2) have "citationOK F fl" by (auto simp: fitchWF_def list_all_iff)
  then have all: "\<And>a c. (a, c) \<in> set (fCitedSubs (flRule fl))
                    \<Longrightarrow> ((a, c), flScope fl) \<in> set (subrefs F)"
    unfolding citationOK_def by (auto simp: list_all_iff)
  obtain a c where sc: "s = (a, c)" by (cases s)
  with assms(3) have "(a, c) \<in> set (fCitedSubs (flRule fl))" by simp
  from all [OF this] sc show ?thesis by simp
qed

section \<open>In a Fitch proof, distinct subproofs end at distinct lines\<close>

text \<open>This is the heart of the matter.  A subproof reference names an assumption
  line and a last line, and @{thm [source] subrefs_lines} says that the last line
  carries the scope path of the subproof.  Line numbers in a well-formed Fitch
  proof are distinct, so a line has only one scope path; two subproofs closing at
  the same line therefore have the same assumption line, and so are the same
  subproof.

  The reason, in the notation: a subproof ends in a line, not in a subproof.  If
  two nested subproofs closed at the same line, the outer one would end with the
  inner one.\<close>

lemma subrefs_same_last:
  assumes wf: "fitchWF F"
      and A: "((a, c), P) \<in> set (subrefs F)"
      and B: "((b, c), Q) \<in> set (subrefs F)"
  shows "a = b"
proof -
  from subrefs_lines [OF wf A] obtain f r
    where fa: "FL c f r (P @ [a]) \<in> set (flatten F)" by blast
  from subrefs_lines [OF wf B] obtain g t
    where gb: "FL c g t (Q @ [b]) \<in> set (flatten F)" by blast
  from wf have "distinct (map flNum (flatten F))" by (rule fitchWF_distinct)
  then have inj: "inj_on flNum (set (flatten F))" by (simp add: distinct_map)
  have "flNum (FL c f r (P @ [a])) = flNum (FL c g t (Q @ [b]))" by simp
  from inj_onD [OF inj this fa gb] have "P @ [a] = Q @ [b]" by simp
  then show ?thesis by simp
qed

section \<open>The third obstruction\<close>

text \<open>A Lemmon proof may discharge two different assumptions at one and the same
  line: nothing in the notation forbids it, because a Lemmon line does not belong
  to a region of the page.  A Fitch proof cannot, because the two subproofs would
  have to close together.\<close>

definition sharedDischarge :: "lemmon_proof \<Rightarrow> bool" where
  "sharedDischarge P \<longleftrightarrow>
     (\<exists>l1 \<in> set P. \<exists>l2 \<in> set P. \<exists>a b c.
        (a, c) \<in> set (dischargePairs (justification l1)) \<and>
        (b, c) \<in> set (dischargePairs (justification l2)) \<and> a \<noteq> b)"

theorem sharedDischarge_no_image:
  assumes sh: "sharedDischarge P"
  shows "\<not> (\<exists>F. fitchWF F \<and> fitchImage F P)"
proof (rule notI, elim exE conjE)
  fix F assume wf: "fitchWF F" and img: "fitchImage F P"
  from sh obtain l1 l2 a b c
    where l1: "l1 \<in> set P" and l2: "l2 \<in> set P"
      and p1: "(a, c) \<in> set (dischargePairs (justification l1))"
      and p2: "(b, c) \<in> set (dischargePairs (justification l2))"
      and ab: "a \<noteq> b"
    unfolding sharedDischarge_def by blast
  from p1 have j1: "justification l1 \<noteq> Assumption" by (cases "justification l1") auto
  from p2 have j2: "justification l2 \<noteq> Assumption" by (cases "justification l2") auto
  from fitchImage_line [OF img l1] obtain fl1
    where m1: "fl1 \<in> set (flatten F)" and lm1: "lineMatches fl1 l1" by blast
  from lm1 j1 have r1: "flRule fl1 = toFitchRule (justification l1)"
    unfolding lineMatches_def using ruleMatches_not_assumption by blast
  from fitchImage_line [OF img l2] obtain fl2
    where m2: "fl2 \<in> set (flatten F)" and lm2: "lineMatches fl2 l2" by blast
  from lm2 j2 have r2: "flRule fl2 = toFitchRule (justification l2)"
    unfolding lineMatches_def using ruleMatches_not_assumption by blast
  from p1 r1 have "(a, c) \<in> set (fCitedSubs (flRule fl1))"
    by (simp add: fCitedSubs_toFitchRule)
  from citationOK_subs [OF wf m1 this]
  have s1: "((a, c), flScope fl1) \<in> set (subrefs F)" .
  from p2 r2 have "(b, c) \<in> set (fCitedSubs (flRule fl2))"
    by (simp add: fCitedSubs_toFitchRule)
  from citationOK_subs [OF wf m2 this]
  have s2: "((b, c), flScope fl2) \<in> set (subrefs F)" .
  from subrefs_same_last [OF wf s1 s2] ab show False by simp
qed

corollary sharedDischarge_no_positional_image:
  "sharedDischarge P \<Longrightarrow> \<not> (\<exists>F. fitchWF F \<and> positionalImage F P)"
  using sharedDischarge_no_image positionalImage_fitchImage by blast

section \<open>Permutation\<close>

text \<open>To permute a Lemmon proof is to renumber its lines injectively and re-sort:
  every reordering of the lines arises this way, since one may take @{term r} to
  send each line to its new position.  Citations and dependency sets are renamed
  with the lines, which is what makes the result a proof of the same thing.  The
  theorem below quantifies over \emph{all} injective renumberings, so it does not
  matter that Conjecture 27 restricts attention to those under which a line still
  follows the lines it cites: the refutation covers those and more.\<close>

fun renumberJust :: "(nat \<Rightarrow> nat) \<Rightarrow> just \<Rightarrow> just" where
  "renumberJust r Assumption = Assumption"
| "renumberJust r (MP i0 i1) = MP (r i0) (r i1)"
| "renumberJust r (CP i0 i1) = CP (r i0) (r i1)"
| "renumberJust r (RAA i0 i1) = RAA (r i0) (r i1)"
| "renumberJust r (DN i0) = DN (r i0)"
| "renumberJust r (BotI i0 i1) = BotI (r i0) (r i1)"
| "renumberJust r (AndIntro i0 i1) = AndIntro (r i0) (r i1)"
| "renumberJust r (AndElimL i0) = AndElimL (r i0)"
| "renumberJust r (AndElimR i0) = AndElimR (r i0)"
| "renumberJust r (OrIntroL i0) = OrIntroL (r i0)"
| "renumberJust r (OrIntroR i0) = OrIntroR (r i0)"
| "renumberJust r (OrElim i0 i1 i2 i3 i4) = OrElim (r i0) (r i1) (r i2) (r i3) (r i4)"
| "renumberJust r (IffIntro i0 i1) = IffIntro (r i0) (r i1)"
| "renumberJust r (IffElimL i0) = IffElimL (r i0)"
| "renumberJust r (IffElimR i0) = IffElimR (r i0)"
| "renumberJust r (ForallElim i0) = ForallElim (r i0)"
| "renumberJust r (ForallIntro i0) = ForallIntro (r i0)"
| "renumberJust r (ExistsIntro i0) = ExistsIntro (r i0)"
| "renumberJust r (ExistsElim i0 i1 i2) = ExistsElim (r i0) (r i1) (r i2)"
| "renumberJust r EqIntro = EqIntro"
| "renumberJust r (EqElim i0 i1) = EqElim (r i0) (r i1)"
| "renumberJust r (Reit i0) = Reit (r i0)"

lemma dischargePairs_renumber:
  "dischargePairs (renumberJust r j) = map (\<lambda>ac. (r (fst ac), r (snd ac))) (dischargePairs j)"
  by (cases j) auto

definition relabel :: "(nat \<Rightarrow> nat) \<Rightarrow> pline \<Rightarrow> pline" where
  "relabel r l = ProofLine (r (lineNumber l)) (formula l)
                   (renumberJust r (justification l)) (r ` references l)"

definition permuteProof :: "(nat \<Rightarrow> nat) \<Rightarrow> lemmon_proof \<Rightarrow> lemmon_proof" where
  "permuteProof r P = sort_key lineNumber (map (relabel r) P)"

lemma set_permuteProof: "set (permuteProof r P) = relabel r ` set P"
  by (simp add: permuteProof_def)

text \<open>Sharing a discharge is a property of the proof, not of the page: renaming
  the lines cannot destroy it.\<close>

lemma sharedDischarge_permute:
  assumes sh: "sharedDischarge P" and r: "inj r"
  shows "sharedDischarge (permuteProof r P)"
proof -
  from sh obtain l1 l2 a b c
    where l1: "l1 \<in> set P" and l2: "l2 \<in> set P"
      and p1: "(a, c) \<in> set (dischargePairs (justification l1))"
      and p2: "(b, c) \<in> set (dischargePairs (justification l2))"
      and ab: "a \<noteq> b"
    unfolding sharedDischarge_def by blast
  have m1: "relabel r l1 \<in> set (permuteProof r P)" using l1 by (simp add: set_permuteProof)
  have m2: "relabel r l2 \<in> set (permuteProof r P)" using l2 by (simp add: set_permuteProof)
  from p1 have q1: "(r a, r c) \<in> set (dischargePairs (justification (relabel r l1)))"
    by (force simp: relabel_def dischargePairs_renumber)
  from p2 have q2: "(r b, r c) \<in> set (dischargePairs (justification (relabel r l2)))"
    by (force simp: relabel_def dischargePairs_renumber)
  from ab r have "r a \<noteq> r b" by (simp add: inj_eq)
  with m1 m2 q1 q2 show ?thesis unfolding sharedDischarge_def by blast
qed

section \<open>The counterexample\<close>

text \<open>Five lines.  Both @{term "CP"} steps discharge from line 3: the first
  discharges assumption 1, the second assumption 2.  Nothing in the Lemmon
  notation objects --- line 3 is a line, and both discharges are legitimate uses
  of it --- but a Fitch proof would need two subproofs both ending at line 3, and
  the outer one would then end in a subproof rather than a line.

  Note what the proof is \emph{not}.  It is not the discharge-order obstruction of
  Example 11, whose boxes overlap; here the boxes @{term "(1::nat, 3::nat)"} and
  @{term "(2::nat, 3::nat)"} nest.  Nor is it the trapping of Example 12; no line
  is stranded inside a box it does not belong to.  It is a third thing.\<close>

definition c27 :: lemmon_proof where
  "c27 =
     [ ProofLine 1 Pf Assumption {1}
     , ProofLine 2 Qf Assumption {2}
     , ProofLine 3 (Conj Pf Qf) (AndIntro 1 2) {1, 2}
     , ProofLine 4 (Impl Pf (Conj Pf Qf)) (CP 1 3) {2}
     , ProofLine 5 (Impl Qf (Conj Pf Qf)) (CP 2 3) {1} ]"

lemma c27_correct: "lemmonCorrect c27"
  by eval

lemma c27_shared: "sharedDischarge c27"
proof -
  have l4: "ProofLine 4 (Impl Pf (Conj Pf Qf)) (CP 1 3) {2} \<in> set c27"
    by (simp add: c27_def)
  have l5: "ProofLine 5 (Impl Qf (Conj Pf Qf)) (CP 2 3) {1} \<in> set c27"
    by (simp add: c27_def)
  have d4: "(1, 3) \<in> set (dischargePairs (justification
              (ProofLine 4 (Impl Pf (Conj Pf Qf)) (CP 1 3) {2})))" by simp
  have d5: "(2, 3) \<in> set (dischargePairs (justification
              (ProofLine 5 (Impl Qf (Conj Pf Qf)) (CP 2 3) {1})))" by simp
  have "(1 :: nat) \<noteq> 2" by simp
  with l4 l5 d4 d5 show ?thesis unfolding sharedDischarge_def by blast
qed

text \<open>No renumbering of the five lines --- in particular no permutation under
  which a line still follows the lines it cites --- yields a proof with a
  positional Fitch image.\<close>

theorem no_permutation_of_c27_works:
  assumes "inj r"
  shows "\<not> (\<exists>F. fitchWF F \<and> positionalImage F (permuteProof r c27))"
  by (rule sharedDischarge_no_positional_image,
      rule sharedDischarge_permute [OF c27_shared assms])

corollary c27_no_positional_image:
  "\<not> (\<exists>F. fitchWF F \<and> positionalImage F c27)"
  by (rule sharedDischarge_no_positional_image [OF c27_shared])

section \<open>Conjecture 27\<close>

text \<open>\textbf{Conjecture 27.}  ``Every correct Lemmon proof can be permuted ---
  preserving the requirement that a line follow the lines it cites --- into one
  with a positional Fitch image.''

  Written out: for every correct Lemmon proof @{term P} there is an injective
  renumbering @{term r} of its lines such that @{term "permuteProof r P"} is again
  a correct Lemmon proof, and some Fitch proof is a positional image of it.

  The side condition of the conjecture --- that a line still follow the lines it
  cites --- needs no separate clause.  A Lemmon check looks a citation up among
  the lines already passed (@{const checkFrom_gen} extends its context line by
  line), so a permutation violating it does not yield a correct Lemmon proof, and
  @{term "lemmonCorrect (permuteProof r P)"} says exactly what the conjecture
  asks.  We do not use the clause anyway: the refutation below rules out every
  injective renumbering, admissible or not.\<close>

theorem conjecture_27_false:
  "\<not> (\<forall>P. lemmonCorrect P \<longrightarrow>
            (\<exists>r. inj r \<and> lemmonCorrect (permuteProof r P) \<and>
                 (\<exists>F. fitchWF F \<and> positionalImage F (permuteProof r P))))"
proof
  assume C: "\<forall>P. lemmonCorrect P \<longrightarrow>
               (\<exists>r. inj r \<and> lemmonCorrect (permuteProof r P) \<and>
                    (\<exists>F. fitchWF F \<and> positionalImage F (permuteProof r P)))"
  from C c27_correct obtain r
    where r: "inj r"
      and F: "\<exists>F. fitchWF F \<and> positionalImage F (permuteProof r c27)" by blast
  from no_permutation_of_c27_works [OF r] F show False by blast
qed

section \<open>Direct-translation diagnostics\<close>

text \<open>None of the three obstructions of Section 4 detects this.  @{const nestingError}
  sees two nested boxes; @{const premiseError} sees no undischarged assumption;
  and @{const scopeError} inspects only @{const fCitedLines}, which is empty for a
  discharging rule --- the pair a discharging rule names is a @{const fCitedSubs},
  and none of the three looks at those.\<close>

lemma c27_passes_the_three:
  "nestingError c27 = None" "premiseError c27 = None" "scopeError c27 = None"
  by eval+

text \<open>The unchecked layout candidate is useful to inspect: it is what
  @{const buildItems} makes of the boxes, and it is not a Fitch proof.\<close>

lemma c27_image_would_be_malformed:
  "\<not> fitchWF (buildItems (boxesOf c27) c27)"
  "fitchWellFormed (buildItems (boxesOf c27) c27)
     = Some (STR ''a subproof does not end in a line'')"
  by eval+

text \<open>@{const subScopeError} checks that a cited subproof sits at the level of
  the line citing it.  The direct translation therefore rejects @{const c27},
  naming the line, the subproof's conclusion, and the box that closed over it.\<close>

lemma c27_rejected:
  "lemmonToFitchDirect c27 = Inl (OutOfScope 5 3 2)"
  by eval

section \<open>All four orderings, by evaluation\<close>

text \<open>The abstract argument above already settles every renumbering.  For the
  reader who would rather see it, line 3 must follow lines 1 and 2, and lines 4
  and 5 must follow line 3, so there are exactly four orderings under which a line
  follows the lines it cites.  Each is a correct Lemmon proof; each passes the
  three obstructions of Section 4; and each is caught only by
  @{const subScopeError}.\<close>

definition c27_orders :: "lemmon_proof list" where
  "c27_orders =
     [ c27
     , [ ProofLine 1 Pf Assumption {1}
       , ProofLine 2 Qf Assumption {2}
       , ProofLine 3 (Conj Pf Qf) (AndIntro 1 2) {1, 2}
       , ProofLine 4 (Impl Qf (Conj Pf Qf)) (CP 2 3) {1}
       , ProofLine 5 (Impl Pf (Conj Pf Qf)) (CP 1 3) {2} ]
     , [ ProofLine 1 Qf Assumption {1}
       , ProofLine 2 Pf Assumption {2}
       , ProofLine 3 (Conj Pf Qf) (AndIntro 2 1) {1, 2}
       , ProofLine 4 (Impl Pf (Conj Pf Qf)) (CP 2 3) {1}
       , ProofLine 5 (Impl Qf (Conj Pf Qf)) (CP 1 3) {2} ]
     , [ ProofLine 1 Qf Assumption {1}
       , ProofLine 2 Pf Assumption {2}
       , ProofLine 3 (Conj Pf Qf) (AndIntro 2 1) {1, 2}
       , ProofLine 4 (Impl Qf (Conj Pf Qf)) (CP 1 3) {2}
       , ProofLine 5 (Impl Pf (Conj Pf Qf)) (CP 2 3) {1} ] ]"

lemma c27_orders_correct: "list_all lemmonCorrect c27_orders"
  by eval

lemma c27_orders_boxes_nest:
  "list_all (\<lambda>P. nestingError P = None \<and> premiseError P = None \<and> scopeError P = None)
            c27_orders"
  by eval

lemma c27_orders_images_malformed:
  "list_all (\<lambda>P. \<not> fitchWF (buildItems (boxesOf P) P)) c27_orders"
  by eval

lemma c27_orders_rejected:
  "list_all (\<lambda>P. case lemmonToFitchDirect P of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False)
            c27_orders"
  by eval

section \<open>Conjecture 28\<close>

text \<open>\textbf{Conjecture 28.}  ``No translation requires duplication.  That is,
  every correct Lemmon proof has a Fitch image in which each line of the source
  occurs exactly once.''

  Written out: for every correct Lemmon proof @{term P} there is a correct Fitch
  proof carrying exactly the lines of @{term P} --- each with its number, its
  formula and the corresponding rule --- and carrying each of them once.  Nothing
  is said about the order, which is what distinguishes this from Conjecture 27:
  @{thm [source] positionalImage_noDuplication} says a positional image is in
  particular a duplication-free one, so Conjecture 28 asks for strictly less.

  It is false, and for the same reason.  The obstruction was never about where the
  lines are written; it is that two subproofs would have to close at one line, and
  reordering does not help because there is only one such line to close at.\<close>

theorem conjecture_28_false:
  "\<not> (\<forall>P. lemmonCorrect P \<longrightarrow> (\<exists>F. fitchCorrect F \<and> noDuplication F P))"
proof
  assume C: "\<forall>P. lemmonCorrect P \<longrightarrow> (\<exists>F. fitchCorrect F \<and> noDuplication F P)"
  from C c27_correct obtain F
    where cor: "fitchCorrect F" and nd: "noDuplication F c27" by blast
  from cor have "fitchWF F" by (simp add: fitchCorrect_def)
  moreover from nd have "fitchImage F c27" by (simp add: noDuplication_def)
  ultimately show False using sharedDischarge_no_image [OF c27_shared] by blast
qed

text \<open>The refutation does not even need the count: no Fitch proof carries exactly
  these five lines, however often it repeats them.\<close>

corollary c27_no_image_at_all:
  "\<not> (\<exists>F. fitchWF F \<and> fitchImage F c27)"
  by (rule sharedDischarge_no_image [OF c27_shared])

subsection \<open>The paper's own argument, and where it breaks\<close>

text \<open>Section 6.3 offers this in support of Conjecture 28: if @{term L} is cited by
  @{term M} under a non-discharging rule then \<open>\<Gamma>(L) \<subseteq> \<Gamma>(M)\<close>, so placing every
  line at the depth of the innermost assumption in its dependency set places
  @{term L} within @{term M}'s scope.  ``What this argument does not establish is
  that the resulting family of subproofs is laminar, which is what a Fitch proof
  requires, and we have not been able to settle whether it must be.''

  The counterexample settles it: the family need not be laminar, and @{const c27}
  is where it fails.  Under that construction the box for an assumption
  @{term a} holds the lines that depend on @{term a}.\<close>

definition dependents :: "lemmon_proof \<Rightarrow> nat \<Rightarrow> nat list" where
  "dependents P a = map lineNumber (filter (\<lambda>l. a \<in> references l) P)"

definition assumptionNums :: "lemmon_proof \<Rightarrow> nat set" where
  "assumptionNums P = lineNumber ` {l \<in> set P. justification l = Assumption}"

definition dependencyLaminar :: "lemmon_proof \<Rightarrow> bool" where
  "dependencyLaminar P \<longleftrightarrow>
     (\<forall>a \<in> assumptionNums P. \<forall>b \<in> assumptionNums P.
        set (dependents P a) \<subseteq> set (dependents P b) \<or>
        set (dependents P b) \<subseteq> set (dependents P a) \<or>
        set (dependents P a) \<inter> set (dependents P b) = {})"

lemma c27_dependents:
  "dependents c27 1 = [1, 3, 5]"
  "dependents c27 2 = [2, 3, 4]"
  by eval+

text \<open>Neither box contains the other, and they are not disjoint: line 3 depends on
  both assumptions, line 5 on the first alone and line 4 on the second alone.  So
  the family is not laminar, and the construction the paper proposes does not
  return a Fitch proof on this input.  The theorem above says more --- that no
  other placement of the same five lines returns one either.\<close>

lemma c27_not_laminar:
  "\<not> set (dependents c27 1) \<subseteq> set (dependents c27 2)"
  "\<not> set (dependents c27 2) \<subseteq> set (dependents c27 1)"
  "set (dependents c27 1) \<inter> set (dependents c27 2) \<noteq> {}"
  by (simp_all add: c27_dependents del: One_nat_def)

text \<open>Laminarity alone is not sufficient for an image.  In Example 12 the
  two assumption regions are disjoint: the first consists of lines 1, 3 and 6,
  and the second of lines 2 and 4.  The later use of line 3 after the second box
  closes is nevertheless the trapping obstruction of Theorem 10.\<close>

lemma ex12_dependents:
  "dependents ex12 1 = [1, 3, 6]"
  "dependents ex12 2 = [2, 4]"
  by eval+

lemma ex12_dependency_laminar: "dependencyLaminar ex12"
  by eval

subsection \<open>Auxiliary lines do not repair Conjecture 28\<close>

text \<open>@{const fitchImage} asks both that every source line occur in the Fitch
  proof and that every Fitch line come from the source.  To permit arbitrary
  auxiliary lines, retain only the first half.  Thus @{term "sourceCovered F P"}
  says that every numbered source line occurs with its formula and corresponding
  rule, while imposing no condition at all on additional target lines.\<close>

definition sourceCovered :: "fitch_proof \<Rightarrow> lemmon_proof \<Rightarrow> bool" where
  "sourceCovered F P \<longleftrightarrow>
     (\<forall>l \<in> set P. \<exists>fl \<in> set (flatten F). lineMatches fl l)"

lemma fitchImage_sourceCovered:
  "fitchImage F P \<Longrightarrow> sourceCovered F P"
  by (simp add: fitchImage_def sourceCovered_def)

lemma sourceCovered_line:
  assumes "sourceCovered F P" and "l \<in> set P"
  shows "\<exists>fl \<in> set (flatten F). lineMatches fl l"
  using assms unfolding sourceCovered_def by blast

text \<open>The shared-discharge obstruction uses only source coverage.  Extra
  lines cannot make two distinct subproofs have the same last line: the two
  source discharge rules still have to cite @{term "(a, c)"} and @{term
  "(b, c)"}, and well-formed Fitch syntax makes their assumptions equal.\<close>

theorem sharedDischarge_no_auxiliary_image:
  assumes sh: "sharedDischarge P"
  shows "\<not> (\<exists>F. fitchWF F \<and> sourceCovered F P)"
proof (rule notI, elim exE conjE)
  fix F assume wf: "fitchWF F" and img: "sourceCovered F P"
  from sh obtain l1 l2 a b c
    where l1: "l1 \<in> set P" and l2: "l2 \<in> set P"
      and p1: "(a, c) \<in> set (dischargePairs (justification l1))"
      and p2: "(b, c) \<in> set (dischargePairs (justification l2))"
      and ab: "a \<noteq> b"
    unfolding sharedDischarge_def by blast
  from p1 have j1: "justification l1 \<noteq> Assumption"
    by (cases "justification l1") auto
  from p2 have j2: "justification l2 \<noteq> Assumption"
    by (cases "justification l2") auto
  from sourceCovered_line [OF img l1] obtain fl1
    where m1: "fl1 \<in> set (flatten F)" and lm1: "lineMatches fl1 l1" by blast
  from lm1 j1 have r1: "flRule fl1 = toFitchRule (justification l1)"
    unfolding lineMatches_def using ruleMatches_not_assumption by blast
  from sourceCovered_line [OF img l2] obtain fl2
    where m2: "fl2 \<in> set (flatten F)" and lm2: "lineMatches fl2 l2" by blast
  from lm2 j2 have r2: "flRule fl2 = toFitchRule (justification l2)"
    unfolding lineMatches_def using ruleMatches_not_assumption by blast
  from p1 r1 have "(a, c) \<in> set (fCitedSubs (flRule fl1))"
    by (simp add: fCitedSubs_toFitchRule)
  from citationOK_subs [OF wf m1 this]
  have s1: "((a, c), flScope fl1) \<in> set (subrefs F)" .
  from p2 r2 have "(b, c) \<in> set (fCitedSubs (flRule fl2))"
    by (simp add: fCitedSubs_toFitchRule)
  from citationOK_subs [OF wf m2 this]
  have s2: "((b, c), flScope fl2) \<in> set (subrefs F)" .
  from subrefs_same_last [OF wf s1 s2] ab show False by simp
qed

corollary c27_no_auxiliary_image:
  "\<not> (\<exists>F. fitchWF F \<and> sourceCovered F c27)"
  by (rule sharedDischarge_no_auxiliary_image [OF c27_shared])

theorem conjecture_28_with_auxiliaries_false:
  "\<not> (\<forall>P. lemmonCorrect P \<longrightarrow>
          (\<exists>F. fitchCorrect F \<and> sourceCovered F P))"
proof
  assume C: "\<forall>P. lemmonCorrect P \<longrightarrow>
               (\<exists>F. fitchCorrect F \<and> sourceCovered F P)"
  from C c27_correct obtain F
    where cor: "fitchCorrect F" and cov: "sourceCovered F c27" by blast
  from cor have "fitchWF F" by (simp add: fitchCorrect_def)
  with cov c27_no_auxiliary_image show False by blast
qed

text \<open>This result permits auxiliary lines without restricting their formulas,
  rules, or number.  What remains essential is that a source line is represented
  with its own citation-bearing rule.  A different notion that allows a
  translation to rewrite those citations is not the claim formalized by
  Definition 9 or by @{const fitchImage}; it would require a separate mapping
  from source occurrences to target derivations.\<close>

end
