(*  Title:      LF_HLW_Examples.thy

    The paper's worked examples, in the exact hl_* datatypes of
    LF_HLW_Formula.thy/LF_HLW.thy/LF_HLW_Fitch.thy.  These
    are the same examples LF_Examples.thy checks against the compact fm/just
    layer; here they are checked against the authoritative Haskell-shaped
    checker instead.
*)

theory LF_HLW_Examples
  imports LF_HLW_Unfold
begin

section \<open>Shared vocabulary\<close>

abbreviation hlR :: hl_formula where "hlR \<equiv> HL_Predicate (STR ''R'') []"
abbreviation hlPredG :: "hl_term \<Rightarrow> hl_formula" where
  "hlPredG t \<equiv> HL_Predicate (STR ''G'') [t]"
abbreviation hly :: hl_name where "hly \<equiv> STR ''y''"

definition hl_allx_G :: hl_formula where "hl_allx_G = (\<forall>\<^sub>H hlx. hlPredG (HL_Var hlx))"
definition hl_ally_G :: hl_formula where "hl_ally_G = (\<forall>\<^sub>H hly. hlPredG (HL_Var hly))"

section \<open>Section 2: the running example\<close>

definition hl_sec2_lemmon :: hl_proof where
  "hl_sec2_lemmon =
     [ HL_ProofLine 1 hlP HL_Assumption {1},
       HL_ProofLine 2 hlQ HL_Assumption {2},
       HL_ProofLine 3 (hlP \<and>\<^sub>H hlQ) (HL_AndIntro 1 2) {1,2},
       HL_ProofLine 4 (hlQ \<longrightarrow>\<^sub>H (hlP \<and>\<^sub>H hlQ)) (HL_CP 2 3) {1} ]"

definition hl_sec2_fitch :: hl_fitch_proof where
  "hl_sec2_fitch =
     [ HL_FLine 1 hlP HL_FPremise,
       HL_FSub (HL_Subproof 2 hlQ
         [HL_FLine 3 (hlP \<and>\<^sub>H hlQ) (HL_FAndI 1 2)]),
       HL_FLine 4 (hlQ \<longrightarrow>\<^sub>H (hlP \<and>\<^sub>H hlQ)) (HL_FCP (2,3)) ]"

section \<open>Example 11: discharge order\<close>

definition hl_ex11 :: hl_proof where
  "hl_ex11 =
     [ HL_ProofLine 1 hlP HL_Assumption {1},
       HL_ProofLine 2 hlQ HL_Assumption {2},
       HL_ProofLine 3 (hlP \<and>\<^sub>H hlQ) (HL_AndIntro 1 2) {1,2},
       HL_ProofLine 4 (hlP \<longrightarrow>\<^sub>H (hlP \<and>\<^sub>H hlQ)) (HL_CP 1 3) {2},
       HL_ProofLine 5 (hlQ \<longrightarrow>\<^sub>H (hlP \<longrightarrow>\<^sub>H (hlP \<and>\<^sub>H hlQ))) (HL_CP 2 4) {} ]"

section \<open>Example 12: positional trapping\<close>

definition hl_ex12 :: hl_proof where
  "hl_ex12 =
     [ HL_ProofLine 1 hlP HL_Assumption {1},
       HL_ProofLine 2 hlQ HL_Assumption {2},
       HL_ProofLine 3 (hlP \<or>\<^sub>H hlR) (HL_OrIntro 1) {1},
       HL_ProofLine 4 (hlQ \<and>\<^sub>H hlQ) (HL_AndIntro 2 2) {2},
       HL_ProofLine 5 (hlQ \<longrightarrow>\<^sub>H (hlQ \<and>\<^sub>H hlQ)) (HL_CP 2 4) {},
       HL_ProofLine 6 ((hlP \<or>\<^sub>H hlR) \<and>\<^sub>H (hlQ \<longrightarrow>\<^sub>H (hlQ \<and>\<^sub>H hlQ))) (HL_AndIntro 3 5) {1} ]"

section \<open>Theorem 22: the eigenvariable proof\<close>

definition hl_thm22_lemmon :: hl_proof where
  "hl_thm22_lemmon =
     [ HL_ProofLine 1 hl_allx_G HL_Assumption {1},
       HL_ProofLine 2 (hlPredF (HL_Const hla)) HL_Assumption {2},
       HL_ProofLine 3 (hlPredG (HL_Const hla)) (HL_ForallElim 1) {1},
       HL_ProofLine 4 hl_ally_G (HL_ForallIntro 3) {1},
       HL_ProofLine 5 (hlPredF (HL_Const hla) \<and>\<^sub>H hl_ally_G) (HL_AndIntro 2 4) {1,2},
       HL_ProofLine 6 (hlPredF (HL_Const hla) \<longrightarrow>\<^sub>H (hlPredF (HL_Const hla) \<and>\<^sub>H hl_ally_G))
         (HL_CP 2 5) {1} ]"

definition hl_thm22_fitch_bad :: hl_fitch_proof where
  "hl_thm22_fitch_bad =
     [ HL_FLine 1 hl_allx_G HL_FPremise,
       HL_FSub (HL_Subproof 2 (hlPredF (HL_Const hla))
         [ HL_FLine 3 (hlPredG (HL_Const hla)) (HL_FForallE 1),
           HL_FLine 4 hl_ally_G (HL_FForallI 3),
           HL_FLine 5 (hlPredF (HL_Const hla) \<and>\<^sub>H hl_ally_G) (HL_FAndI 2 4) ]),
       HL_FLine 6 (hlPredF (HL_Const hla) \<longrightarrow>\<^sub>H (hlPredF (HL_Const hla) \<and>\<^sub>H hl_ally_G))
         (HL_FCP (2,5)) ]"

definition hl_thm22_fitch_good :: hl_fitch_proof where
  "hl_thm22_fitch_good =
     [ HL_FLine 1 hl_allx_G HL_FPremise,
       HL_FSub (HL_Subproof 2 (hlPredF (HL_Const hla))
         [ HL_FLine 3 (hlPredG (HL_Const hlb)) (HL_FForallE 1),
           HL_FLine 4 hl_ally_G (HL_FForallI 3),
           HL_FLine 5 (hlPredF (HL_Const hla) \<and>\<^sub>H hl_ally_G) (HL_FAndI 2 4) ]),
       HL_FLine 6 (hlPredF (HL_Const hla) \<longrightarrow>\<^sub>H (hlPredF (HL_Const hla) \<and>\<^sub>H hl_ally_G))
         (HL_FCP (2,5)) ]"

section \<open>What the examples show\<close>

subsection \<open>The examples are correct proofs\<close>

lemma hl_correct_sources:
  "hlVerifiedCorrect hl_sec2_lemmon"
  "hlVerifiedCorrect hl_ex11"
  "hlVerifiedCorrect hl_ex12"
  "hlVerifiedCorrect hl_thm22_lemmon"
  "hlFitchVerified hl_sec2_fitch"
  by eval+

subsection \<open>Section 2: the two notations agree\<close>

lemma hl_sec2_delta: "\<delta>\<^sub>H hl_sec2_fitch = hl_sec2_lemmon"
  by eval

lemma hl_sec2_roundtrip: "hlLemmonToFitchDirect hl_sec2_lemmon = Inr hl_sec2_fitch"
  by eval

subsection \<open>Theorem 10: two correct Lemmon proofs with no positional Fitch image\<close>

lemma hl_example_11_not_positional:
  "case hlLemmonToFitchDirect hl_ex11 of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False"
  by eval

lemma hl_example_12_not_positional:
  "case hlLemmonToFitchDirect hl_ex12 of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False"
  by eval

theorem hl_theorem_10:
  "hlVerifiedCorrect hl_ex11 \<and> (\<forall>F. hlLemmonToFitchDirect hl_ex11 \<noteq> Inr F)"
  "hlVerifiedCorrect hl_ex12 \<and> (\<forall>F. hlLemmonToFitchDirect hl_ex12 \<noteq> Inr F)"
  using hl_example_11_not_positional hl_example_12_not_positional hl_correct_sources
  by auto

subsection \<open>Theorem 22 and its Fitch images\<close>

text \<open>@{const hlFitchVerified} checks genuine nesting, an outermost
  conclusion, premise closure, and dependency-based validity of the erased
  Lemmon proof. It does not impose the stronger Fitch eigenconstant condition
  against every assumption in scope. The paper's bad line 4 has dependency
  \<open>{1}\<close>, while its actual enclosing assumptions are \<open>{1,2}\<close>:
  \<open>F(a)\<close> blocks generalisation. The weaker predicate still accepts it:\<close>

lemma hl_thm22_fitch_bad_currently_accepted: "hlFitchVerified hl_thm22_fitch_bad"
  by eval

text \<open>\<open>LF_HLW_Scope.thy\<close> defines the stronger scope-based
  @{const hlFitchCorrect}. It rejects this example, reproducing Theorem 22
  and refuting Theorem 4's converse; \<open>LF_HLW_Delta.thy\<close> records
  \<open>hl_theorem_4_backward_fails\<close>. No authoritative Lemmon rule changed.\<close>

lemma hl_renaming_repair: "hlFitchVerified hl_thm22_fitch_good"
  by eval

lemma hl_theorem_22_delta: "\<delta>\<^sub>H hl_thm22_fitch_bad = hl_thm22_lemmon"
  by eval

section \<open>Conjectures 27/28: the shared-discharge witness\<close>

text \<open>Two subproofs both closing at line 3: line 4 discharges assumption 1,
  line 5 discharges assumption 2, and both cite the same conclusion line.
  Section 6.3's two obstructions (Example 11's overlap, Example 12's
  trapping) are absent --- the boxes @{term "(1::int,3::int)"} and
  @{term "(2::int,3::int)"} nest --- so this is a \<^emph>\<open>third\<close> obstruction, the
  one \<open>LF_Conjecture27.thy\<close> uses to refute Conjectures 27 and 28.\<close>

definition hl_c27 :: hl_proof where
  "hl_c27 =
     [ HL_ProofLine 1 hlP HL_Assumption {1},
       HL_ProofLine 2 hlQ HL_Assumption {2},
       HL_ProofLine 3 (hlP \<and>\<^sub>H hlQ) (HL_AndIntro 1 2) {1,2},
       HL_ProofLine 4 (hlP \<longrightarrow>\<^sub>H (hlP \<and>\<^sub>H hlQ)) (HL_CP 1 3) {2},
       HL_ProofLine 5 (hlQ \<longrightarrow>\<^sub>H (hlP \<and>\<^sub>H hlQ)) (HL_CP 2 3) {1} ]"

lemma hl_c27_correct: "hlVerifiedCorrect hl_c27"
  by eval

text \<open>Caught by the same diagnostic and at the same numbers as the compact
  layer's @{text c27_rejected}: line 5's discharge box @{term "(2::int,3::int)"}
  is not at the level line 3 sits at, since line 3 is also the head of the box
  @{term "(1::int,3::int)"}.\<close>

lemma hl_c27_rejected: "hlLemmonToFitchDirect hl_c27 = Inl (HL_OutOfScope 5 3 2)"
  by eval

section \<open>What the soundness theorem does not cover\<close>

text \<open>@{thm [source] hlVerifiedCorrect_sound} is stated of
  @{const hlVerifiedCorrect}, which is @{const hlCorrect} --- the Haskell's own
  check --- together with @{const hlDependencyClosed} and
  @{const hlCanonicalOrder}.  So it is worth knowing whether those two extra
  invariants are ones the supplied checker actually enforces.
  @{const hlCanonicalOrder} is not: it demands that the line numbers increase
  down the list, and \<open>checkStructure\<close> compares a cited number with the citing
  line's number rather than checking physical order (finding 4 of the audit).

  The gap is therefore not empty, and this is a witness for it: the running
  @{const hl_cp_example} with its first two lines swapped in the list, the
  numbers left alone.\<close>

definition hl_cp_misordered :: hl_proof where
  "hl_cp_misordered =
     [ HL_ProofLine 2 hlQ HL_Assumption {2},
       HL_ProofLine 1 hlP HL_Assumption {1},
       HL_ProofLine 3 (hlP \<and>\<^sub>H hlQ) (HL_AndIntro 1 2) {1,2},
       HL_ProofLine 4 (hlQ \<longrightarrow>\<^sub>H (hlP \<and>\<^sub>H hlQ)) (HL_CP 2 3) {1} ]"

lemma hl_cp_misordered_accepted_but_unverified:
  "hlCorrect hl_cp_misordered"
  "\<not> hlVerifiedCorrect hl_cp_misordered"
  by eval+

text \<open>@{const hlCanonicalOrder} is the sole discriminator: the other added
  invariant holds of it.\<close>

lemma hl_cp_misordered_only_order_fails:
  "hlDependencyClosed hl_cp_misordered"
  "\<not> hlCanonicalOrder hl_cp_misordered"
  by eval+

text \<open>What this does \emph{not} show is unsoundness.  The witness is a perfectly
  good proof --- it has the same conclusion as @{const hl_cp_example}, and its
  dependency sets are honest, because the rule checker verified them wherever the
  lines happen to sit.  No proof is known that @{const hlCorrect} accepts and
  that is semantically invalid, and none is ruled out either: the sound direction
  is proved only for @{const hlVerifiedCorrect}.  Given how the fourth
  obstruction was found, that question should be settled by building a witness,
  not by arguing from the shape of the definitions.\<close>

lemma hl_cp_misordered_same_conclusion:
  "hlConclusion hl_cp_misordered = hlConclusion hl_cp_example"
  by eval

subsection \<open>The other added invariant\<close>

text \<open>@{const hlDependencyClosed} is extra too, and for a sharper reason.
  @{const hlRuleOK} fixes the dependency set in every branch but one:
  @{term HL_LEM} asks only that the formula be an instance of excluded middle
  and says nothing whatever about \<open>G\<close> (finding 5 of the audit; the freedom is
  @{thm [source] hl_LEM_preserves_legacy_dependency_behavior}).  So such a line
  may name anything, including a line that is not an assumption at all.\<close>

definition hl_lem_free_dependency :: hl_proof where
  "hl_lem_free_dependency =
     [ HL_ProofLine 1 hlP HL_Assumption {1},
       HL_ProofLine 2 (hlQ \<or>\<^sub>H \<not>\<^sub>H hlQ) HL_LEM {2} ]"

lemma hl_lem_free_dependency_accepted_but_unverified:
  "hlCorrect hl_lem_free_dependency"
  "\<not> hlVerifiedCorrect hl_lem_free_dependency"
  by eval+

text \<open>This witness isolates @{const hlDependencyClosed} exactly as
  @{const hl_cp_misordered} isolates @{const hlCanonicalOrder}: neither added
  invariant follows from @{const hlCorrect}.\<close>

lemma hl_lem_free_dependency_only_closure_fails:
  "hlCanonicalOrder hl_lem_free_dependency"
  "\<not> hlDependencyClosed hl_lem_free_dependency"
  by eval+

text \<open>It is not an unsoundness.  Line 2's dependency set names line 2, which is
  not an assumption, so @{const hlOpenPremises} drops it and the proof reports no
  premises at all --- but what it concludes is a tautology.\<close>

lemma hl_lem_free_dependency_sequent:
  "hlOpenPremises hl_lem_free_dependency = []"
  "hlConclusion hl_lem_free_dependency = Some (hlQ \<or>\<^sub>H \<not>\<^sub>H hlQ)"
  by eval+

lemma hl_lem_free_dependency_conclusion_valid:
  "hlSatisfies M assignment (hlQ \<or>\<^sub>H \<not>\<^sub>H hlQ)"
  by simp

text \<open>The freedom survives @{const hlVerifiedCorrect} whenever the invented
  numbers happen to belong to assumption lines, which says what
  @{const hlDependencyClosed} does and does not buy: it constrains where a
  number comes from, not whether the line earned it.  Here line 3 claims to
  depend on both assumptions and line 4 discharges one of them.\<close>

definition hl_lem_inflated :: hl_proof where
  "hl_lem_inflated =
     [ HL_ProofLine 1 hlP HL_Assumption {1},
       HL_ProofLine 2 hlQ HL_Assumption {2},
       HL_ProofLine 3 (hlQ \<or>\<^sub>H \<not>\<^sub>H hlQ) HL_LEM {1,2},
       HL_ProofLine 4 (hlP \<longrightarrow>\<^sub>H (hlQ \<or>\<^sub>H \<not>\<^sub>H hlQ)) (HL_CP 1 3) {2} ]"

lemma hl_lem_inflated_fully_verified: "hlVerifiedCorrect hl_lem_inflated"
  by eval

lemma hl_lem_inflated_reports_a_premise: "hlOpenPremises hl_lem_inflated = [hlQ]"
  by eval

lemma hl_lem_inflated_conclusion_valid:
  "hlSatisfies M assignment (hlP \<longrightarrow>\<^sub>H (hlQ \<or>\<^sub>H \<not>\<^sub>H hlQ))"
  by simp

subsection \<open>Why no unsoundness was found, and what is still open\<close>

text \<open>Both added invariants are therefore genuinely extra, and neither witness
  above is unsound.  Reading @{const hlRuleOK} branch by branch says why the
  obvious attacks fail.

  Every branch except @{term HL_LEM} determines \<open>G\<close> from the cited lines --- as
  \<open>{n}\<close> for an assumption, as \<open>{}\<close> for @{term HL_EqIntro}, and otherwise as a
  union of the cited lines' sets.  @{term HL_LEM} leaves \<open>G\<close> free, but its
  formula is valid, so a free set can only make the reported premises
  \emph{larger}, and a sequent with more premises is a weaker claim.  And the
  only subtractions anywhere --- @{term HL_CP}, @{term HL_RAA}, the two branches
  of @{term HL_OrElim}, and @{term HL_ExistsElim} --- remove exactly the number
  of a line the checker separately requires to be an assumption, whose formula
  reappears in the conclusion as an antecedent, a negation, a case hypothesis or
  a witness.  So no rule lets a dependency that was really used go unreported.

  That is an argument, not a proof.  @{thm [source] hlVerifiedCorrect_sound} is still
  proved only of @{const hlVerifiedCorrect}, and whether @{const hlCorrect} alone
  is sound is open.  The fourth obstruction of \<open>LF_Positional.thy\<close> is the
  standing reason not to settle a question of this shape by argument: the claim
  that \<open>scopeError\<close> must catch a shared discharge was of exactly this
  form, and it was false.\<close>


end
