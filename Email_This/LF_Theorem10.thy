(*  Title:      LF_Theorem10.thy

    Theorem 10 of the paper, as the paper states it.

    LF_Examples proves that the checker rejects Examples 11 and 12.  That is a
    fact about the implementation, and --- since the checker turned out to accept
    sources with no image (see LF_Conjecture27) --- it is strictly weaker than the
    paper's claim, which is that no Fitch proof whatever is a positional image of
    them.  With the span theorem the claim itself is provable.
*)

theory LF_Theorem10
  imports LF_Conjecture27 LF_Span
begin

section \<open>Reading a Fitch proof's citations\<close>

lemma citationOK_lines:
  assumes "fitchWF F" and "fl \<in> set (flatten F)"
      and "m \<in> set (fCitedLines (flRule fl))"
  shows "\<exists>fl'. findFL (flatten F) m = Some fl' \<and> is_prefix (flScope fl') (flScope fl)"
proof -
  from assms(1,2) have "citationOK F fl" by (auto simp: fitchWF_def list_all_iff)
  with assms(3) show ?thesis
    unfolding citationOK_def by (auto simp: list_all_iff split: option.splits)
qed

text \<open>A discharging line of the source names a subproof of any image.\<close>

lemma image_subproof:
  assumes wf: "fitchWF F" and img: "fitchImage F P"
      and l: "l \<in> set P" and jl: "justification l \<noteq> Assumption"
      and d: "(a, c) \<in> set (dischargePairs (justification l))"
  shows "\<exists>s q. (s, q) \<in> set (subs F) \<and> subAssumeLine s = a \<and> subLastLine s = c"
proof -
  from fitchImage_line [OF img l] obtain fl
    where m: "fl \<in> set (flatten F)" and lm: "lineMatches fl l" by blast
  from lm jl have r: "flRule fl = toFitchRule (justification l)"
    unfolding lineMatches_def using ruleMatches_not_assumption by blast
  from d r have "(a, c) \<in> set (fCitedSubs (flRule fl))"
    by (simp add: fCitedSubs_toFitchRule)
  from citationOK_subs [OF wf m this] have "((a, c), flScope fl) \<in> set (subrefs F)" .
  from subrefs_subs_proof [OF this] show ?thesis by blast
qed

section \<open>Example 11: the discharges do not nest\<close>

text \<open>Assumption 1 is made first and discharged first.  In an image, the subproof
  discharged at line 4 runs from line 1 to line 3 and the one discharged at line 5
  from line 2 to line 4.  Line 2 then lies inside the first, so its scope extends
  the first's path; line 3 lies inside the second, so its scope extends the
  second's.  But line 2 is the assumption line of the second and line 3 the last
  line of the first, so those two scopes are the two paths themselves --- each an
  extension of the other, hence equal, hence \<open>1 = 2\<close>.\<close>

theorem theorem_10_ex11: "\<not> (\<exists>F. fitchWF F \<and> fitchImage F ex11)"
proof (rule notI, elim exE conjE)
  fix F assume wf: "fitchWF F" and img: "fitchImage F ex11"
  define L4 where "L4 = ProofLine 4 (Impl Pf (Conj Pf Qf)) (CP 1 3) {2}"
  define L5 where "L5 = ProofLine 5 (Impl Qf (Impl Pf (Conj Pf Qf))) (CP 2 4) {}"
  have l4: "L4 \<in> set ex11" by (simp add: ex11_def L4_def)
  have l5: "L5 \<in> set ex11" by (simp add: ex11_def L5_def)
  have j4: "justification L4 \<noteq> Assumption" by (simp add: L4_def)
  have j5: "justification L5 \<noteq> Assumption" by (simp add: L5_def)
  have d4: "(1, 3) \<in> set (dischargePairs (justification L4))" by (simp add: L4_def)
  have d5: "(2, 4) \<in> set (dischargePairs (justification L5))" by (simp add: L5_def)
  from image_subproof [OF wf img l4 j4 d4] obtain s1 p1
    where s1: "(s1, p1) \<in> set (subs F)" "subAssumeLine s1 = 1" "subLastLine s1 = 3"
    by blast
  from image_subproof [OF wf img l5 j5 d5] obtain s2 p2
    where s2: "(s2, p2) \<in> set (subs F)" "subAssumeLine s2 = 2" "subLastLine s2 = 4"
    by blast
  from subs_subrefs_proof [OF s1(1)] s1(2,3)
  have r1: "((1, 3), p1) \<in> set (subrefs F)" by simp
  from subs_subrefs_proof [OF s2(1)] s2(2,3)
  have r2: "((2, 4), p2) \<in> set (subrefs F)" by simp
  from subrefs_lines [OF wf r1] obtain f3 rr3
    where e3: "FL 3 f3 rr3 (p1 @ [1]) \<in> set (flatten F)" by blast
  from subrefs_lines [OF wf r2] obtain f2
    where e2: "FL 2 f2 FAssume (p2 @ [2]) \<in> set (flatten F)" by blast
  from subs_span [OF wf s1(1) e2] s1(2,3)
  have A: "is_prefix (p1 @ [1]) (p2 @ [2])" by simp
  from subs_span [OF wf s2(1) e3] s2(2,3)
  have B: "is_prefix (p2 @ [2]) (p1 @ [1])" by simp
  from is_prefix_antisym [OF A B] show False by simp
qed

section \<open>Example 12: a line trapped inside a subproof it does not depend on\<close>

text \<open>Line 3 is written between assumption 2 and its discharge at 5, so in any
  image it lies inside that subproof --- its dependency set does not matter.  Line
  6 cites it, so line 6's scope extends line 3's, hence the subproof's; but line 6
  is numbered past the subproof's last line, and the span theorem says a line whose
  scope extends that path is numbered within it.\<close>

theorem theorem_10_ex12: "\<not> (\<exists>F. fitchWF F \<and> fitchImage F ex12)"
proof (rule notI, elim exE conjE)
  fix F assume wf: "fitchWF F" and img: "fitchImage F ex12"
  define L5 where "L5 = ProofLine 5 (Impl Qf (Conj Qf Qf)) (CP 2 4) {}"
  define L6 where
    "L6 = ProofLine 6 (Conj (Disj Pf Rf) (Impl Qf (Conj Qf Qf))) (AndIntro 3 5) {1}"
  have l5: "L5 \<in> set ex12" by (simp add: ex12_def L5_def)
  have l6: "L6 \<in> set ex12" by (simp add: ex12_def L6_def)
  have j5: "justification L5 \<noteq> Assumption" by (simp add: L5_def)
  have j6: "justification L6 \<noteq> Assumption" by (simp add: L6_def)
  have d5: "(2, 4) \<in> set (dischargePairs (justification L5))" by (simp add: L5_def)
  from image_subproof [OF wf img l5 j5 d5] obtain s p
    where s: "(s, p) \<in> set (subs F)" "subAssumeLine s = 2" "subLastLine s = 4"
    by blast
  from fitchImage_line [OF img l6] obtain fl6
    where m6: "fl6 \<in> set (flatten F)" and lm6: "lineMatches fl6 L6" by blast
  from lm6 have n6: "flNum fl6 = 6" by (simp add: lineMatches_def L6_def)
  from lm6 have "ruleMatches (AndIntro 3 5) (flRule fl6)"
    by (simp add: lineMatches_def L6_def)
  then have r6: "flRule fl6 = FAndIntro 3 5" by (simp add: ruleMatches_def)
  have "3 \<in> set (fCitedLines (flRule fl6))" using r6 by simp
  from citationOK_lines [OF wf m6 this] obtain fl3
    where f3: "findFL (flatten F) 3 = Some fl3"
      and pre: "is_prefix (flScope fl3) (flScope fl6)" by blast
  from findFL_Some [OF f3] have n3: "flNum fl3 = 3" and m3: "fl3 \<in> set (flatten F)" by auto
  from subs_span [OF wf s(1) m3] s(2,3) n3
  have "is_prefix (p @ [2]) (flScope fl3)" by simp
  from is_prefix_trans [OF this pre] have "is_prefix (p @ [2]) (flScope fl6)" .
  with subs_span [OF wf s(1) m6] s(2,3) n6 show False by simp
qed

text \<open>A laminar dependency family does not guarantee an image preserving
  the original numbering and order. Example 12 has a laminar family but no
  such image. This theorem uses the fixed-number relation @{const fitchImage};
  it does not rule out a repairing permutation. The original Remark 13
  explicitly gives such a permutation for Example 12.\<close>

theorem dependency_laminar_not_sufficient:
  "\<not> (\<forall>P. lemmonCorrect P \<and> dependencyLaminar P \<longrightarrow>
          (\<exists>F. fitchWF F \<and> noDuplication F P))"
proof
  assume C: "\<forall>P. lemmonCorrect P \<and> dependencyLaminar P \<longrightarrow>
               (\<exists>F. fitchWF F \<and> noDuplication F P)"
  from C correct_sources(3) ex12_dependency_laminar obtain F
    where wf: "fitchWF F" and nd: "noDuplication F ex12" by blast
  from nd have "fitchImage F ex12" by (simp add: noDuplication_def)
  with wf theorem_10_ex12 show False by blast
qed

section \<open>Theorem 10\<close>

text \<open>``There are correct Lemmon proofs with no positional Fitch image.''  Both
  examples are correct Lemmon proofs, and neither has a Fitch image at all ---
  positional or otherwise --- so in particular neither has a positional one.\<close>

theorem theorem_10:
  "lemmonCorrect ex11 \<and> \<not> (\<exists>F. fitchWF F \<and> positionalImage F ex11)"
  "lemmonCorrect ex12 \<and> \<not> (\<exists>F. fitchWF F \<and> positionalImage F ex12)"
  using correct_sources theorem_10_ex11 theorem_10_ex12 positionalImage_fitchImage
  by blast+

section \<open>The remaining two rejections also have no image\<close>

text \<open>With @{const premLate} settled, six of the seven checks reject only
  sources that genuinely have no well-formed positional image.  The last two ---
  @{const boxOrderError} and @{const boxHeadError} --- follow from one fact each
  about the subproofs of an image.

  First: a cited subproof runs forwards.  Its assumption line lies in its own
  span, and @{thm [source] subs_span} bounds that span by the subproof's first
  and last lines.\<close>

lemma image_subproof_ordered:
  assumes wf: "fitchWF F" and img: "fitchImage F P"
      and l: "l \<in> set P" and jl: "justification l \<noteq> Assumption"
      and d: "(a, c) \<in> set (dischargePairs (justification l))"
  shows "a \<le> c"
proof -
  from image_subproof [OF wf img l jl d] obtain s q
    where sq: "(s, q) \<in> set (subs F)" and A: "subAssumeLine s = a"
      and C: "subLastLine s = c" by blast
  from subs_subrefs_proof [OF sq] A C have sr: "((a, c), q) \<in> set (subrefs F)" by simp
  from subrefs_lines [OF wf sr] obtain f
    where fl: "FL a f FAssume (q @ [a]) \<in> set (flatten F)" by blast
  have "is_prefix (q @ [subAssumeLine s]) (flScope (FL a f FAssume (q @ [a])))"
    using A by simp
  with subs_span [OF wf sq fl] A C show ?thesis by simp
qed

theorem backCP_no_positional_image:
  "\<not> (\<exists>F. fitchWF F \<and> positionalImage F backCP)"
proof (rule notI, elim exE conjE)
  fix F assume wf: "fitchWF F" and img: "positionalImage F backCP"
  define L3 where "L3 = ProofLine 3 (Impl Qf Pf) (CP 2 1) {1}"
  have l: "L3 \<in> set backCP" by (simp add: L3_def backCP_def)
  have jl: "justification L3 \<noteq> Assumption" by (simp add: L3_def)
  have d: "(2, 1) \<in> set (dischargePairs (justification L3))" by (simp add: L3_def)
  from image_subproof_ordered [OF wf positionalImage_fitchImage [OF img] l jl d]
  show False by simp
qed

text \<open>Second: a subproof is determined by its assumption line
  (@{thm [source] subs_unique_proof}), so one assumption cannot head two
  subproofs closing at different lines.\<close>

theorem reused_no_positional_image:
  "\<not> (\<exists>F. fitchWF F \<and> positionalImage F reused)"
proof (rule notI, elim exE conjE)
  fix F assume wf: "fitchWF F" and img: "positionalImage F reused"
  note fimg = positionalImage_fitchImage [OF img]
  define L5 where "L5 = ProofLine 5 (Impl Qf (Conj Pf Qf)) (CP 2 3) {1}"
  define L6 where "L6 = ProofLine 6 (Impl Qf (Disj Pf Rf)) (CP 2 4) {1}"
  have l5: "L5 \<in> set reused" by (simp add: L5_def reused_def)
  have l6: "L6 \<in> set reused" by (simp add: L6_def reused_def)
  from image_subproof [OF wf fimg l5 _ _] obtain s q
    where sq: "(s, q) \<in> set (subs F)" and A: "subAssumeLine s = 2"
      and C: "subLastLine s = 3" by (auto simp: L5_def)
  from image_subproof [OF wf fimg l6 _ _] obtain s' q'
    where sq': "(s', q') \<in> set (subs F)" and A': "subAssumeLine s' = 2"
      and C': "subLastLine s' = 4" by (auto simp: L6_def)
  from subs_unique_proof [OF fitchWF_distinct [OF wf] sq sq'] A A'
  have "s = s'" by simp
  with C C' show False by simp
qed


section \<open>Every check rejects only sources that have no image\<close>

text \<open>Collecting the six witnesses the seven checks were built from.  Each is a
  correct Lemmon proof that @{const lemmonToFitchDirect} rejects, and each is now
  known to have no well-formed positional Fitch image at all --- so on these
  sources the checker and the existence question agree exactly.

  This is evidence for the converse of @{thm [source]
  lemmonToFitchDirect_fitchWF}, not a proof of it: six sources are not all
  sources.  The counterexample that used to refute the converse was
  @{const premLate_fitch_alt}, and it fell to @{const concludesAtTop}.\<close>

theorem checks_reject_only_imageless_sources:
  "\<not> (\<exists>F. fitchWF F \<and> positionalImage F ex11)"
  "\<not> (\<exists>F. fitchWF F \<and> positionalImage F ex12)"
  "\<not> (\<exists>F. fitchWF F \<and> positionalImage F c27)"
  "\<not> (\<exists>F. fitchWF F \<and> positionalImage F premLate)"
  "\<not> (\<exists>F. fitchWF F \<and> positionalImage F backCP)"
  "\<not> (\<exists>F. fitchWF F \<and> positionalImage F reused)"
  using theorem_10 c27_no_positional_image premLate_no_positional_image
        backCP_no_positional_image reused_no_positional_image
  by auto


end
