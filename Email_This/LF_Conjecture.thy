(*  Title:      LF_Conjecture.thy

    The corrected compact form of Conjecture 26, proved.

    The four lemmas Section 6.1 says a proof requires are, in the present terms:
    (L1) in LF_Unfold, (L2) and (L3) in LF_WellFormed, (L4) in LF_Check.  That
    unfolding yields a correct derivation at all --- Section 5.1 --- is
    LF_Faithful.  This theory is the conjunction.
*)

theory LF_Conjecture
  imports LF_Check
begin

section \<open>The four lemmas\<close>

text \<open>
  \<^item> \<open>L1\<close>, that unfolding terminates: @{thm [source] unfolding_terminates}.
  \<^item> \<open>L2\<close>, that citations precede uses, and \<open>L3\<close>, that every citation is in
    scope: together @{thm [source] L2_L3}, which needs no hypothesis at all ---
    they are properties of the traversal, not of the rules.
  \<^item> \<open>L4\<close>, that each rule transfers: @{thm [source] L4_derivation}, by way of
    @{thm [source] emit_rules}.  Its content is the two rules that read the
    assumption list, and for those @{thm [source] uniD_genOK} and
    @{thm [source] exD_witOK} say that after the repair of Section 5.4 the
    eigenvariable occurs in no assumption Fitch has in scope.

  Section 5.1, that unfolding a correct Lemmon proof of \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close> yields a
  derivation of \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close>, is @{thm [source] toDerivation_sound}.  That the
  traversal carries that sequent over to the Fitch side is
  @{thm [source] derivationToFitch_conclusion} for \<open>\<psi>\<close> and
  @{thm [source] derivationToFitch_premises} for \<open>\<Gamma>\<close>.
\<close>

lemma labelsConsistent_fmAt:
  assumes "\<forall>nf \<in> set (openAsms d). fmAt P (fst nf) = Some (snd nf)"
  shows "labelsConsistent d"
  unfolding labelsConsistent_def
proof (intro ballI impI)
  fix nf mg assume nfd: "nf \<in> set (openAsms d)" and mgd: "mg \<in> set (openAsms d)"
    and eq: "fst nf = fst mg"
  from assms nfd have A: "fmAt P (fst nf) = Some (snd nf)" by blast
  from assms mgd have B: "fmAt P (fst mg) = Some (snd mg)" by blast
  from A B eq show "snd nf = snd mg" by simp
qed

section \<open>(L4) for the construction of Definition 21\<close>

theorem L4:
  assumes ok: "derivOK d" and lc: "labelsConsistent d"
  shows "fitchCorrect (derivationToFitch d)"
proof (rule fitchCorrect_ruleLines)
  show "fitchWF (derivationToFitch d)" by (rule L2_L3)
next
  fix fl assume m: "fl \<in> set (flatten (derivationToFitch d))"
    and a: "flRule fl \<noteq> FAssume" and p: "flRule fl \<noteq> FPremise"
  from L4_derivation [OF ok lc] m have "lineOK (derivationToFitch d) fl" by blast
  with a p
  show "ruleOK (\<delta> (derivationToFitch d)) (flFm fl)
          (depFms (\<delta> (derivationToFitch d))
                  (scopeOf (derivationToFitch d) (flNum fl)))
          (toLemmonRule (flRule fl))"
    by (simp add: lineOK_def)
qed

section \<open>Conjecture 26\<close>

text \<open>The original draft specifies a repair only for universal introduction.
  The construction proved here is its corrected compact variant: it repairs
  existential elimination too. This is a general theorem for the compact
  calculus, not a theorem about the separate exact @{text "HL_"} implementation.\<close>

text \<open>``Let the construction of Definition 21 be modified as above, renaming the
  eigenvariable of a universal introduction whenever it occurs in an assumption
  in scope.  So modified, it yields for every correct Lemmon proof a well-formed
  and correct Fitch proof with the same conclusion.''\<close>

theorem conjecture_26:
  assumes "lemmonCorrect P" and "P \<noteq> []"
  shows "\<exists>d. toDerivation P = Inr d \<and>
             fitchCorrect (derivationToFitch d) \<and>
             fitchConclusion (derivationToFitch d) = conclusion P"
proof -
  from unfolding_terminates [OF assms] obtain d where d: "toDerivation P = Inr d" by blast
  note S = toDerivation_sound [OF assms d]
  from labelsConsistent_fmAt [OF S(4)] have lc: "labelsConsistent d" .
  from L4 [OF S(1) lc] have ok: "fitchCorrect (derivationToFitch d)" .
  have "fitchConclusion (derivationToFitch d) = conclusion P"
    using derivationToFitch_conclusion [of d] S(2) by simp
  with d ok show ?thesis by blast
qed

text \<open>Section 7 records the translation as being total ``by way of the
  unfolding''.  That is a consequence of the conjecture, for the variant that
  checks the positional image before accepting it --- and, by Theorem 22, only
  for that variant.\<close>

corollary translation_total:
  assumes "lemmonCorrect P" and "P \<noteq> []"
  shows "\<exists>r F. lemmonToFitchChecked P = Inr (r, F) \<and> fitchCorrect F
                \<and> fitchConclusion F = conclusion P"
proof -
  from conjecture_26 [OF assms] obtain d
    where d: "toDerivation P = Inr d"
      and ok: "fitchCorrect (derivationToFitch d)"
      and cc: "fitchConclusion (derivationToFitch d) = conclusion P" by blast
  show ?thesis
  proof (cases "lemmonToFitchDirect P")
    case (Inl e)
    with d ok cc show ?thesis by (auto simp: lemmonToFitchChecked_def viaTree_def)
  next
    case (Inr F)
    show ?thesis
    proof (cases "fitchCorrect F")
      case True
      with Inr assms(2) show ?thesis
        by (auto simp: lemmonToFitchChecked_def lemmonToFitchDirect_conclusion)
    next
      case False
      with Inr d ok cc show ?thesis
        by (auto simp: lemmonToFitchChecked_def viaTree_def)
    qed
  qed
qed

section \<open>Conjecture 26 as a statement about the two turnstiles\<close>

text \<open>The original conjecture and the form above name the construction.
  The following corollary names the two systems: whatever the Lemmon system proves from \<open>\<Gamma>\<close>, the Fitch system
  proves from \<open>\<Gamma>\<close>.  Getting there needs one thing beyond the theorem above,
  namely that the image asserts the same assumptions: that is
  @{thm [source] derivationToFitch_premises} on the Fitch side and the lemma
  below on the Lemmon side.\<close>

lemma lookupLine_self:
  assumes "distinct (map lineNumber P)" and "l \<in> set P"
  shows "lookupLine P (lineNumber l) = Some l"
  using assms by (induction P) auto

lemma fmAt_witness:
  assumes "fmAt P n = Some f"
  shows "\<exists>l \<in> set P. lineNumber l = n \<and> formula l = f"
  using assms by (auto simp: fmAt_def dest: lookupLine_Some split: option.splits)

text \<open>The undischarged leaves of the unfolded derivation carry exactly the
  formulas of the source's dependency set.  One direction is
  @{term \<open>fmAt P\<close>} read forwards; the other needs the line numbers of a correct
  Lemmon proof to be distinct, so that a line is recovered from its number.\<close>

lemma openFms_openPremises:
  assumes P: "lemmonCorrect P" and ne: "P \<noteq> []"
      and refs: "fst ` set (openAsms d) = references (last P)"
      and fms: "\<forall>nf \<in> set (openAsms d). fmAt P (fst nf) = Some (snd nf)"
  shows "set (openFms d) = set (openPremises P)"
proof -
  from P have dist: "distinct (map lineNumber P)"
    by (simp add: lemmonCorrect_def sorted_wrt_less_distinct)
  have prem: "set (openPremises P)
                = {formula l | l. l \<in> set P \<and> lineNumber l \<in> references (last P)}"
    using ne by (auto simp: openPremises_def depFms_def)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix f assume "f \<in> set (openFms d)"
    then obtain n where nf: "(n, f) \<in> set (openAsms d)" by auto
    from fms nf have "fmAt P n = Some f" by fastforce
    then obtain l where l: "l \<in> set P" and ln: "lineNumber l = n"
      and lf: "formula l = f" using fmAt_witness by blast
    from nf refs have "n \<in> references (last P)" by force
    with l ln lf prem show "f \<in> set (openPremises P)" by auto
  next
    fix f assume "f \<in> set (openPremises P)"
    with prem obtain l where l: "l \<in> set P"
      and ln: "lineNumber l \<in> references (last P)" and lf: "formula l = f" by auto
    from ln refs obtain g where g: "(lineNumber l, g) \<in> set (openAsms d)" by force
    from fms g have "fmAt P (lineNumber l) = Some g" by fastforce
    moreover from lookupLine_self [OF dist l] have "fmAt P (lineNumber l) = Some (formula l)"
      by (simp add: fmAt_def)
    ultimately have "g = f" using lf by simp
    with g show "f \<in> set (openFms d)" by force
  qed
qed

text \<open>Section 5.1 in sequent form: unfolding a correct Lemmon proof of
  \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close> yields a derivation of \<open>\<Gamma> \<turnstile>\<^sub>L \<psi>\<close>.\<close>

theorem unfolding_sequent:
  assumes P: "lemmonCorrect P" and ne: "P \<noteq> []" and c: "conclusion P = Some psi"
  shows "\<exists>d. toDerivation P = Inr d \<and> d \<tturnstile> openPremises P \<turnstile>\<^sub>L psi"
proof -
  from unfolding_terminates [OF P ne] obtain d where d: "toDerivation P = Inr d" by blast
  note S = toDerivation_sound [OF P ne d]
  from S(2) c have "dForm d = psi" by simp
  moreover from openFms_openPremises [OF P ne S(3) S(4)]
  have "set (openFms d) = set (openPremises P)" .
  ultimately have "d \<tturnstile> openPremises P \<turnstile>\<^sub>L psi" using S(1) by simp
  with d show ?thesis by blast
qed

text \<open>Conjecture 26, as the containment of one turnstile in the other.  Note
  that the witness is not merely some Fitch proof of @{term psi}: it is the
  image under the construction of Definition 21 of the very Lemmon proof one
  started from, and it rests on the same assumptions.\<close>

theorem conjecture_26_sequent:
  assumes "G \<turnstile>\<^sub>L psi"
  shows "G \<turnstile>\<^sub>F psi"
proof -
  from assms obtain P where P: "lemmonCorrect P" and ne: "P \<noteq> []"
    and pre: "set (openPremises P) = set G" and c: "conclusion P = Some psi"
    by (rule LseqE)
  from conjecture_26 [OF P ne] obtain d
    where ok: "fitchCorrect (derivationToFitch d)"
      and cc: "fitchConclusion (derivationToFitch d) = conclusion P"
      and d: "toDerivation P = Inr d" by blast
  note S = toDerivation_sound [OF P ne d]
  have "set (fitchPremises (derivationToFitch d)) = set (openFms d)"
    by (rule derivationToFitch_premises)
  also have "\<dots> = set (openPremises P)"
    by (rule openFms_openPremises [OF P ne S(3) S(4)])
  also note pre
  finally have pf: "set (fitchPremises (derivationToFitch d)) = set G" .
  show ?thesis
  proof (rule FseqI [OF ok pf])
    show "fitchConclusion (derivationToFitch d) = Some psi" using cc c by simp
  qed
qed

end
