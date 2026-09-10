(* Exact-layer scope-checking regressions and the failed converse of Theorem 4. *)

theory LF_HLW_Delta
  imports LF_HLW_Examples
begin

section \<open>Regression: Theorem 22 under the real Fitch checker\<close>

lemma hl_thm22_fitch_bad_rejected: "\<not> hlFitchCorrect hl_thm22_fitch_bad"
  by eval

lemma hl_renaming_repair_hlFitchCorrect: "hlFitchCorrect hl_thm22_fitch_good"
  by eval

lemma hl_sec2_fitch_hlFitchCorrect: "hlFitchCorrect hl_sec2_fitch"
  by eval

lemma hl_ex11_ex12_fitch_witnesses_still_hold:
  "hlFitchWellFormed hl_thm22_fitch_bad"
  by eval

section \<open>Theorem 4, the direction that fails\<close>

text \<open>Theorem 22 is again the counterexample: its bad Fitch proof is rejected
  by the real (scope-based) Fitch checker, but its \<open>\<delta>\<^sub>H\<close>-image is a verified
  Lemmon proof --- indeed it is exactly @{const hl_thm22_lemmon}.\<close>

theorem hl_theorem_4_backward_fails:
  "\<not> hlFitchCorrect hl_thm22_fitch_bad \<and> hlVerifiedCorrect (\<delta>\<^sub>H hl_thm22_fitch_bad)"
  by eval

lemma hl_theorem_22_delta_verified: "\<delta>\<^sub>H hl_thm22_fitch_bad = hl_thm22_lemmon"
  by eval

section \<open>Regressions for actual nesting\<close>

definition hlClosedBoxEscape :: hl_fitch_proof where
  "hlClosedBoxEscape =
     [HL_FSub (HL_Subproof 1 hlP [HL_FLine 2 hlP (HL_FReit 1)]),
      HL_FLine 3 hlP (HL_FReit 2)]"

lemma hlClosedBoxEscape_rejected:
  "hlFitchWellFormed hlClosedBoxEscape"
  "hlVerifiedCorrect (\<delta>\<^sub>H hlClosedBoxEscape)"
  "hlConcludesAtTop hlClosedBoxEscape"
  "hlFitchPremises hlClosedBoxEscape = []"
  "hlFitchConclusion hlClosedBoxEscape = Some hlP"
  "\<not> hlFitchNestedWellFormed hlClosedBoxEscape"
  "\<not> hlFitchPremiseClosed hlClosedBoxEscape"
  "\<not> hlFitchVerified hlClosedBoxEscape"
  "\<not> hlFitchCorrect hlClosedBoxEscape"
  by eval+

text \<open>The nesting check rejects inaccessible citations even when the
  cited formula is valid and the sequent boundary check would allow it.\<close>

lemma hlClosedBoxTautologyEscape_rejected:
  "\<not> hlFitchNestedWellFormed
     [HL_FSub (HL_Subproof 1 hlP
        [HL_FLine 2 (hlQ \<or>\<^sub>H \<not>\<^sub>H hlQ) HL_FLEM]),
      HL_FLine 3 (hlQ \<or>\<^sub>H \<not>\<^sub>H hlQ) (HL_FReit 2)]"
  by eval

lemma hlFakeDischarge_rejected:
  "\<not> hlFitchNestedWellFormed
     [HL_FLine 1 hlP HL_FPremise,
      HL_FLine 2 hlP (HL_FReit 1),
      HL_FLine 3 (hlP \<longrightarrow>\<^sub>H hlP) (HL_FCP (1,2))]"
  by eval

lemma hlDischargeFromOtherLevel_rejected:
  "\<not> hlFitchNestedWellFormed
     [HL_FSub (HL_Subproof 1 hlP
        [HL_FSub (HL_Subproof 2 hlQ [HL_FLine 3 hlQ (HL_FReit 2)]),
         HL_FLine 4 hlP (HL_FReit 1)]),
      HL_FLine 5 (hlQ \<longrightarrow>\<^sub>H hlQ) (HL_FCP (2,3))]"
  by eval

lemma hlMalformedPlacement_rejected:
  "\<not> hlFitchNestedWellFormed [HL_FLine 1 hlP HL_FAssume]"
  "\<not> hlFitchNestedWellFormed
     [HL_FLine 1 (hlP \<or>\<^sub>H \<not>\<^sub>H hlP) HL_FLEM,
      HL_FLine 2 hlQ HL_FPremise]"
  "\<not> hlFitchNestedWellFormed
     [HL_FSub (HL_Subproof 1 hlP [HL_FLine 2 hlQ HL_FPremise]),
      HL_FLine 3 (hlP \<longrightarrow>\<^sub>H hlQ) (HL_FCP (1,2))]"
  "\<not> hlFitchNestedWellFormed
     [HL_FSub (HL_Subproof 1 hlP [HL_FSub (HL_Subproof 2 hlQ [])]),
      HL_FLine 3 (hlP \<longrightarrow>\<^sub>H hlQ) (HL_FCP (1,2))]"
  "\<not> hlFitchNestedWellFormed
     [HL_FLine 2 hlP HL_FPremise, HL_FLine 1 hlQ HL_FPremise]"
  "\<not> hlFitchNestedWellFormed
     [HL_FLine 1 hlP HL_FPremise, HL_FLine 1 hlQ HL_FPremise]"
  by eval+

lemma hlImmediateAssumptionDischarge_accepted:
  "hlFitchCorrect
     [HL_FSub (HL_Subproof 1 hlP []),
      HL_FLine 2 (hlP \<longrightarrow>\<^sub>H hlP) (HL_FCP (1,1))]"
  by eval

lemma hlEnclosingCitation_accepted:
  "hlFitchCorrect hl_fitch_cp_example"
  by eval

end
