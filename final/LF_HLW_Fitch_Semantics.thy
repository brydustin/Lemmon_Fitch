(* Semantic soundness of exact-layer Fitch proofs from displayed outer premises. *)

theory LF_HLW_Fitch_Semantics
  imports LF_HLW_Semantics
begin

text \<open>Checking the Lemmon erasure alone establishes a sequent over the
  erasure's recorded dependencies. The additional sequent boundary invariant
  in @{const hlFitchVerified} connects those dependencies to the actual outer
  premises displayed in the Fitch proof. This yields a theorem about Fitch
  proofs themselves, independently of which translation produced them.\<close>

theorem hlFitchVerified_sound:
  assumes verified: "hlFitchVerified F"
      and standard: "hlStandardInterpretation M"
      and conclusion: "hlFitchConclusion F = Some goal"
      and premises_true: "list_all (hlSatisfies M assignment) (hlFitchPremises F)"
  shows "hlSatisfies M assignment goal"
proof -
  have correct: "hlVerifiedCorrect (\<delta>\<^sub>H F)"
    using verified by (simp add: hlFitchVerified_def)
  have closed: "set (hlOpenPremises (\<delta>\<^sub>H F)) \<subseteq> set (hlFitchPremises F)"
    using verified by (simp add: hlFitchVerified_def hlFitchPremiseClosed_def)
  have open_true:
    "list_all (hlSatisfies M assignment) (hlOpenPremises (\<delta>\<^sub>H F))"
    using closed premises_true by (auto simp: list_all_iff)
  have goal: "hlConclusion (\<delta>\<^sub>H F) = Some goal"
    using conclusion by (simp add: hlFitchConclusion_delta)
  show ?thesis
    by (rule hlVerifiedCorrect_sound[OF correct standard goal open_true])
qed

theorem hlFitchCorrect_sound:
  assumes "hlFitchCorrect F"
      and "hlStandardInterpretation M"
      and "hlFitchConclusion F = Some goal"
      and "list_all (hlSatisfies M assignment) (hlFitchPremises F)"
  shows "hlSatisfies M assignment goal"
  by (rule hlFitchVerified_sound[OF hlFitchCorrect_verified[OF assms(1)] assms(2-4)])

end
