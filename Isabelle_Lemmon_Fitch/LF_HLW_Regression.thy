theory LF_HLW_Regression
  imports LF_HLW_Delta
begin

section \<open>Eigenconstants in outer premises\<close>

definition hl_premise_scope_source :: hl_proof where
  "hl_premise_scope_source = take 5 hl_thm22_lemmon"

lemma hl_premise_scope_source_verified:
  "hlVerifiedCorrect hl_premise_scope_source"
  by eval

lemma hl_premise_scope_checked_repaired:
  "case hlLemmonToFitchChecked hl_premise_scope_source of
     Inl _ \<Rightarrow> False
   | Inr (r,F) \<Rightarrow>
       r = HL_ViaTreeRoute \<and> hlFitchCorrect F \<and>
       hlConclusion (\<delta>\<^sub>H F) = hlConclusion hl_premise_scope_source"
  by eval

lemma hl_premise_scope_tree_repaired:
  "case hlToDerivation hl_premise_scope_source of
     None \<Rightarrow> False
   | Some d \<Rightarrow> hlFitchCorrect (hlDerivationToFitch d)"
  by eval

definition hl_exists_premise_scope_source :: hl_proof where
  "hl_exists_premise_scope_source =
     [HL_ProofLine 1 (HL_Exists hlx (hlPredG (HL_Var hlx))) HL_Assumption {1},
      HL_ProofLine 2 (HL_ForAll hlx (HL_Implies (hlPredG (HL_Var hlx)) hlP))
        HL_Assumption {2},
      HL_ProofLine 3 (hlPredF (HL_Const hla)) HL_Assumption {3},
      HL_ProofLine 4 (hlPredG (HL_Const hla)) HL_Assumption {4},
      HL_ProofLine 5 (HL_Implies (hlPredG (HL_Const hla)) hlP) (HL_ForallElim 2) {2},
      HL_ProofLine 6 hlP (HL_MP 5 4) {2,4},
      HL_ProofLine 7 hlP (HL_ExistsElim 1 4 6) {1,2},
      HL_ProofLine 8 (HL_And (hlPredF (HL_Const hla)) hlP) (HL_AndIntro 3 7) {1,2,3}]"

lemma hl_exists_premise_source_verified:
  "hlVerifiedCorrect hl_exists_premise_scope_source"
  by eval

lemma hl_exists_premise_scope_checked_repaired:
  "case hlLemmonToFitchChecked hl_exists_premise_scope_source of
     Inl _ \<Rightarrow> False
   | Inr (r,F) \<Rightarrow>
       r = HL_ViaTreeRoute \<and> hlFitchCorrect F \<and>
       hlConclusion (\<delta>\<^sub>H F) = hlConclusion hl_exists_premise_scope_source"
  by eval

lemma hl_exists_premise_scope_tree_repaired:
  "case hlToDerivation hl_exists_premise_scope_source of
     None \<Rightarrow> False
   | Some d \<Rightarrow> hlFitchCorrect (hlDerivationToFitch d)"
  by eval

section \<open>Every authoritative rule has a checked tree example\<close>

lemma hl_all_rules_tree_examples:
  "list_all (\<lambda>P.
     case hlViaTree P of
       Inl _ \<Rightarrow> False
     | Inr (r,F) \<Rightarrow> hlFitchCorrect F \<and>
         hlConclusion (\<delta>\<^sub>H F) = hlConclusion P)
       hl_all_rule_examples"
  by eval

end
