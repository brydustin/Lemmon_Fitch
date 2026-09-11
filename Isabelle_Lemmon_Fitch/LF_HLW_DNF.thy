(*  Title:      LF_HLW_DNF.thy

    Executable propositional normalisation for the formula datatype supplied
    in Halvorson/lemmon-checker-main/src/PropDNF.hs.  The handwritten program
    omits biconditionals in several pattern matches.  The Isabelle operation
    is total and eliminates biconditionals before constructing DNF.
*)

theory LF_HLW_DNF
  imports LF_HLW_Semantics
begin

section \<open>Propositional syntax\<close>

fun hlIsPropositional :: "hl_formula \<Rightarrow> bool" where
  "hlIsPropositional (HL_Predicate P ts) \<longleftrightarrow> ts = []"
| "hlIsPropositional (HL_Boolean b) \<longleftrightarrow> True"
| "hlIsPropositional (HL_Not p) \<longleftrightarrow> hlIsPropositional p"
| "hlIsPropositional (HL_And p q) \<longleftrightarrow>
     hlIsPropositional p \<and> hlIsPropositional q"
| "hlIsPropositional (HL_Or p q) \<longleftrightarrow>
     hlIsPropositional p \<and> hlIsPropositional q"
| "hlIsPropositional (HL_Implies p q) \<longleftrightarrow>
     hlIsPropositional p \<and> hlIsPropositional q"
| "hlIsPropositional (HL_Iff p q) \<longleftrightarrow>
     hlIsPropositional p \<and> hlIsPropositional q"
| "hlIsPropositional (HL_ForAll x p) \<longleftrightarrow> False"
| "hlIsPropositional (HL_Exists x p) \<longleftrightarrow> False"

section \<open>Implication elimination and negation normal form\<close>

fun hlEliminateImplications :: "hl_formula \<Rightarrow> hl_formula" where
  "hlEliminateImplications (HL_Predicate P ts) = HL_Predicate P ts"
| "hlEliminateImplications (HL_Boolean b) = HL_Boolean b"
| "hlEliminateImplications (HL_Not p) =
     HL_Not (hlEliminateImplications p)"
| "hlEliminateImplications (HL_And p q) =
     HL_And (hlEliminateImplications p) (hlEliminateImplications q)"
| "hlEliminateImplications (HL_Or p q) =
     HL_Or (hlEliminateImplications p) (hlEliminateImplications q)"
| "hlEliminateImplications (HL_Implies p q) =
     HL_Or (HL_Not (hlEliminateImplications p))
           (hlEliminateImplications q)"
| "hlEliminateImplications (HL_Iff p q) =
     (let p' = hlEliminateImplications p;
          q' = hlEliminateImplications q
      in HL_And (HL_Or (HL_Not p') q') (HL_Or (HL_Not q') p'))"
| "hlEliminateImplications (HL_ForAll x p) =
     HL_ForAll x (hlEliminateImplications p)"
| "hlEliminateImplications (HL_Exists x p) =
     HL_Exists x (hlEliminateImplications p)"

fun hlPushNegations :: "hl_formula \<Rightarrow> hl_formula" where
  "hlPushNegations (HL_Not (HL_Not p)) = hlPushNegations p"
| "hlPushNegations (HL_Not (HL_And p q)) =
     HL_Or (hlPushNegations (HL_Not p)) (hlPushNegations (HL_Not q))"
| "hlPushNegations (HL_Not (HL_Or p q)) =
     HL_And (hlPushNegations (HL_Not p)) (hlPushNegations (HL_Not q))"
| "hlPushNegations (HL_Not (HL_Boolean b)) = HL_Boolean (\<not> b)"
| "hlPushNegations (HL_Not (HL_ForAll x p)) =
     HL_Exists x (hlPushNegations (HL_Not p))"
| "hlPushNegations (HL_Not (HL_Exists x p)) =
     HL_ForAll x (hlPushNegations (HL_Not p))"
| "hlPushNegations (HL_Not p) = HL_Not p"
| "hlPushNegations (HL_And p q) =
     HL_And (hlPushNegations p) (hlPushNegations q)"
| "hlPushNegations (HL_Or p q) =
     HL_Or (hlPushNegations p) (hlPushNegations q)"
| "hlPushNegations (HL_ForAll x p) = HL_ForAll x (hlPushNegations p)"
| "hlPushNegations (HL_Exists x p) = HL_Exists x (hlPushNegations p)"
| "hlPushNegations p = p"

definition hlToNNF :: "hl_formula \<Rightarrow> hl_formula" where
  "hlToNNF p = hlPushNegations (hlEliminateImplications p)"

section \<open>Disjunctive normal form\<close>

type_synonym hl_literal = "hl_name \<times> bool"
type_synonym hl_clause = "hl_literal list"

fun hlDNFClauses :: "hl_formula \<Rightarrow> hl_clause list option" where
  "hlDNFClauses (HL_Boolean True) = Some [[]]"
| "hlDNFClauses (HL_Boolean False) = Some []"
| "hlDNFClauses (HL_Or p q) =
     (case (hlDNFClauses p,hlDNFClauses q) of
        (Some ps,Some qs) \<Rightarrow> Some (ps @ qs)
      | _ \<Rightarrow> None)"
| "hlDNFClauses (HL_And p q) =
     (case (hlDNFClauses p,hlDNFClauses q) of
        (Some ps,Some qs) \<Rightarrow> Some [r @ s. r \<leftarrow> ps, s \<leftarrow> qs]
      | _ \<Rightarrow> None)"
| "hlDNFClauses (HL_Predicate P []) = Some [[(P,True)]]"
| "hlDNFClauses (HL_Not (HL_Predicate P [])) = Some [[(P,False)]]"
| "hlDNFClauses p = None"

fun hlLiteralFormula :: "hl_literal \<Rightarrow> hl_formula" where
  "hlLiteralFormula (P,True) = HL_Predicate P []"
| "hlLiteralFormula (P,False) = HL_Not (HL_Predicate P [])"

definition hlConjoin :: "hl_formula list \<Rightarrow> hl_formula" where
  "hlConjoin ps =
     (case ps of [] \<Rightarrow> HL_Boolean True | p # rest \<Rightarrow> foldl HL_And p rest)"

definition hlDisjoin :: "hl_formula list \<Rightarrow> hl_formula" where
  "hlDisjoin ps =
     (case ps of [] \<Rightarrow> HL_Boolean False | p # rest \<Rightarrow> foldl HL_Or p rest)"

definition hlClausesFormula :: "hl_clause list \<Rightarrow> hl_formula" where
  "hlClausesFormula clauses =
     hlDisjoin (map (hlConjoin \<circ> map hlLiteralFormula) clauses)"

definition hlToDNF :: "hl_formula \<Rightarrow> hl_formula option" where
  "hlToDNF p =
     (if hlIsPropositional p
      then map_option hlClausesFormula (hlDNFClauses (hlToNNF p))
      else None)"

section \<open>Semantic and executable guards\<close>

lemma hlEliminateImplications_sound:
  "hlSatisfies M assignment (hlEliminateImplications p) =
   hlSatisfies M assignment p"
  by (induction p arbitrary: assignment) (auto simp: Let_def)

lemma hl_dnf_biconditional_example:
  "hlToDNF (hlP \<longleftrightarrow>\<^sub>H hlQ) =
   Some (((((\<not>\<^sub>H hlP) \<and>\<^sub>H (\<not>\<^sub>H hlQ)) \<or>\<^sub>H
           ((\<not>\<^sub>H hlP) \<and>\<^sub>H hlP)) \<or>\<^sub>H
           (hlQ \<and>\<^sub>H (\<not>\<^sub>H hlQ))) \<or>\<^sub>H
           (hlQ \<and>\<^sub>H hlP))"
  by eval

lemma hl_dnf_rejects_predicate_arguments:
  "hlToDNF (hlPredF (HL_Const hla)) = None"
  by eval

end
