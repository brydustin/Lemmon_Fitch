(*  Title:      LF_HLW_Canonical.thy

    Original Definition 3 and Proposition 7 on the exact HL rule language.
    The faithful checker deliberately preserves the Haskell LEM branch's
    unconstrained dependency set.  Paper correctness additionally requires
    the exact dependency arithmetic used in the original argument.
*)

theory LF_HLW_Canonical
  imports LF_HLW
begin

section \<open>The original paper's exact dependency arithmetic\<close>

fun hlPaperDependenciesOf ::
    "(int \<Rightarrow> int set) \<Rightarrow> hl_justification \<Rightarrow> int \<Rightarrow> int set" where
  "hlPaperDependenciesOf look HL_Assumption self = {self}"
| "hlPaperDependenciesOf look (HL_CP a c) self = look c - {a}"
| "hlPaperDependenciesOf look (HL_RAA a c) self = look c - {a}"
| "hlPaperDependenciesOf look (HL_OrElim d a1 c1 a2 c2) self =
     look d \<union> (look c1 - {a1}) \<union> (look c2 - {a2})"
| "hlPaperDependenciesOf look (HL_ExistsElim m a c) self =
     look m \<union> (look c - {a})"
| "hlPaperDependenciesOf look j self =
     \<Union> (set (map look (hlCitedLines j)))"

definition hlPaperDependencyAt :: "hl_proof \<Rightarrow> int \<Rightarrow> int set" where
  "hlPaperDependencyAt E n =
     (case hlReferencesAt E n of None \<Rightarrow> {} | Some G \<Rightarrow> G)"

fun hlCanonicalFrom :: "hl_proof \<Rightarrow> hl_proof \<Rightarrow> bool" where
  "hlCanonicalFrom E [] \<longleftrightarrow> True"
| "hlCanonicalFrom E (l # ls) \<longleftrightarrow>
     hlReferences l = hlPaperDependenciesOf (hlPaperDependencyAt E)
       (hlJustification l) (hlLineNumber l) \<and>
     hlCanonicalFrom (E @ [l]) ls"

definition hlCanonicalDependencies :: "hl_proof \<Rightarrow> bool" where
  "hlCanonicalDependencies P \<longleftrightarrow> hlCanonicalFrom [] P"

definition hlPaperCorrect :: "hl_proof \<Rightarrow> bool" where
  "hlPaperCorrect P \<longleftrightarrow>
     hlVerifiedCorrect P \<and> hlCanonicalDependencies P"

lemma hlPaperCorrect_verified:
  "hlPaperCorrect P \<Longrightarrow> hlVerifiedCorrect P"
  by (simp add: hlPaperCorrect_def)

text \<open>The faithful executable interface @{const hlCorrect} is unchanged.
  @{const hlPaperCorrect} states the extra hypothesis the original paper uses
  when calling a line's dependencies exact.  In particular, a rule without
  citations, such as excluded middle, contributes no dependencies.\<close>

lemma hlCanonicalFrom_LEM_empty:
  "hlCanonicalFrom E P \<Longrightarrow> l \<in> set P \<Longrightarrow>
   hlJustification l = HL_LEM \<Longrightarrow> hlReferences l = {}"
  by (induction P arbitrary: E) auto

corollary hlPaperCorrect_LEM_empty:
  "hlPaperCorrect P \<Longrightarrow> l \<in> set P \<Longrightarrow>
   hlJustification l = HL_LEM \<Longrightarrow> hlReferences l = {}"
  unfolding hlPaperCorrect_def hlCanonicalDependencies_def
  using hlCanonicalFrom_LEM_empty by blast

section \<open>Proposition 7: reconstructing the deleted column\<close>

type_synonym hl_stripped_line = "int \<times> hl_formula \<times> hl_justification"

definition hlStripDependencies :: "hl_proof \<Rightarrow> hl_stripped_line list" where
  "hlStripDependencies P =
     map (\<lambda>l. (hlLineNumber l, hlFormula l, hlJustification l)) P"

fun hlRecomputeDependenciesFrom ::
    "hl_proof \<Rightarrow> hl_stripped_line list \<Rightarrow> hl_proof" where
  "hlRecomputeDependenciesFrom E [] = E"
| "hlRecomputeDependenciesFrom E ((n,p,j) # ls) =
     hlRecomputeDependenciesFrom
       (E @ [HL_ProofLine n p j
         (hlPaperDependenciesOf (hlPaperDependencyAt E) j n)]) ls"

definition hlRecomputeDependencies :: "hl_stripped_line list \<Rightarrow> hl_proof" where
  "hlRecomputeDependencies = hlRecomputeDependenciesFrom []"

lemma hlRecomputeDependenciesFrom_id:
  "hlCanonicalFrom E P \<Longrightarrow>
   hlRecomputeDependenciesFrom E (hlStripDependencies P) = E @ P"
proof (induction P arbitrary: E)
  case (Cons l ls)
  from Cons.prems have refs:
    "hlReferences l = hlPaperDependenciesOf (hlPaperDependencyAt E)
       (hlJustification l) (hlLineNumber l)"
    by simp
  have line:
    "HL_ProofLine (hlLineNumber l) (hlFormula l) (hlJustification l)
       (hlPaperDependenciesOf (hlPaperDependencyAt E)
         (hlJustification l) (hlLineNumber l)) = l"
    using refs by (cases l) simp
  from Cons line show ?case
    by (simp add: hlStripDependencies_def)
qed (simp add: hlStripDependencies_def)

theorem hl_proposition_7:
  assumes "hlPaperCorrect P"
  shows "hlRecomputeDependencies (hlStripDependencies P) = P"
  using assms hlRecomputeDependenciesFrom_id[of "[]" P]
  by (simp add: hlPaperCorrect_def hlCanonicalDependencies_def
      hlRecomputeDependencies_def)

theorem hlPaperCorrect_dependencies_unique:
  assumes "hlPaperCorrect P" "hlPaperCorrect Q"
    "hlStripDependencies P = hlStripDependencies Q"
  shows "P = Q"
  using hl_proposition_7[OF assms(1)] hl_proposition_7[OF assms(2)] assms(3)
  by metis

section \<open>Why the strengthened legacy predicate is insufficient\<close>

definition hlDependencyAmbiguity :: "int set \<Rightarrow> hl_proof" where
  "hlDependencyAmbiguity G =
     [HL_ProofLine 1 hlP HL_Assumption {1},
      HL_ProofLine 2 (hlQ \<or>\<^sub>H \<not>\<^sub>H hlQ) HL_LEM G]"

lemma hlDependencyAmbiguity_verified:
  "hlVerifiedCorrect (hlDependencyAmbiguity {})"
  "hlVerifiedCorrect (hlDependencyAmbiguity {1})"
  by eval+

lemma hlDependencyAmbiguity_same_stripped:
  "hlStripDependencies (hlDependencyAmbiguity G) =
   hlStripDependencies (hlDependencyAmbiguity H)"
  by (simp add: hlStripDependencies_def hlDependencyAmbiguity_def)

lemma hlDependencyAmbiguity_distinct:
  "hlDependencyAmbiguity {} \<noteq> hlDependencyAmbiguity {1}"
  by eval

lemma hlDependencyAmbiguity_paper_status:
  "hlPaperCorrect (hlDependencyAmbiguity {})"
  "\<not> hlPaperCorrect (hlDependencyAmbiguity {1})"
  by eval+

theorem hlVerifiedCorrect_does_not_determine_dependencies:
  "\<exists>P Q. hlVerifiedCorrect P \<and> hlVerifiedCorrect Q \<and>
     hlStripDependencies P = hlStripDependencies Q \<and> P \<noteq> Q"
  using hlDependencyAmbiguity_verified hlDependencyAmbiguity_same_stripped
    hlDependencyAmbiguity_distinct by blast

theorem hlVerifiedCorrect_has_no_dependency_reconstructor:
  "\<not> (\<exists>R. \<forall>P. hlVerifiedCorrect P \<longrightarrow>
     R (hlStripDependencies P) = P)"
  using hlVerifiedCorrect_does_not_determine_dependencies by metis

text \<open>This distinction is about exact bookkeeping, not an unsound LEM
  conclusion.  Both accepted examples conclude a tautology.  The canonical
  predicate recovers the original Proposition 7 without changing the faithful
  Haskell behavior or claiming a general HL translation theorem.\<close>

end
