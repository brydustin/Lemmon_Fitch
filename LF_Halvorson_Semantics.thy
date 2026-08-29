(*  Title:      LF_Halvorson_Semantics.thy

    Standard semantics for the authoritative Haskell-shaped formula language.
    ModelSemantics.hs treats every predicate name uniformly; the equality
    rules are sound only for models in which the name "=" denotes identity.
*)

theory LF_Halvorson_Semantics
  imports LF_Halvorson_Fitch
begin

section \<open>Interpretations\<close>

record 'a hl_interpretation =
  hlDomain :: "'a set"
  hlConstantValue :: "hl_name \<Rightarrow> 'a"
  hlPredicateValue :: "hl_name \<Rightarrow> 'a list \<Rightarrow> bool"

fun hlDenoteTerm ::
    "'a hl_interpretation \<Rightarrow> (hl_name \<Rightarrow> 'a) \<Rightarrow> hl_term \<Rightarrow> 'a" where
  "hlDenoteTerm M assignment (HL_Var x) = assignment x"
| "hlDenoteTerm M assignment (HL_Const a) = hlConstantValue M a"

fun hlSatisfies ::
    "'a hl_interpretation \<Rightarrow> (hl_name \<Rightarrow> 'a) \<Rightarrow> hl_formula \<Rightarrow> bool" where
  "hlSatisfies M assignment (HL_Predicate P ts) \<longleftrightarrow>
     hlPredicateValue M P (map (hlDenoteTerm M assignment) ts)"
| "hlSatisfies M assignment (HL_Boolean b) \<longleftrightarrow> b"
| "hlSatisfies M assignment (HL_Not p) \<longleftrightarrow>
     \<not> hlSatisfies M assignment p"
| "hlSatisfies M assignment (HL_And p q) \<longleftrightarrow>
     hlSatisfies M assignment p \<and> hlSatisfies M assignment q"
| "hlSatisfies M assignment (HL_Or p q) \<longleftrightarrow>
     hlSatisfies M assignment p \<or> hlSatisfies M assignment q"
| "hlSatisfies M assignment (HL_Implies p q) \<longleftrightarrow>
     (hlSatisfies M assignment p \<longrightarrow> hlSatisfies M assignment q)"
| "hlSatisfies M assignment (HL_Iff p q) \<longleftrightarrow>
     (hlSatisfies M assignment p \<longleftrightarrow> hlSatisfies M assignment q)"
| "hlSatisfies M assignment (HL_ForAll x p) \<longleftrightarrow>
     (\<forall>d \<in> hlDomain M. hlSatisfies M (assignment(x := d)) p)"
| "hlSatisfies M assignment (HL_Exists x p) \<longleftrightarrow>
     (\<exists>d \<in> hlDomain M. hlSatisfies M (assignment(x := d)) p)"

definition hlStandardEquality :: "'a hl_interpretation \<Rightarrow> bool" where
  "hlStandardEquality M \<longleftrightarrow>
     (\<forall>x y. hlPredicateValue M (STR ''='') [x,y] \<longleftrightarrow> x = y)"

definition hlStandardInterpretation :: "'a hl_interpretation \<Rightarrow> bool" where
  "hlStandardInterpretation M \<longleftrightarrow>
     hlDomain M \<noteq> {} \<and>
     (\<forall>a. hlConstantValue M a \<in> hlDomain M) \<and>
     hlStandardEquality M"

definition hlModelEntails ::
    "'a hl_interpretation \<Rightarrow> hl_formula list \<Rightarrow> hl_formula \<Rightarrow> bool" where
  "hlModelEntails M premises conclusion \<longleftrightarrow>
     (\<forall>assignment.
       list_all (hlSatisfies M assignment) premises \<longrightarrow>
       hlSatisfies M assignment conclusion)"

section \<open>Finite evaluator corresponding to ModelSemantics.hs\<close>

text \<open>
  The preceding record is the mathematical semantics used in proofs.  The
  Haskell service instead stores finite maps and reports interpretation errors.
  The following datatype makes that behavior executable.  Error messages are
  intentionally represented by @{const None}; the logical distinction between
  success and failure is preserved without making generated code depend on a
  particular user-interface wording.
\<close>

datatype 'a hl_finite_model =
  HL_FiniteModel
    (hlFiniteDomain: "'a list")
    (hlFiniteConstants: "(hl_name \<times> 'a) list")
    (hlFinitePredicates: "((hl_name \<times> nat) \<times> 'a list list) list")

fun hlSequenceOptions :: "'a option list \<Rightarrow> 'a list option" where
  "hlSequenceOptions [] = Some []"
| "hlSequenceOptions (None # xs) = None"
| "hlSequenceOptions (Some x # xs) =
     map_option ((#) x) (hlSequenceOptions xs)"

fun hlFiniteEvalTerm ::
    "'a hl_finite_model \<Rightarrow> (hl_name \<times> 'a) list \<Rightarrow>
      hl_term \<Rightarrow> 'a option" where
  "hlFiniteEvalTerm M assignment (HL_Var x) = map_of assignment x"
| "hlFiniteEvalTerm M assignment (HL_Const a) =
     map_of (hlFiniteConstants M) a"

fun hlOptionAll :: "('a \<Rightarrow> bool option) \<Rightarrow> 'a list \<Rightarrow> bool option" where
  "hlOptionAll f [] = Some True"
| "hlOptionAll f (x # xs) =
     (case f x of
        None \<Rightarrow> None
      | Some False \<Rightarrow> Some False
      | Some True \<Rightarrow> hlOptionAll f xs)"

fun hlOptionAny :: "('a \<Rightarrow> bool option) \<Rightarrow> 'a list \<Rightarrow> bool option" where
  "hlOptionAny f [] = Some False"
| "hlOptionAny f (x # xs) =
     (case f x of
        None \<Rightarrow> None
      | Some True \<Rightarrow> Some True
      | Some False \<Rightarrow> hlOptionAny f xs)"

fun hlFiniteEval ::
    "'a hl_finite_model \<Rightarrow> (hl_name \<times> 'a) list \<Rightarrow>
      hl_formula \<Rightarrow> bool option" where
  "hlFiniteEval M assignment (HL_Boolean b) = Some b"
| "hlFiniteEval M assignment (HL_Predicate P ts) =
     (case hlSequenceOptions (map (hlFiniteEvalTerm M assignment) ts) of
        None \<Rightarrow> None
      | Some values \<Rightarrow>
          (case map_of (hlFinitePredicates M) (P,length ts) of
             None \<Rightarrow> None
           | Some relation \<Rightarrow> Some (values \<in> set relation)))"
| "hlFiniteEval M assignment (HL_Not p) =
     map_option (\<lambda>b. \<not> b) (hlFiniteEval M assignment p)"
| "hlFiniteEval M assignment (HL_And p q) =
     (case (hlFiniteEval M assignment p,hlFiniteEval M assignment q) of
        (Some a,Some b) \<Rightarrow> Some (a \<and> b)
      | _ \<Rightarrow> None)"
| "hlFiniteEval M assignment (HL_Or p q) =
     (case (hlFiniteEval M assignment p,hlFiniteEval M assignment q) of
        (Some a,Some b) \<Rightarrow> Some (a \<or> b)
      | _ \<Rightarrow> None)"
| "hlFiniteEval M assignment (HL_Implies p q) =
     (case (hlFiniteEval M assignment p,hlFiniteEval M assignment q) of
        (Some a,Some b) \<Rightarrow> Some (a \<longrightarrow> b)
      | _ \<Rightarrow> None)"
| "hlFiniteEval M assignment (HL_Iff p q) =
     (case (hlFiniteEval M assignment p,hlFiniteEval M assignment q) of
        (Some a,Some b) \<Rightarrow> Some (a = b)
      | _ \<Rightarrow> None)"
| "hlFiniteEval M assignment (HL_ForAll x p) =
     (if hlFiniteDomain M = [] then None
      else hlOptionAll (\<lambda>d. hlFiniteEval M ((x,d) # assignment) p)
             (hlFiniteDomain M))"
| "hlFiniteEval M assignment (HL_Exists x p) =
     (if hlFiniteDomain M = [] then None
      else hlOptionAny (\<lambda>d. hlFiniteEval M ((x,d) # assignment) p)
             (hlFiniteDomain M))"

definition hlFiniteEvalClosed ::
    "'a hl_finite_model \<Rightarrow> hl_formula \<Rightarrow> bool option" where
  "hlFiniteEvalClosed M p =
     (if hlFreeVariables p = {} then hlFiniteEval M [] p else None)"

definition hlFiniteStandardEquality :: "'a::equal hl_finite_model \<Rightarrow> bool" where
  "hlFiniteStandardEquality M \<longleftrightarrow>
     (case map_of (hlFinitePredicates M) (STR ''='',2) of
        None \<Rightarrow> False
      | Some relation \<Rightarrow>
          (let diagonal = [[x,x]. x \<leftarrow> hlFiniteDomain M]
           in list_all (\<lambda>tuple. tuple \<in> set diagonal) relation \<and>
              list_all (\<lambda>tuple. tuple \<in> set relation) diagonal))"

definition hl_finite_boolean_model :: "hl_name hl_finite_model" where
  "hl_finite_boolean_model =
     HL_FiniteModel [STR ''d''] []
       [((STR ''P'',0),[[]]), ((STR ''Q'',0),[])]"

lemma hl_finite_evaluator_handles_biconditional:
  "hlFiniteEvalClosed hl_finite_boolean_model (hlP \<longleftrightarrow>\<^sub>H hlQ) =
   Some False"
  by eval

lemma hl_finite_evaluator_reports_empty_quantifier_domain:
  "hlFiniteEval
     (HL_FiniteModel [] [] [] :: hl_name hl_finite_model) []
     (\<forall>\<^sub>H hlx. hlPredF (HL_Var hlx)) = None"
  by eval

section \<open>Substitution\<close>

lemma hl_fun_upd_override [simp]:
  "(f(x := a))(x := b) = f(x := b)"
  by (rule ext) auto

lemma hl_fun_upd_commute:
  assumes "x \<noteq> y"
  shows "(f(x := a))(y := b) = (f(y := b))(x := a)"
  using assms by (rule fun_upd_twist)

lemma hl_lambda_update_same [simp]:
  "(\<lambda>b. if b = x then a else f b)(x := d) = f(x := d)"
  by (rule ext) (auto simp: fun_upd_def)

lemma hl_lambda_update_commute:
  assumes "x \<noteq> y"
  shows "(\<lambda>b. if b = x then a else f b)(y := d) =
         (\<lambda>b. if b = x then a else (f(y := d)) b)"
proof (rule ext)
  fix z
  show "((\<lambda>b. if b = x then a else f b)(y := d)) z =
        (if z = x then a else (f(y := d)) z)"
    using assms by (auto simp: fun_upd_def)
qed

lemma hlDenote_substitute_constant:
  "hlDenoteTerm M assignment (hlSubstituteTerm x (HL_Const a) t) =
   hlDenoteTerm M (assignment(x := hlConstantValue M a)) t"
  by (cases t) auto

lemma hlDenote_substitute_constant_list:
  "map (\<lambda>t. hlDenoteTerm M assignment
      (hlSubstituteTerm x (HL_Const a) t)) ts =
   map (hlDenoteTerm M
      (\<lambda>b. if b = x then hlConstantValue M a else assignment b)) ts"
  by (simp add: hlDenote_substitute_constant fun_upd_def)

lemma hlSatisfies_substitute_constant:
  "hlSatisfies M assignment (hlSubstituteFree x (HL_Const a) p) =
   hlSatisfies M (assignment(x := hlConstantValue M a)) p"
proof (induction p arbitrary: assignment)
  case (HL_Predicate P ts)
  then show ?case
    by (simp add: hlDenote_substitute_constant_list comp_def)
next
  case (HL_ForAll y p)
  then show ?case
    by (cases "x = y")
       (simp_all add: hl_fun_upd_commute hl_lambda_update_commute)
next
  case (HL_Exists y p)
  then show ?case
    by (cases "x = y")
       (simp_all add: hl_fun_upd_commute hl_lambda_update_commute)
qed auto

lemma hlSubstituteTerm_not_variable:
  assumes "x \<notin> hlVariablesInTerm u"
  shows "hlSubstituteTerm x t u = u"
  using assms by (cases u) auto

lemma hlSubstituteTerms_not_variable:
  assumes "x \<notin> \<Union> (hlVariablesInTerm ` set us)"
  shows "map (hlSubstituteTerm x t) us = us"
  using assms
  by (induction us) (auto intro: hlSubstituteTerm_not_variable)

lemma hlSubstituteFree_not_free:
  assumes "x \<notin> hlFreeVariables p"
  shows "hlSubstituteFree x t p = p"
  using assms
  by (induction p) (auto intro: hlSubstituteTerms_not_variable)

lemma hlDenoteTerm_assignment_cong:
  assumes "\<And>x. x \<in> hlVariablesInTerm t \<Longrightarrow>
    assignment x = assignment' x"
  shows "hlDenoteTerm M assignment t = hlDenoteTerm M assignment' t"
  using assms by (cases t) auto

lemma hlDenoteTerms_assignment_cong:
  assumes "\<And>t x. t \<in> set ts \<Longrightarrow> x \<in> hlVariablesInTerm t \<Longrightarrow>
    assignment x = assignment' x"
  shows "map (hlDenoteTerm M assignment) ts =
    map (hlDenoteTerm M assignment') ts"
  using assms
  by (induction ts) (auto intro: hlDenoteTerm_assignment_cong)

lemma hlSatisfies_assignment_cong:
  assumes "\<And>x. x \<in> hlFreeVariables p \<Longrightarrow>
    assignment x = assignment' x"
  shows "hlSatisfies M assignment p = hlSatisfies M assignment' p"
  using assms
proof (induction p arbitrary: assignment assignment')
  case (HL_Predicate P ts)
  have "map (hlDenoteTerm M assignment) ts =
      map (hlDenoteTerm M assignment') ts"
    by (rule hlDenoteTerms_assignment_cong)
       (use HL_Predicate.prems in auto)
  then show ?case by (simp only: hlSatisfies.simps)
next
  case (HL_Boolean b)
  then show ?case by simp
next
  case (HL_Not p)
  have "hlSatisfies M assignment p = hlSatisfies M assignment' p"
    by (rule HL_Not.IH) (use HL_Not.prems in auto)
  then show ?case by simp
next
  case (HL_And p q)
  have left: "hlSatisfies M assignment p = hlSatisfies M assignment' p"
    by (rule HL_And.IH(1)) (use HL_And.prems in auto)
  have right: "hlSatisfies M assignment q = hlSatisfies M assignment' q"
    by (rule HL_And.IH(2)) (use HL_And.prems in auto)
  from left right show ?case by simp
next
  case (HL_Or p q)
  have left: "hlSatisfies M assignment p = hlSatisfies M assignment' p"
    by (rule HL_Or.IH(1)) (use HL_Or.prems in auto)
  have right: "hlSatisfies M assignment q = hlSatisfies M assignment' q"
    by (rule HL_Or.IH(2)) (use HL_Or.prems in auto)
  from left right show ?case by simp
next
  case (HL_Implies p q)
  have left: "hlSatisfies M assignment p = hlSatisfies M assignment' p"
    by (rule HL_Implies.IH(1)) (use HL_Implies.prems in auto)
  have right: "hlSatisfies M assignment q = hlSatisfies M assignment' q"
    by (rule HL_Implies.IH(2)) (use HL_Implies.prems in auto)
  from left right show ?case by simp
next
  case (HL_Iff p q)
  have left: "hlSatisfies M assignment p = hlSatisfies M assignment' p"
    by (rule HL_Iff.IH(1)) (use HL_Iff.prems in auto)
  have right: "hlSatisfies M assignment q = hlSatisfies M assignment' q"
    by (rule HL_Iff.IH(2)) (use HL_Iff.prems in auto)
  from left right show ?case by simp
next
  case (HL_ForAll x p)
  have body: "\<And>d. hlSatisfies M (assignment(x := d)) p =
      hlSatisfies M (assignment'(x := d)) p"
    by (rule HL_ForAll.IH) (use HL_ForAll.prems in auto)
  then show ?case by simp
next
  case (HL_Exists x p)
  have body: "\<And>d. hlSatisfies M (assignment(x := d)) p =
      hlSatisfies M (assignment'(x := d)) p"
    by (rule HL_Exists.IH) (use HL_Exists.prems in auto)
  then show ?case by simp
qed

lemma hlSatisfies_not_free:
  assumes "x \<notin> hlFreeVariables p"
  shows "hlSatisfies M (assignment(x := d)) p =
    hlSatisfies M assignment p"
  by (rule hlSatisfies_assignment_cong)
     (use assms in auto)

lemma hlVariablesInTerm_substitute_constant:
  "hlVariablesInTerm (hlSubstituteTerm x (HL_Const a) t) =
    hlVariablesInTerm t - {x}"
  by (cases t) auto

lemma hlFreeVariables_substitute_constant:
  "hlFreeVariables (hlSubstituteFree x (HL_Const a) p) =
    hlFreeVariables p - {x}"
  by (induction p)
     (auto simp: hlVariablesInTerm_substitute_constant)

lemma hlDenoteTerm_constants_cong:
  assumes "\<And>a. a \<in> hlConstantsInTerm t \<Longrightarrow>
    hlConstantValue N a = hlConstantValue M a"
  shows "hlDenoteTerm N assignment t = hlDenoteTerm M assignment t"
  using assms by (cases t) auto

lemma hlDenoteTerms_constants_cong:
  assumes "\<And>t a. t \<in> set ts \<Longrightarrow> a \<in> hlConstantsInTerm t \<Longrightarrow>
    hlConstantValue N a = hlConstantValue M a"
  shows "map (hlDenoteTerm N assignment) ts =
    map (hlDenoteTerm M assignment) ts"
  using assms
  by (induction ts) (auto intro: hlDenoteTerm_constants_cong)

lemma hlSatisfies_interpretation_cong:
  assumes domain: "hlDomain N = hlDomain M"
      and predicates: "hlPredicateValue N = hlPredicateValue M"
      and constants: "\<And>a. a \<in> hlConstantsInFormula p \<Longrightarrow>
        hlConstantValue N a = hlConstantValue M a"
  shows "hlSatisfies N assignment p = hlSatisfies M assignment p"
  using constants
proof (induction p arbitrary: assignment)
  case (HL_Predicate P ts)
  have terms: "map (hlDenoteTerm N assignment) ts =
      map (hlDenoteTerm M assignment) ts"
    by (rule hlDenoteTerms_constants_cong) (use HL_Predicate.prems in auto)
  show ?case
    by (simp only: hlSatisfies.simps predicates terms)
next
  case (HL_ForAll x p)
  have body: "\<And>assignment.
      hlSatisfies N assignment p = hlSatisfies M assignment p"
    by (rule HL_ForAll.IH) (use HL_ForAll.prems in auto)
  with domain show ?case by simp
next
  case (HL_Exists x p)
  have body: "\<And>assignment.
      hlSatisfies N assignment p = hlSatisfies M assignment p"
    by (rule HL_Exists.IH) (use HL_Exists.prems in auto)
  with domain show ?case by simp
qed (use predicates in auto)

lemma hlSatisfies_constant_update:
  assumes "a \<notin> hlConstantsInFormula p"
  shows "hlSatisfies
      (M\<lparr>hlConstantValue := (hlConstantValue M)(a := d)\<rparr>) assignment p =
    hlSatisfies M assignment p"
  by (rule hlSatisfies_interpretation_cong)
     (use assms in auto)

lemma hlPredicateValue_update_constant [simp]:
  "hlPredicateValue (M\<lparr>hlConstantValue := f\<rparr>) =
    hlPredicateValue M"
  by simp

lemma hlDomain_update_constant [simp]:
  "hlDomain (M\<lparr>hlConstantValue := f\<rparr>) = hlDomain M"
  by simp

lemma hlConstantValue_update_constant [simp]:
  "hlConstantValue (M\<lparr>hlConstantValue := f\<rparr>) = f"
  by simp

lemma hlDenote_abstracted_term:
  "hlDenoteTerm M assignment (hlReplaceConstantInTerm a x t) =
   hlDenoteTerm
     (M\<lparr>hlConstantValue :=
       (hlConstantValue M)(a := assignment x)\<rparr>) assignment t"
  by (cases t) auto

lemma hlDenote_abstracted_terms:
  "map (hlDenoteTerm M assignment)
      (map (hlReplaceConstantInTerm a x) ts) =
   map (hlDenoteTerm
      (M\<lparr>hlConstantValue :=
        (hlConstantValue M)(a := assignment x)\<rparr>) assignment) ts"
  by (induction ts) (simp_all only: list.map hlDenote_abstracted_term)

lemma hlAbstractConstantFree_semantics:
  assumes abstracted: "hlAbstractConstantFree a x p = Some q"
  shows "hlSatisfies M assignment q =
    hlSatisfies
      (M\<lparr>hlConstantValue :=
        (hlConstantValue M)(a := assignment x)\<rparr>) assignment p"
  using abstracted
proof (induction p arbitrary: q assignment)
  case (HL_Predicate P ts)
  from HL_Predicate.prems have q:
      "q = HL_Predicate P (map (hlReplaceConstantInTerm a x) ts)"
    by simp
  show ?case
    by (simp only: q hlSatisfies.simps hlDenote_abstracted_terms
        hlPredicateValue_update_constant)
next
  case (HL_Boolean b)
  from HL_Boolean.prems have q: "q = HL_Boolean b" by simp
  then show ?case by (simp only: hlSatisfies.simps)
next
  case (HL_Not p)
  then obtain r where r:
      "hlAbstractConstantFree a x p = Some r" "q = HL_Not r"
    by (cases "hlAbstractConstantFree a x p") auto
  have "hlSatisfies M assignment r =
      hlSatisfies
       (M\<lparr>hlConstantValue :=
         (hlConstantValue M)(a := assignment x)\<rparr>) assignment p"
    by (rule HL_Not.IH[OF r(1)])
  with r show ?case by (simp add: fun_upd_def)
next
  case (HL_And p s)
  then obtain r t where rt:
      "hlAbstractConstantFree a x p = Some r"
      "hlAbstractConstantFree a x s = Some t"
      "q = HL_And r t"
    by (cases "hlAbstractConstantFree a x p";
        cases "hlAbstractConstantFree a x s") auto
  have left: "hlSatisfies M assignment r =
      hlSatisfies
       (M\<lparr>hlConstantValue :=
         (hlConstantValue M)(a := assignment x)\<rparr>) assignment p"
    by (rule HL_And.IH(1)[OF rt(1)])
  have right: "hlSatisfies M assignment t =
      hlSatisfies
       (M\<lparr>hlConstantValue :=
         (hlConstantValue M)(a := assignment x)\<rparr>) assignment s"
    by (rule HL_And.IH(2)[OF rt(2)])
  with left rt show ?case by (simp add: fun_upd_def)
next
  case (HL_Or p s)
  then obtain r t where rt:
      "hlAbstractConstantFree a x p = Some r"
      "hlAbstractConstantFree a x s = Some t"
      "q = HL_Or r t"
    by (cases "hlAbstractConstantFree a x p";
        cases "hlAbstractConstantFree a x s") auto
  have left: "hlSatisfies M assignment r =
      hlSatisfies
       (M\<lparr>hlConstantValue :=
         (hlConstantValue M)(a := assignment x)\<rparr>) assignment p"
    by (rule HL_Or.IH(1)[OF rt(1)])
  have right: "hlSatisfies M assignment t =
      hlSatisfies
       (M\<lparr>hlConstantValue :=
         (hlConstantValue M)(a := assignment x)\<rparr>) assignment s"
    by (rule HL_Or.IH(2)[OF rt(2)])
  with left rt show ?case by (simp add: fun_upd_def)
next
  case (HL_Implies p s)
  then obtain r t where rt:
      "hlAbstractConstantFree a x p = Some r"
      "hlAbstractConstantFree a x s = Some t"
      "q = HL_Implies r t"
    by (cases "hlAbstractConstantFree a x p";
        cases "hlAbstractConstantFree a x s") auto
  have left: "hlSatisfies M assignment r =
      hlSatisfies
       (M\<lparr>hlConstantValue :=
         (hlConstantValue M)(a := assignment x)\<rparr>) assignment p"
    by (rule HL_Implies.IH(1)[OF rt(1)])
  have right: "hlSatisfies M assignment t =
      hlSatisfies
       (M\<lparr>hlConstantValue :=
         (hlConstantValue M)(a := assignment x)\<rparr>) assignment s"
    by (rule HL_Implies.IH(2)[OF rt(2)])
  with left rt show ?case by (simp add: fun_upd_def)
next
  case (HL_Iff p s)
  then obtain r t where rt:
      "hlAbstractConstantFree a x p = Some r"
      "hlAbstractConstantFree a x s = Some t"
      "q = HL_Iff r t"
    by (cases "hlAbstractConstantFree a x p";
        cases "hlAbstractConstantFree a x s") auto
  have left: "hlSatisfies M assignment r =
      hlSatisfies
       (M\<lparr>hlConstantValue :=
         (hlConstantValue M)(a := assignment x)\<rparr>) assignment p"
    by (rule HL_Iff.IH(1)[OF rt(1)])
  have right: "hlSatisfies M assignment t =
      hlSatisfies
       (M\<lparr>hlConstantValue :=
         (hlConstantValue M)(a := assignment x)\<rparr>) assignment s"
    by (rule HL_Iff.IH(2)[OF rt(2)])
  with left rt show ?case by (simp add: fun_upd_def)
next
  case (HL_ForAll y p)
  then obtain r where r:
      "y \<noteq> x" "hlAbstractConstantFree a x p = Some r"
      "q = HL_ForAll y r"
    by (cases "y = x"; cases "hlAbstractConstantFree a x p") auto
  have body: "\<And>d. hlSatisfies M (assignment(y := d)) r =
      hlSatisfies
       (M\<lparr>hlConstantValue :=
         (hlConstantValue M)(a := assignment x)\<rparr>)
       (assignment(y := d)) p"
  proof -
    fix d
    have step: "hlSatisfies M (assignment(y := d)) r =
        hlSatisfies
         (M\<lparr>hlConstantValue :=
           (hlConstantValue M)(a := (assignment(y := d)) x)\<rparr>)
         (assignment(y := d)) p"
      by (rule HL_ForAll.IH[OF r(2)])
    from step r(1) show "hlSatisfies M (assignment(y := d)) r =
        hlSatisfies
         (M\<lparr>hlConstantValue :=
           (hlConstantValue M)(a := assignment x)\<rparr>)
         (assignment(y := d)) p"
      by simp
  qed
  with r show ?case by (simp add: fun_upd_def)
next
  case (HL_Exists y p)
  then obtain r where r:
      "y \<noteq> x" "hlAbstractConstantFree a x p = Some r"
      "q = HL_Exists y r"
    by (cases "y = x"; cases "hlAbstractConstantFree a x p") auto
  have body: "\<And>d. hlSatisfies M (assignment(y := d)) r =
      hlSatisfies
       (M\<lparr>hlConstantValue :=
         (hlConstantValue M)(a := assignment x)\<rparr>)
       (assignment(y := d)) p"
  proof -
    fix d
    have step: "hlSatisfies M (assignment(y := d)) r =
        hlSatisfies
         (M\<lparr>hlConstantValue :=
           (hlConstantValue M)(a := (assignment(y := d)) x)\<rparr>)
         (assignment(y := d)) p"
      by (rule HL_Exists.IH[OF r(2)])
    from step r(1) show "hlSatisfies M (assignment(y := d)) r =
        hlSatisfies
         (M\<lparr>hlConstantValue :=
           (hlConstantValue M)(a := assignment x)\<rparr>)
         (assignment(y := d)) p"
      by simp
  qed
  with r show ?case by (simp add: fun_upd_def)
qed

fun hlReinterpretConstants ::
    "(hl_name \<times> hl_name) list \<Rightarrow> 'a hl_interpretation \<Rightarrow>
      (hl_name \<Rightarrow> 'a) \<Rightarrow> 'a hl_interpretation" where
  "hlReinterpretConstants [] M assignment = M"
| "hlReinterpretConstants ((x,a) # pairs) M assignment =
     (let N = hlReinterpretConstants pairs M assignment
      in N\<lparr>hlConstantValue :=
           (hlConstantValue N)(a := assignment x)\<rparr>)"

lemma hlReinterpretConstants_domain [simp]:
  "hlDomain (hlReinterpretConstants pairs M assignment) = hlDomain M"
proof (induction pairs)
  case Nil
  then show ?case by simp
next
  case (Cons pair pairs)
  obtain x a where "pair = (x,a)" by (cases pair)
  with Cons show ?case
    by (simp only: hlReinterpretConstants.simps Let_def
        hlDomain_update_constant)
qed

lemma hlReinterpretConstants_predicates [simp]:
  "hlPredicateValue (hlReinterpretConstants pairs M assignment) =
    hlPredicateValue M"
proof (induction pairs)
  case Nil
  then show ?case by simp
next
  case (Cons pair pairs)
  obtain x a where "pair = (x,a)" by (cases pair)
  with Cons show ?case
    by (simp only: hlReinterpretConstants.simps Let_def
        hlPredicateValue_update_constant)
qed

lemma hlReinterpretConstants_fresh:
  assumes "a \<notin> snd ` set pairs"
  shows "hlConstantValue (hlReinterpretConstants pairs M assignment) a =
    hlConstantValue M a"
  using assms
proof (induction pairs)
  case Nil
  then show ?case by simp
next
  case (Cons pair pairs)
  obtain x b where pair: "pair = (x,b)" by (cases pair)
  from Cons.prems pair have different: "a \<noteq> b"
    and fresh: "a \<notin> snd ` set pairs" by auto
  have tail: "hlConstantValue
      (hlReinterpretConstants pairs M assignment) a =
      hlConstantValue M a"
    by (rule Cons.IH[OF fresh])
  show ?case
    using tail different
    by (simp only: pair hlReinterpretConstants.simps Let_def
        hlConstantValue_update_constant fun_upd_def if_False)
qed

lemma hlStandardInterpretation_update_constant:
  assumes standard: "hlStandardInterpretation M"
      and in_domain: "d \<in> hlDomain M"
  shows "hlStandardInterpretation
    (M\<lparr>hlConstantValue := (hlConstantValue M)(a := d)\<rparr>)"
proof -
  have nonempty: "hlDomain M \<noteq> {}"
    using standard unfolding hlStandardInterpretation_def by blast
  have constants: "\<forall>b. ((hlConstantValue M)(a := d)) b \<in> hlDomain M"
  proof
    fix b
    show "((hlConstantValue M)(a := d)) b \<in> hlDomain M"
    proof (cases "b = a")
      case True
      with in_domain show ?thesis by simp
    next
      case False
      have "hlConstantValue M b \<in> hlDomain M"
        using standard unfolding hlStandardInterpretation_def by blast
      with False show ?thesis by simp
    qed
  qed
  have equality: "hlStandardEquality M"
    using standard unfolding hlStandardInterpretation_def by blast
  show ?thesis
    using nonempty constants equality
    unfolding hlStandardInterpretation_def hlStandardEquality_def
    by simp
qed

lemma hlReinterpretConstants_standard:
  assumes standard: "hlStandardInterpretation M"
      and assigned_values: "\<And>x a. (x,a) \<in> set pairs \<Longrightarrow>
        assignment x \<in> hlDomain M"
  shows "hlStandardInterpretation
    (hlReinterpretConstants pairs M assignment)"
  using assigned_values
proof (induction pairs)
  case Nil
  then show ?case using standard by simp
next
  case (Cons pair pairs)
  obtain x a where pair: "pair = (x,a)" by (cases pair)
  let ?N = "hlReinterpretConstants pairs M assignment"
  have N_standard: "hlStandardInterpretation ?N"
    by (rule Cons.IH) (use Cons.prems pair in auto)
  have assigned_value: "assignment x \<in> hlDomain ?N"
    using Cons.prems(1)[of x a] pair by simp
  have updated: "hlStandardInterpretation
      (?N\<lparr>hlConstantValue :=
        (hlConstantValue ?N)(a := assignment x)\<rparr>)"
    by (rule hlStandardInterpretation_update_constant
        [OF N_standard assigned_value])
  show ?case
    using updated
    by (simp only: pair hlReinterpretConstants.simps Let_def)
qed

lemma hlSatisfies_reinterpreted_constants:
  assumes fresh: "snd ` set pairs \<inter> hlConstantsInFormula p = {}"
  shows "hlSatisfies (hlReinterpretConstants pairs M assignment) valuation p =
    hlSatisfies M valuation p"
proof (rule hlSatisfies_interpretation_cong)
  fix a
  assume "a \<in> hlConstantsInFormula p"
  with fresh have "a \<notin> snd ` set pairs" by blast
  then show "hlConstantValue
      (hlReinterpretConstants pairs M assignment) a =
      hlConstantValue M a"
    by (rule hlReinterpretConstants_fresh)
qed simp_all

lemma hlSatisfies_reinterpreted_constants_list:
  assumes fresh: "snd ` set pairs \<inter>
      \<Union> (hlConstantsInFormula ` set formulas) = {}"
  shows "list_all
      (hlSatisfies (hlReinterpretConstants pairs M assignment) valuation)
      formulas =
    list_all (hlSatisfies M valuation) formulas"
  using fresh
proof (induction formulas)
  case Nil
  then show ?case by simp
next
  case (Cons p formulas)
  have p_fresh: "snd ` set pairs \<inter> hlConstantsInFormula p = {}"
    using Cons.prems by (simp add: disjoint_iff_not_equal) 
  have formulas_fresh: "snd ` set pairs \<inter>
      \<Union> (hlConstantsInFormula ` set formulas) = {}"
    using Cons.prems by auto
  have p_unchanged: "hlSatisfies
      (hlReinterpretConstants pairs M assignment) valuation p =
      hlSatisfies M valuation p"
    by (rule hlSatisfies_reinterpreted_constants[OF p_fresh])
  show ?case
    using p_unchanged Cons.IH[OF formulas_fresh] by simp
qed

lemma hlAbstractMany_semantics:
  assumes abstracted: "hlAbstractMany pairs p = Some q"
  shows "hlSatisfies M assignment q =
    hlSatisfies (hlReinterpretConstants pairs M assignment) assignment p"
  using abstracted
proof (induction pairs arbitrary: p q M)
  case Nil
  then show ?case by simp
next
  case (Cons pair pairs)
  obtain x a where pair: "pair = (x,a)" by (cases pair)
  then obtain r where first: "hlAbstractConstantFree a x p = Some r"
      and rest: "hlAbstractMany pairs r = Some q"
    using Cons.prems
    by (cases "hlAbstractConstantFree a x p") auto
  let ?N = "hlReinterpretConstants pairs M assignment"
  have tail: "hlSatisfies M assignment q = hlSatisfies ?N assignment r"
    by (rule Cons.IH[OF rest])
  have head: "hlSatisfies ?N assignment r =
      hlSatisfies
       (?N\<lparr>hlConstantValue :=
         (hlConstantValue ?N)(a := assignment x)\<rparr>) assignment p"
    by (rule hlAbstractConstantFree_semantics[OF first])
  have combined: "hlSatisfies M assignment q =
      hlSatisfies
       (?N\<lparr>hlConstantValue :=
         (hlConstantValue ?N)(a := assignment x)\<rparr>) assignment p"
    using tail head by simp
  show ?case
    using combined
    by (simp only: pair hlReinterpretConstants.simps Let_def)
qed

section \<open>Readable contracts for multi-quantifier bookkeeping\<close>

lemma hlPrefixForalls_Cons [simp]:
  "hlPrefixForalls (x # xs) p = HL_ForAll x (hlPrefixForalls xs p)"
  by (simp add: hlPrefixForalls_def)

lemma hlPrefixExists_Cons [simp]:
  "hlPrefixExists (x # xs) p = HL_Exists x (hlPrefixExists xs p)"
  by (simp add: hlPrefixExists_def)

lemma hlPrefixForalls_append:
  "hlPrefixForalls (xs @ ys) p =
    hlPrefixForalls xs (hlPrefixForalls ys p)"
  by (induction xs) (simp_all add: hlPrefixForalls_def)

lemma hlPrefixExists_append:
  "hlPrefixExists (xs @ ys) p =
    hlPrefixExists xs (hlPrefixExists ys p)"
  by (induction xs) (simp_all add: hlPrefixExists_def)

lemma hlPrefixForalls_from_variants:
  assumes variants: "\<And>variant.
      (\<And>x. x \<notin> set xs \<Longrightarrow> variant x = assignment x) \<Longrightarrow>
      (\<And>x. x \<in> set xs \<Longrightarrow> variant x \<in> hlDomain M) \<Longrightarrow>
      hlSatisfies M variant p"
  shows "hlSatisfies M assignment (hlPrefixForalls xs p)"
  using variants
proof (induction xs arbitrary: assignment)
  case Nil
  then show ?case by (simp add: hlPrefixForalls_def)
next
  case (Cons x xs)
  show ?case
  proof (simp only: hlPrefixForalls_Cons hlSatisfies.simps; intro ballI)
    fix d
    assume d: "d \<in> hlDomain M"
    show "hlSatisfies M (assignment(x := d)) (hlPrefixForalls xs p)"
    proof (rule Cons.IH)
      fix variant
      assume outside_tail:
          "\<And>y. y \<notin> set xs \<Longrightarrow>
            variant y = (assignment(x := d)) y"
        and inside_tail:
          "\<And>y. y \<in> set xs \<Longrightarrow>
            variant y \<in> hlDomain M"
      show "hlSatisfies M variant p"
      proof (rule Cons.prems)
        fix y
        assume "y \<notin> set (x # xs)"
        with outside_tail[of y] show "variant y = assignment y" by simp
      next
        fix y
        assume member: "y \<in> set (x # xs)"
        show "variant y \<in> hlDomain M"
        proof (cases "y \<in> set xs")
          case True
          then show ?thesis by (rule inside_tail)
        next
          case False
          with member have "y = x" by simp
          with outside_tail[of y] d show ?thesis
            using False by simp 
        qed
      qed
    qed
  qed
qed

lemma hlPrefixExists_to_variant:
  assumes source: "hlSatisfies M assignment (hlPrefixExists xs p)"
  obtains variant where
      "\<And>x. x \<notin> set xs \<Longrightarrow> variant x = assignment x"
      "\<And>x. x \<in> set xs \<Longrightarrow> variant x \<in> hlDomain M"
      "hlSatisfies M variant p"
  using source
proof (induction xs arbitrary: assignment thesis)
  case Nil
  show ?case
  proof (rule Nil.prems(1)[of assignment])
    show "hlSatisfies M assignment p"
      using Nil.prems(2) by (simp add: hlPrefixExists_def)
  qed simp_all
next
  case (Cons x xs)
  have witness: "\<exists>d \<in> hlDomain M.
      hlSatisfies M (assignment(x := d)) (hlPrefixExists xs p)"
    using Cons.prems(2) by simp
  obtain d where d: "d \<in> hlDomain M"
      "hlSatisfies M (assignment(x := d)) (hlPrefixExists xs p)"
    using witness by blast
  obtain variant where outside_tail:
      "\<And>y. y \<notin> set xs \<Longrightarrow>
        variant y = (assignment(x := d)) y"
      and inside_tail:
      "\<And>y. y \<in> set xs \<Longrightarrow> variant y \<in> hlDomain M"
      and body: "hlSatisfies M variant p"
    by (rule Cons.IH[OF _ d(2)]) blast
  show ?case
  proof (rule Cons.prems(1)[of variant])
    fix y
    assume "y \<notin> set (x # xs)"
    with outside_tail[of y] show "variant y = assignment y" by simp
  next
    fix y
    assume member: "y \<in> set (x # xs)"
    show "variant y \<in> hlDomain M"
    proof (cases "y \<in> set xs")
      case True
      then show ?thesis by (rule inside_tail)
    next
      case False
      with member have "y = x" by simp
      with outside_tail[of y] d(1) False show ?thesis by simp
    qed
  next
    show "hlSatisfies M variant p" by (rule body)
  qed
qed

lemma hlFreeVariables_prefix_foralls:
  "hlFreeVariables (hlPrefixForalls xs p) =
    hlFreeVariables p - set xs"
  by (induction xs) (auto simp: hlPrefixForalls_def)

lemma hlFreeVariables_prefix_exists:
  "hlFreeVariables (hlPrefixExists xs p) =
    hlFreeVariables p - set xs"
  by (induction xs) (auto simp: hlPrefixExists_def)

lemma hlCollectForalls_rebuild:
  "case hlCollectForalls p of (xs,core) \<Rightarrow>
     hlPrefixForalls xs core = p"
  by (induction p) (auto simp: hlPrefixForalls_def split: prod.splits)

lemma hlCollectExists_rebuild:
  "case hlCollectExists p of (xs,core) \<Rightarrow>
     hlPrefixExists xs core = p"
  by (induction p) (auto simp: hlPrefixExists_def split: prod.splits)

lemma hlEliminationCount_Some:
  assumes "hlEliminationCount source destination = Some k"
  shows "length destination \<le> length source"
    and "drop k source = destination"
    and "k = length source - length destination"
  using assms
  unfolding hlEliminationCount_def
  by (auto simp: Let_def split: if_splits)

lemma hlWitnessLists_length:
  assumes "cs \<in> set (hlWitnessLists xs p q)"
  shows "length cs = length xs"
  using assms
proof (induction xs arbitrary: p cs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (auto split: if_splits)
qed

lemma hlWitnessLists_free_variables:
  assumes "cs \<in> set (hlWitnessLists xs p q)"
  shows "hlFreeVariables q \<subseteq> hlFreeVariables p - set xs"
  using assms
proof (induction xs arbitrary: p cs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "x \<in> hlFreeVariables p")
    case False
    then obtain ds where member:
        "ds \<in> set (hlWitnessLists xs p q)"
      using Cons.prems by auto
    have "hlFreeVariables q \<subseteq> hlFreeVariables p - set xs"
      by (rule Cons.IH[OF member])
    with False show ?thesis by auto
  next
    case True
    then obtain a ds where member:
        "ds \<in> set
          (hlWitnessLists xs (hlSubstituteFree x (HL_Const a) p) q)"
      using Cons.prems by auto
    have "hlFreeVariables q \<subseteq>
        hlFreeVariables (hlSubstituteFree x (HL_Const a) p) - set xs"
      by (rule Cons.IH[OF member])
    then show ?thesis
      by (auto simp: hlFreeVariables_substitute_constant)
  qed
qed

lemma hlInferWitnessConstsK_witness:
  assumes "hlInferWitnessConstsK xs p k q = Some cs"
  shows "cs \<in> set (hlWitnessLists (take k xs) p q)"
  using assms
  unfolding hlInferWitnessConstsK_def
  by (auto simp: Let_def split: if_splits)

lemma hlInferWitnessConstsK_length:
  assumes "hlInferWitnessConstsK xs p k q = Some cs"
  shows "length cs = length (take k xs)"
  by (rule hlWitnessLists_length)
     (rule hlInferWitnessConstsK_witness[OF assms])

lemma hlZippedPair_first_in_left:
  assumes "(x,a) \<in> set (zip xs cs)"
  shows "x \<in> set xs"
  using assms
proof (induction xs arbitrary: cs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  obtain c ds where cs: "cs = c # ds"
    using Cons.prems by (cases cs) auto
  have alternatives: "(x,a) = (y,c) \<or> (x,a) \<in> set (zip ys ds)"
    using Cons.prems cs by simp
  then show ?case
  proof
    assume "(x,a) = (y,c)"
    then show ?thesis by simp
  next
    assume "(x,a) \<in> set (zip ys ds)"
    then have "x \<in> set ys" by (rule Cons.IH)
    then show ?thesis by simp
  qed
qed

lemma hlPrefixForalls_substitute_constant:
  assumes standard: "hlStandardInterpretation M"
      and source: "hlSatisfies M
        (assignment(x := hlConstantValue M a)) (hlPrefixForalls xs p)"
  shows "hlSatisfies M assignment
    (hlPrefixForalls xs (hlSubstituteFree x (HL_Const a) p))"
  using source
proof (induction xs arbitrary: assignment p)
  case Nil
  then show ?case
    by (simp add: hlPrefixForalls_def hlSatisfies_substitute_constant
        fun_upd_def)
next
  case (Cons y ys)
  have constant_in_domain:
      "hlConstantValue M a \<in> hlDomain M"
    using standard unfolding hlStandardInterpretation_def by blast
  show ?case
  proof (simp only: hlPrefixForalls_Cons hlSatisfies.simps; intro ballI)
    fix d
    assume d: "d \<in> hlDomain M"
    show "hlSatisfies M (assignment(y := d))
      (hlPrefixForalls ys (hlSubstituteFree x (HL_Const a) p))"
    proof (rule Cons.IH[OF _])
      show "hlSatisfies M
        ((assignment(y := d))(x := hlConstantValue M a))
        (hlPrefixForalls ys p)"
      proof (cases "y = x")
        case True
        have "hlSatisfies M
          ((assignment(x := hlConstantValue M a))
            (y := hlConstantValue M a))
          (hlPrefixForalls ys p)"
          using Cons.prems constant_in_domain
          by (simp add: fun_upd_def)
        with True show ?thesis by simp
      next
        case False
        have "hlSatisfies M
          ((assignment(x := hlConstantValue M a))(y := d))
          (hlPrefixForalls ys p)"
          using Cons.prems d by (simp add: fun_upd_def)
        with False show ?thesis
          by (simp add: hl_fun_upd_commute)
      qed
    qed
  qed
qed

lemma hlPrefixExists_substitute_constant:
  assumes standard: "hlStandardInterpretation M"
      and instance_true: "hlSatisfies M assignment
        (hlPrefixExists xs (hlSubstituteFree x (HL_Const a) p))"
  shows "hlSatisfies M (assignment(x := hlConstantValue M a))
    (hlPrefixExists xs p)"
  using instance_true
proof (induction xs arbitrary: assignment p)
  case Nil
  then show ?case
    by (simp add: hlPrefixExists_def hlSatisfies_substitute_constant
        fun_upd_def)
next
  case (Cons y ys)
  obtain d where d:
      "d \<in> hlDomain M"
      "hlSatisfies M (assignment(y := d))
        (hlPrefixExists ys (hlSubstituteFree x (HL_Const a) p))"
    using Cons.prems by auto
  have body: "hlSatisfies M
      ((assignment(y := d))(x := hlConstantValue M a))
      (hlPrefixExists ys p)"
    by (rule Cons.IH[OF d(2)])
  show ?case
  proof (cases "y = x")
    case True
    have constant_in_domain:
        "hlConstantValue M a \<in> hlDomain M"
      using standard unfolding hlStandardInterpretation_def by blast
    have inner: "hlSatisfies M
        ((assignment(x := hlConstantValue M a))
          (y := hlConstantValue M a))
        (hlPrefixExists ys p)"
      using body True by simp
    have "\<exists>e \<in> hlDomain M. hlSatisfies M
        ((assignment(x := hlConstantValue M a))(y := e))
        (hlPrefixExists ys p)"
      using constant_in_domain inner by blast
    then show ?thesis by (simp add: fun_upd_def)
  next
    case False
    have inner: "hlSatisfies M
        ((assignment(x := hlConstantValue M a))(y := d))
        (hlPrefixExists ys p)"
      using body False by (simp add: hl_fun_upd_commute)
    have "\<exists>e \<in> hlDomain M. hlSatisfies M
        ((assignment(x := hlConstantValue M a))(y := e))
        (hlPrefixExists ys p)"
      using d(1) inner by blast
    then show ?thesis by (simp add: fun_upd_def)
  qed
qed

theorem hlWitnessLists_forall_suffix_sound:
  assumes standard: "hlStandardInterpretation M"
      and witnesses: "cs \<in> set (hlWitnessLists xs p q)"
      and source: "hlSatisfies M assignment
        (hlPrefixForalls (xs @ suffix) p)"
  shows "hlSatisfies M assignment (hlPrefixForalls suffix q)"
  using witnesses source
proof (induction xs arbitrary: p cs assignment)
  case Nil
  then show ?case by (simp add: hlPrefixForalls_def)
next
  case (Cons x xs)
  show ?case
  proof (cases "x \<in> hlFreeVariables p")
    case False
    then obtain ds where member:
        "ds \<in> set (hlWitnessLists xs p q)"
      using Cons.prems(1) by auto
    obtain d where d: "d \<in> hlDomain M"
      using standard unfolding hlStandardInterpretation_def by blast
    have inner: "hlSatisfies M (assignment(x := d))
        (hlPrefixForalls (xs @ suffix) p)"
      using Cons.prems(2) d by simp
    have q_at_d: "hlSatisfies M (assignment(x := d))
        (hlPrefixForalls suffix q)"
      by (rule Cons.IH[OF member inner])
    have not_free: "x \<notin>
        hlFreeVariables (hlPrefixForalls suffix q)"
      using hlWitnessLists_free_variables[OF Cons.prems(1)]
      by (auto simp: hlFreeVariables_prefix_foralls)
    have update_eq: "hlSatisfies M (assignment(x := d))
        (hlPrefixForalls suffix q) =
        hlSatisfies M assignment (hlPrefixForalls suffix q)"
      by (rule hlSatisfies_not_free[OF not_free])
    from q_at_d update_eq show ?thesis by simp
  next
    case True
    then obtain a ds where member:
        "ds \<in> set
          (hlWitnessLists xs (hlSubstituteFree x (HL_Const a) p) q)"
      using Cons.prems(1) by auto
    have constant_in_domain:
        "hlConstantValue M a \<in> hlDomain M"
      using standard unfolding hlStandardInterpretation_def by blast
    have at_constant: "hlSatisfies M
        (assignment(x := hlConstantValue M a))
        (hlPrefixForalls (xs @ suffix) p)"
      using Cons.prems(2) constant_in_domain by simp
    have instantiated_prefix: "hlSatisfies M assignment
        (hlPrefixForalls (xs @ suffix)
          (hlSubstituteFree x (HL_Const a) p))"
      by (rule hlPrefixForalls_substitute_constant[OF standard at_constant])
    show ?thesis
      by (rule Cons.IH[OF member instantiated_prefix])
  qed
qed

theorem hlWitnessLists_forall_sound:
  assumes "hlStandardInterpretation M"
      and "cs \<in> set (hlWitnessLists xs p q)"
      and "hlSatisfies M assignment (hlPrefixForalls xs p)"
  shows "hlSatisfies M assignment q"
proof -
  have source: "hlSatisfies M assignment
      (hlPrefixForalls (xs @ []) p)"
    using assms(3) by simp
  have "hlSatisfies M assignment (hlPrefixForalls [] q)"
    by (rule hlWitnessLists_forall_suffix_sound
        [OF assms(1) assms(2) source])
  then show ?thesis by (simp add: hlPrefixForalls_def)
qed

theorem hlWitnessLists_exists_sound:
  assumes standard: "hlStandardInterpretation M"
      and witnesses: "cs \<in> set (hlWitnessLists xs p q)"
      and instance_true: "hlSatisfies M assignment q"
  shows "hlSatisfies M assignment (hlPrefixExists xs p)"
  using witnesses instance_true
proof (induction xs arbitrary: p cs assignment)
  case Nil
  then show ?case by (simp add: hlPrefixExists_def)
next
  case (Cons x xs)
  show ?case
  proof (cases "x \<in> hlFreeVariables p")
    case False
    then obtain ds where member:
        "ds \<in> set (hlWitnessLists xs p q)"
      using Cons.prems(1) by auto
    have inner: "hlSatisfies M assignment (hlPrefixExists xs p)"
      by (rule Cons.IH[OF member Cons.prems(2)])
    obtain d where d: "d \<in> hlDomain M"
      using standard unfolding hlStandardInterpretation_def by blast
    have not_free: "x \<notin> hlFreeVariables (hlPrefixExists xs p)"
      using False by (simp add: hlFreeVariables_prefix_exists)
    have update_eq: "hlSatisfies M (assignment(x := d))
        (hlPrefixExists xs p) =
        hlSatisfies M assignment (hlPrefixExists xs p)"
      by (rule hlSatisfies_not_free[OF not_free])
    have at_d: "hlSatisfies M (assignment(x := d))
        (hlPrefixExists xs p)"
      using inner update_eq by simp
    have "\<exists>e \<in> hlDomain M.
        hlSatisfies M (assignment(x := e)) (hlPrefixExists xs p)"
      using d at_d by blast
    then show ?thesis by simp
  next
    case True
    then obtain a ds where member:
        "ds \<in> set
          (hlWitnessLists xs (hlSubstituteFree x (HL_Const a) p) q)"
      using Cons.prems(1) by auto
    have instantiated_prefix: "hlSatisfies M assignment
        (hlPrefixExists xs (hlSubstituteFree x (HL_Const a) p))"
      by (rule Cons.IH[OF member Cons.prems(2)])
    have original_prefix: "hlSatisfies M
        (assignment(x := hlConstantValue M a))
        (hlPrefixExists xs p)"
      by (rule hlPrefixExists_substitute_constant
          [OF standard instantiated_prefix])
    have constant_in_domain:
        "hlConstantValue M a \<in> hlDomain M"
      using standard unfolding hlStandardInterpretation_def by blast
    have "\<exists>e \<in> hlDomain M.
        hlSatisfies M (assignment(x := e)) (hlPrefixExists xs p)"
      using constant_in_domain original_prefix by blast
    then show ?thesis by simp
  qed
qed

theorem hlForallElimination_sound:
  assumes standard: "hlStandardInterpretation M"
      and source_split: "hlCollectForalls source = (sourceVars,sourceCore)"
      and target_split: "hlCollectForalls target = (targetVars,targetCore)"
      and count: "hlEliminationCount sourceVars targetVars = Some k"
      and inferred: "hlInferWitnessConstsK
        sourceVars sourceCore k targetCore \<noteq> None"
      and source_true: "hlSatisfies M assignment source"
  shows "hlSatisfies M assignment target"
proof -
  obtain cs where infer:
      "hlInferWitnessConstsK sourceVars sourceCore k targetCore = Some cs"
    using inferred by (cases "hlInferWitnessConstsK
      sourceVars sourceCore k targetCore") auto
  have witness: "cs \<in> set
      (hlWitnessLists (take k sourceVars) sourceCore targetCore)"
    by (rule hlInferWitnessConstsK_witness[OF infer])
  have suffix: "drop k sourceVars = targetVars"
    by (rule hlEliminationCount_Some(2)[OF count])
  have source_rebuilt: "hlPrefixForalls sourceVars sourceCore = source"
    using hlCollectForalls_rebuild[of source] source_split by simp
  have target_rebuilt: "hlPrefixForalls targetVars targetCore = target"
    using hlCollectForalls_rebuild[of target] target_split by simp
  have source_as_blocks:
      "sourceVars = take k sourceVars @ targetVars"
    using suffix by (metis append_take_drop_id)
  have blocks_true: "hlSatisfies M assignment
      (hlPrefixForalls (take k sourceVars @ targetVars) sourceCore)"
    using source_true source_rebuilt source_as_blocks by simp
  have "hlSatisfies M assignment
      (hlPrefixForalls targetVars targetCore)"
    by (rule hlWitnessLists_forall_suffix_sound
        [OF standard witness blocks_true])
  with target_rebuilt show ?thesis by simp
qed

theorem hlExistentialIntroduction_sound:
  assumes standard: "hlStandardInterpretation M"
      and goal_split: "hlCollectExists goal = (xs,core)"
      and bound: "k \<le> length xs"
      and inferred: "hlInferWitnessConstsK xs
        (hlPrefixExists (drop k xs) core) k source \<noteq> None"
      and source_true: "hlSatisfies M assignment source"
  shows "hlSatisfies M assignment goal"
proof -
  obtain cs where infer: "hlInferWitnessConstsK xs
      (hlPrefixExists (drop k xs) core) k source = Some cs"
    using inferred by (cases "hlInferWitnessConstsK xs
      (hlPrefixExists (drop k xs) core) k source") auto
  have witness: "cs \<in> set (hlWitnessLists (take k xs)
      (hlPrefixExists (drop k xs) core) source)"
    by (rule hlInferWitnessConstsK_witness[OF infer])
  have introduced: "hlSatisfies M assignment
      (hlPrefixExists (take k xs) (hlPrefixExists (drop k xs) core))"
    by (rule hlWitnessLists_exists_sound[OF standard witness source_true])
  have prefix: "hlPrefixExists (take k xs)
      (hlPrefixExists (drop k xs) core) = hlPrefixExists xs core"
    using bound
    by (simp add: hlPrefixExists_append[symmetric])
  have goal_rebuilt: "hlPrefixExists xs core = goal"
    using hlCollectExists_rebuild[of goal] goal_split by simp
  from introduced prefix goal_rebuilt show ?thesis by simp
qed

section \<open>Eigenconstant rules are semantically sound\<close>

theorem hlForallIntroduction_sound:
  assumes standard: "hlStandardInterpretation M"
      and goal_split: "hlCollectForalls goal = (xs,core)"
      and inferred: "hlInferWitnessConstsK xs core (length xs) source =
        Some cs"
      and pairs: "pairs = filter (\<lambda>xc. snd xc \<noteq> STR '''')
        (zip xs cs)"
      and abstracted: "hlAbstractMany pairs source = Some core"
      and fresh: "snd ` set pairs \<inter>
        \<Union> (hlConstantsInFormula ` set formulas) = {}"
      and source_follows: "\<And>N. hlStandardInterpretation N \<Longrightarrow>
        list_all (hlSatisfies N assignment) formulas \<Longrightarrow>
        hlSatisfies N assignment source"
      and formulas_true: "list_all (hlSatisfies M assignment) formulas"
  shows "hlSatisfies M assignment goal"
proof -
  have witnesses: "cs \<in> set (hlWitnessLists xs core source)"
    using hlInferWitnessConstsK_witness[OF inferred] by simp
  have source_variables:
      "hlFreeVariables source \<subseteq> hlFreeVariables core - set xs"
    by (rule hlWitnessLists_free_variables[OF witnesses])
  have pair_variables: "\<And>x a. (x,a) \<in> set pairs \<Longrightarrow> x \<in> set xs"
  proof -
    fix x a
    assume "(x,a) \<in> set pairs"
    with pairs have "(x,a) \<in> set (zip xs cs)" by simp
    then show "x \<in> set xs" by (rule hlZippedPair_first_in_left)
  qed
  have prefix_true: "hlSatisfies M assignment (hlPrefixForalls xs core)"
  proof (rule hlPrefixForalls_from_variants)
    fix variant
    assume outside: "\<And>x. x \<notin> set xs \<Longrightarrow>
        variant x = assignment x"
      and inside: "\<And>x. x \<in> set xs \<Longrightarrow>
        variant x \<in> hlDomain M"
    let ?N = "hlReinterpretConstants pairs M variant"
    have N_standard: "hlStandardInterpretation ?N"
    proof (rule hlReinterpretConstants_standard[OF standard])
      fix x a
      assume "(x,a) \<in> set pairs"
      then have "x \<in> set xs" by (rule pair_variables)
      then show "variant x \<in> hlDomain M" by (rule inside)
    qed
    have formulas_unchanged:
        "list_all (hlSatisfies ?N assignment) formulas =
         list_all (hlSatisfies M assignment) formulas"
      by (rule hlSatisfies_reinterpreted_constants_list[OF fresh])
    have formulas_true_in_N:
        "list_all (hlSatisfies ?N assignment) formulas"
      using formulas_true formulas_unchanged by simp
    have source_true_at_assignment: "hlSatisfies ?N assignment source"
      by (rule source_follows[OF N_standard formulas_true_in_N])
    have source_true_at_variant: "hlSatisfies ?N variant source"
    proof -
      have unchanged: "hlSatisfies ?N variant source =
          hlSatisfies ?N assignment source"
      proof (rule hlSatisfies_assignment_cong)
        fix x
        assume "x \<in> hlFreeVariables source"
        with source_variables have "x \<notin> set xs" by auto
        then show "variant x = assignment x" by (rule outside)
      qed
      from source_true_at_assignment unchanged show ?thesis by simp
    qed
    have abstraction_equivalence:
        "hlSatisfies M variant core = hlSatisfies ?N variant source"
      by (rule hlAbstractMany_semantics[OF abstracted])
    from source_true_at_variant abstraction_equivalence
    show "hlSatisfies M variant core" by simp
  qed
  have goal_rebuilt: "hlPrefixForalls xs core = goal"
    using hlCollectForalls_rebuild[of goal] goal_split by simp
  from prefix_true goal_rebuilt show ?thesis by simp
qed

theorem hlExistentialElimination_sound:
  assumes standard: "hlStandardInterpretation M"
      and source_split:
        "hlCollectExists source = (sourceVars,sourceCore)"
      and count:
        "hlEliminationCount sourceVars targetVars = Some k"
      and inferred: "hlInferWitnessConstsK sourceVars
        (hlPrefixExists targetVars sourceCore) k assumption = Some cs"
      and pairs: "pairs = filter (\<lambda>xc. snd xc \<noteq> STR '''')
        (zip (take k sourceVars) cs)"
      and abstracted: "hlAbstractMany pairs assumption =
        Some (hlPrefixExists targetVars sourceCore)"
      and fresh_conclusion:
        "snd ` set pairs \<inter> hlConstantsInFormula conclusion = {}"
      and fresh_formulas: "snd ` set pairs \<inter>
        \<Union> (hlConstantsInFormula ` set formulas) = {}"
      and source_true: "hlSatisfies M assignment source"
      and subproof_follows: "\<And>N. hlStandardInterpretation N \<Longrightarrow>
        list_all (hlSatisfies N assignment) formulas \<Longrightarrow>
        hlSatisfies N assignment assumption \<Longrightarrow>
        hlSatisfies N assignment conclusion"
      and formulas_true: "list_all (hlSatisfies M assignment) formulas"
  shows "hlSatisfies M assignment conclusion"
proof -
  have suffix: "drop k sourceVars = targetVars"
    by (rule hlEliminationCount_Some(2)[OF count])
  have source_rebuilt: "hlPrefixExists sourceVars sourceCore = source"
    using hlCollectExists_rebuild[of source] source_split by simp
  have source_as_blocks:
      "sourceVars = take k sourceVars @ targetVars"
    using suffix by (metis append_take_drop_id)
  have blocks_true: "hlSatisfies M assignment
      (hlPrefixExists (take k sourceVars @ targetVars) sourceCore)"
    using source_true source_rebuilt source_as_blocks by simp
  have leading_exists: "hlSatisfies M assignment
      (hlPrefixExists (take k sourceVars)
        (hlPrefixExists targetVars sourceCore))"
    using blocks_true by (simp add: hlPrefixExists_append)
  have witnesses: "cs \<in> set (hlWitnessLists (take k sourceVars)
      (hlPrefixExists targetVars sourceCore) assumption)"
    by (rule hlInferWitnessConstsK_witness[OF inferred])
  have assumption_variables: "hlFreeVariables assumption \<subseteq>
      hlFreeVariables (hlPrefixExists targetVars sourceCore) -
        set (take k sourceVars)"
    by (rule hlWitnessLists_free_variables[OF witnesses])
  have pair_variables: "\<And>x a. (x,a) \<in> set pairs \<Longrightarrow>
      x \<in> set (take k sourceVars)"
  proof -
    fix x a
    assume "(x,a) \<in> set pairs"
    with pairs have "(x,a) \<in> set (zip (take k sourceVars) cs)"
      by simp
    then show "x \<in> set (take k sourceVars)"
      by (rule hlZippedPair_first_in_left)
  qed
  obtain variant where outside:
      "\<And>x. x \<notin> set (take k sourceVars) \<Longrightarrow>
        variant x = assignment x"
      and inside:
      "\<And>x. x \<in> set (take k sourceVars) \<Longrightarrow>
        variant x \<in> hlDomain M"
      and template_true: "hlSatisfies M variant
        (hlPrefixExists targetVars sourceCore)"
    using leading_exists by (metis hlPrefixExists_to_variant)
  let ?N = "hlReinterpretConstants pairs M variant"
  have N_standard: "hlStandardInterpretation ?N"
  proof (rule hlReinterpretConstants_standard[OF standard])
    fix x a
    assume "(x,a) \<in> set pairs"
    then have "x \<in> set (take k sourceVars)" by (rule pair_variables)
    then show "variant x \<in> hlDomain M" by (rule inside)
  qed
  have assumption_equivalence: "hlSatisfies M variant
      (hlPrefixExists targetVars sourceCore) =
      hlSatisfies ?N variant assumption"
    by (rule hlAbstractMany_semantics[OF abstracted])
  have assumption_true_at_variant: "hlSatisfies ?N variant assumption"
    using template_true assumption_equivalence by simp
  have assumption_true: "hlSatisfies ?N assignment assumption"
  proof -
    have unchanged: "hlSatisfies ?N variant assumption =
        hlSatisfies ?N assignment assumption"
    proof (rule hlSatisfies_assignment_cong)
      fix x
      assume "x \<in> hlFreeVariables assumption"
      with assumption_variables have "x \<notin> set (take k sourceVars)"
        by auto
      then show "variant x = assignment x" by (rule outside)
    qed
    from assumption_true_at_variant unchanged show ?thesis by simp
  qed
  have formulas_unchanged:
      "list_all (hlSatisfies ?N assignment) formulas =
       list_all (hlSatisfies M assignment) formulas"
    by (rule hlSatisfies_reinterpreted_constants_list[OF fresh_formulas])
  have formulas_true_in_N:
      "list_all (hlSatisfies ?N assignment) formulas"
    using formulas_true formulas_unchanged by simp
  have conclusion_true_in_N: "hlSatisfies ?N assignment conclusion"
    by (rule subproof_follows
        [OF N_standard formulas_true_in_N assumption_true])
  have conclusion_unchanged:
      "hlSatisfies ?N assignment conclusion =
       hlSatisfies M assignment conclusion"
    by (rule hlSatisfies_reinterpreted_constants[OF fresh_conclusion])
  from conclusion_true_in_N conclusion_unchanged show ?thesis by simp
qed

section \<open>Propositional consequence is semantically sound\<close>

lemma hlValuations_complete:
  "\<exists>v \<in> set (hlValuations atoms). \<forall>p \<in> set atoms. v p = wanted p"
proof (induction atoms)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then obtain v where v:
      "v \<in> set (hlValuations ps)"
      "\<forall>q \<in> set ps. v q = wanted q"
    by blast
  show ?case
  proof (cases "wanted p")
    case True
    show ?thesis
      using v True
      by (intro bexI[of _ "v(p := True)"]) auto
  next
    case False
    show ?thesis
      using v False
      by (intro bexI[of _ "v(p := False)"]) auto
  qed
qed

lemma hlPropositionalValue_agrees:
  assumes "\<And>a. a \<in> set (hlPropositionalAtoms p) \<Longrightarrow>
             v a = hlSatisfies M assignment a"
  shows "hlPropositionalValue v p = hlSatisfies M assignment p"
  using assms
  by (induction p) auto

theorem hlPropositionalConsequence_sound:
  assumes consequence: "hlPropositionalConsequence Gamma conclusion"
      and premises_true: "list_all (hlSatisfies M assignment) Gamma"
  shows "hlSatisfies M assignment conclusion"
proof -
  let ?atoms = "remdups
    (concat (map hlPropositionalAtoms (conclusion # Gamma)))"
  let ?wanted = "hlSatisfies M assignment"
  obtain v where v:
      "v \<in> set (hlValuations ?atoms)"
      "\<forall>a \<in> set ?atoms. v a = ?wanted a"
    using hlValuations_complete[of ?atoms ?wanted] by blast
  have agrees:
      "\<And>p. p \<in> set (conclusion # Gamma) \<Longrightarrow>
        hlPropositionalValue v p = ?wanted p"
  proof -
    fix p
    assume p: "p \<in> set (conclusion # Gamma)"
    show "hlPropositionalValue v p = ?wanted p"
      by (rule hlPropositionalValue_agrees)
         (use v(2) p in auto)
  qed
  have premise_values: "list_all (hlPropositionalValue v) Gamma"
    using premises_true agrees by (induction Gamma) auto
  have "hlPropositionalValue v conclusion"
    using consequence v(1) premise_values
    unfolding hlPropositionalConsequence_def
    by (auto simp: Let_def list_all_iff)
  then show ?thesis
    using agrees[of conclusion] by simp
qed

section \<open>Why equality must denote identity\<close>

definition hl_bad_equality_model :: "hl_name hl_interpretation" where
  "hl_bad_equality_model =
     \<lparr> hlDomain = {STR ''d''},
       hlConstantValue = (\<lambda>_. STR ''d''),
       hlPredicateValue = (\<lambda>_ _. False) \<rparr>"

lemma hl_haskell_model_semantics_needs_equality_condition:
  "hlCorrect hl_eq_intro_example \<and>
   \<not> hlSatisfies hl_bad_equality_model assignment
        (HL_Const hla =\<^sub>H HL_Const hla)"
  by (simp add: hl_eq_intro_example_def hlCorrect_def hlLineOK_def
      hlStructureOK_def hlRuleOK_def hl_bad_equality_model_def)

lemma hl_equality_introduction_sound:
  assumes "hlStandardEquality M"
  shows "hlSatisfies M assignment (HL_Const a =\<^sub>H HL_Const a)"
  using assms by (simp add: hlStandardEquality_def)

lemma hl_excluded_middle_sound:
  "hlSatisfies M assignment (p \<or>\<^sub>H \<not>\<^sub>H p)"
  by simp

lemma hl_contradiction_false:
  assumes "hlContradiction p"
  shows "\<not> hlSatisfies M assignment p"
  using assms
  by (cases p; auto simp: hlContradiction_def split: hl_formula.splits)

section \<open>Quantifier negation and equality elimination\<close>

lemma hlQuantifierNegationForms_sound:
  assumes "q \<in> set (hlQuantifierNegationForms p)"
  shows "hlSatisfies M assignment q = hlSatisfies M assignment p"
  using assms
proof (induction p arbitrary: q assignment rule: hlQuantifierNegationForms.induct)
  case (1 x p)
  then show ?case by (auto simp: fun_upd_def)
next
  case (2 x p)
  then show ?case by (auto simp: fun_upd_def)
next
  case (3 x p)
  then show ?case by (auto simp: fun_upd_def)
next
  case (4 x p)
  then show ?case by (auto simp: fun_upd_def)
qed auto

theorem hlQuantifierNegationEquivalent_sound:
  assumes "hlQuantifierNegationEquivalent p q"
  shows "hlSatisfies M assignment p = hlSatisfies M assignment q"
proof -
  from assms have reachable:
      "hlQuantifierNegationReachable p q \<or>
       hlQuantifierNegationReachable q p"
    unfolding hlQuantifierNegationEquivalent_def .
  then show ?thesis
  proof
    assume "hlQuantifierNegationReachable p q"
    then have "q \<in> set (hlQuantifierNegationForms p)"
      unfolding hlQuantifierNegationReachable_def
      by (cases p) auto
    then show ?thesis
      by (rule hlQuantifierNegationForms_sound[symmetric])
  next
    assume "hlQuantifierNegationReachable q p"
    then have "p \<in> set (hlQuantifierNegationForms q)"
      unfolding hlQuantifierNegationReachable_def
      by (cases q) auto
    then show ?thesis
      by (rule hlQuantifierNegationForms_sound)
  qed
qed

lemma hlTermReplacement_denotation:
  assumes names_equal: "hlConstantValue M a = hlConstantValue M b"
      and replacement: "hlTermEqualUpToConstantReplacement a b t u"
  shows "hlDenoteTerm M assignment t = hlDenoteTerm M assignment u"
  using names_equal replacement
  by (cases t; cases u) auto

lemma hlTermReplacements_denotation:
  assumes names_equal: "hlConstantValue M a = hlConstantValue M b"
      and replacements:
        "list_all2 (hlTermEqualUpToConstantReplacement a b) ts us"
  shows "map (hlDenoteTerm M assignment) ts =
         map (hlDenoteTerm M assignment) us"
  using replacements
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons t u ts us)
  then show ?case
    using hlTermReplacement_denotation[OF names_equal Cons.hyps(1)]
    by simp
qed

lemma hlConstantReplacement_semantics:
  assumes names_equal: "hlConstantValue M a = hlConstantValue M b"
      and replacement: "hlEqualUpToConstantReplacement a b p q"
  shows "hlSatisfies M assignment p = hlSatisfies M assignment q"
  using replacement
proof (induction p arbitrary: q assignment)
  case (HL_Predicate P ts)
  then obtain Q us where q: "q = HL_Predicate Q us"
    by (cases q) auto
  with HL_Predicate have symbol: "P = Q" and terms:
      "list_all2 (hlTermEqualUpToConstantReplacement a b) ts us"
    by auto
  show ?case
    using hlTermReplacements_denotation[OF names_equal terms]
    by (simp add: q symbol)
next
  case (HL_Boolean c)
  then show ?case by (cases q) auto
next
  case (HL_Not p)
  then show ?case by (cases q) auto
next
  case (HL_And p1 p2)
  then show ?case by (cases q) auto
next
  case (HL_Or p1 p2)
  then show ?case by (cases q) auto
next
  case (HL_Implies p1 p2)
  then show ?case by (cases q) auto
next
  case (HL_Iff p1 p2)
  then show ?case by (cases q) auto
next
  case (HL_ForAll x p)
  then show ?case by (cases q) auto
next
  case (HL_Exists x p)
  then show ?case by (cases q) auto
qed

theorem hlEqualityElimination_sound:
  assumes standard: "hlStandardEquality M"
      and equality_true:
        "hlSatisfies M assignment (HL_Const a =\<^sub>H HL_Const b)"
      and source_true: "hlSatisfies M assignment p"
      and replacement: "hlEqualUpToConstantReplacement a b p q"
  shows "hlSatisfies M assignment q"
proof -
  have names_equal: "hlConstantValue M a = hlConstantValue M b"
    using standard equality_true by (simp add: hlStandardEquality_def)
  have "hlSatisfies M assignment p = hlSatisfies M assignment q"
    by (rule hlConstantReplacement_semantics[OF names_equal replacement])
  with source_true show ?thesis by simp
qed

section \<open>Truth under a Lemmon dependency set\<close>

definition hlDependenciesTrue ::
    "hl_proof \<Rightarrow> 'a hl_interpretation \<Rightarrow>
      (hl_name \<Rightarrow> 'a) \<Rightarrow> int set \<Rightarrow> bool" where
  "hlDependenciesTrue P M assignment G \<longleftrightarrow>
     (\<forall>n \<in> G. case hlLookupLine P n of
        None \<Rightarrow> False
      | Some l \<Rightarrow>
          hlJustification l = HL_Assumption \<and>
          hlSatisfies M assignment (hlFormula l))"

definition hlAssumptionFormulas ::
    "hl_proof \<Rightarrow> int set \<Rightarrow> hl_formula list" where
  "hlAssumptionFormulas P G =
     map hlFormula
       (filter (\<lambda>l. hlLineNumber l \<in> G \<and>
          hlJustification l = HL_Assumption) P)"

lemma hlLookupLine_in_set:
  assumes "hlLookupLine P n = Some l"
  shows "l \<in> set P"
  using assms by (induction P) (auto split: if_splits)

lemma hlLookupLine_self_if_unique:
  assumes member: "l \<in> set P"
      and unique: "length (filter
        (\<lambda>k. hlLineNumber k = hlLineNumber l) P) = 1"
  shows "hlLookupLine P (hlLineNumber l) = Some l"
  using member unique
proof (induction P)
  case Nil
  then show ?case by simp
next
  case (Cons h P)
  show ?case
  proof (cases "h = l")
    case True
    then show ?thesis by simp
  next
    case different: False
    with Cons.prems(1) have member_tail: "l \<in> set P" by simp
    show ?thesis
    proof (cases "hlLineNumber h = hlLineNumber l")
      case True
      with Cons.prems(2) have empty:
          "filter (\<lambda>k. hlLineNumber k = hlLineNumber l) P = []"
        by simp
      have "l \<in> set (filter
          (\<lambda>k. hlLineNumber k = hlLineNumber l) P)"
        using member_tail by simp
      with empty show ?thesis by simp
    next
      case False
      with Cons.prems(2) have tail_unique: "length (filter
          (\<lambda>k. hlLineNumber k = hlLineNumber l) P) = 1"
        by simp
      have tail_lookup: "hlLookupLine P (hlLineNumber l) = Some l"
        by (rule Cons.IH[OF member_tail tail_unique])
      with False show ?thesis by simp
    qed
  qed
qed

lemma hlCorrect_lookup_self:
  assumes correct: "hlCorrect P"
      and member: "l \<in> set P"
  shows "hlLookupLine P (hlLineNumber l) = Some l"
proof -
  have line_ok: "hlLineOK P l"
    using correct member unfolding hlCorrect_def list_all_iff by blast
  have unique: "length (filter
      (\<lambda>k. hlLineNumber k = hlLineNumber l) P) = 1"
    using line_ok unfolding hlLineOK_def hlStructureOK_def by blast
  show ?thesis by (rule hlLookupLine_self_if_unique[OF member unique])
qed

lemma hlDependenciesTrue_mono:
  assumes "G \<subseteq> H" "hlDependenciesTrue P M assignment H"
  shows "hlDependenciesTrue P M assignment G"
  using assms unfolding hlDependenciesTrue_def by blast

lemma hlDependenciesTrue_union:
  assumes "hlDependenciesTrue P M assignment (G \<union> H)"
  shows "hlDependenciesTrue P M assignment G"
    and "hlDependenciesTrue P M assignment H"
  using assms by (auto intro: hlDependenciesTrue_mono)

lemma hlDependenciesTrue_restore:
  assumes remainder: "hlDependenciesTrue P M assignment (G - {a})"
      and assumption_line: "hlLookupLine P a = Some la"
      and assumption: "hlJustification la = HL_Assumption"
      and assumption_true: "hlSatisfies M assignment (hlFormula la)"
  shows "hlDependenciesTrue P M assignment G"
  unfolding hlDependenciesTrue_def
proof (intro ballI)
  fix n
  assume "n \<in> G"
  show "case hlLookupLine P n of
      None \<Rightarrow> False
    | Some l \<Rightarrow>
        hlJustification l = HL_Assumption \<and>
        hlSatisfies M assignment (hlFormula l)"
  proof (cases "n = a")
    case True
    with assumption_line assumption assumption_true show ?thesis by simp
  next
    case False
    with \<open>n \<in> G\<close> have "n \<in> G - {a}" by simp
    with remainder show ?thesis unfolding hlDependenciesTrue_def by blast
  qed
qed

lemma hlAssumptionFormulas_constants:
  "\<Union> (hlConstantsInFormula ` set (hlAssumptionFormulas P G)) =
    hlAssumptionConstants P G"
  unfolding hlAssumptionFormulas_def hlAssumptionConstants_def
  by auto

lemma hlDependenciesTrue_assumption_formulas:
  assumes correct: "hlCorrect P"
      and closed: "G \<subseteq> hlLineNumber `
        {l \<in> set P. hlJustification l = HL_Assumption}"
  shows "hlDependenciesTrue P M assignment G \<longleftrightarrow>
    list_all (hlSatisfies M assignment) (hlAssumptionFormulas P G)"
proof
  assume dependencies: "hlDependenciesTrue P M assignment G"
  show "list_all (hlSatisfies M assignment) (hlAssumptionFormulas P G)"
    unfolding hlAssumptionFormulas_def list_all_iff
  proof (intro ballI)
    fix p
    assume "p \<in> set (map hlFormula
      (filter (\<lambda>l. hlLineNumber l \<in> G \<and>
        hlJustification l = HL_Assumption) P))"
    then obtain l where member: "l \<in> set P"
        and number: "hlLineNumber l \<in> G"
        and assumption: "hlJustification l = HL_Assumption"
        and p: "p = hlFormula l" by auto
    have lookup: "hlLookupLine P (hlLineNumber l) = Some l"
      by (rule hlCorrect_lookup_self[OF correct member])
    have at_number: "case hlLookupLine P (hlLineNumber l) of
        None \<Rightarrow> False
      | Some k \<Rightarrow>
          hlJustification k = HL_Assumption \<and>
          hlSatisfies M assignment (hlFormula k)"
      using dependencies number unfolding hlDependenciesTrue_def by blast
    from at_number lookup p show "hlSatisfies M assignment p" by simp
  qed
next
  assume formulas:
      "list_all (hlSatisfies M assignment) (hlAssumptionFormulas P G)"
  show "hlDependenciesTrue P M assignment G"
    unfolding hlDependenciesTrue_def
  proof (intro ballI)
    fix n
    assume "n \<in> G"
    with closed obtain l where member: "l \<in> set P"
        and assumption: "hlJustification l = HL_Assumption"
        and number: "hlLineNumber l = n" by blast
    have lookup: "hlLookupLine P n = Some l"
      using hlCorrect_lookup_self[OF correct member] number by simp
    have formula_member: "hlFormula l \<in>
        set (hlAssumptionFormulas P G)"
      using member assumption number \<open>n \<in> G\<close>
      unfolding hlAssumptionFormulas_def by auto
    have true: "hlSatisfies M assignment (hlFormula l)"
      using formulas formula_member unfolding list_all_iff by blast
    show "case hlLookupLine P n of
        None \<Rightarrow> False
      | Some l \<Rightarrow>
          hlJustification l = HL_Assumption \<and>
          hlSatisfies M assignment (hlFormula l)"
      using lookup assumption true by simp
  qed
qed

lemma hlLookupLine_number:
  assumes "hlLookupLine P n = Some l"
  shows "hlLineNumber l = n"
  using assms by (induction P) (auto split: if_splits)

lemma hlCanonicalOrder_positive:
  assumes canonical: "hlCanonicalOrder P"
      and lookup: "hlLookupLine P n = Some l"
  shows "0 < n"
proof -
  have member: "l \<in> set P" by (rule hlLookupLine_in_set[OF lookup])
  have positive: "list_all (\<lambda>m. 0 < m) (map hlLineNumber P)"
    using canonical unfolding hlCanonicalOrder_def by blast
  have "0 < hlLineNumber l"
    using positive member unfolding list_all_iff by auto
  with hlLookupLine_number[OF lookup] show ?thesis by simp
qed

lemma hlDependencyClosedD:
  assumes closed: "hlDependencyClosed P"
      and member: "l \<in> set P"
  shows "hlReferences l \<subseteq> hlLineNumber `
    {a \<in> set P. hlJustification a = HL_Assumption}"
  using closed member unfolding hlDependencyClosed_def by blast

lemma hlAssumptionConstants_subset_referenced:
  "hlAssumptionConstants P G \<subseteq> hlReferencedConstants P G"
  unfolding hlAssumptionConstants_def hlReferencedConstants_def by auto

lemma hlMapFilter_formulas_true:
  assumes truth: "\<And>m l. m \<in> set ms \<Longrightarrow>
      hlLookupLine P m = Some l \<Longrightarrow>
      hlSatisfies M assignment (hlFormula l)"
  shows "list_all (hlSatisfies M assignment)
    (hlMapFilter (hlFormulaAt P) ms)"
  using truth
proof (induction ms)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
  have tail_truth: "\<And>n l. n \<in> set ms \<Longrightarrow>
      hlLookupLine P n = Some l \<Longrightarrow>
      hlSatisfies M assignment (hlFormula l)"
    using Cons.prems by auto
  have tail: "list_all (hlSatisfies M assignment)
      (hlMapFilter (hlFormulaAt P) ms)"
    using Cons.IH tail_truth by blast
  show ?case
  proof (cases "hlLookupLine P m")
    case None
    have none_formula: "hlFormulaAt P m = None"
      using None by (simp add: hlFormulaAt_def)
    show ?thesis using tail none_formula by simp
  next
    case (Some l)
    have head: "hlSatisfies M assignment (hlFormula l)"
      using Cons.prems Some by auto
    have some_formula: "hlFormulaAt P m = Some (hlFormula l)"
      using Some by (simp add: hlFormulaAt_def)
    show ?thesis using head tail some_formula by simp
  qed
qed

lemma hlReferences_subset_referenceUnion:
  assumes member: "m \<in> set ms"
      and lookup: "hlLookupLine P m = Some l"
  shows "hlReferences l \<subseteq> hlReferenceUnion P ms"
  using member
proof (induction ms)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  show ?case
  proof (cases "m = n")
    case True
    with lookup show ?thesis
      unfolding hlReferenceUnion_def hlReferencesAt_def by simp
  next
    case False
    with Cons.prems have "m \<in> set ns" by simp
    then have subset: "hlReferences l \<subseteq> hlReferenceUnion P ns"
      by (rule Cons.IH)
    show ?thesis
      using subset unfolding hlReferenceUnion_def hlReferencesAt_def
      by (cases "hlLookupLine P n") auto
  qed
qed

section \<open>Every accepted checker rule preserves truth\<close>

theorem hlRuleOK_sound:
  assumes correct: "hlCorrect P"
      and dependency_closed: "hlDependencyClosed P"
      and standard:
        "hlStandardInterpretation (M :: 'a hl_interpretation)"
      and current_lookup:
        "hlLookupLine P (hlLineNumber l) = Some l"
      and rule_ok: "hlRuleOK P l"
      and dependencies:
        "hlDependenciesTrue P M assignment (hlReferences l)"
      and cited:
        "\<And>m lm N. m \<in> set (hlCitedLines (hlJustification l)) \<Longrightarrow>
          hlLookupLine P m = Some lm \<Longrightarrow>
          hlStandardInterpretation N \<Longrightarrow>
          hlDependenciesTrue P N assignment (hlReferences lm) \<Longrightarrow>
          hlSatisfies N assignment (hlFormula lm)"
  shows "hlSatisfies M assignment (hlFormula l)"
proof (cases "hlJustification l")
  case HL_Assumption
  have refs: "hlReferences l = {hlLineNumber l}"
    using rule_ok HL_Assumption by (simp add: hlRuleOK_def)
  show ?thesis
    using dependencies current_lookup HL_Assumption refs
    unfolding hlDependenciesTrue_def by simp
next
  case (HL_MP m n)
  obtain lm ln p q where facts:
      "hlLookupLine P m = Some lm"
      "hlLookupLine P n = Some ln"
      "hlFormula lm = HL_Implies p q"
      "hlFormula ln = p"
      "hlFormula l = q"
      "hlReferences l = hlReferences lm \<union> hlReferences ln"
    using rule_ok HL_MP
    by (auto simp: hlRuleOK_def Let_def split: option.splits hl_formula.splits)
  have lm_deps: "hlDependenciesTrue P M assignment (hlReferences lm)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies]) (use facts in auto)
  have ln_deps: "hlDependenciesTrue P M assignment (hlReferences ln)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies]) (use facts in auto)
  have lm_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ facts(1) standard lm_deps]) (simp add: HL_MP)
  have ln_true: "hlSatisfies M assignment (hlFormula ln)"
    by (rule cited[OF _ facts(2) standard ln_deps]) (simp add: HL_MP)
  show ?thesis using facts lm_true ln_true by simp
next
  case (HL_MT m n)
  obtain lm ln p q where facts:
      "hlLookupLine P m = Some lm"
      "hlLookupLine P n = Some ln"
      "hlFormula lm = HL_Implies p q"
      "hlFormula ln = HL_Not q"
      "hlFormula l = HL_Not p"
      "hlReferences l = hlReferences lm \<union> hlReferences ln"
    using rule_ok HL_MT
    by (auto simp: hlRuleOK_def Let_def split: option.splits hl_formula.splits)
  have lm_deps: "hlDependenciesTrue P M assignment (hlReferences lm)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies]) (use facts in auto)
  have ln_deps: "hlDependenciesTrue P M assignment (hlReferences ln)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies]) (use facts in auto)
  have lm_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ facts(1) standard lm_deps]) (simp add: HL_MT)
  have ln_true: "hlSatisfies M assignment (hlFormula ln)"
    by (rule cited[OF _ facts(2) standard ln_deps]) (simp add: HL_MT)
  show ?thesis using facts lm_true ln_true by simp
next
  case (HL_DN m)
  have not_none: "hlLookupLine P m \<noteq> None"
    using rule_ok HL_DN
    by (auto simp: hlRuleOK_def Let_def split: option.splits)
  obtain lm where lookup: "hlLookupLine P m = Some lm"
    using not_none by (cases "hlLookupLine P m") auto
  have facts:
      "hlFormula lm = HL_Not (HL_Not (hlFormula l)) \<or>
       hlFormula l = HL_Not (HL_Not (hlFormula lm))"
      "hlReferences l = hlReferences lm"
    using rule_ok HL_DN lookup by (simp_all add: hlRuleOK_def Let_def)
  have lm_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ lookup standard])
       (use dependencies facts HL_DN in auto)
  show ?thesis using facts lm_true by auto
next
  case (HL_CP a c)
  obtain la lc where facts:
      "hlLookupLine P a = Some la"
      "hlLookupLine P c = Some lc"
      "hlJustification la = HL_Assumption"
      "hlFormula l = HL_Implies (hlFormula la) (hlFormula lc)"
      "hlReferences l = hlReferences lc - {hlLineNumber la}"
    using rule_ok HL_CP
    by (auto simp: hlRuleOK_def Let_def split: option.splits)
  have implication:
      "hlSatisfies M assignment (hlFormula la) \<longrightarrow>
       hlSatisfies M assignment (hlFormula lc)"
  proof
    assume antecedent: "hlSatisfies M assignment (hlFormula la)"
    have number: "hlLineNumber la = a"
      by (rule hlLookupLine_number[OF facts(1)])
    have discharged: "hlDependenciesTrue P M assignment
        (hlReferences lc - {a})"
      using dependencies facts(5) number by simp
    have lc_deps: "hlDependenciesTrue P M assignment (hlReferences lc)"
      by (rule hlDependenciesTrue_restore
          [OF discharged facts(1) facts(3) antecedent])
    show "hlSatisfies M assignment (hlFormula lc)"
      by (rule cited[OF _ facts(2) standard lc_deps]) (simp add: HL_CP)
  qed
  show ?thesis using implication facts by simp
next
  case (HL_AndIntro m n)
  obtain lm ln where facts:
      "hlLookupLine P m = Some lm"
      "hlLookupLine P n = Some ln"
      "hlFormula l = HL_And (hlFormula lm) (hlFormula ln) \<or>
       hlFormula l = HL_And (hlFormula ln) (hlFormula lm)"
      "hlReferences l = hlReferences lm \<union> hlReferences ln"
    using rule_ok HL_AndIntro
    by (auto simp: hlRuleOK_def Let_def split: option.splits)
  have lm_deps: "hlDependenciesTrue P M assignment (hlReferences lm)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies])
       (use facts in auto)
  have ln_deps: "hlDependenciesTrue P M assignment (hlReferences ln)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies])
       (use facts in auto)
  have lm_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ facts(1) standard lm_deps])
       (simp add: HL_AndIntro)
  have ln_true: "hlSatisfies M assignment (hlFormula ln)"
    by (rule cited[OF _ facts(2) standard ln_deps])
       (simp add: HL_AndIntro)
  show ?thesis using facts lm_true ln_true by auto
next
  case (HL_AndElim m)
  obtain lm p q where facts:
      "hlLookupLine P m = Some lm"
      "hlFormula lm = HL_And p q"
      "hlFormula l = p \<or> hlFormula l = q"
      "hlReferences l = hlReferences lm"
    using rule_ok HL_AndElim
    by (auto simp: hlRuleOK_def Let_def split: option.splits hl_formula.splits)
  have lm_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ facts(1) standard])
       (use dependencies facts HL_AndElim in auto)
  show ?thesis using facts lm_true by auto
next
  case (HL_OrIntro m)
  obtain lm p q where facts:
      "hlLookupLine P m = Some lm"
      "hlFormula l = HL_Or p q"
      "hlFormula lm = p \<or> hlFormula lm = q"
      "hlReferences l = hlReferences lm"
    using rule_ok HL_OrIntro
    by (auto simp: hlRuleOK_def Let_def split: option.splits hl_formula.splits)
  have lm_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ facts(1) standard])
       (use dependencies facts HL_OrIntro in auto)
  show ?thesis using facts lm_true by auto
next
  case (HL_OrElim d a1 c1 a2 c2)
  obtain ld la1 lc1 la2 lc2 p q where facts:
      "hlLookupLine P d = Some ld"
      "hlLookupLine P a1 = Some la1"
      "hlLookupLine P c1 = Some lc1"
      "hlLookupLine P a2 = Some la2"
      "hlLookupLine P c2 = Some lc2"
      "hlJustification la1 = HL_Assumption"
      "hlJustification la2 = HL_Assumption"
      "hlFormula lc1 = hlFormula l"
      "hlFormula lc2 = hlFormula l"
      "hlFormula ld = HL_Or p q"
      "(hlFormula la1 = p \<and> hlFormula la2 = q) \<or>
       (hlFormula la1 = q \<and> hlFormula la2 = p)"
      "hlReferences l = hlReferences ld \<union>
        (hlReferences lc1 - {hlLineNumber la1}) \<union>
        (hlReferences lc2 - {hlLineNumber la2})"
    using rule_ok HL_OrElim
    by (auto simp: hlRuleOK_def Let_def
        split: option.splits hl_formula.splits)
  have number1: "hlLineNumber la1 = a1"
    by (rule hlLookupLine_number[OF facts(2)])
  have number2: "hlLineNumber la2 = a2"
    by (rule hlLookupLine_number[OF facts(4)])
  have disjunction_deps:
      "hlDependenciesTrue P M assignment (hlReferences ld)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies])
       (use facts in auto)
  have disjunction_true:
      "hlSatisfies M assignment (hlFormula ld)"
    by (rule cited[OF _ facts(1) standard disjunction_deps])
       (simp add: HL_OrElim)
  have first_branch:
      "hlSatisfies M assignment (hlFormula la1) \<longrightarrow>
       hlSatisfies M assignment (hlFormula l)"
  proof
    assume assumption_true:
      "hlSatisfies M assignment (hlFormula la1)"
    have discharged: "hlDependenciesTrue P M assignment
        (hlReferences lc1 - {a1})"
      by (rule hlDependenciesTrue_mono[OF _ dependencies])
         (use facts number1 in auto)
    have conclusion_deps:
        "hlDependenciesTrue P M assignment (hlReferences lc1)"
      by (rule hlDependenciesTrue_restore
          [OF discharged facts(2) facts(6) assumption_true])
    have "hlSatisfies M assignment (hlFormula lc1)"
      by (rule cited[OF _ facts(3) standard conclusion_deps])
         (simp add: HL_OrElim)
    with facts show "hlSatisfies M assignment (hlFormula l)" by simp
  qed
  have second_branch:
      "hlSatisfies M assignment (hlFormula la2) \<longrightarrow>
       hlSatisfies M assignment (hlFormula l)"
  proof
    assume assumption_true:
      "hlSatisfies M assignment (hlFormula la2)"
    have discharged: "hlDependenciesTrue P M assignment
        (hlReferences lc2 - {a2})"
      by (rule hlDependenciesTrue_mono[OF _ dependencies])
         (use facts number2 in auto)
    have conclusion_deps:
        "hlDependenciesTrue P M assignment (hlReferences lc2)"
      by (rule hlDependenciesTrue_restore
          [OF discharged facts(4) facts(7) assumption_true])
    have "hlSatisfies M assignment (hlFormula lc2)"
      by (rule cited[OF _ facts(5) standard conclusion_deps])
         (simp add: HL_OrElim)
    with facts show "hlSatisfies M assignment (hlFormula l)" by simp
  qed
  show ?thesis
    using disjunction_true first_branch second_branch facts by auto
next
  case (HL_RAA a c)
  obtain la lc where facts:
      "hlLookupLine P a = Some la"
      "hlLookupLine P c = Some lc"
      "hlJustification la = HL_Assumption"
      "hlFormula l = HL_Not (hlFormula la)"
      "hlContradiction (hlFormula lc)"
      "hlReferences l = hlReferences lc - {hlLineNumber la}"
    using rule_ok HL_RAA
    by (auto simp: hlRuleOK_def Let_def split: option.splits)
  have number: "hlLineNumber la = a"
    by (rule hlLookupLine_number[OF facts(1)])
  have negation: "\<not> hlSatisfies M assignment (hlFormula la)"
  proof
    assume assumption_true: "hlSatisfies M assignment (hlFormula la)"
    have discharged: "hlDependenciesTrue P M assignment
        (hlReferences lc - {a})"
      using dependencies facts(6) number by simp
    have conclusion_deps:
        "hlDependenciesTrue P M assignment (hlReferences lc)"
      by (rule hlDependenciesTrue_restore
          [OF discharged facts(1) facts(3) assumption_true])
    have conclusion_true: "hlSatisfies M assignment (hlFormula lc)"
      by (rule cited[OF _ facts(2) standard conclusion_deps])
         (simp add: HL_RAA)
    show False
      using conclusion_true hl_contradiction_false[OF facts(5)] by blast
  qed
  show ?thesis using negation facts by simp
next
  case (HL_ForallElim m)
  obtain lm sourceVars sourceCore targetVars targetCore k where facts:
      "hlLookupLine P m = Some lm"
      "hlCollectForalls (hlFormula lm) = (sourceVars,sourceCore)"
      "hlCollectForalls (hlFormula l) = (targetVars,targetCore)"
      "hlEliminationCount sourceVars targetVars = Some k"
      "hlInferWitnessConstsK sourceVars sourceCore k targetCore \<noteq> None"
      "hlReferences l = hlReferences lm"
    using rule_ok HL_ForallElim
    by (auto simp: hlRuleOK_def Let_def
        split: option.splits prod.splits)
  have source_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ facts(1) standard])
       (use dependencies facts HL_ForallElim in auto)
  show ?thesis
    by (rule hlForallElimination_sound
        [OF standard facts(2) facts(3) facts(4) facts(5) source_true])
next
  case (HL_ExistsIntro m)
  have not_none: "hlLookupLine P m \<noteq> None"
    using rule_ok HL_ExistsIntro
    by (cases "hlLookupLine P m")
       (simp_all add: hlRuleOK_def Let_def split: prod.splits)
  obtain lm where lookup: "hlLookupLine P m = Some lm"
    using not_none by (cases "hlLookupLine P m") auto
  obtain xs core where goal_split:
      "hlCollectExists (hlFormula l) = (xs,core)"
    by (cases "hlCollectExists (hlFormula l)") auto
  have conditions:
      "xs \<noteq> []"
      "list_ex (\<lambda>k. hlInferWitnessConstsK xs
        (hlPrefixExists (drop k xs) core) k (hlFormula lm) \<noteq> None)
        [0..<Suc (length xs)]"
      "hlReferences l = hlReferences lm"
    using rule_ok HL_ExistsIntro lookup goal_split
    by (simp_all add: hlRuleOK_def Let_def)
  obtain k where member: "k \<in> set [0..<Suc (length xs)]"
      and inferred: "hlInferWitnessConstsK xs
        (hlPrefixExists (drop k xs) core) k (hlFormula lm) \<noteq> None"
    using conditions(2) unfolding list_ex_iff by blast
  have bound: "k \<le> length xs" using member by auto
  have source_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ lookup standard])
       (use dependencies conditions HL_ExistsIntro in auto)
  show ?thesis
    by (rule hlExistentialIntroduction_sound
        [OF standard goal_split bound inferred source_true])
next
  case (HL_ForallIntro m)
  have not_none: "hlLookupLine P m \<noteq> None"
    using rule_ok HL_ForallIntro
    by (cases "hlLookupLine P m")
       (simp_all add: hlRuleOK_def Let_def split: prod.splits)
  obtain lm where lookup: "hlLookupLine P m = Some lm"
    using not_none by (cases "hlLookupLine P m") auto
  obtain xs core where goal_split:
      "hlCollectForalls (hlFormula l) = (xs,core)"
    by (cases "hlCollectForalls (hlFormula l)") auto
  have nonempty: "xs \<noteq> []"
    using rule_ok HL_ForallIntro lookup goal_split
    by (simp add: hlRuleOK_def Let_def split: option.splits)
  have infer_not_none:
      "hlInferWitnessConstsK xs core (length xs) (hlFormula lm) \<noteq> None"
    using rule_ok HL_ForallIntro lookup goal_split
    by (cases "hlInferWitnessConstsK xs core (length xs) (hlFormula lm)")
       (simp_all add: hlRuleOK_def Let_def)
  obtain cs where inferred:
      "hlInferWitnessConstsK xs core (length xs) (hlFormula lm) = Some cs"
    using infer_not_none
    by (cases "hlInferWitnessConstsK xs core (length xs) (hlFormula lm)") auto
  let ?pairs = "filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs)"
  have conditions:
      "hlAbstractMany ?pairs (hlFormula lm) = Some core"
      "hlReferences l = hlReferences lm"
    using rule_ok HL_ForallIntro lookup goal_split inferred
    by (simp_all add: hlRuleOK_def Let_def)
  have checked_fresh:
      "\<forall>a b. (a,b) \<in> set (zip xs cs) \<and> b \<noteq> STR '''' \<longrightarrow>
        b \<notin> hlAssumptionConstants P (hlReferences lm)"
    using rule_ok HL_ForallIntro lookup goal_split inferred
    by (simp add: hlRuleOK_def Let_def; blast)
  have lm_member: "lm \<in> set P"
    by (rule hlLookupLine_in_set[OF lookup])
  have lm_closed: "hlReferences lm \<subseteq> hlLineNumber `
      {a \<in> set P. hlJustification a = HL_Assumption}"
    by (rule hlDependencyClosedD[OF dependency_closed lm_member])
  let ?formulas = "hlAssumptionFormulas P (hlReferences lm)"
  have formulas_true:
      "list_all (hlSatisfies M assignment) ?formulas"
  proof -
    have lm_deps: "hlDependenciesTrue P M assignment (hlReferences lm)"
      using dependencies conditions(2) by simp
    have open_semantics:
        "hlDependenciesTrue P M assignment (hlReferences lm) =
         list_all (hlSatisfies M assignment) ?formulas"
      by (rule hlDependenciesTrue_assumption_formulas
          [OF correct lm_closed])
    show ?thesis
      using lm_deps open_semantics by simp
  qed
  have fresh: "snd ` set ?pairs \<inter>
      \<Union> (hlConstantsInFormula ` set ?formulas) = {}"
    using checked_fresh
      hlAssumptionFormulas_constants[of P "hlReferences lm"]
    by auto
  have source_follows:
      "\<And>N. hlStandardInterpretation N \<Longrightarrow>
        list_all (hlSatisfies N assignment) ?formulas \<Longrightarrow>
        hlSatisfies N assignment (hlFormula lm)"
  proof -
    fix N
    assume N_standard: "hlStandardInterpretation N"
      and N_formulas: "list_all (hlSatisfies N assignment) ?formulas"
    have open_semantics:
        "hlDependenciesTrue P N assignment (hlReferences lm) =
         list_all (hlSatisfies N assignment) ?formulas"
      by (rule hlDependenciesTrue_assumption_formulas
          [OF correct lm_closed])
    have N_deps: "hlDependenciesTrue P N assignment (hlReferences lm)"
      using N_formulas open_semantics by simp
    show "hlSatisfies N assignment (hlFormula lm)"
      by (rule cited[OF _ lookup N_standard N_deps])
         (simp add: HL_ForallIntro)
  qed
  show ?thesis
    by (rule hlForallIntroduction_sound
        [OF standard goal_split inferred refl conditions(1) fresh
            source_follows formulas_true])
next
  case (HL_ExistsElim m a c)
  obtain lm la lc sourceVars sourceCore targetVars targetCore k cs where facts:
      "hlLookupLine P m = Some lm"
      "hlLookupLine P a = Some la"
      "hlLookupLine P c = Some lc"
      "hlCollectExists (hlFormula lm) = (sourceVars,sourceCore)"
      "hlCollectExists (hlFormula la) = (targetVars,targetCore)"
      "sourceVars \<noteq> []"
      "hlJustification la = HL_Assumption"
      "hlEliminationCount sourceVars targetVars = Some k"
      "hlInferWitnessConstsK sourceVars
        (hlPrefixExists targetVars sourceCore) k (hlFormula la) = Some cs"
      "hlAbstractMany
        (filter (\<lambda>xc. snd xc \<noteq> STR '''')
          (zip (take k sourceVars) cs))
        (hlFormula la) = Some (hlPrefixExists targetVars sourceCore)"
      "hlFormula l = hlFormula lc"
      "hlReferences l = hlReferences lm \<union>
        (hlReferences lc - {hlLineNumber la})"
    using rule_ok HL_ExistsElim
    by (auto simp: hlRuleOK_def Let_def
        split: option.splits prod.splits)
  let ?delta = "hlReferences lc - {hlLineNumber la}"
  let ?pairs = "filter (\<lambda>xc. snd xc \<noteq> STR '''')
    (zip (take k sourceVars) cs)"
  have checked_fresh:
      "\<forall>x w. (x,w) \<in> set (zip (take k sourceVars) cs) \<and>
        w \<noteq> STR '''' \<longrightarrow>
        w \<notin> hlConstantsInFormula (hlFormula lc) \<and>
        w \<notin> hlReferencedConstants P ?delta"
    using rule_ok HL_ExistsElim facts
    by (simp add: hlRuleOK_def Let_def; blast)
  have lm_member: "lm \<in> set P"
    by (rule hlLookupLine_in_set[OF facts(1)])
  have lc_member: "lc \<in> set P"
    by (rule hlLookupLine_in_set[OF facts(3)])
  have lm_closed: "hlReferences lm \<subseteq> hlLineNumber `
      {b \<in> set P. hlJustification b = HL_Assumption}"
    by (rule hlDependencyClosedD[OF dependency_closed lm_member])
  have lc_closed: "hlReferences lc \<subseteq> hlLineNumber `
      {b \<in> set P. hlJustification b = HL_Assumption}"
    by (rule hlDependencyClosedD[OF dependency_closed lc_member])
  have delta_closed: "?delta \<subseteq> hlLineNumber `
      {b \<in> set P. hlJustification b = HL_Assumption}"
    using lc_closed by auto
  have source_deps:
      "hlDependenciesTrue P M assignment (hlReferences lm)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies])
       (use facts in auto)
  have delta_deps: "hlDependenciesTrue P M assignment ?delta"
    by (rule hlDependenciesTrue_mono[OF _ dependencies])
       (use facts in auto)
  have source_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ facts(1) standard source_deps])
       (simp add: HL_ExistsElim)
  let ?formulas = "hlAssumptionFormulas P ?delta"
  have open_semantics:
      "hlDependenciesTrue P M assignment ?delta =
       list_all (hlSatisfies M assignment) ?formulas"
    by (rule hlDependenciesTrue_assumption_formulas
        [OF correct delta_closed])
  have formulas_true:
      "list_all (hlSatisfies M assignment) ?formulas"
    using delta_deps open_semantics by simp
  have fresh_conclusion:
      "snd ` set ?pairs \<inter> hlConstantsInFormula (hlFormula l) = {}"
    using checked_fresh facts(11) by auto
  have fresh_formulas: "snd ` set ?pairs \<inter>
      \<Union> (hlConstantsInFormula ` set ?formulas) = {}"
  proof -
    have constants: "\<Union> (hlConstantsInFormula ` set ?formulas) =
        hlAssumptionConstants P ?delta"
      by (rule hlAssumptionFormulas_constants)
    have subset: "hlAssumptionConstants P ?delta \<subseteq>
        hlReferencedConstants P ?delta"
      by (rule hlAssumptionConstants_subset_referenced)
    show ?thesis using checked_fresh constants subset by auto
  qed
  have subproof_follows:
      "\<And>N. hlStandardInterpretation N \<Longrightarrow>
        list_all (hlSatisfies N assignment) ?formulas \<Longrightarrow>
        hlSatisfies N assignment (hlFormula la) \<Longrightarrow>
        hlSatisfies N assignment (hlFormula l)"
  proof -
    fix N
    assume N_standard: "hlStandardInterpretation N"
      and N_formulas: "list_all (hlSatisfies N assignment) ?formulas"
      and assumption_true: "hlSatisfies N assignment (hlFormula la)"
    have N_open_semantics:
        "hlDependenciesTrue P N assignment ?delta =
         list_all (hlSatisfies N assignment) ?formulas"
      by (rule hlDependenciesTrue_assumption_formulas
          [OF correct delta_closed])
    have N_delta: "hlDependenciesTrue P N assignment ?delta"
      using N_formulas N_open_semantics by simp
    have number: "hlLineNumber la = a"
      by (rule hlLookupLine_number[OF facts(2)])
    have N_discharged:
        "hlDependenciesTrue P N assignment (hlReferences lc - {a})"
      using N_delta number by simp
    have N_conclusion:
        "hlDependenciesTrue P N assignment (hlReferences lc)"
      by (rule hlDependenciesTrue_restore
          [OF N_discharged facts(2) facts(7) assumption_true])
    have "hlSatisfies N assignment (hlFormula lc)"
      by (rule cited[OF _ facts(3) N_standard N_conclusion])
         (simp add: HL_ExistsElim)
    with facts show "hlSatisfies N assignment (hlFormula l)" by simp
  qed
  show ?thesis
    by (rule hlExistentialElimination_sound
        [OF standard facts(4) facts(8) facts(9) refl facts(10)
            fresh_conclusion fresh_formulas source_true
            subproof_follows formulas_true])
next
  case HL_EqIntro
  have shape: "\<exists>a. hlFormula l =
      HL_Predicate (STR ''='') [HL_Const a,HL_Const a] \<and>
      hlReferences l = {}"
  proof (cases "hlFormula l")
    case (HL_Predicate E ts)
    show ?thesis
    proof (cases ts)
      case terms_nil: Nil
      with rule_ok HL_EqIntro HL_Predicate show ?thesis
        by (simp add: hlRuleOK_def Let_def)
    next
      case terms_cons: (Cons t rest)
      show ?thesis
      proof (cases rest)
        case rest_nil: Nil
        with rule_ok HL_EqIntro HL_Predicate terms_cons show ?thesis
          by (cases t) (simp_all add: hlRuleOK_def Let_def)
      next
        case rest_cons: (Cons u tail)
        show ?thesis
        proof (cases tail)
          case tail_nil: Nil
          with rule_ok HL_EqIntro HL_Predicate terms_cons rest_cons
          show ?thesis
            by (cases t; cases u; auto simp: hlRuleOK_def Let_def)
        next
          case tail_cons: (Cons v more)
          with rule_ok HL_EqIntro HL_Predicate terms_cons rest_cons
          show ?thesis
            by (cases t; cases u; simp_all add: hlRuleOK_def Let_def)
        qed
      qed
    qed
  qed (use rule_ok HL_EqIntro in
      \<open>auto simp: hlRuleOK_def Let_def\<close>)
  then obtain a where facts:
      "hlFormula l = HL_Predicate (STR ''='') [HL_Const a,HL_Const a]"
      "hlReferences l = {}"
    by blast
  have standard_equality: "hlStandardEquality M"
    using standard unfolding hlStandardInterpretation_def by blast
  have "hlSatisfies M assignment
      (HL_Predicate (STR ''='') [HL_Const a,HL_Const a])"
    by (rule hl_equality_introduction_sound[OF standard_equality])
  with facts show ?thesis by simp
next
  case (HL_EqElim m n)
  obtain lm ln t u where preliminary:
      "hlLookupLine P m = Some lm"
      "hlLookupLine P n = Some ln"
      "hlEqualityFormula (hlFormula ln) = Some (t,u)"
    using rule_ok HL_EqElim
    by (auto simp: hlRuleOK_def Let_def
        split: option.splits prod.splits)
  obtain a b where facts:
      "hlLookupLine P m = Some lm"
      "hlLookupLine P n = Some ln"
      "hlEqualityFormula (hlFormula ln) = Some (HL_Const a,HL_Const b)"
      "hlEqualUpToConstantReplacement a b (hlFormula lm) (hlFormula l)"
      "hlReferences l = hlReferences lm \<union> hlReferences ln"
    using rule_ok HL_EqElim preliminary
    by (cases t; cases u; auto simp: hlRuleOK_def Let_def)
  have equality_formula:
      "hlFormula ln = HL_Predicate (STR ''='') [HL_Const a,HL_Const b]"
  proof (cases "hlFormula ln")
    case (HL_Predicate E ts)
    show ?thesis
    proof (cases ts)
      case terms_nil: Nil
      with facts(3) HL_Predicate show ?thesis by simp
    next
      case terms_cons: (Cons t rest)
      show ?thesis
      proof (cases rest)
        case rest_nil: Nil
        with facts(3) HL_Predicate terms_cons show ?thesis by simp
      next
        case rest_cons: (Cons u tail)
        show ?thesis
        proof (cases tail)
          case tail_nil: Nil
          with facts(3) HL_Predicate terms_cons rest_cons
          show ?thesis by (auto split: if_splits)
        next
          case tail_cons: (Cons v more)
          with facts(3) HL_Predicate terms_cons rest_cons
          show ?thesis by simp
        qed
      qed
    qed
  qed (use facts(3) in simp_all)
  have lm_deps: "hlDependenciesTrue P M assignment (hlReferences lm)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies])
       (use facts in auto)
  have ln_deps: "hlDependenciesTrue P M assignment (hlReferences ln)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies])
       (use facts in auto)
  have source_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ facts(1) standard lm_deps])
       (simp add: HL_EqElim)
  have equality_true: "hlSatisfies M assignment
      (HL_Predicate (STR ''='') [HL_Const a,HL_Const b])"
  proof -
    have "hlSatisfies M assignment (hlFormula ln)"
      by (rule cited[OF _ facts(2) standard ln_deps])
         (simp add: HL_EqElim)
    with equality_formula show ?thesis by simp
  qed
  have standard_equality: "hlStandardEquality M"
    using standard unfolding hlStandardInterpretation_def by blast
  show ?thesis
    by (rule hlEqualityElimination_sound
        [OF standard_equality equality_true source_true facts(4)])
next
  case HL_LEM
  show ?thesis
    using rule_ok HL_LEM
    by (cases "hlFormula l")
       (auto simp: hlRuleOK_def Let_def hlExcludedMiddle_def
          split: hl_formula.splits)
next
  case (HL_PropTaut ms)
  have facts:
      "list_all (\<lambda>m. hlLookupLine P m \<noteq> None) ms"
      "hlPropositionalConsequence
        (hlMapFilter (hlFormulaAt P) ms) (hlFormula l)"
      "hlReferences l = hlReferenceUnion P ms"
    using rule_ok HL_PropTaut
    by (simp_all add: hlRuleOK_def Let_def)
  have premises_true: "list_all (hlSatisfies M assignment)
      (hlMapFilter (hlFormulaAt P) ms)"
  proof (rule hlMapFilter_formulas_true)
    fix n ln
    assume member: "n \<in> set ms"
      and lookup: "hlLookupLine P n = Some ln"
    have subset: "hlReferences ln \<subseteq> hlReferenceUnion P ms"
      by (rule hlReferences_subset_referenceUnion[OF member lookup])
    have ln_deps:
        "hlDependenciesTrue P M assignment (hlReferences ln)"
      by (rule hlDependenciesTrue_mono[OF subset])
         (use dependencies facts in simp)
    show "hlSatisfies M assignment (hlFormula ln)"
      by (rule cited[OF _ lookup standard ln_deps])
         (use member HL_PropTaut in simp)
  qed
  show ?thesis
    by (rule hlPropositionalConsequence_sound
        [OF facts(2) premises_true])
next
  case (HL_IffIntro m n)
  obtain lm ln p q u v where facts:
      "hlLookupLine P m = Some lm"
      "hlLookupLine P n = Some ln"
      "hlFormula lm = HL_Implies p q"
      "hlFormula ln = HL_Implies q p"
      "hlFormula l = HL_Iff u v"
      "(u = p \<and> v = q) \<or> (u = q \<and> v = p)"
      "hlReferences l = hlReferences lm \<union> hlReferences ln"
    using rule_ok HL_IffIntro
    by (auto simp: hlRuleOK_def Let_def
        split: option.splits hl_formula.splits)
  have lm_deps: "hlDependenciesTrue P M assignment (hlReferences lm)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies])
       (use facts in auto)
  have ln_deps: "hlDependenciesTrue P M assignment (hlReferences ln)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies])
       (use facts in auto)
  have lm_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ facts(1) standard lm_deps])
       (simp add: HL_IffIntro)
  have ln_true: "hlSatisfies M assignment (hlFormula ln)"
    by (rule cited[OF _ facts(2) standard ln_deps])
       (simp add: HL_IffIntro)
  show ?thesis using facts lm_true ln_true by auto
next
  case (HL_IffElim m n)
  obtain lm ln p q where facts:
      "hlLookupLine P m = Some lm"
      "hlLookupLine P n = Some ln"
      "hlFormula lm = HL_Iff p q"
      "(hlFormula ln = p \<and> hlFormula l = q) \<or>
       (hlFormula ln = q \<and> hlFormula l = p)"
      "hlReferences l = hlReferences lm \<union> hlReferences ln"
    using rule_ok HL_IffElim
    by (auto simp: hlRuleOK_def Let_def
        split: option.splits hl_formula.splits)
  have lm_deps: "hlDependenciesTrue P M assignment (hlReferences lm)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies])
       (use facts in auto)
  have ln_deps: "hlDependenciesTrue P M assignment (hlReferences ln)"
    by (rule hlDependenciesTrue_mono[OF _ dependencies])
       (use facts in auto)
  have lm_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ facts(1) standard lm_deps])
       (simp add: HL_IffElim)
  have ln_true: "hlSatisfies M assignment (hlFormula ln)"
    by (rule cited[OF _ facts(2) standard ln_deps])
       (simp add: HL_IffElim)
  show ?thesis using facts lm_true ln_true by auto
next
  case (HL_QN m)
  obtain lm where facts:
      "hlLookupLine P m = Some lm"
      "hlQuantifierNegationEquivalent (hlFormula lm) (hlFormula l)"
      "hlReferences l = hlReferences lm"
    using rule_ok HL_QN
    by (auto simp: hlRuleOK_def Let_def split: option.splits)
  have source_true: "hlSatisfies M assignment (hlFormula lm)"
    by (rule cited[OF _ facts(1) standard])
       (use dependencies facts HL_QN in auto)
  have equivalence: "hlSatisfies M assignment (hlFormula lm) =
      hlSatisfies M assignment (hlFormula l)"
    by (rule hlQuantifierNegationEquivalent_sound[OF facts(2)])
  show ?thesis using source_true equivalence by simp
qed

section \<open>Soundness of a verified Lemmon proof\<close>

theorem hlVerifiedCorrect_line_sound:
  assumes verified: "hlVerifiedCorrect P"
      and lookup: "hlLookupLine P n = Some l"
      and standard: "hlStandardInterpretation M"
      and dependencies:
        "hlDependenciesTrue P M assignment (hlReferences l)"
  shows "hlSatisfies M assignment (hlFormula l)"
proof -
  have correct: "hlCorrect P"
    and dependency_closed: "hlDependencyClosed P"
    and canonical: "hlCanonicalOrder P"
    using verified unfolding hlVerifiedCorrect_def by blast+
  let ?R = "{(m,n::int). 0 < m \<and> m < n}"
  have well_founded: "wf ?R"
  proof (rule wf_subset[OF wf_measure[of nat]])
    show "?R \<subseteq> measure nat" by auto
  qed
  have all_lines: "\<And>n l (N :: 'a hl_interpretation) valuation.
      hlLookupLine P n = Some l \<Longrightarrow>
      hlStandardInterpretation N \<Longrightarrow>
      hlDependenciesTrue P N valuation (hlReferences l) \<Longrightarrow>
      hlSatisfies N valuation (hlFormula l)"
  proof -
    fix n l N valuation
    assume line_lookup: "hlLookupLine P n = Some l"
      and N_standard: "hlStandardInterpretation N"
      and line_dependencies:
        "hlDependenciesTrue P N valuation (hlReferences l)"
    from well_founded line_lookup N_standard line_dependencies
    show "hlSatisfies N valuation (hlFormula l)"
    proof (induction n arbitrary: l N valuation rule: wf_induct_rule)
      case (less n)
      have member: "l \<in> set P"
        by (rule hlLookupLine_in_set[OF less.prems(1)])
      have line_ok: "hlLineOK P l"
        using correct member unfolding hlCorrect_def list_all_iff by blast
      then have line_structure: "hlStructureOK P l"
        and rule_ok: "hlRuleOK P l"
        unfolding hlLineOK_def by blast+
      have number: "hlLineNumber l = n"
        by (rule hlLookupLine_number[OF less.prems(1)])
      have current_lookup:
          "hlLookupLine P (hlLineNumber l) = Some l"
        using less.prems(1) number by simp
      show "hlSatisfies N valuation (hlFormula l)"
      proof (rule hlRuleOK_sound
          [OF correct dependency_closed less.prems(2) current_lookup
              rule_ok less.prems(3)])
        fix m lm N'
        assume cited: "m \<in> set (hlCitedLines (hlJustification l))"
          and cited_lookup: "hlLookupLine P m = Some lm"
          and N'_standard: "hlStandardInterpretation N'"
          and cited_dependencies:
            "hlDependenciesTrue P N' valuation (hlReferences lm)"
        have smaller: "m < n"
          using line_structure cited number unfolding hlStructureOK_def by blast
        have positive: "0 < m"
          by (rule hlCanonicalOrder_positive[OF canonical cited_lookup])
        have relation: "(m,n) \<in> ?R" using positive smaller by simp
        show "hlSatisfies N' valuation (hlFormula lm)"
          by (rule less.IH[OF relation cited_lookup N'_standard
                cited_dependencies])
      qed
    qed
  qed
  show ?thesis by (rule all_lines[OF lookup standard dependencies])
qed

lemma hlOpenPremises_as_assumption_formulas:
  assumes "P \<noteq> []"
  shows "hlOpenPremises P =
    hlAssumptionFormulas P (hlReferences (last P))"
  using assms
  unfolding hlOpenPremises_def hlAssumptionFormulas_def by simp

theorem hlVerifiedCorrect_sound:
  assumes verified: "hlVerifiedCorrect P"
      and standard: "hlStandardInterpretation M"
      and conclusion: "hlConclusion P = Some goal"
      and premises_true:
        "list_all (hlSatisfies M assignment) (hlOpenPremises P)"
  shows "hlSatisfies M assignment goal"
proof -
  have nonempty: "P \<noteq> []"
    using conclusion unfolding hlConclusion_def by auto
  have correct: "hlCorrect P"
    and dependency_closed: "hlDependencyClosed P"
    using verified unfolding hlVerifiedCorrect_def by blast+
  have last_member: "last P \<in> set P"
    using nonempty by simp
  have last_lookup:
      "hlLookupLine P (hlLineNumber (last P)) = Some (last P)"
    by (rule hlCorrect_lookup_self[OF correct last_member])
  have last_closed: "hlReferences (last P) \<subseteq> hlLineNumber `
      {a \<in> set P. hlJustification a = HL_Assumption}"
    by (rule hlDependencyClosedD
        [OF dependency_closed last_member])
  have open_formulas: "hlOpenPremises P =
      hlAssumptionFormulas P (hlReferences (last P))"
    by (rule hlOpenPremises_as_assumption_formulas[OF nonempty])
  have open_semantics:
      "hlDependenciesTrue P M assignment (hlReferences (last P)) =
       list_all (hlSatisfies M assignment)
        (hlAssumptionFormulas P (hlReferences (last P)))"
    by (rule hlDependenciesTrue_assumption_formulas
        [OF correct last_closed])
  have last_dependencies:
      "hlDependenciesTrue P M assignment (hlReferences (last P))"
    using premises_true open_formulas open_semantics by simp
  have last_true: "hlSatisfies M assignment (hlFormula (last P))"
    by (rule hlVerifiedCorrect_line_sound
        [OF verified last_lookup standard last_dependencies])
  have goal: "goal = hlFormula (last P)"
    using conclusion nonempty unfolding hlConclusion_def by simp
  with last_true show ?thesis by simp
qed

end
