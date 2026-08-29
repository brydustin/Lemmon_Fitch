(*  Title:      LF_Halvorson_Formula.thy

    A total Isabelle model of the formula language in
    Halvorson/lemmon-checker-main/src/ProofTypes.hs.  This datatype is kept
    distinct from the paper-oriented internal datatype fm: PredFormula has a
    genuine Boolean constructor and represents equality by the predicate name
    "=".  Keeping those choices makes the Haskell program reproducible rather
    than silently normalising its input language.
*)

theory LF_Halvorson_Formula
  imports LF_Formula
begin

section \<open>The formula datatype implemented in Haskell\<close>

type_synonym hl_name = String.literal

datatype hl_term =
    HL_Var hl_name
  | HL_Const hl_name

datatype hl_formula =
    HL_Predicate hl_name "hl_term list"
  | HL_Boolean bool
  | HL_Not hl_formula
  | HL_And hl_formula hl_formula
  | HL_Or hl_formula hl_formula
  | HL_Implies hl_formula hl_formula
  | HL_Iff hl_formula hl_formula
  | HL_ForAll hl_name hl_formula
  | HL_Exists hl_name hl_formula

type_synonym halvorson_term = hl_term
type_synonym halvorson_formula = hl_formula

abbreviation hlFalsum :: hl_formula (\<open>\<bottom>\<^sub>H\<close>) where
  "\<bottom>\<^sub>H \<equiv> HL_Boolean False"

abbreviation hlVerum :: hl_formula (\<open>\<top>\<^sub>H\<close>) where
  "\<top>\<^sub>H \<equiv> HL_Boolean True"

abbreviation hlNegation :: "hl_formula \<Rightarrow> hl_formula"
    (\<open>\<not>\<^sub>H _\<close> [40] 40) where
  "\<not>\<^sub>H p \<equiv> HL_Not p"

abbreviation hlConjunction :: "hl_formula \<Rightarrow> hl_formula \<Rightarrow> hl_formula"
    (infixr \<open>\<and>\<^sub>H\<close> 35) where
  "p \<and>\<^sub>H q \<equiv> HL_And p q"

abbreviation hlDisjunction :: "hl_formula \<Rightarrow> hl_formula \<Rightarrow> hl_formula"
    (infixr \<open>\<or>\<^sub>H\<close> 30) where
  "p \<or>\<^sub>H q \<equiv> HL_Or p q"

abbreviation hlImplication :: "hl_formula \<Rightarrow> hl_formula \<Rightarrow> hl_formula"
    (infixr \<open>\<longrightarrow>\<^sub>H\<close> 25) where
  "p \<longrightarrow>\<^sub>H q \<equiv> HL_Implies p q"

abbreviation hlBiconditional :: "hl_formula \<Rightarrow> hl_formula \<Rightarrow> hl_formula"
    (infixr \<open>\<longleftrightarrow>\<^sub>H\<close> 25) where
  "p \<longleftrightarrow>\<^sub>H q \<equiv> HL_Iff p q"

abbreviation hlEquality :: "hl_term \<Rightarrow> hl_term \<Rightarrow> hl_formula"
    (infix \<open>=\<^sub>H\<close> 50) where
  "t =\<^sub>H u \<equiv> HL_Predicate (STR ''='') [t,u]"

abbreviation hlUniversal :: "hl_name \<Rightarrow> hl_formula \<Rightarrow> hl_formula"
    (\<open>\<forall>\<^sub>H _./ _\<close> [0,10] 10) where
  "\<forall>\<^sub>H x. p \<equiv> HL_ForAll x p"

abbreviation hlExistential :: "hl_name \<Rightarrow> hl_formula \<Rightarrow> hl_formula"
    (\<open>\<exists>\<^sub>H _./ _\<close> [0,10] 10) where
  "\<exists>\<^sub>H x. p \<equiv> HL_Exists x p"

section \<open>Total versions of ProofTypes operations\<close>

fun hlVariablesInTerm :: "hl_term \<Rightarrow> hl_name set" where
  "hlVariablesInTerm (HL_Var x) = {x}"
| "hlVariablesInTerm (HL_Const _) = {}"

fun hlConstantsInTerm :: "hl_term \<Rightarrow> hl_name set" where
  "hlConstantsInTerm (HL_Var _) = {}"
| "hlConstantsInTerm (HL_Const a) = {a}"

fun hlVariablesInFormula :: "hl_formula \<Rightarrow> hl_name set" where
  "hlVariablesInFormula (HL_Predicate _ ts) = \<Union> (hlVariablesInTerm ` set ts)"
| "hlVariablesInFormula (HL_Boolean _) = {}"
| "hlVariablesInFormula (HL_Not p) = hlVariablesInFormula p"
| "hlVariablesInFormula (HL_And p q) = hlVariablesInFormula p \<union> hlVariablesInFormula q"
| "hlVariablesInFormula (HL_Or p q) = hlVariablesInFormula p \<union> hlVariablesInFormula q"
| "hlVariablesInFormula (HL_Implies p q) = hlVariablesInFormula p \<union> hlVariablesInFormula q"
| "hlVariablesInFormula (HL_Iff p q) = hlVariablesInFormula p \<union> hlVariablesInFormula q"
| "hlVariablesInFormula (HL_ForAll _ p) = hlVariablesInFormula p"
| "hlVariablesInFormula (HL_Exists _ p) = hlVariablesInFormula p"

fun hlConstantsInFormula :: "hl_formula \<Rightarrow> hl_name set" where
  "hlConstantsInFormula (HL_Predicate _ ts) = \<Union> (hlConstantsInTerm ` set ts)"
| "hlConstantsInFormula (HL_Boolean _) = {}"
| "hlConstantsInFormula (HL_Not p) = hlConstantsInFormula p"
| "hlConstantsInFormula (HL_And p q) = hlConstantsInFormula p \<union> hlConstantsInFormula q"
| "hlConstantsInFormula (HL_Or p q) = hlConstantsInFormula p \<union> hlConstantsInFormula q"
| "hlConstantsInFormula (HL_Implies p q) = hlConstantsInFormula p \<union> hlConstantsInFormula q"
| "hlConstantsInFormula (HL_Iff p q) = hlConstantsInFormula p \<union> hlConstantsInFormula q"
| "hlConstantsInFormula (HL_ForAll _ p) = hlConstantsInFormula p"
| "hlConstantsInFormula (HL_Exists _ p) = hlConstantsInFormula p"

fun hlFreeVariables :: "hl_formula \<Rightarrow> hl_name set" where
  "hlFreeVariables (HL_Predicate _ ts) = \<Union> (hlVariablesInTerm ` set ts)"
| "hlFreeVariables (HL_Boolean _) = {}"
| "hlFreeVariables (HL_Not p) = hlFreeVariables p"
| "hlFreeVariables (HL_And p q) = hlFreeVariables p \<union> hlFreeVariables q"
| "hlFreeVariables (HL_Or p q) = hlFreeVariables p \<union> hlFreeVariables q"
| "hlFreeVariables (HL_Implies p q) = hlFreeVariables p \<union> hlFreeVariables q"
| "hlFreeVariables (HL_Iff p q) = hlFreeVariables p \<union> hlFreeVariables q"
| "hlFreeVariables (HL_ForAll x p) = hlFreeVariables p - {x}"
| "hlFreeVariables (HL_Exists x p) = hlFreeVariables p - {x}"

fun hlSubstituteTerm :: "hl_name \<Rightarrow> hl_term \<Rightarrow> hl_term \<Rightarrow> hl_term" where
  "hlSubstituteTerm x t (HL_Var y) = (if x = y then t else HL_Var y)"
| "hlSubstituteTerm x t (HL_Const a) = HL_Const a"

fun hlSubstituteFree :: "hl_name \<Rightarrow> hl_term \<Rightarrow> hl_formula \<Rightarrow> hl_formula" where
  "hlSubstituteFree x t (HL_Predicate P ts) =
     HL_Predicate P (map (hlSubstituteTerm x t) ts)"
| "hlSubstituteFree x t (HL_Boolean b) = HL_Boolean b"
| "hlSubstituteFree x t (HL_Not p) = HL_Not (hlSubstituteFree x t p)"
| "hlSubstituteFree x t (HL_And p q) =
     HL_And (hlSubstituteFree x t p) (hlSubstituteFree x t q)"
| "hlSubstituteFree x t (HL_Or p q) =
     HL_Or (hlSubstituteFree x t p) (hlSubstituteFree x t q)"
| "hlSubstituteFree x t (HL_Implies p q) =
     HL_Implies (hlSubstituteFree x t p) (hlSubstituteFree x t q)"
| "hlSubstituteFree x t (HL_Iff p q) =
     HL_Iff (hlSubstituteFree x t p) (hlSubstituteFree x t q)"
| "hlSubstituteFree x t (HL_ForAll y p) =
     HL_ForAll y (if x = y then p else hlSubstituteFree x t p)"
| "hlSubstituteFree x t (HL_Exists y p) =
     HL_Exists y (if x = y then p else hlSubstituteFree x t p)"

fun hlFreeForUnder :: "hl_name set \<Rightarrow> hl_name \<Rightarrow> hl_term \<Rightarrow> hl_formula \<Rightarrow> bool" where
  "hlFreeForUnder B x t (HL_Predicate P ts) \<longleftrightarrow>
     (\<forall>u \<in> set ts. case u of
        HL_Var y \<Rightarrow> y \<noteq> x \<or> hlVariablesInTerm t \<inter> B = {}
      | HL_Const _ \<Rightarrow> True)"
| "hlFreeForUnder B x t (HL_Boolean _) \<longleftrightarrow> True"
| "hlFreeForUnder B x t (HL_Not p) \<longleftrightarrow> hlFreeForUnder B x t p"
| "hlFreeForUnder B x t (HL_And p q) \<longleftrightarrow>
     hlFreeForUnder B x t p \<and> hlFreeForUnder B x t q"
| "hlFreeForUnder B x t (HL_Or p q) \<longleftrightarrow>
     hlFreeForUnder B x t p \<and> hlFreeForUnder B x t q"
| "hlFreeForUnder B x t (HL_Implies p q) \<longleftrightarrow>
     hlFreeForUnder B x t p \<and> hlFreeForUnder B x t q"
| "hlFreeForUnder B x t (HL_Iff p q) \<longleftrightarrow>
     hlFreeForUnder B x t p \<and> hlFreeForUnder B x t q"
| "hlFreeForUnder B x t (HL_ForAll y p) \<longleftrightarrow>
     hlFreeForUnder (insert y B) x t p"
| "hlFreeForUnder B x t (HL_Exists y p) \<longleftrightarrow>
     hlFreeForUnder (insert y B) x t p"

definition hlFreeFor :: "hl_name \<Rightarrow> hl_term \<Rightarrow> hl_formula \<Rightarrow> bool" where
  "hlFreeFor x t p \<longleftrightarrow> hlFreeForUnder {} x t p"

fun hlReplaceConstantInTerm :: "hl_name \<Rightarrow> hl_name \<Rightarrow> hl_term \<Rightarrow> hl_term" where
  "hlReplaceConstantInTerm a x (HL_Const b) =
     (if a = b then HL_Var x else HL_Const b)"
| "hlReplaceConstantInTerm a x (HL_Var y) = HL_Var y"

fun hlAbstractConstantFree ::
    "hl_name \<Rightarrow> hl_name \<Rightarrow> hl_formula \<Rightarrow> hl_formula option" where
  "hlAbstractConstantFree a x (HL_Predicate P ts) =
     Some (HL_Predicate P (map (hlReplaceConstantInTerm a x) ts))"
| "hlAbstractConstantFree a x (HL_Boolean b) = Some (HL_Boolean b)"
| "hlAbstractConstantFree a x (HL_Not p) =
     map_option HL_Not (hlAbstractConstantFree a x p)"
| "hlAbstractConstantFree a x (HL_And p q) =
     (case (hlAbstractConstantFree a x p,hlAbstractConstantFree a x q) of
        (Some r,Some s) \<Rightarrow> Some (HL_And r s) | _ \<Rightarrow> None)"
| "hlAbstractConstantFree a x (HL_Or p q) =
     (case (hlAbstractConstantFree a x p,hlAbstractConstantFree a x q) of
        (Some r,Some s) \<Rightarrow> Some (HL_Or r s) | _ \<Rightarrow> None)"
| "hlAbstractConstantFree a x (HL_Implies p q) =
     (case (hlAbstractConstantFree a x p,hlAbstractConstantFree a x q) of
        (Some r,Some s) \<Rightarrow> Some (HL_Implies r s) | _ \<Rightarrow> None)"
| "hlAbstractConstantFree a x (HL_Iff p q) =
     (case (hlAbstractConstantFree a x p,hlAbstractConstantFree a x q) of
        (Some r,Some s) \<Rightarrow> Some (HL_Iff r s) | _ \<Rightarrow> None)"
| "hlAbstractConstantFree a x (HL_ForAll y p) =
     (if y = x then None else map_option (HL_ForAll y) (hlAbstractConstantFree a x p))"
| "hlAbstractConstantFree a x (HL_Exists y p) =
     (if y = x then None else map_option (HL_Exists y) (hlAbstractConstantFree a x p))"

fun hlAbstractMany ::
    "(hl_name \<times> hl_name) list \<Rightarrow> hl_formula \<Rightarrow> hl_formula option" where
  "hlAbstractMany [] p = Some p"
| "hlAbstractMany ((x,a) # ps) p =
     (case hlAbstractConstantFree a x p of
        None \<Rightarrow> None
      | Some q \<Rightarrow> hlAbstractMany ps q)"

fun hlEqualityFormula :: "hl_formula \<Rightarrow> (hl_term \<times> hl_term) option" where
  "hlEqualityFormula (HL_Predicate P [t,u]) =
     (if P = STR ''='' then Some (t,u) else None)"
| "hlEqualityFormula _ = None"

fun hlTermEqualUpToConstantReplacement ::
    "hl_name \<Rightarrow> hl_name \<Rightarrow> hl_term \<Rightarrow> hl_term \<Rightarrow> bool" where
  "hlTermEqualUpToConstantReplacement a b (HL_Var x) (HL_Var y) \<longleftrightarrow> x = y"
| "hlTermEqualUpToConstantReplacement a b (HL_Const c) (HL_Const d) \<longleftrightarrow>
     (c = a \<and> d = b) \<or> c = d"
| "hlTermEqualUpToConstantReplacement a b _ _ \<longleftrightarrow> False"

fun hlEqualUpToConstantReplacement ::
    "hl_name \<Rightarrow> hl_name \<Rightarrow> hl_formula \<Rightarrow> hl_formula \<Rightarrow> bool" where
  "hlEqualUpToConstantReplacement a b p q =
     (case p of
        HL_Predicate P ts \<Rightarrow>
          (case q of HL_Predicate Q us \<Rightarrow>
             P = Q \<and> list_all2 (hlTermEqualUpToConstantReplacement a b) ts us
           | _ \<Rightarrow> False)
      | HL_Boolean c \<Rightarrow>
          (case q of HL_Boolean d \<Rightarrow> c = d | _ \<Rightarrow> False)
      | HL_Not r \<Rightarrow>
          (case q of HL_Not s \<Rightarrow> hlEqualUpToConstantReplacement a b r s
           | _ \<Rightarrow> False)
      | HL_And r s \<Rightarrow>
          (case q of HL_And u v \<Rightarrow>
             hlEqualUpToConstantReplacement a b r u \<and>
             hlEqualUpToConstantReplacement a b s v
           | _ \<Rightarrow> False)
      | HL_Or r s \<Rightarrow>
          (case q of HL_Or u v \<Rightarrow>
             hlEqualUpToConstantReplacement a b r u \<and>
             hlEqualUpToConstantReplacement a b s v
           | _ \<Rightarrow> False)
      | HL_Implies r s \<Rightarrow>
          (case q of HL_Implies u v \<Rightarrow>
             hlEqualUpToConstantReplacement a b r u \<and>
             hlEqualUpToConstantReplacement a b s v
           | _ \<Rightarrow> False)
      | HL_Iff r s \<Rightarrow>
          (case q of HL_Iff u v \<Rightarrow>
             hlEqualUpToConstantReplacement a b r u \<and>
             hlEqualUpToConstantReplacement a b s v
           | _ \<Rightarrow> False)
      | HL_ForAll x r \<Rightarrow>
          (case q of HL_ForAll y s \<Rightarrow>
             x = y \<and> hlEqualUpToConstantReplacement a b r s
           | _ \<Rightarrow> False)
      | HL_Exists x r \<Rightarrow>
          (case q of HL_Exists y s \<Rightarrow>
             x = y \<and> hlEqualUpToConstantReplacement a b r s
           | _ \<Rightarrow> False))"

section \<open>Quantifier-prefix operations used by the checker\<close>

fun hlCollectForalls :: "hl_formula \<Rightarrow> hl_name list \<times> hl_formula" where
  "hlCollectForalls (HL_ForAll x p) =
     (let (xs,q) = hlCollectForalls p in (x # xs,q))"
| "hlCollectForalls p = ([],p)"

fun hlCollectExists :: "hl_formula \<Rightarrow> hl_name list \<times> hl_formula" where
  "hlCollectExists (HL_Exists x p) =
     (let (xs,q) = hlCollectExists p in (x # xs,q))"
| "hlCollectExists p = ([],p)"

definition hlPrefixForalls :: "hl_name list \<Rightarrow> hl_formula \<Rightarrow> hl_formula" where
  "hlPrefixForalls xs p = foldr HL_ForAll xs p"

definition hlPrefixExists :: "hl_name list \<Rightarrow> hl_formula \<Rightarrow> hl_formula" where
  "hlPrefixExists xs p = foldr HL_Exists xs p"

definition hlEliminationCount :: "hl_name list \<Rightarrow> hl_name list \<Rightarrow> nat option" where
  "hlEliminationCount source destination =
     (let k = length source - length destination
      in if length destination \<le> length source \<and> drop k source = destination
         then Some k else None)"

text \<open>
  The Haskell implementation uses the empty string as the marker for a
  vacuous quantifier.  We retain that representation here so that even this
  implementation detail can be tested against generated code.
\<close>

fun hlWitnessLists ::
    "hl_name list \<Rightarrow> hl_formula \<Rightarrow> hl_formula \<Rightarrow> hl_name list list" where
  "hlWitnessLists [] p q = (if p = q then [[]] else [])"
| "hlWitnessLists (x # xs) p q =
     (if x \<notin> hlFreeVariables p
      then map ((#) (STR '''')) (hlWitnessLists xs p q)
      else concat
        (map (\<lambda>a. map ((#) a)
                    (hlWitnessLists xs (hlSubstituteFree x (HL_Const a) p) q))
             (sorted_list_of_set (hlConstantsInFormula q))))"

definition hlInferWitnessConstsK ::
    "hl_name list \<Rightarrow> hl_formula \<Rightarrow> nat \<Rightarrow> hl_formula
      \<Rightarrow> hl_name list option" where
  "hlInferWitnessConstsK xs p k q =
     (let candidates = hlWitnessLists (take k xs) p q
      in if candidates = [] then None else Some (last candidates))"

fun hlQuantifierNegationForms :: "hl_formula \<Rightarrow> hl_formula list" where
  "hlQuantifierNegationForms (HL_Not (HL_ForAll x p)) =
     HL_Not (HL_ForAll x p) #
       map (HL_Exists x) (hlQuantifierNegationForms (HL_Not p))"
| "hlQuantifierNegationForms (HL_Not (HL_Exists x p)) =
     HL_Not (HL_Exists x p) #
       map (HL_ForAll x) (hlQuantifierNegationForms (HL_Not p))"
| "hlQuantifierNegationForms (HL_ForAll x p) =
     map (HL_ForAll x) (hlQuantifierNegationForms p)"
| "hlQuantifierNegationForms (HL_Exists x p) =
     map (HL_Exists x) (hlQuantifierNegationForms p)"
| "hlQuantifierNegationForms p = [p]"

definition hlQuantifierNegationReachable :: "hl_formula \<Rightarrow> hl_formula \<Rightarrow> bool" where
  "hlQuantifierNegationReachable p q \<longleftrightarrow>
     (case p of HL_Not _ \<Rightarrow> q \<in> set (hlQuantifierNegationForms p) | _ \<Rightarrow> False)"

definition hlQuantifierNegationEquivalent :: "hl_formula \<Rightarrow> hl_formula \<Rightarrow> bool" where
  "hlQuantifierNegationEquivalent p q \<longleftrightarrow>
     hlQuantifierNegationReachable p q \<or> hlQuantifierNegationReachable q p"

section \<open>Regression guards for formerly partial Haskell cases\<close>

lemma hl_boolean_operations_are_total:
  "hlVariablesInFormula (HL_Boolean b) = {} \<and>
   hlConstantsInFormula (HL_Boolean b) = {} \<and>
   hlFreeVariables (HL_Boolean b) = {} \<and>
   hlSubstituteFree x t (HL_Boolean b) = HL_Boolean b \<and>
   hlAbstractConstantFree a x (HL_Boolean b) = Some (HL_Boolean b)"
  by simp

lemma hl_biconditional_replacement_is_total:
  "hlEqualUpToConstantReplacement a b (HL_Iff p q) (HL_Iff r s) \<longleftrightarrow>
   hlEqualUpToConstantReplacement a b p r \<and>
   hlEqualUpToConstantReplacement a b q s"
  by simp

end
