(*  Title:      LF_Halvorson_Fitch.thy

    Isabelle representation of Halvorson/lemmon-checker-main/src/FitchTypes.hs
    and the total Fitch-to-Lemmon half of FitchConvert.hs.
*)

theory LF_Halvorson_Fitch
  imports LF_Halvorson
begin

section \<open>The Fitch datatype implemented in Haskell\<close>

type_synonym hl_subproof_reference = "int \<times> int"

datatype hl_fitch_rule =
    HL_FPremise
  | HL_FAssume
  | HL_FMP int int
  | HL_FMT int int
  | HL_FDN int
  | HL_FCP hl_subproof_reference
  | HL_FAndI int int
  | HL_FAndE int
  | HL_FOrI int
  | HL_FOrE int hl_subproof_reference hl_subproof_reference
  | HL_FRAA hl_subproof_reference
  | HL_FForallE int
  | HL_FForallI int
  | HL_FExistsI int
  | HL_FExistsE int hl_subproof_reference
  | HL_FEqI
  | HL_FEqE int int
  | HL_FLEM
  | HL_FPropTaut "int list"
  | HL_FIffI int int
  | HL_FIffE int int
  | HL_FQN int
  | HL_FReit int

datatype hl_fitch_item =
    HL_FLine int hl_formula hl_fitch_rule
  | HL_FSub hl_subproof
and hl_subproof =
    HL_Subproof int hl_formula "hl_fitch_item list"

type_synonym hl_fitch_proof = "hl_fitch_item list"

fun hlSubAssumptionLine :: "hl_subproof \<Rightarrow> int" where
  "hlSubAssumptionLine (HL_Subproof a p body) = a"

fun hlSubAssumptionFormula :: "hl_subproof \<Rightarrow> hl_formula" where
  "hlSubAssumptionFormula (HL_Subproof a p body) = p"

fun hlSubBody :: "hl_subproof \<Rightarrow> hl_fitch_item list" where
  "hlSubBody (HL_Subproof a p body) = body"

fun hlFitchLineNumbers :: "hl_fitch_proof \<Rightarrow> int list"
and hlFitchItemLineNumbers :: "hl_fitch_item \<Rightarrow> int list" where
  "hlFitchLineNumbers [] = []"
| "hlFitchLineNumbers (i # is) = hlFitchItemLineNumbers i @ hlFitchLineNumbers is"
| "hlFitchItemLineNumbers (HL_FLine n p r) = [n]"
| "hlFitchItemLineNumbers (HL_FSub (HL_Subproof a p body)) =
     a # hlFitchLineNumbers body"

fun hlSubLastLine :: "hl_subproof \<Rightarrow> int" where
  "hlSubLastLine (HL_Subproof a p body) =
     (if hlFitchLineNumbers body = [] then a else last (hlFitchLineNumbers body))"

fun hlItemLastLine :: "hl_fitch_item \<Rightarrow> int" where
  "hlItemLastLine (HL_FLine n p r) = n"
| "hlItemLastLine (HL_FSub s) = hlSubLastLine s"

section \<open>Rule correspondence and \<delta>\<close>

fun hlFitchCitedLines :: "hl_fitch_rule \<Rightarrow> int list" where
  "hlFitchCitedLines HL_FPremise = []"
| "hlFitchCitedLines HL_FAssume = []"
| "hlFitchCitedLines (HL_FMP m n) = [m,n]"
| "hlFitchCitedLines (HL_FMT m n) = [m,n]"
| "hlFitchCitedLines (HL_FDN m) = [m]"
| "hlFitchCitedLines (HL_FCP s) = []"
| "hlFitchCitedLines (HL_FAndI m n) = [m,n]"
| "hlFitchCitedLines (HL_FAndE m) = [m]"
| "hlFitchCitedLines (HL_FOrI m) = [m]"
| "hlFitchCitedLines (HL_FOrE d s1 s2) = [d]"
| "hlFitchCitedLines (HL_FRAA s) = []"
| "hlFitchCitedLines (HL_FForallE m) = [m]"
| "hlFitchCitedLines (HL_FForallI m) = [m]"
| "hlFitchCitedLines (HL_FExistsI m) = [m]"
| "hlFitchCitedLines (HL_FExistsE m s) = [m]"
| "hlFitchCitedLines HL_FEqI = []"
| "hlFitchCitedLines (HL_FEqE m n) = [m,n]"
| "hlFitchCitedLines HL_FLEM = []"
| "hlFitchCitedLines (HL_FPropTaut ms) = ms"
| "hlFitchCitedLines (HL_FIffI m n) = [m,n]"
| "hlFitchCitedLines (HL_FIffE m n) = [m,n]"
| "hlFitchCitedLines (HL_FQN m) = [m]"
| "hlFitchCitedLines (HL_FReit m) = [m]"

fun hlToLemmonRule :: "hl_fitch_rule \<Rightarrow> hl_justification" where
  "hlToLemmonRule HL_FPremise = HL_Assumption"
| "hlToLemmonRule HL_FAssume = HL_Assumption"
| "hlToLemmonRule (HL_FMP m n) = HL_MP m n"
| "hlToLemmonRule (HL_FMT m n) = HL_MT m n"
| "hlToLemmonRule (HL_FDN m) = HL_DN m"
| "hlToLemmonRule (HL_FCP (a,c)) = HL_CP a c"
| "hlToLemmonRule (HL_FAndI m n) = HL_AndIntro m n"
| "hlToLemmonRule (HL_FAndE m) = HL_AndElim m"
| "hlToLemmonRule (HL_FOrI m) = HL_OrIntro m"
| "hlToLemmonRule (HL_FOrE d (a1,c1) (a2,c2)) = HL_OrElim d a1 c1 a2 c2"
| "hlToLemmonRule (HL_FRAA (a,c)) = HL_RAA a c"
| "hlToLemmonRule (HL_FForallE m) = HL_ForallElim m"
| "hlToLemmonRule (HL_FForallI m) = HL_ForallIntro m"
| "hlToLemmonRule (HL_FExistsI m) = HL_ExistsIntro m"
| "hlToLemmonRule (HL_FExistsE m (a,c)) = HL_ExistsElim m a c"
| "hlToLemmonRule HL_FEqI = HL_EqIntro"
| "hlToLemmonRule (HL_FEqE m n) = HL_EqElim m n"
| "hlToLemmonRule HL_FLEM = HL_LEM"
| "hlToLemmonRule (HL_FPropTaut ms) = HL_PropTaut ms"
| "hlToLemmonRule (HL_FIffI m n) = HL_IffIntro m n"
| "hlToLemmonRule (HL_FIffE m n) = HL_IffElim m n"
| "hlToLemmonRule (HL_FQN m) = HL_QN m"
| "hlToLemmonRule (HL_FReit m) = HL_PropTaut [m]"

fun hlFlattenFitch :: "hl_fitch_proof \<Rightarrow> (int \<times> hl_formula \<times> hl_fitch_rule) list"
and hlFlattenFitchItem :: "hl_fitch_item \<Rightarrow> (int \<times> hl_formula \<times> hl_fitch_rule) list" where
  "hlFlattenFitch [] = []"
| "hlFlattenFitch (i # is) = hlFlattenFitchItem i @ hlFlattenFitch is"
| "hlFlattenFitchItem (HL_FLine n p r) = [(n,p,r)]"
| "hlFlattenFitchItem (HL_FSub (HL_Subproof a p body)) =
     (a,p,HL_FAssume) # hlFlattenFitch body"

fun hlDependencyLookup :: "(int \<times> int set) list \<Rightarrow> int \<Rightarrow> int set" where
  "hlDependencyLookup [] n = {}"
| "hlDependencyLookup ((m,G) # env) n =
     (if m = n then G else hlDependencyLookup env n)"

definition hlFitchDependenciesOf ::
    "(int \<Rightarrow> int set) \<Rightarrow> hl_fitch_rule \<Rightarrow> int \<Rightarrow> int set" where
  "hlFitchDependenciesOf look r self =
     (case r of
        HL_FPremise \<Rightarrow> {self}
      | HL_FAssume \<Rightarrow> {self}
      | HL_FCP (a,c) \<Rightarrow> look c - {a}
      | HL_FRAA (a,c) \<Rightarrow> look c - {a}
      | HL_FOrE d (a1,c1) (a2,c2) \<Rightarrow>
          look d \<union> (look c1 - {a1}) \<union> (look c2 - {a2})
      | HL_FExistsE m (a,c) \<Rightarrow> look m \<union> (look c - {a})
      | _ \<Rightarrow> \<Union> (set (map look (hlFitchCitedLines r))))"

fun hlFitchToLemmonFrom ::
    "(int \<times> int set) list \<Rightarrow>
      (int \<times> hl_formula \<times> hl_fitch_rule) list \<Rightarrow>
      (int \<times> int set) list \<times> hl_proof" where
  "hlFitchToLemmonFrom env [] = (env,[])"
| "hlFitchToLemmonFrom env ((n,p,r) # ls) =
     (let G = hlFitchDependenciesOf (hlDependencyLookup env) r n;
          line = HL_ProofLine n p (hlToLemmonRule r) G;
          (env',tail) = hlFitchToLemmonFrom ((n,G) # env) ls
      in (env',line # tail))"

definition hlFitchToLemmon :: "hl_fitch_proof \<Rightarrow> hl_proof" where
  "hlFitchToLemmon F = snd (hlFitchToLemmonFrom [] (hlFlattenFitch F))"

abbreviation hlDelta :: "hl_fitch_proof \<Rightarrow> hl_proof" (\<open>\<delta>\<^sub>H _\<close> [1000] 1000) where
  "\<delta>\<^sub>H F \<equiv> hlFitchToLemmon F"

section \<open>The structural check in FitchTypes.hs\<close>

fun hlFitchScopeFrom ::
    "nat \<Rightarrow> int set \<Rightarrow> hl_fitch_proof \<Rightarrow> int set option" where
  "hlFitchScopeFrom depth visible [] = Some visible"
| "hlFitchScopeFrom depth visible (HL_FLine n p r # rest) =
     (if (case r of HL_FPremise \<Rightarrow> depth = 0 | _ \<Rightarrow> True) \<and>
         set (hlFitchCitedLines r) \<subseteq> visible
      then hlFitchScopeFrom depth (insert n visible) rest
      else None)"
| "hlFitchScopeFrom depth visible
       (HL_FSub (HL_Subproof a p body) # rest) =
     (case hlFitchScopeFrom (Suc depth) (insert a visible) body of
        None \<Rightarrow> None
      | Some _ \<Rightarrow>
          hlFitchScopeFrom depth (insert a (insert (hlSubLastLine (HL_Subproof a p body)) visible)) rest)"

definition hlFitchWellFormed :: "hl_fitch_proof \<Rightarrow> bool" where
  "hlFitchWellFormed F \<longleftrightarrow> hlFitchScopeFrom 0 {} F \<noteq> None"

text \<open>
  As in the Haskell source, this check does not validate that a subproof pair
  cited by a discharge rule actually names a subproof.  The exact behavior is
  useful for correspondence tests; verified translation will use a stronger
  predicate that checks the flattened Lemmon proof as well.
\<close>

definition hlFitchVerified :: "hl_fitch_proof \<Rightarrow> bool" where
  "hlFitchVerified F \<longleftrightarrow>
     hlFitchWellFormed F \<and> hlVerifiedCorrect (\<delta>\<^sub>H F)"

section \<open>Executable examples\<close>

definition hl_fitch_mp_example :: hl_fitch_proof where
  "hl_fitch_mp_example =
     [ HL_FLine 1 (hlP \<longrightarrow>\<^sub>H hlQ) HL_FPremise,
       HL_FLine 2 hlP HL_FPremise,
       HL_FLine 3 hlQ (HL_FMP 1 2) ]"

definition hl_fitch_cp_example :: hl_fitch_proof where
  "hl_fitch_cp_example =
     [ HL_FLine 1 hlP HL_FPremise,
       HL_FSub (HL_Subproof 2 hlQ
         [HL_FLine 3 hlP (HL_FReit 1)]),
       HL_FLine 4 (hlQ \<longrightarrow>\<^sub>H hlP) (HL_FCP (2,3)) ]"

lemma hl_delta_mp_example:
  "\<delta>\<^sub>H hl_fitch_mp_example = hl_mp_example"
  by eval

lemma hl_delta_cp_example:
  "hlFitchVerified hl_fitch_cp_example \<and>
   hlCorrect (\<delta>\<^sub>H hl_fitch_cp_example)"
  by eval

end
