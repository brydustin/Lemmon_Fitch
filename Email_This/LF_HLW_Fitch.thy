(*  Title:      LF_HLW_Fitch.thy

    Isabelle representation of Halvorson/lemmon-checker-main/src/FitchTypes.hs
    and the total Fitch-to-Lemmon half of FitchConvert.hs.
*)

theory LF_HLW_Fitch
  imports LF_HLW
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
  cited by a discharge rule actually names a subproof, nor that the proof ends
  at the outermost level.  The exact behavior is useful for correspondence
  tests. The stronger predicate below checks genuine nesting, placement and
  order, the flattened Lemmon proof, and the displayed sequent boundary.
\<close>

text \<open>The condition the Haskell omits.  A proof's conclusion is the formula on
  its last line, so that line must stand outside every box: a proof ending
  inside an undischarged subproof asserts something it never established.  This
  is \<open>concludesAtTop\<close> of \<open>LF_Fitch.thy\<close>, on the exact datatypes.  (That
  theory is not imported here: the authoritative layer is a parallel stack over
  \<open>LF_Formula.thy\<close>, so the condition is restated rather than reused.)\<close>

definition hlConcludesAtTop :: "hl_fitch_proof \<Rightarrow> bool" where
  "hlConcludesAtTop F \<longleftrightarrow>
     (F = [] \<or> (case last F of HL_FLine _ _ _ \<Rightarrow> True | HL_FSub _ \<Rightarrow> False))"

section \<open>Verified nesting and the sequent boundary\<close>

fun hlFitchCitedSubs :: "hl_fitch_rule \<Rightarrow> hl_subproof_reference list" where
  "hlFitchCitedSubs (HL_FCP s) = [s]"
| "hlFitchCitedSubs (HL_FRAA s) = [s]"
| "hlFitchCitedSubs (HL_FOrE _ s1 s2) = [s1,s2]"
| "hlFitchCitedSubs (HL_FExistsE _ s) = [s]"
| "hlFitchCitedSubs _ = []"

text \<open>Ordinary citations see only earlier lines in the same box or an
  enclosing box. Completed subproofs are kept separately, and their pairs may
  be cited only at the level where those subproofs occur. Closing a box restores
  the earlier line environment; neither its assumption nor its last line
  becomes an ordinary accessible line. A box must end at its own level.\<close>

fun hlFitchNestingFrom ::
    "nat \<Rightarrow> int set \<Rightarrow> hl_subproof_reference set \<Rightarrow>
      hl_fitch_proof \<Rightarrow> bool" where
  "hlFitchNestingFrom depth visible boxes [] = True"
| "hlFitchNestingFrom depth visible boxes (HL_FLine n p r # rest) =
     (r \<noteq> HL_FAssume \<and>
      (r = HL_FPremise \<longrightarrow> depth = 0) \<and>
      set (hlFitchCitedLines r) \<subseteq> visible \<and>
      set (hlFitchCitedSubs r) \<subseteq> boxes \<and>
      hlFitchNestingFrom depth (insert n visible) boxes rest)"
| "hlFitchNestingFrom depth visible boxes
       (HL_FSub (HL_Subproof a p body) # rest) =
     (hlConcludesAtTop body \<and>
      hlFitchNestingFrom (Suc depth) (insert a visible) {} body \<and>
      hlFitchNestingFrom depth visible
        (insert (a,hlSubLastLine (HL_Subproof a p body)) boxes) rest)"

definition hlFitchPremisesFirst :: "hl_fitch_proof \<Rightarrow> bool" where
  "hlFitchPremisesFirst F \<longleftrightarrow>
     list_all (\<lambda>(n,p,r). r \<noteq> HL_FPremise)
       (dropWhile (\<lambda>(n,p,r). r = HL_FPremise) (hlFlattenFitch F))"

definition hlFitchNestedWellFormed :: "hl_fitch_proof \<Rightarrow> bool" where
  "hlFitchNestedWellFormed F \<longleftrightarrow>
     hlFitchNestingFrom 0 {} {} F \<and> hlFitchPremisesFirst F \<and>
     list_all (\<lambda>n. 0 < n) (hlFitchLineNumbers F) \<and>
     sorted_wrt (<) (hlFitchLineNumbers F) \<and> hlConcludesAtTop F"

fun hlFitchPremises :: "hl_fitch_proof \<Rightarrow> hl_formula list" where
  "hlFitchPremises [] = []"
| "hlFitchPremises (HL_FLine n p r # rest) =
     (if r = HL_FPremise then p # hlFitchPremises rest else hlFitchPremises rest)"
| "hlFitchPremises (HL_FSub s # rest) = hlFitchPremises rest"

definition hlFitchConclusion :: "hl_fitch_proof \<Rightarrow> hl_formula option" where
  "hlFitchConclusion F =
     (if hlFlattenFitch F = [] then None
      else Some (fst (snd (last (hlFlattenFitch F)))))"

text \<open>The erased Lemmon proof must assert a consequence of the displayed
  outer premises. This is an explicit executable invariant at the sequent
  boundary, in addition to the independent nesting check. No theorem here
  assumes that this invariant follows from the other checks.\<close>

definition hlFitchPremiseClosed :: "hl_fitch_proof \<Rightarrow> bool" where
  "hlFitchPremiseClosed F \<longleftrightarrow>
     set (hlOpenPremises (\<delta>\<^sub>H F)) \<subseteq> set (hlFitchPremises F)"

definition hlFitchVerified :: "hl_fitch_proof \<Rightarrow> bool" where
  "hlFitchVerified F \<longleftrightarrow>
     hlFitchWellFormed F \<and> hlConcludesAtTop F \<and>
     hlFitchNestedWellFormed F \<and> hlFitchPremiseClosed F \<and>
     hlVerifiedCorrect (\<delta>\<^sub>H F)"

lemma hlFitchToLemmonFrom_formulas:
  "map hlFormula (snd (hlFitchToLemmonFrom env ls)) = map (fst \<circ> snd) ls"
  by (induction ls arbitrary: env)
     (auto simp: Let_def case_prod_beta split: prod.splits)

lemma hlFitchConclusion_delta:
  "hlConclusion (\<delta>\<^sub>H F) = hlFitchConclusion F"
proof -
  have formulas:
    "map hlFormula (\<delta>\<^sub>H F) = map (fst \<circ> snd) (hlFlattenFitch F)"
    by (simp add: hlFitchToLemmon_def hlFitchToLemmonFrom_formulas)
  have empty: "(\<delta>\<^sub>H F = []) = (hlFlattenFitch F = [])"
    using formulas by (metis map_is_Nil_conv)
  have last_formulas:
    "last (map hlFormula (\<delta>\<^sub>H F)) =
     last (map (fst \<circ> snd) (hlFlattenFitch F))"
    using formulas by simp
  show ?thesis
    using last_formulas empty
    by (auto simp: hlConclusion_def hlFitchConclusion_def last_map)
qed

text \<open>The witness the omission admits: a bare subproof, accepted by the
  Haskell-faithful check, rejected by the verified one.\<close>

definition hlOpenAssumptionFitch :: hl_fitch_proof where
  "hlOpenAssumptionFitch = [HL_FSub (HL_Subproof 1 (HL_Predicate (STR ''P'') []) [])]"

lemma hlOpenAssumptionFitch_wellFormed_but_not_verified:
  "hlFitchWellFormed hlOpenAssumptionFitch"
  "\<not> hlConcludesAtTop hlOpenAssumptionFitch"
  "\<not> hlFitchVerified hlOpenAssumptionFitch"
  by eval+

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
