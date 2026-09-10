(*  Title:      LF_HLW_Report.thy

    Diagnostics for the authoritative checker.  hlLineOK answers yes or no;
    the handwritten checker answers with a message.  This theory supplies the
    structured reason, so that a caller can render Halvorson's exact wording
    while the decision itself stays the one the theorems are about.

    The bridge is hlLineError_None: the diagnostic reports no error exactly
    when hlLineOK holds.  Everything already proved of hlLineOK therefore
    transfers, and the messages add no trust.

    Isabelle's String.literal generates to ASCII only (see Str_Literal.hs in
    the export: it raises on any code point above 127), and the handwritten
    messages are full of U+274C and the logical connectives.  So the wording
    cannot live here.  It lives in the renderer, driven by the constructors
    below; this theory owns which error and with what data.
*)

theory LF_HLW_Report
  imports LF_HLW_Delta
begin

section \<open>The structured reason a line fails\<close>

datatype hl_check_error =
    HL_DuplicateLine int int
      \<comment> \<open>the line number, and how many lines carry it\<close>
  | HL_LateCitation int "int list"
      \<comment> \<open>the line number, and the cited lines that do not come earlier\<close>
  | HL_InvalidAssumption int
      \<comment> \<open>the line number: an assumption whose dependency set is not itself\<close>
  | HL_MissingCited hl_justification int
      \<comment> \<open>the rule, and the line number, when a citation names no line.  The
        source words this differently for each rule, so the renderer needs the
        rule as well as the number.\<close>
  | HL_MPFirstNotConditional int
      \<comment> \<open>MP: the first cited line is not a conditional\<close>
  | HL_MPSecondNotAntecedent int
      \<comment> \<open>MP: the second cited line is not its antecedent\<close>
  | HL_AndElimNotConjunction int
      \<comment> \<open>the cited line, which is not a conjunction\<close>
  | HL_OrIntroNotDisjunct
      \<comment> \<open>the goal does not contain the cited formula as a disjunct\<close>
  | HL_DNShape int
      \<comment> \<open>the line: neither cited formula is the double negation of the other\<close>
  | HL_MTFailed int int int bool bool bool
      \<comment> \<open>line, the two cited lines, and whether the pattern matches, whether it
        matches with the citations reversed, and whether the dependencies are
        the union.  The source composes its sentence from these three.\<close>
  | HL_EqElimNotEquality
      \<comment> \<open>=E: the second cited line is not an equality between two constants\<close>
  | HL_AndIntroMismatch int hl_formula hl_formula hl_formula
      \<comment> \<open>line, the two cited formulas, and the goal.  The source quotes all
        three, so they travel to the renderer rather than being rendered here:
        Isabelle's string literals are ASCII and the connectives are not.\<close>
  | HL_MPNotConsequent hl_formula
      \<comment> \<open>the expected consequent, which the source quotes with Haskell's
        derived \<open>show\<close> rather than with its pretty-printer\<close>
  | HL_ForallIntroNotInstance int
      \<comment> \<open>the cited line, not recognisable as an instance of the goal\<close>
  | HL_ForallIntroAbstraction
      \<comment> \<open>abstracting the instance does not give the goal's core\<close>
  | HL_ForallElimNoConstants
      \<comment> \<open>no constants instantiate the eliminated variables\<close>
  | HL_ExistsIntroNotWitness
      \<comment> \<open>the cited line is not a witness instance of the goal\<close>
  | HL_ExistsElimNotAssumption int
      \<comment> \<open>the assumption line, which is not an assumption\<close>
  | HL_ExistsElimNotRepeated int int
      \<comment> \<open>this line and the subproof's last line, whose formula it must repeat\<close>
  | HL_RAAFailed int int int bool bool bool "int list" "int list"
      \<comment> \<open>line, the assumption line, the contradiction line, and whether each
        of the three conditions holds, then the expected and actual references.
        The source concatenates one clause per failure.\<close>
  | HL_OrElimFailed int int int int bool bool
      \<comment> \<open>line, the disjunction line, the two assumption lines, and whether
        each assumption really is one\<close>
  | HL_RuleRejected hl_justification int
      \<comment> \<open>the rule and the line number, when every citation resolves but the
        rule's own condition fails.  The source words this per rule.\<close>
  | HL_RuleFailed int
      \<comment> \<open>the line number: a failure not yet refined further\<close>

section \<open>Structural errors\<close>

text \<open>Mirrors \<open>checkStructure\<close>: a line number used more than once, or a
  citation to a line whose number is not smaller.  The order of the two tests
  is the source's, because a line failing both must report the first.\<close>

definition hlStructureError :: "hl_proof \<Rightarrow> hl_line \<Rightarrow> hl_check_error option" where
  "hlStructureError P l =
     (let n = hlLineNumber l;
          dupes = length (filter (\<lambda>k. hlLineNumber k = n) P);
          late  = filter (\<lambda>m. \<not> m < n) (hlCitedLines (hlJustification l))
      in if 1 < dupes then Some (HL_DuplicateLine n (int dupes))
         else if late \<noteq> [] then Some (HL_LateCitation n late)
         else None)"

text \<open>The two agree on the lines of the proof.  The hypothesis is needed and is
  not a technicality: @{const hlStructureOK} demands that the line occur
  exactly once, while \<open>checkStructure\<close> only rejects it for occurring more than
  once, so the two differ on a line that is not in the proof at all.  That case
  never arises in @{const hlCorrect}, which applies the check to the proof's own
  lines.\<close>

lemma hlStructureError_None:
  assumes "l \<in> set P"
  shows "hlStructureError P l = None \<longleftrightarrow> hlStructureOK P l"
proof -
  have "1 \<le> length (filter (\<lambda>k. hlLineNumber k = hlLineNumber l) P)"
    using assms by (induction P) auto
  then show ?thesis
    by (auto simp: hlStructureError_def hlStructureOK_def Let_def
                   filter_empty_conv not_less)
qed

section \<open>The whole line check\<close>

text \<open>Which message a failing rule gets.  The decision that the rule fails is
  @{const hlRuleOK}'s and is not re-derived here: this only chooses how to
  describe a failure that has already been established.  That is what keeps
  \<open>hlRuleError_None\<close> trivial, and it is why adding messages
  cannot change which proofs are accepted.\<close>

definition hlAnyCitationMissing :: "hl_proof \<Rightarrow> hl_justification \<Rightarrow> bool" where
  "hlAnyCitationMissing P j =
     (\<exists>m \<in> set (hlCitedLines j). hlLookupLine P m = None)"

text \<open>The pattern Modus Tollens wants, as the source states it: a conditional,
  the negation of its consequent, and the negation of its antecedent.\<close>

definition hlIsMT :: "hl_formula \<Rightarrow> hl_formula \<Rightarrow> hl_formula \<Rightarrow> bool" where
  "hlIsMT a b goal =
     (case (a, b, goal) of
        (HL_Implies phi psi, HL_Not psi', HL_Not phi') \<Rightarrow> psi = psi' \<and> phi = phi'
      | _ \<Rightarrow> False)"

text \<open>Which condition of a rule failed, when every citation resolves.  Only
  the rules whose wording the renderer distinguishes are refined here; the rest
  fall through to @{const HL_RuleRejected}, which names the rule.\<close>

fun hlRejectionReason ::
    "hl_proof \<Rightarrow> hl_line \<Rightarrow> hl_justification \<Rightarrow> int \<Rightarrow> hl_check_error" where
  "hlRejectionReason P l (HL_MP m k) n =
     (case hlLookupLine P m of
        Some lm \<Rightarrow>
          (case hlFormula lm of
             HL_Implies p q \<Rightarrow>
               (case hlLookupLine P k of
                  Some lk \<Rightarrow> (if hlFormula lk \<noteq> p
                                then HL_MPSecondNotAntecedent n
                                else if hlFormula l \<noteq> q
                                then HL_MPNotConsequent q
                                else HL_RuleRejected (HL_MP m k) n)
                | None \<Rightarrow> HL_RuleRejected (HL_MP m k) n)
           | _ \<Rightarrow> HL_MPFirstNotConditional n)
      | None \<Rightarrow> HL_RuleRejected (HL_MP m k) n)"
| "hlRejectionReason P l (HL_AndElim m) n =
     (case hlLookupLine P m of
        Some lm \<Rightarrow> (case hlFormula lm of
                        HL_And _ _ \<Rightarrow> HL_RuleRejected (HL_AndElim m) n
                      | _ \<Rightarrow> HL_AndElimNotConjunction m)
      | None \<Rightarrow> HL_RuleRejected (HL_AndElim m) n)"
| "hlRejectionReason P l (HL_OrIntro m) n =
     (case hlFormula l of
        HL_Or _ _ \<Rightarrow> HL_OrIntroNotDisjunct
      | _ \<Rightarrow> HL_RuleRejected (HL_OrIntro m) n)"
| "hlRejectionReason P l (HL_DN m) n = HL_DNShape n"
| "hlRejectionReason P l (HL_ForallIntro m) n =
     (case hlLookupLine P m of
        Some lm \<Rightarrow>
          (let (xs, core) = hlCollectForalls (hlFormula l)
           in if xs = [] then HL_RuleRejected (HL_ForallIntro m) n
              else (case hlInferWitnessConstsK xs core (length xs) (hlFormula lm) of
                      None \<Rightarrow> HL_ForallIntroNotInstance m
                    | Some cs \<Rightarrow>
                        (let pairs = filter (\<lambda>xc. snd xc \<noteq> STR '''') (zip xs cs)
                         in if hlAbstractMany pairs (hlFormula lm) \<noteq> Some core
                              then HL_ForallIntroAbstraction
                              else HL_RuleRejected (HL_ForallIntro m) n)))
      | None \<Rightarrow> HL_RuleRejected (HL_ForallIntro m) n)"
| "hlRejectionReason P l (HL_ForallElim m) n =
     (case hlLookupLine P m of
        Some lm \<Rightarrow>
          (let (sv, sc) = hlCollectForalls (hlFormula lm);
               (dv, dc) = hlCollectForalls (hlFormula l)
           in (case hlEliminationCount sv dv of
                 None \<Rightarrow> HL_RuleRejected (HL_ForallElim m) n
               | Some k \<Rightarrow>
                   (case hlInferWitnessConstsK sv sc k dc of
                      None \<Rightarrow> HL_ForallElimNoConstants
                    | Some _ \<Rightarrow> HL_RuleRejected (HL_ForallElim m) n)))
      | None \<Rightarrow> HL_RuleRejected (HL_ForallElim m) n)"
| "hlRejectionReason P l (HL_ExistsIntro m) n =
     (case hlLookupLine P m of
        Some lm \<Rightarrow>
          (let (xs, _) = hlCollectExists (hlFormula l)
           in if xs = [] then HL_RuleRejected (HL_ExistsIntro m) n
              else HL_ExistsIntroNotWitness)
      | None \<Rightarrow> HL_RuleRejected (HL_ExistsIntro m) n)"
| "hlRejectionReason P l (HL_ExistsElim m a c) n =
     (case (hlLookupLine P m, hlLookupLine P a, hlLookupLine P c) of
        (Some lm, Some la, Some lc) \<Rightarrow>
          (let (sv, _) = hlCollectExists (hlFormula lm)
           in if sv = [] then HL_RuleRejected (HL_ExistsElim m a c) n
              else if hlJustification la \<noteq> HL_Assumption
                then HL_ExistsElimNotAssumption a
              else if hlFormula l \<noteq> hlFormula lc
                then HL_ExistsElimNotRepeated n c
              else HL_RuleRejected (HL_ExistsElim m a c) n)
      | _ \<Rightarrow> HL_RuleRejected (HL_ExistsElim m a c) n)"
| "hlRejectionReason P l (HL_RAA m k) n =
     (case (hlLookupLine P m, hlLookupLine P k) of
        (Some lm, Some lk) \<Rightarrow>
          (let expected = hlReferences lk - {hlLineNumber lm}
           in HL_RAAFailed n m k
                (hlJustification lm = HL_Assumption)
                (case hlFormula lk of
                   HL_And ps (HL_Not ps') \<Rightarrow> ps = ps'
                 | HL_And (HL_Not ps) ps' \<Rightarrow> ps = ps'
                 | _ \<Rightarrow> False)
                (hlFormula l = HL_Not (hlFormula lm))
                (sorted_list_of_set expected)
                (sorted_list_of_set (hlReferences l)))
      | _ \<Rightarrow> HL_RuleRejected (HL_RAA m k) n)"
| "hlRejectionReason P l (HL_OrElim d a1 c1 a2 c2) n =
     (case (hlLookupLine P a1, hlLookupLine P a2) of
        (Some la1, Some la2) \<Rightarrow>
          HL_OrElimFailed n d a1 a2
            (hlJustification la1 = HL_Assumption)
            (hlJustification la2 = HL_Assumption)
      | _ \<Rightarrow> HL_RuleRejected (HL_OrElim d a1 c1 a2 c2) n)"
| "hlRejectionReason P l (HL_AndIntro m k) n =
     (case (hlLookupLine P m, hlLookupLine P k) of
        (Some lm, Some lk) \<Rightarrow>
          (if hlFormula l \<noteq> HL_And (hlFormula lm) (hlFormula lk) \<and>
              hlFormula l \<noteq> HL_And (hlFormula lk) (hlFormula lm)
             then HL_AndIntroMismatch n (hlFormula lm) (hlFormula lk) (hlFormula l)
             else HL_RuleRejected (HL_AndIntro m k) n)
      | _ \<Rightarrow> HL_RuleRejected (HL_AndIntro m k) n)"
| "hlRejectionReason P l (HL_EqElim m k) n =
     (case hlLookupLine P k of
        Some lk \<Rightarrow>
          (case hlFormula lk of
             HL_Predicate e [HL_Const a, HL_Const b] \<Rightarrow>
               (if e = STR ''='' then HL_RuleRejected (HL_EqElim m k) n
                else HL_EqElimNotEquality)
           | _ \<Rightarrow> HL_EqElimNotEquality)
      | None \<Rightarrow> HL_RuleRejected (HL_EqElim m k) n)"
| "hlRejectionReason P l (HL_MT m k) n =
     (case (hlLookupLine P m, hlLookupLine P k) of
        (Some lm, Some lk) \<Rightarrow>
          HL_MTFailed n m k
            (hlIsMT (hlFormula lm) (hlFormula lk) (hlFormula l))
            (hlIsMT (hlFormula lk) (hlFormula lm) (hlFormula l))
            (hlReferences l = hlReferences lm \<union> hlReferences lk)
      | _ \<Rightarrow> HL_RuleRejected (HL_MT m k) n)"
| "hlRejectionReason P l j n = HL_RuleRejected j n"

definition hlRuleError :: "hl_proof \<Rightarrow> hl_line \<Rightarrow> hl_check_error option" where
  "hlRuleError P l =
     (if hlRuleOK P l then None
      else Some (let n = hlLineNumber l; j = hlJustification l in
                 if j = HL_Assumption then HL_InvalidAssumption n
                 else if hlAnyCitationMissing P j then HL_MissingCited j n
                 else hlRejectionReason P l j n))"



lemma hlRuleError_None: "hlRuleError P l = None \<longleftrightarrow> hlRuleOK P l"
  by (simp add: hlRuleError_def)

definition hlLineError :: "hl_proof \<Rightarrow> hl_line \<Rightarrow> hl_check_error option" where
  "hlLineError P l =
     (case hlStructureError P l of
        Some e \<Rightarrow> Some e
      | None \<Rightarrow> hlRuleError P l)"

theorem hlLineError_None:
  assumes "l \<in> set P"
  shows "hlLineError P l = None \<longleftrightarrow> hlLineOK P l"
  using hlStructureError_None [OF assms]
  by (auto simp: hlLineError_def hlLineOK_def hlRuleError_None split: option.splits)

text \<open>So a report built from @{const hlLineError} accepts exactly the proofs
  @{const hlCorrect} accepts.\<close>

definition hlProofReport :: "hl_proof \<Rightarrow> (int \<times> hl_check_error option) list" where
  "hlProofReport P = map (\<lambda>l. (hlLineNumber l, hlLineError P l)) P"

theorem hlProofReport_valid:
  "list_all (\<lambda>e. snd e = None) (hlProofReport P) \<longleftrightarrow> hlCorrect P"
proof -
  have "list_all (\<lambda>e. snd e = None) (hlProofReport P)
          \<longleftrightarrow> (\<forall>l \<in> set P. hlLineError P l = None)"
    by (auto simp: hlProofReport_def list_all_iff)
  also have "\<dots> \<longleftrightarrow> (\<forall>l \<in> set P. hlLineOK P l)"
    using hlLineError_None by blast
  also have "\<dots> \<longleftrightarrow> hlCorrect P"
    by (simp add: hlCorrect_def list_all_iff)
  finally show ?thesis .
qed

end
