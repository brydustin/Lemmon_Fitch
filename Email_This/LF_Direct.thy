(*  Title:      LF_Direct.thy

    Section 4 of the paper: the positional translation from Lemmon to Fitch,
    the three ways it can fail, and Theorem 10.
*)

theory LF_Direct
  imports LF_Delta
begin

section \<open>The positional translation\<close>

text \<open>A translation is \emph{positional} (Definition 9) if it preserves the
  sequence of lines: the \<open>n\<close>th line of the Lemmon proof becomes the \<open>n\<close>th line
  of the Fitch proof, with the same formula and the corresponding rule.

  A positional image is determined by one thing only: where the boxes go.  Each
  discharging justification names a pair @{term "(a, c)"} --- an assumption line
  and a line derived from it --- and in the image that pair must be the first and
  last line of a subproof.  So the boxes of a positional image are exactly the
  intervals @{term "[a, c]"} named by the discharging rules, and the translation
  succeeds precisely when those intervals can be the subproofs of a Fitch proof.
  Three things can go wrong, and they are the paper's three constructors.\<close>

datatype translation_error =
    NotNested nat nat "nat list"     \<comment> \<open>line, assumption discharged, boxes open\<close>
  | OutOfScope nat nat nat           \<comment> \<open>line, line cited, box that closed over it\<close>
  | PremiseInBox nat nat             \<comment> \<open>line, the box it was written inside\<close>
  | PremiseLate nat nat              \<comment> \<open>premise line, the earlier line that is not one\<close>
  | BoxReversed nat nat              \<comment> \<open>assumption discharged, the line it was discharged from\<close>
  | AssumptionReused nat nat nat     \<comment> \<open>assumption line, and the two lines discharging it\<close>
  | NotCorrect nat                   \<comment> \<open>the source is not a correct Lemmon proof\<close>

subsection \<open>The rule correspondence, the other way\<close>

fun toFitchRule :: "just \<Rightarrow> fitch_rule" where
  "toFitchRule Assumption = FPremise"
| "toFitchRule (MP i j) = FMP i j"
| "toFitchRule (CP a c) = FCP (a, c)"
| "toFitchRule (RAA a c) = FRAA (a, c)"
| "toFitchRule (DN i) = FDN i"
| "toFitchRule (BotI i j) = FBotI i j"
| "toFitchRule (AndIntro i j) = FAndIntro i j"
| "toFitchRule (AndElimL i) = FAndElimL i"
| "toFitchRule (AndElimR i) = FAndElimR i"
| "toFitchRule (OrIntroL i) = FOrIntroL i"
| "toFitchRule (OrIntroR i) = FOrIntroR i"
| "toFitchRule (OrElim d a1 c1 a2 c2) = FOrElim d (a1, c1) (a2, c2)"
| "toFitchRule (IffIntro i j) = FIffIntro i j"
| "toFitchRule (IffElimL i) = FIffElimL i"
| "toFitchRule (IffElimR i) = FIffElimR i"
| "toFitchRule (ForallElim i) = FForallElim i"
| "toFitchRule (ForallIntro i) = FForallIntro i"
| "toFitchRule (ExistsIntro i) = FExistsIntro i"
| "toFitchRule (ExistsElim m a c) = FExistsElim m (a, c)"
| "toFitchRule EqIntro = FEqIntro"
| "toFitchRule (EqElim i j) = FEqElim i j"
| "toFitchRule (Reit i) = FReit i"

text \<open>The two rule maps are a section and a retraction: the Fitch rule set says
  everything the Lemmon rule set says, and the only thing it says in addition is
  whether an undischarged assumption is a premise.\<close>

lemma toLemmonRule_toFitchRule [simp]: "toLemmonRule (toFitchRule j) = j"
  by (cases j) auto

subsection \<open>Boxes\<close>

definition boxesOf :: "lemmon_proof \<Rightarrow> (nat \<times> nat) list" where
  "boxesOf P = concat (map (\<lambda>l. dischargePairs (justification l)) P)"

definition dischargedAssumps :: "lemmon_proof \<Rightarrow> nat list" where
  "dischargedAssumps P = map fst (boxesOf P)"

definition dischargerOf :: "lemmon_proof \<Rightarrow> nat \<times> nat \<Rightarrow> nat" where
  "dischargerOf P ac =
     (case find (\<lambda>l. ac \<in> set (dischargePairs (justification l))) P of
        Some l \<Rightarrow> lineNumber l | None \<Rightarrow> 0)"

text \<open>The boxes a line sits inside, outermost first.\<close>

definition boxPath :: "lemmon_proof \<Rightarrow> nat \<Rightarrow> nat list" where
  "boxPath P m = sort (map fst (filter (\<lambda>ac. fst ac \<le> m \<and> m \<le> snd ac) (boxesOf P)))"

subsection \<open>The three obstructions\<close>

text \<open>A sixth obstruction, and the first one the others all presuppose: a
  discharge must run forwards.  Lemmon writes \<open>CP a c\<close> for ``discharge the
  assumption at line \<open>a\<close> from line \<open>c\<close>'', and nothing requires \<open>a\<close> to precede
  \<open>c\<close> --- a vacuous discharge, where \<open>c\<close> does not depend on \<open>a\<close> at all, may cite
  an assumption made after it.  The interval \<open>[a, c]\<close> is then empty, and a box
  cannot be built from it: the subproof would have no last line inside itself.

  This is checked first, because every check below reads a box as an interval and
  reasons about the lines between its endpoints.\<close>

definition boxOrderError :: "lemmon_proof \<Rightarrow> translation_error option" where
  "boxOrderError P =
     (case filter (\<lambda>ac. snd ac < fst ac) (boxesOf P) of
        [] \<Rightarrow> None
      | ac # _ \<Rightarrow> Some (BoxReversed (fst ac) (snd ac)))"

lemma boxOrderError_None:
  assumes "boxOrderError P = None" and "ac \<in> set (boxesOf P)"
  shows "fst ac \<le> snd ac"
proof -
  from assms(1) have "filter (\<lambda>ac. snd ac < fst ac) (boxesOf P) = []"
    unfolding boxOrderError_def by (auto split: list.splits)
  with assms(2) show ?thesis by (auto simp: filter_empty_conv)
qed

text \<open>A seventh obstruction.  Lemmon may discharge one assumption more than once,
  from two different lines --- \<open>CP a c\<close> and \<open>CP a c'\<close> with \<open>c \<noteq> c'\<close> --- and the
  two boxes then share their opening line.  A positional image would need two
  subproofs starting at the same line, which is impossible: \<open>buildItems\<close> below
  builds one of them, and the other discharge cites a subproof that is not there.

  Discharging the same assumption twice from the \emph{same} line is harmless ---
  the two pairs are equal and name one subproof --- so the check compares the
  closing lines, not the number of discharges.\<close>

definition boxHeadError :: "lemmon_proof \<Rightarrow> translation_error option" where
  "boxHeadError P =
     (case filter (\<lambda>x. fst (fst x) = fst (snd x) \<and> snd (fst x) \<noteq> snd (snd x))
                  (List.product (boxesOf P) (boxesOf P)) of
        [] \<Rightarrow> None
      | x # _ \<Rightarrow> Some (AssumptionReused (fst (fst x)) (snd (fst x)) (snd (snd x))))"

lemma boxHeadError_None:
  assumes "boxHeadError P = None"
      and "ac \<in> set (boxesOf P)" and "b \<in> set (boxesOf P)" and "fst ac = fst b"
  shows "snd ac = snd b"
proof -
  from assms(1)
  have H:
    "filter (\<lambda>x. fst (fst x) = fst (snd x) \<and> snd (fst x) \<noteq> snd (snd x))
               (List.product (boxesOf P) (boxesOf P)) = []"
    unfolding boxHeadError_def
    by (auto split: list.splits)

  have prod_mem:
    "(ac, b) \<in> set (List.product (boxesOf P) (boxesOf P))"
    using assms(2,3)
    by auto

  from H prod_mem assms(4)
  show ?thesis
    by (auto simp: filter_empty_conv)
qed

text \<open>Two boxes overlap improperly when neither contains the other and they are
  not disjoint.  Fitch permits discharge only in last-in-first-out order; Lemmon
  imposes no such restriction, and this is Example 11.\<close>

definition overlapping :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "overlapping ac b \<longleftrightarrow> fst ac < fst b \<and> fst b \<le> snd ac \<and> snd ac < snd b"

definition nestingError :: "lemmon_proof \<Rightarrow> translation_error option" where
  "nestingError P =
     (case filter (\<lambda>ac. \<exists>b \<in> set (boxesOf P). overlapping ac b) (boxesOf P) of
        [] \<Rightarrow> None
      | ac # _ \<Rightarrow>
          Some (NotNested (dischargerOf P ac) (fst ac)
                  (map fst (filter (overlapping ac) (boxesOf P)))))"

text \<open>An assumption never discharged becomes a premise, and a premise may stand
  only at the outermost level.\<close>

definition premiseError :: "lemmon_proof \<Rightarrow> translation_error option" where
  "premiseError P =
     (case filter (\<lambda>l. justification l = Assumption
                        \<and> lineNumber l \<notin> set (dischargedAssumps P)
                        \<and> boxPath P (lineNumber l) \<noteq> []) P of
        [] \<Rightarrow> None
      | l # _ \<Rightarrow> Some (PremiseInBox (lineNumber l) (last (boxPath P (lineNumber l)))))"

text \<open>A line written between an assumption and its discharge lies inside the box,
  and passes out of scope when the box closes --- even if it never depended on
  the assumption.  This is Example 12, and it is the obstruction that has nothing
  to do with the order of discharges.\<close>

fun firstDiff :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
  "firstDiff [] ys = 0"
| "firstDiff (x # xs) [] = x"
| "firstDiff (x # xs) (y # ys) = (if x = y then firstDiff xs ys else x)"

definition badCitations :: "lemmon_proof \<Rightarrow> (nat \<times> nat) list" where
  "badCitations P =
     concat (map (\<lambda>l. map (Pair (lineNumber l))
                       (filter (\<lambda>m. \<not> is_prefix (boxPath P m) (boxPath P (lineNumber l)))
                               (fCitedLines (toFitchRule (justification l)))))
                 P)"

definition scopeError :: "lemmon_proof \<Rightarrow> translation_error option" where
  "scopeError P =
     (case badCitations P of
        [] \<Rightarrow> None
      | (n, m) # _ \<Rightarrow> Some (OutOfScope n m (firstDiff (boxPath P m) (boxPath P n))))"

text \<open>A fourth obstruction, which the paper does not list and which the three
  above do not detect.  A discharging rule cites a \emph{subproof}, and Fitch
  requires the citing line to stand at the level the subproof sits at ---
  @{const citationOK} asks for @{term "((a, c), flScope fl) \<in> set (subrefs F)"}.
  @{const scopeError} cannot see this, because it inspects @{const fCitedLines},
  which is empty for every discharging rule: the pair such a rule names is an
  @{const fCitedSubs}.

  Without this check the positional translation is unsound --- it accepts sources
  with no positional image at all.  See \<open>LF_Conjecture27\<close>, where a proof
  discharging two different assumptions at one line slips past the other three.\<close>

definition subLevel :: "lemmon_proof \<Rightarrow> nat \<times> nat \<Rightarrow> nat list" where
  "subLevel P ac = removeAll (fst ac) (boxPath P (fst ac))"

definition badSubCitations :: "lemmon_proof \<Rightarrow> (nat \<times> nat \<times> nat) list" where
  "badSubCitations P =
     concat (map (\<lambda>l. map (\<lambda>ac. (lineNumber l, snd ac, fst ac))
                        (filter (\<lambda>ac. boxPath P (lineNumber l) \<noteq> subLevel P ac)
                                (dischargePairs (justification l))))
                 P)"

definition subScopeError :: "lemmon_proof \<Rightarrow> translation_error option" where
  "subScopeError P =
     (case badSubCitations P of
        [] \<Rightarrow> None
      | (n, c, a) # _ \<Rightarrow> Some (OutOfScope n c a))"

text \<open>A fifth obstruction, and the second the paper does not list.  Fitch writes
  the premises at the top: a premise is an assumption of the whole proof, and
  @{const premisesFirst} is what Proposition 5's scope argument needs.  Lemmon has
  no such convention --- an assumption that is never discharged may be made at any
  point --- and none of the four checks above looks at where.  So a source whose
  undischarged assumptions do not come first has no positional image either.
  Unlike the shared-discharge obstruction, this one a permutation does repair.\<close>

definition isPremiseLine :: "lemmon_proof \<Rightarrow> pline \<Rightarrow> bool" where
  "isPremiseLine P l \<longleftrightarrow>
     justification l = Assumption \<and> lineNumber l \<notin> set (dischargedAssumps P)"

definition premiseOrderError :: "lemmon_proof \<Rightarrow> translation_error option" where
  "premiseOrderError P =
     (let rest = dropWhile (isPremiseLine P) P in
      case filter (isPremiseLine P) rest of
        [] \<Rightarrow> None
      | l # _ \<Rightarrow>
          (case rest of
             [] \<Rightarrow> None
           | e # _ \<Rightarrow> Some (PremiseLate (lineNumber l) (lineNumber e))))"

subsection \<open>Building the image\<close>

function (sequential) buildItems :: "(nat \<times> nat) list \<Rightarrow> lemmon_proof \<Rightarrow> fitch_item list" where
  "buildItems boxes [] = []"
| "buildItems boxes (l # ls) =
     (case find (\<lambda>ac. fst ac = lineNumber l) boxes of
        None \<Rightarrow>
          FLine (lineNumber l) (formula l) (toFitchRule (justification l))
            # buildItems boxes ls
      | Some ac \<Rightarrow>
          FSub (Subproof (lineNumber l) (formula l)
                  (buildItems boxes (takeWhile (\<lambda>l'. lineNumber l' \<le> snd ac) ls)))
            # buildItems boxes (dropWhile (\<lambda>l'. lineNumber l' \<le> snd ac) ls))"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(boxes, ls). length ls)",
      auto simp: le_imp_less_Suc length_takeWhile_le intro: le_less_trans [OF length_dropWhile_le])

definition lemmonToFitchDirect :: "lemmon_proof \<Rightarrow> translation_error + fitch_proof" where
  "lemmonToFitchDirect P =
     (if \<not> lemmonCorrect P then Inl (NotCorrect 0)
      else case boxOrderError P of Some e \<Rightarrow> Inl e
      | None \<Rightarrow>
       (case boxHeadError P of Some e \<Rightarrow> Inl e
        | None \<Rightarrow>
        (case nestingError P of Some e \<Rightarrow> Inl e
      | None \<Rightarrow>
        (case premiseError P of Some e \<Rightarrow> Inl e
         | None \<Rightarrow>
           (case scopeError P of Some e \<Rightarrow> Inl e
            | None \<Rightarrow>
              (case subScopeError P of Some e \<Rightarrow> Inl e
               | None \<Rightarrow>
                 (case premiseOrderError P of Some e \<Rightarrow> Inl e
                  | None \<Rightarrow> Inr (buildItems (boxesOf P) P))))))))"

text \<open>A positional image preserves the sequence of lines: the flattened image has
  the same numbers and the same formulas, in the same order, as the source.\<close>

lemma buildItems_positional:
  "map (\<lambda>fl. (flNum fl, flFm fl)) (concat (map (\<lambda>it. flatItem it path) (buildItems boxes ls)))
     = map (\<lambda>l. (lineNumber l, formula l)) ls"
proof (induction boxes ls arbitrary: path rule: buildItems.induct)
  case (2 boxes l ls)
  show ?case
  proof (cases "find (\<lambda>ac. fst ac = lineNumber l) boxes")
    case None
    with 2 show ?thesis by simp
  next
    case (Some ac)
    let ?t = "takeWhile (\<lambda>l'. lineNumber l' \<le> snd ac) ls"
    let ?d = "dropWhile (\<lambda>l'. lineNumber l' \<le> snd ac) ls"
    from 2(2) [OF Some] 2(3) [OF Some] Some
    show ?thesis by (simp, metis map_append takeWhile_dropWhile_id)
  qed
qed simp

theorem lemmonToFitchDirect_positional:
  assumes "lemmonToFitchDirect P = Inr F"
  shows "map (\<lambda>fl. (flNum fl, flFm fl)) (flatten F) = map (\<lambda>l. (lineNumber l, formula l)) P"
  using assms buildItems_positional [where boxes = "boxesOf P" and ls = P and path = "[]"]
  by (auto simp: lemmonToFitchDirect_def flatten_def split: option.splits if_splits)

end
