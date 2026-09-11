(*  Title:      LF_Fitch.thy

    Definition 2 of the paper.  A Fitch proof is a sequence of items, an item
    being either a line or a subproof.  The scope of a line is the set of
    assumptions of the subproofs containing it -- together with the premises,
    which are the assumptions of the root of the scope tree (Definition 19).
*)

theory LF_Fitch
  imports LF_Lemmon
begin

section \<open>The Fitch system\<close>

type_synonym subref = "nat \<times> nat"

datatype fitch_rule =
    FPremise                        \<comment> \<open>never discharged: outermost level\<close>
  | FAssume                         \<comment> \<open>opens a subproof\<close>
  | FMP nat nat
  | FCP subref                      \<comment> \<open>cites the subproof, not two lines\<close>
  | FRAA subref
  | FDN nat
  | FBotI nat nat
  | FAndIntro nat nat
  | FAndElimL nat
  | FAndElimR nat
  | FOrIntroL nat
  | FOrIntroR nat
  | FOrElim nat subref subref
  | FIffIntro nat nat
  | FIffElimL nat
  | FIffElimR nat
  | FForallElim nat
  | FForallIntro nat
  | FExistsIntro nat
  | FExistsElim nat subref
  | FEqIntro
  | FEqElim nat nat
  | FReit nat                       \<comment> \<open>Fitch's reiteration; see Section 5.3\<close>

datatype fitch_item =
    FLine nat fm fitch_rule
  | FSub subproof
and subproof =
  Subproof (subAssumeLine: nat) (subAssumeForm: fm) (subBody: "fitch_item list")

type_synonym fitch_proof = "fitch_item list"

type_synonym fitch_justification = fitch_rule

text \<open>Readable constructors for displayed proofs.  A Fitch line is written
  as its number, formula, and rule; a subproof item is written as its assumption
  number, assumption formula, and body.\<close>

abbreviation fitchLine :: "nat \<Rightarrow> fm \<Rightarrow> fitch_rule \<Rightarrow> fitch_item"
    (\<open>\<langle>_,/ _,/ _\<rangle>\<^sub>F\<close>) where
  "\<langle>n, p, r\<rangle>\<^sub>F \<equiv> FLine n p r"

abbreviation fitchSubproof ::
    "nat \<Rightarrow> fm \<Rightarrow> fitch_item list \<Rightarrow> fitch_item"
    (\<open>\<lbrakk>_ : _;/ _\<rbrakk>\<^sub>F\<close>) where
  "\<lbrakk>a : p; body\<rbrakk>\<^sub>F \<equiv> FSub (Subproof a p body)"

subsection \<open>What a Fitch rule cites\<close>

fun fCitedLines :: "fitch_rule \<Rightarrow> nat list" where
  "fCitedLines FPremise = []"
| "fCitedLines FAssume = []"
| "fCitedLines (FMP i j) = [i, j]"
| "fCitedLines (FCP _) = []"
| "fCitedLines (FRAA _) = []"
| "fCitedLines (FDN i) = [i]"
| "fCitedLines (FBotI i j) = [i, j]"
| "fCitedLines (FAndIntro i j) = [i, j]"
| "fCitedLines (FAndElimL i) = [i]"
| "fCitedLines (FAndElimR i) = [i]"
| "fCitedLines (FOrIntroL i) = [i]"
| "fCitedLines (FOrIntroR i) = [i]"
| "fCitedLines (FOrElim d _ _) = [d]"
| "fCitedLines (FIffIntro i j) = [i, j]"
| "fCitedLines (FIffElimL i) = [i]"
| "fCitedLines (FIffElimR i) = [i]"
| "fCitedLines (FForallElim i) = [i]"
| "fCitedLines (FForallIntro i) = [i]"
| "fCitedLines (FExistsIntro i) = [i]"
| "fCitedLines (FExistsElim m _) = [m]"
| "fCitedLines FEqIntro = []"
| "fCitedLines (FEqElim i j) = [i, j]"
| "fCitedLines (FReit i) = [i]"

fun fCitedSubs :: "fitch_rule \<Rightarrow> subref list" where
  "fCitedSubs (FCP s) = [s]"
| "fCitedSubs (FRAA s) = [s]"
| "fCitedSubs (FOrElim _ s1 s2) = [s1, s2]"
| "fCitedSubs (FExistsElim _ s) = [s]"
| "fCitedSubs _ = []"

text \<open>A rule that discharges cites a subproof, written as the pair of its first
  and last line --- and this is exactly the pair the Lemmon rule already names.\<close>

fun toLemmonRule :: "fitch_rule \<Rightarrow> just" where
  "toLemmonRule FPremise = Assumption"
| "toLemmonRule FAssume = Assumption"
| "toLemmonRule (FMP i j) = MP i j"
| "toLemmonRule (FCP (a, c)) = CP a c"
| "toLemmonRule (FRAA (a, c)) = RAA a c"
| "toLemmonRule (FDN i) = DN i"
| "toLemmonRule (FBotI i j) = BotI i j"
| "toLemmonRule (FAndIntro i j) = AndIntro i j"
| "toLemmonRule (FAndElimL i) = AndElimL i"
| "toLemmonRule (FAndElimR i) = AndElimR i"
| "toLemmonRule (FOrIntroL i) = OrIntroL i"
| "toLemmonRule (FOrIntroR i) = OrIntroR i"
| "toLemmonRule (FOrElim d (a1, c1) (a2, c2)) = OrElim d a1 c1 a2 c2"
| "toLemmonRule (FIffIntro i j) = IffIntro i j"
| "toLemmonRule (FIffElimL i) = IffElimL i"
| "toLemmonRule (FIffElimR i) = IffElimR i"
| "toLemmonRule (FForallElim i) = ForallElim i"
| "toLemmonRule (FForallIntro i) = ForallIntro i"
| "toLemmonRule (FExistsIntro i) = ExistsIntro i"
| "toLemmonRule (FExistsElim m (a, c)) = ExistsElim m a c"
| "toLemmonRule FEqIntro = EqIntro"
| "toLemmonRule (FEqElim i j) = EqElim i j"
| "toLemmonRule (FReit i) = Reit i"

lemma citedLines_toLemmonRule:
  "set (citedLines (toLemmonRule r))
     = set (fCitedLines r) \<union> (\<Union>(a, c) \<in> set (fCitedSubs r). {a, c})"
  by (cases r, auto)

subsection \<open>Flattening, and the scope of a line\<close>

datatype fline = FL (flNum: nat) (flFm: fm) (flRule: fitch_rule) (flScope: "nat list")

type_synonym flattened_fitch_line = fline

abbreviation fitchLineNumber :: "fline \<Rightarrow> nat" where
  "fitchLineNumber l \<equiv> flNum l"

abbreviation fitchLineFormula :: "fline \<Rightarrow> fm" where
  "fitchLineFormula l \<equiv> flFm l"

abbreviation fitchLineRule :: "fline \<Rightarrow> fitch_rule" where
  "fitchLineRule l \<equiv> flRule l"

abbreviation enclosingAssumptions :: "fline \<Rightarrow> nat list" where
  "enclosingAssumptions l \<equiv> flScope l"

text \<open>The scope path of a line: the assumption lines of the subproofs containing
  it, outermost first.  A subproof's own assumption line lies inside it.\<close>

primrec flatItem :: "fitch_item \<Rightarrow> nat list \<Rightarrow> fline list"
    and flatSub :: "subproof \<Rightarrow> nat list \<Rightarrow> fline list" where
  "flatItem (FLine n f r) path = [FL n f r path]"
| "flatItem (FSub s) path = flatSub s path"
| "flatSub (Subproof a fa body) path =
     FL a fa FAssume (path @ [a]) # concat (map (\<lambda>it. flatItem it (path @ [a])) body)"

definition flatten :: "fitch_proof \<Rightarrow> fline list" where
  "flatten F = concat (map (\<lambda>it. flatItem it []) F)"

lemma flatSub_nonempty [simp]: "flatSub s path \<noteq> []"
  by (cases s, simp)

lemma flatItem_nonempty [simp]: "flatItem it path \<noteq> []"
  by (cases it, auto)

definition subLastLine :: "subproof \<Rightarrow> nat" where
  "subLastLine s = flNum (last (flatSub s []))"

definition subRefOf :: "subproof \<Rightarrow> subref" where
  "subRefOf s = (subAssumeLine s, subLastLine s)"

text \<open>The subproofs of a Fitch proof, each with the scope path of the level it
  sits at (that is, the path of the lines that may cite it).\<close>

primrec subrefsItem :: "fitch_item \<Rightarrow> nat list \<Rightarrow> (subref \<times> nat list) list"
    and subrefsSub :: "subproof \<Rightarrow> nat list \<Rightarrow> (subref \<times> nat list) list" where
  "subrefsItem (FLine _ _ _) path = []"
| "subrefsItem (FSub s) path = subrefsSub s path"
| "subrefsSub (Subproof a fa body) path =
     ((a, subLastLine (Subproof a fa body)), path)
       # concat (map (\<lambda>it. subrefsItem it (path @ [a])) body)"

definition subrefs :: "fitch_proof \<Rightarrow> (subref \<times> nat list) list" where
  "subrefs F = concat (map (\<lambda>it. subrefsItem it []) F)"

fun is_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_prefix [] ys \<longleftrightarrow> True"
| "is_prefix (x # xs) [] \<longleftrightarrow> False"
| "is_prefix (x # xs) (y # ys) \<longleftrightarrow> x = y \<and> is_prefix xs ys"

lemma is_prefix_set: "is_prefix xs ys \<Longrightarrow> set xs \<subseteq> set ys"
  by (induction xs ys rule: is_prefix.induct, auto)

lemma is_prefix_refl [simp]: "is_prefix xs xs"
  by (induction xs, auto)

fun findFL :: "fline list \<Rightarrow> nat \<Rightarrow> fline option" where
  "findFL [] n = None"
| "findFL (fl # fls) n = (if flNum fl = n then Some fl else findFL fls n)"

definition scopePath :: "fitch_proof \<Rightarrow> nat \<Rightarrow> nat list" where
  "scopePath F n = (case findFL (flatten F) n of None \<Rightarrow> [] | Some fl \<Rightarrow> flScope fl)"

definition premiseLines :: "fitch_proof \<Rightarrow> nat list" where
  "premiseLines F = map flNum (filter (\<lambda>fl. flRule fl = FPremise) (flatten F))"

text \<open>What a Fitch proof asserts.  It keeps no dependency sets, so its
  assumptions are simply the formulas standing on its premise lines, and its
  conclusion is the formula on its last line.\<close>

definition fitchPremises :: "fitch_proof \<Rightarrow> fm list" where
  "fitchPremises F = map flFm (filter (\<lambda>fl. flRule fl = FPremise) (flatten F))"

definition fitchConclusion :: "fitch_proof \<Rightarrow> fm option" where
  "fitchConclusion F = (if flatten F = [] then None else Some (flFm (last (flatten F))))"

text \<open>Definition 19: the scope tree has a root representing the whole proof, whose
  assumptions are the premises.  So the assumptions in scope at a line are the
  premises together with the assumptions of the enclosing subproofs.\<close>

definition scopeOf :: "fitch_proof \<Rightarrow> nat \<Rightarrow> nat set" where
  "scopeOf F n = set (premiseLines F) \<union> set (scopePath F n)"

subsection \<open>Well-formedness\<close>

text \<open>The conditions the notation imposes, which (Section 7) a round trip cannot
  detect: a premise may occur only at the outermost level; a line may cite only
  what is in scope.\<close>

primrec noAssumeLinesItem :: "fitch_item \<Rightarrow> bool"
    and noAssumeLinesSub :: "subproof \<Rightarrow> bool" where
  "noAssumeLinesItem (FLine _ _ r) \<longleftrightarrow> r \<noteq> FAssume"
| "noAssumeLinesItem (FSub s) \<longleftrightarrow> noAssumeLinesSub s"
| "noAssumeLinesSub (Subproof _ _ body) \<longleftrightarrow> list_all noAssumeLinesItem body"

text \<open>Two conventions of the notation that Definition 2 leaves implicit and that
  the scope argument of Proposition 5 needs.  A subproof ends in a line rather
  than in a further subproof --- otherwise its conclusion, which a discharging
  rule cites, would not be a line of the level that cites it.  And the premises
  come first, so that every line sees them.\<close>

primrec lastIsLineItem :: "fitch_item \<Rightarrow> bool"
    and lastIsLineSub :: "subproof \<Rightarrow> bool" where
  "lastIsLineItem (FLine _ _ _) \<longleftrightarrow> True"
| "lastIsLineItem (FSub s) \<longleftrightarrow> lastIsLineSub s"
| "lastIsLineSub (Subproof _ _ body) \<longleftrightarrow>
     list_all lastIsLineItem body \<and>
     (body = [] \<or> (case last body of FLine _ _ _ \<Rightarrow> True | FSub _ \<Rightarrow> False))"

text \<open>A third convention, and the one the sequent reading needs.  The proof's
  conclusion is the formula on its last flattened line, so that line must stand
  at the outermost level: a proof that ends inside a box has not discharged the
  assumption it ends under, and asserting its last formula outright would assert
  something the proof never established.  @{const lastIsLineItem} does not give
  this --- it constrains the inside of each subproof, not the top level --- and
  an empty subproof body satisfies it vacuously.\<close>

definition concludesAtTop :: "fitch_proof \<Rightarrow> bool" where
  "concludesAtTop F \<longleftrightarrow>
     (F = [] \<or> (case last F of FLine _ _ _ \<Rightarrow> True | FSub _ \<Rightarrow> False))"

definition premisesFirst :: "fitch_proof \<Rightarrow> bool" where
  "premisesFirst F \<longleftrightarrow>
     list_all (\<lambda>fl. flRule fl \<noteq> FPremise)
              (dropWhile (\<lambda>fl. flRule fl = FPremise) (flatten F))"

definition citationOK :: "fitch_proof \<Rightarrow> fline \<Rightarrow> bool" where
  "citationOK F fl \<longleftrightarrow>
     list_all (\<lambda>m. m < flNum fl \<and>
                   (case findFL (flatten F) m of
                      None \<Rightarrow> False
                    | Some fl' \<Rightarrow> is_prefix (flScope fl') (flScope fl)))
              (fCitedLines (flRule fl)) \<and>
     list_all (\<lambda>(a, c). c < flNum fl \<and> ((a, c), flScope fl) \<in> set (subrefs F))
              (fCitedSubs (flRule fl))"

definition fitchWF :: "fitch_proof \<Rightarrow> bool" where
  "fitchWF F \<longleftrightarrow>
     sorted_wrt (<) (map flNum (flatten F)) \<and>
     list_all noAssumeLinesItem F \<and>
     list_all (\<lambda>fl. flRule fl = FPremise \<longrightarrow> flScope fl = []) (flatten F) \<and>
     premisesFirst F \<and>
     list_all lastIsLineItem F \<and>
     concludesAtTop F \<and>
     list_all (citationOK F) (flatten F)"

text \<open>The paper's diagnostic version.\<close>

definition fitchWellFormed :: "fitch_proof \<Rightarrow> String.literal option" where
  "fitchWellFormed F =
     (if \<not> sorted_wrt (<) (map flNum (flatten F))
        then Some (STR ''line numbers are not strictly increasing'')
      else if \<not> list_all noAssumeLinesItem F
        then Some (STR ''an assumption occurs otherwise than as the head of a subproof'')
      else if \<not> list_all (\<lambda>fl. flRule fl = FPremise \<longrightarrow> flScope fl = []) (flatten F)
        then Some (STR ''a premise occurs inside a subproof'')
      else if \<not> premisesFirst F
        then Some (STR ''a premise occurs after a line that is not a premise'')
      else if \<not> list_all lastIsLineItem F
        then Some (STR ''a subproof does not end in a line'')
      else if \<not> concludesAtTop F
        then Some (STR ''the proof does not end at the outermost level'')
      else if \<not> list_all (citationOK F) (flatten F)
        then Some (STR ''a line cites something not in its scope'')
      else None)"

text \<open>What the new conjunct buys, and the reason it is there: the line whose
  formula @{const fitchConclusion} reports stands outside every box, so the
  conclusion is asserted, not merely reached under an assumption.\<close>

lemma flatten_last_top:
  assumes top: "concludesAtTop F" and ne: "F \<noteq> []"
  shows "flScope (last (flatten F)) = []"
proof -
  from ne obtain xs it where F: "F = xs @ [it]"
    by (metis append_butlast_last_id)
  with top obtain n f r where it: "it = FLine n f r"
    by (cases it) (auto simp: concludesAtTop_def)
  have "flatten F = flatten xs @ [FL n f r []]"
    using F it by (simp add: flatten_def)
  then show ?thesis by simp
qed

lemma fitchWF_conclusion_top:
  assumes "fitchWF F" and "F \<noteq> []"
  shows "flScope (last (flatten F)) = []"
  using assms flatten_last_top by (simp add: fitchWF_def)

lemma fitchWellFormed_iff: "(fitchWellFormed F = None) \<longleftrightarrow> fitchWF F"
  by (auto simp: fitchWellFormed_def fitchWF_def)

subsection \<open>Descriptive aliases\<close>

abbreviation flattenFitchProof :: "fitch_proof \<Rightarrow> fline list" where
  "flattenFitchProof F \<equiv> flatten F"

abbreviation scopeAt :: "fitch_proof \<Rightarrow> nat \<Rightarrow> nat set" where
  "scopeAt F n \<equiv> scopeOf F n"

abbreviation isWellFormedFitchProof :: "fitch_proof \<Rightarrow> bool" where
  "isWellFormedFitchProof F \<equiv> fitchWF F"

end
