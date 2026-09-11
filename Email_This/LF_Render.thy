(*  Title:      LF_Render.thy

    Proofs are objects here, not text: a Lemmon proof is a list of ProofLine
    values and a Fitch proof a list of FLine and FSub values, and the maps
    between them are ordinary executable functions.  What this theory adds is a
    way to look at them.  Every function below generates code, so the Haskell
    module exported by Lemmon_Fitch can print proofs as well as translate them.
*)

theory LF_Render
  imports LF_Unfold
  keywords "print_proof" :: diag
begin

section \<open>Numerals and strings\<close>

fun digitsAux :: "nat \<Rightarrow> char list" where
  "digitsAux 0 = []"
| "digitsAux n = digitsAux (n div 10) @ [char_of (48 + n mod 10)]"

definition showNat :: "nat \<Rightarrow> String.literal" where
  "showNat n = (if n = 0 then STR ''0'' else String.implode (digitsAux n))"

definition cat :: "String.literal list \<Rightarrow> String.literal" where
  "cat ss = foldr (+) ss (STR '''')"

definition sepBy :: "String.literal \<Rightarrow> String.literal list \<Rightarrow> String.literal" where
  "sepBy s ss = (case ss of [] \<Rightarrow> STR '''' | t # ts \<Rightarrow> t + cat (map ((+) s) ts))"

section \<open>Logical symbols\<close>

text \<open>An Isabelle symbol is written as an ASCII escape sequence --- the six
  characters that print as \<open>\<and>\<close> --- so a @{typ String.literal} can
  carry one, and the Output panel,
  @{command print_proof} and @{command value} all render it.  Only the column
  padding has to know better, and \<open>dispLen\<close> below tells it: a symbol occupies
  the one column it is printed in, not the several it is written in.\<close>

definition isaSym :: "String.literal \<Rightarrow> String.literal" where
  "isaSym s = String.implode [CHR 0x5C, CHR ''<''] + s + STR ''>''"

definition symNot :: String.literal where "symNot = isaSym (STR ''not'')"
definition symAnd :: String.literal where "symAnd = isaSym (STR ''and'')"
definition symOr :: String.literal where "symOr = isaSym (STR ''or'')"
definition symImp :: String.literal where "symImp = isaSym (STR ''longrightarrow'')"
definition symIff :: String.literal where "symIff = isaSym (STR ''longleftrightarrow'')"
definition symBot :: String.literal where "symBot = isaSym (STR ''bottom'')"
definition symAll :: String.literal where "symAll = isaSym (STR ''forall'')"
definition symEx :: String.literal where "symEx = isaSym (STR ''exists'')"

lemma length_tl_dropWhile [termination_simp]:
  "length (tl (dropWhile P xs)) < Suc (length xs)"
proof -
  have "length (tl (dropWhile P xs)) \<le> length (dropWhile P xs)"
    by (cases "dropWhile P xs") auto
  also have "\<dots> \<le> length xs" by (rule length_dropWhile_le)
  finally show ?thesis by simp
qed

function dispLen :: "char list \<Rightarrow> nat" where
  "dispLen [] = 0"
| "dispLen (c # cs) =
     (if c = CHR 0x5C
        then Suc (dispLen (tl (dropWhile (\<lambda>x. x \<noteq> CHR ''>'') cs)))
        else Suc (dispLen cs))"
  by pat_completeness auto

termination
  by (relation "measure length")
     (auto intro: le_imp_less_Suc le_trans [OF diff_le_self length_dropWhile_le])

definition dispWidth :: "String.literal \<Rightarrow> nat" where
  "dispWidth s = dispLen (String.explode s)"

definition padTo :: "nat \<Rightarrow> String.literal \<Rightarrow> String.literal" where
  "padTo n s = s + String.implode (replicate (n - dispWidth s) CHR '' '')"

section \<open>Formulas\<close>

fun showTrm :: "trm \<Rightarrow> String.literal" where
  "showTrm (Nm a) = a"
| "showTrm (Vr x) = x"

fun showFm :: "fm \<Rightarrow> String.literal" where
  "showFm (Atom p []) = p"
| "showFm (Atom p ts) = p + STR ''('' + sepBy (STR '','') (map showTrm ts) + STR '')''"
| "showFm (Eqf s t) = showTrm s + STR '' = '' + showTrm t"
| "showFm Bot = symBot"
| "showFm (Neg Bot) = isaSym (STR ''top'')"
| "showFm (Neg p) = symNot + showFm p"
| "showFm (Conj p q) = STR ''('' + showFm p + STR '' '' + symAnd + STR '' '' + showFm q + STR '')''"
| "showFm (Disj p q) = STR ''('' + showFm p + STR '' '' + symOr + STR '' '' + showFm q + STR '')''"
| "showFm (Impl p q) = STR ''('' + showFm p + STR '' '' + symImp + STR '' '' + showFm q + STR '')''"
| "showFm (Iff p q) = STR ''('' + showFm p + STR '' '' + symIff + STR '' '' + showFm q + STR '')''"
| "showFm (Uni x p) = symAll + x + STR ''. '' + showFm p"
| "showFm (Exi x p) = symEx + x + STR ''. '' + showFm p"

section \<open>Lemmon proofs\<close>

definition showNats :: "nat list \<Rightarrow> String.literal" where
  "showNats ns = sepBy (STR '','') (map showNat ns)"

definition showDeps :: "nat set \<Rightarrow> String.literal" where
  "showDeps G = showNats (sorted_list_of_set G)"

fun showJust :: "just \<Rightarrow> String.literal" where
  "showJust Assumption = STR ''A''"
| "showJust (MP i j) = showNats [i, j] + STR '' MP''"
| "showJust (CP a c) = showNats [a, c] + STR '' CP''"
| "showJust (RAA a c) = showNats [a, c] + STR '' RAA''"
| "showJust (DN i) = showNat i + STR '' DN''"
| "showJust (BotI i j) = showNats [i, j] + STR '' '' + symBot + STR ''I''"
| "showJust (AndIntro i j) = showNats [i, j] + STR '' '' + symAnd + STR ''I''"
| "showJust (AndElimL i) = showNat i + STR '' '' + symAnd + STR ''E''"
| "showJust (AndElimR i) = showNat i + STR '' '' + symAnd + STR ''E''"
| "showJust (OrIntroL i) = showNat i + STR '' '' + symOr + STR ''I''"
| "showJust (OrIntroR i) = showNat i + STR '' '' + symOr + STR ''I''"
| "showJust (OrElim d a1 c1 a2 c2) = showNats [d, a1, c1, a2, c2] + STR '' '' + symOr + STR ''E''"
| "showJust (IffIntro i j) = showNats [i, j] + STR '' '' + symIff + STR ''I''"
| "showJust (IffElimL i) = showNat i + STR '' '' + symIff + STR ''E''"
| "showJust (IffElimR i) = showNat i + STR '' '' + symIff + STR ''E''"
| "showJust (ForallElim i) = showNat i + STR '' '' + symAll + STR ''E''"
| "showJust (ForallIntro i) = showNat i + STR '' '' + symAll + STR ''I''"
| "showJust (ExistsIntro i) = showNat i + STR '' '' + symEx + STR ''I''"
| "showJust (ExistsElim m a c) = showNats [m, a, c] + STR '' '' + symEx + STR ''E''"
| "showJust EqIntro = STR ''=I''"
| "showJust (EqElim i j) = showNats [i, j] + STR '' =E''"
| "showJust (Reit i) = showNat i + STR '' R''"

definition showLemmonLine :: "pline \<Rightarrow> String.literal" where
  "showLemmonLine l =
     padTo 10 (showDeps (references l))
       + padTo 6 (STR ''('' + showNat (lineNumber l) + STR '')'')
       + padTo 32 (showFm (formula l))
       + showJust (justification l)"

definition showLemmon :: "lemmon_proof \<Rightarrow> String.literal list" where
  "showLemmon P = map showLemmonLine P"

section \<open>Fitch proofs\<close>

fun showFRule :: "fitch_rule \<Rightarrow> String.literal" where
  "showFRule FPremise = STR ''Premise''"
| "showFRule FAssume = STR ''Assume''"
| "showFRule (FMP i j) = STR ''MP '' + showNats [i, j]"
| "showFRule (FCP (a, c)) = STR ''CP '' + showNat a + STR ''-'' + showNat c"
| "showFRule (FRAA (a, c)) = STR ''RAA '' + showNat a + STR ''-'' + showNat c"
| "showFRule (FDN i) = STR ''DN '' + showNat i"
| "showFRule (FBotI i j) = symBot + STR ''I '' + showNats [i, j]"
| "showFRule (FAndIntro i j) = symAnd + STR ''I '' + showNats [i, j]"
| "showFRule (FAndElimL i) = symAnd + STR ''E '' + showNat i"
| "showFRule (FAndElimR i) = symAnd + STR ''E '' + showNat i"
| "showFRule (FOrIntroL i) = symOr + STR ''I '' + showNat i"
| "showFRule (FOrIntroR i) = symOr + STR ''I '' + showNat i"
| "showFRule (FOrElim d (a1, c1) (a2, c2)) =
     symOr + STR ''E '' + showNat d + STR '', '' + showNat a1 + STR ''-'' + showNat c1
       + STR '', '' + showNat a2 + STR ''-'' + showNat c2"
| "showFRule (FIffIntro i j) = symIff + STR ''I '' + showNats [i, j]"
| "showFRule (FIffElimL i) = symIff + STR ''E '' + showNat i"
| "showFRule (FIffElimR i) = symIff + STR ''E '' + showNat i"
| "showFRule (FForallElim i) = symAll + STR ''E '' + showNat i"
| "showFRule (FForallIntro i) = symAll + STR ''I '' + showNat i"
| "showFRule (FExistsIntro i) = symEx + STR ''I '' + showNat i"
| "showFRule (FExistsElim m (a, c)) =
     symEx + STR ''E '' + showNat m + STR '', '' + showNat a + STR ''-'' + showNat c"
| "showFRule FEqIntro = STR ''=I''"
| "showFRule (FEqElim i j) = STR ''=E '' + showNats [i, j]"
| "showFRule (FReit i) = STR ''R '' + showNat i"

definition showFitchLine :: "fline \<Rightarrow> String.literal" where
  "showFitchLine fl =
     padTo 5 (showNat (flNum fl))
       + padTo 36 (cat (replicate (length (flScope fl)) (STR ''| '')) + showFm (flFm fl))
       + showFRule (flRule fl)"

definition showFitch :: "fitch_proof \<Rightarrow> String.literal list" where
  "showFitch F = map showFitchLine (flatten F)"

section \<open>Translations\<close>

fun showError :: "translation_error \<Rightarrow> String.literal" where
  "showError (NotNested n a bs) =
     STR ''line '' + showNat n + STR '' discharges '' + showNat a
       + STR '' while the box(es) opened at '' + showNats bs + STR '' are still open''"
| "showError (OutOfScope n m b) =
     STR ''line '' + showNat n + STR '' cites '' + showNat m
       + STR '', which the box opened at '' + showNat b + STR '' has closed over''"
| "showError (PremiseInBox n b) =
     STR ''premise '' + showNat n + STR '' is written inside the box opened at '' + showNat b"
| "showError (PremiseLate n m) =
     STR ''premise '' + showNat n + STR '' is written after line '' + showNat m
       + STR '', which is not a premise''"
| "showError (BoxReversed a c) =
     STR ''the assumption at line '' + showNat a
       + STR '' is discharged from line '' + showNat c + STR '', which precedes it''"
| "showError (AssumptionReused a c c') =
     STR ''the assumption at line '' + showNat a + STR '' is discharged both at line ''
       + showNat c + STR '' and at line '' + showNat c'
       + STR '', so two subproofs would have to open together''"
| "showError (NotCorrect n) =
     STR ''the source is not a correct Lemmon proof (line '' + showNat n + STR '')''"

fun showRoute :: "route \<Rightarrow> String.literal" where
  "showRoute Direct = STR ''-- positional''"
| "showRoute ViaTree = STR ''-- via a derivation tree''"

definition showTranslation ::
    "translation_error + (route \<times> fitch_proof) \<Rightarrow> String.literal list" where
  "showTranslation r =
     (case r of
        Inl e \<Rightarrow> [STR ''no translation: '' + showError e]
      | Inr (rt, F) \<Rightarrow> showRoute rt # showFitch F)"

section \<open>Printing a proof\<close>

text \<open>@{command value} prints a @{typ "String.literal list"} as a term, which
  for a proof is the wrong shape: the quotation marks and the list punctuation
  are noise, and a proof wants one step to a line.  The diagnostic command
  @{command print_proof} evaluates the term and writes the lines out as text.\<close>

ML \<open>
local
  fun eval_lines ctxt raw =
    let val t = Value_Command.value ctxt (Syntax.read_term ctxt raw)
    in map HOLogic.dest_literal (HOLogic.dest_list t) end;
in
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_proof\<close>
    "evaluate a proof and print it one step to a line"
    (Parse.term >> (fn raw =>
      Toplevel.keep (fn st =>
        writeln ("\n" ^ cat_lines (eval_lines (Toplevel.context_of st) raw)))));
end
\<close>

end
