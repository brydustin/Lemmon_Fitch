-- | Renders Isabelle's structured check errors into Halvorson's exact wording.
--
-- The decision of WHICH error, and with what data, comes from Isabelle
-- (hlLineError, proved in LF_HLW_Report to agree with hlLineOK).  Only
-- the wording lives here, because Isabelle's String.literal generates to ASCII
-- and his messages use U+274C and the logical connectives.
--
-- Every string below is transcribed from LemmonChecker.hs.  RESULT.messages
-- records how many of his messages are reproduced byte for byte.
module Render (renderCheckError) where

import qualified LemmonFitch as L
import           Data.List (intercalate)

-- Haskell's derived Show for his PredFormula, which one message uses
-- instead of the pretty-printer.
showFormula :: L.Hl_formula -> String
showFormula f = showsF 0 f ""

-- Haskell's derived Show, in full: constructor application, with nested
-- arguments parenthesised at precedence 11.  Only Predicate is reached by the
-- corpus, but a stub here would be silently wrong for any other shape.
showsF :: Int -> L.Hl_formula -> ShowS
showsF d f = case f of
  L.HL_Predicate p ts -> showParen (d > 10)
      (showString "Predicate " . shows p . showString " " . showsT ts)
  L.HL_Boolean b      -> showParen (d > 10) (showString "Boolean " . shows b)
  L.HL_Not a          -> showParen (d > 10) (showString "Not " . showsF 11 a)
  L.HL_And a b        -> bin d "And" a b
  L.HL_Or a b         -> bin d "Or" a b
  L.HL_Implies a b    -> bin d "Implies" a b
  L.HL_Iff a b        -> bin d "Iff" a b
  L.HL_ForAll x a     -> showParen (d > 10)
      (showString "ForAll " . shows x . showString " " . showsF 11 a)
  L.HL_Exists x a     -> showParen (d > 10)
      (showString "Exists " . shows x . showString " " . showsF 11 a)
  where
    bin p c a b = showParen (p > 10)
      (showString c . showString " " . showsF 11 a . showString " " . showsF 11 b)
    showsT ts = showString ("[" ++ intercalate "," (map showTermD ts) ++ "]")

showTermD :: L.Hl_term -> String
showTermD (L.HL_Var v)   = "Var " ++ show v
showTermD (L.HL_Const c) = "Const " ++ show c

showIntList :: [L.Int] -> String
showIntList xs = "[" ++ intercalate "," (map (show . L.integer_of_int) xs) ++ "]"

int :: L.Int -> Integer
int = L.integer_of_int

-- checkStructure, first branch
renderCheckError :: L.Hl_check_error -> String
renderCheckError (L.HL_DuplicateLine n dupes) =
  "\10060 Line number " ++ show (int n) ++ " is used "
    ++ show (int dupes) ++ " times. Line numbers must be unique."

-- checkStructure, second branch
renderCheckError (L.HL_LateCitation n late) =
  "\10060 Line " ++ show (int n) ++ " cites "
    ++ (if length late == 1 then "line " else "lines ")
    ++ intercalate ", " (map (show . int) late)
    ++ ", which "
    ++ (if length late == 1 then "does" else "do")
    ++ " not come earlier in the proof. "
    ++ "Every rule must appeal only to lines already established."

-- an assumption whose dependency set is not itself
renderCheckError (L.HL_InvalidAssumption n) =
  "\10060 Invalid assumption at line " ++ show (int n)

-- a citation naming no line.  Each rule words this its own way.
renderCheckError (L.HL_MissingCited j n) = case j of
  L.HL_MP _ _         -> "\10060 MP requires valid line references."
  L.HL_MT _ _         -> "\10060 MT refers to missing lines"
  L.HL_DN m           -> "\10060 DN refers to missing line " ++ show (int m)
  L.HL_CP _ _         -> "\10060 CP refers to missing lines"
  L.HL_AndElim _      -> "\10060 \8743 Elim refers to missing line"
  L.HL_AndIntro m k   -> "\10060 \8743 Intro at line " ++ show (int n)
                           ++ " refers to missing line(s) " ++ show (int m)
                           ++ " or " ++ show (int k) ++ "."
  L.HL_RAA a c        -> "\10060 RAA refers to non-existent lines " ++ show (int a)
                           ++ " or " ++ show (int c)
  L.HL_OrIntro _      -> "\10060 \8744 Intro refers to missing line"
  L.HL_OrElim{}       -> "\10060 \8744 Elim requires five valid lines"
  L.HL_ForallElim _   -> "\10060 \8704 Elim refers to missing line"
  L.HL_ForallIntro m  -> "\10060 \8704 Intro refers to missing line " ++ show (int m)
  L.HL_ExistsIntro _  -> "\10060 \8707 Intro refers to missing line"
  L.HL_ExistsElim{}   -> "\10060 \8707 Elim refers to missing lines."
  L.HL_IffIntro _ _   -> "\10060 \8596I refers to missing lines"
  L.HL_IffElim _ _    -> "\10060 \8596E refers to missing lines"
  L.HL_EqElim _ _     -> "\10060 =E: refers to missing line(s)."
  L.HL_QN _           -> "\10060 QN refers to missing line."
  L.HL_PropTaut _     -> "\10060 prop taut requires valid line references (at line "
                           ++ show (int n) ++ ")."
  _                   -> "\10060 Line " ++ show (int n) ++ " is not correct."

renderCheckError (L.HL_MPFirstNotConditional n) =
  "\10060 The first cited line of MP must be a conditional. (at line "
    ++ show (int n) ++ ")"
renderCheckError (L.HL_MPSecondNotAntecedent n) =
  "\10060 The second cited line of MP must be the antecedent of the conditional. (at line "
    ++ show (int n) ++ ")"
renderCheckError (L.HL_AndElimNotConjunction m) =
  "\10060 \8743 Elim requires \8743 formula at line " ++ show (int m)
renderCheckError L.HL_OrIntroNotDisjunct =
  "\10060 \8744 Intro formula must contain cited formula as a disjunct"
renderCheckError (L.HL_MTFailed n m k matches reversed depsOK) =
  "\10060 Invalid MT at line " ++ show (int n) ++ ": " ++ msg
  where
    msg1 | not matches = if reversed
                           then "The first line cited by MT must be the "
                                ++ "conditional and the second the negation "
                                ++ "of its consequent, so cite "
                                ++ show (int k) ++ "," ++ show (int m) ++ " instead"
                           else "Formula pattern does not match Modus Tollens"
         | otherwise   = ""
    msg2 | not depsOK  = "Dependencies on line " ++ show (int n)
                         ++ " are not the union of dependencies on lines "
                         ++ show (int m) ++ " and " ++ show (int k)
         | otherwise   = ""
    msg = intercalate ". " (filter (not . null) [msg1, msg2])
renderCheckError L.HL_EqElimNotEquality =
  "\10060 =E: second cited line must be an equality between constants a=b."
renderCheckError (L.HL_AndIntroMismatch n phi psi goal) =
  "\10060 Invalid \8743 Intro at line " ++ show (int n)
    ++ ": expected " ++ renderFormula (L.HL_And phi psi)
    ++ " (or " ++ renderFormula (L.HL_And psi phi)
    ++ ") but got " ++ renderFormula goal ++ "."
renderCheckError (L.HL_MPNotConsequent q) =
  "\10060 The formula on the inferred line must be the consequent of the conditional "
    ++ "(expected " ++ showFormula q ++ ")."
renderCheckError (L.HL_ForallIntroNotInstance m) =
  "\10060 \8704 Intro: could not recognize line " ++ show (int m)
    ++ " as an instance of the universal goal."
renderCheckError L.HL_ForallIntroAbstraction =
  "\10060 \8704 Intro: abstraction mismatch. "
    ++ "The goal core is not the result of abstracting the instance."
renderCheckError L.HL_ForallElimNoConstants =
  "\10060 \8704 Elim: could not find constants that instantiate the eliminated \8704-variables."
renderCheckError L.HL_ExistsIntroNotWitness =
  "\10060 \8707 Intro: the cited line is not a (possibly multi-step) witness instance of the goal (allowing leftover \8707\8217s)."
renderCheckError (L.HL_ExistsElimNotAssumption a) =
  "\10060 \8707 Elim: line " ++ show (int a) ++ " must be an Assumption."
renderCheckError (L.HL_ExistsElimNotRepeated n c) =
  "\10060 \8707 Elim: the conclusion at line " ++ show (int n)
    ++ " must repeat \968 from line " ++ show (int c) ++ "."
renderCheckError (L.HL_RAAFailed n m k okAsm okContra okGoal expd got) =
  "\10060 Invalid RAA at line " ++ show (int n)
    ++ (if not okAsm then "\n  \128683 Line " ++ show (int m) ++ " must be an assumption." else "")
    ++ (if not okContra then "\n  \128683 Line " ++ show (int k)
                             ++ " must be a contradiction (\968 \8743 \172\968)." else "")
    ++ (if not okGoal then "\n  \129504 Goal must be the negation of formula on line "
                          ++ show (int m) else "")
    ++ (if expd /= got
          then "\n  \128206 Expected references: " ++ showIntList expd
               ++ "\n  But got: " ++ showIntList got
          else "")
renderCheckError (L.HL_OrElimFailed n _ a1 a2 ok1 ok2) =
  "\10060 Invalid \8744 Elim at line " ++ show (int n) ++ ":\n"
    ++ unlines ([ "\128683 Line " ++ show (int a1) ++ " is not an assumption." | not ok1 ]
             ++ [ "\128683 Line " ++ show (int a2) ++ " is not an assumption." | not ok2 ])
renderCheckError (L.HL_DNShape n) =
  "\10060 DN requires \966 and \172\172\966 on one of the lines (either direction) at line "
    ++ show (int n)

-- every citation resolves, but the rule's own condition fails
renderCheckError (L.HL_RuleRejected j n) = case j of
  L.HL_CP _ _  -> "\10060 Invalid CP at line " ++ show (int n)
  _            -> "\10060 Line " ++ show (int n) ++ " is not correct."

-- not yet transcribed; see RESULT.messages for the count
renderCheckError (L.HL_RuleFailed n) =
  "\10060 Line " ++ show (int n) ++ " is not correct."

-- | Mirrors PrettyPrint.renderFormula exactly, including two quirks that are
-- bugs in the source and must be reproduced for the messages to match:
-- isBinary counts Predicate "=" at ANY arity but omits Iff, and Iff prints
-- with an ASCII arrow while every other connective is Unicode.
renderTerm :: L.Hl_term -> String
renderTerm (L.HL_Var v)   = v
renderTerm (L.HL_Const c) = c

isBinary :: L.Hl_formula -> Bool
isBinary L.HL_And{}     = True
isBinary L.HL_Or{}      = True
isBinary L.HL_Implies{} = True
isBinary (L.HL_Predicate p _) = p == "="
isBinary _              = False

wrapIfBin :: L.Hl_formula -> String
wrapIfBin f | isBinary f = "(" ++ renderFormula f ++ ")"
            | otherwise  = renderFormula f

renderFormula :: L.Hl_formula -> String
renderFormula (L.HL_Boolean True)  = "\8868"
renderFormula (L.HL_Boolean False) = "\8869"
renderFormula (L.HL_Predicate "=" [t1,t2]) = renderTerm t1 ++ " = " ++ renderTerm t2
renderFormula (L.HL_Predicate name ts)
  | null ts   = name
  | otherwise = name ++ "(" ++ intercalate "," (map renderTerm ts) ++ ")"
renderFormula (L.HL_Not f)       = "\172" ++ wrapIfBin f
renderFormula (L.HL_And f g)     = wrapIfBin f ++ " \8743 " ++ wrapIfBin g
renderFormula (L.HL_Or f g)      = wrapIfBin f ++ " \8744 " ++ wrapIfBin g
renderFormula (L.HL_Implies f g) = wrapIfBin f ++ " \8594 " ++ wrapIfBin g
renderFormula (L.HL_Iff f g)     = wrapIfBin f ++ " <-> " ++ wrapIfBin g
renderFormula (L.HL_ForAll x f)  = "\8704" ++ x ++ "(" ++ renderFormula f ++ ")"
renderFormula (L.HL_Exists x f)  = "\8707" ++ x ++ "(" ++ renderFormula f ++ ")"
