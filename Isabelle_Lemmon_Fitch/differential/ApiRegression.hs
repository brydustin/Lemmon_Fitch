-- External client regression: imports only the generated public kernel API.
-- Run after regenerating generated/haskell/LemmonFitch.hs:
-- ghc --make -O1 -igenerated/haskell -outputdir /tmp/lf_api_regression \
--   -o /tmp/lf_api_regression/api-regression differential/ApiRegression.hs
module Main (main) where

import qualified LemmonFitch as L
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

i :: Integer -> L.Int
i = L.Int_of_integer

line :: Integer -> L.Hl_formula -> L.Hl_justification -> [Integer] -> L.Hl_line
line n formula rule dependencies =
  L.HL_ProofLine (i n) formula rule (L.Set (map i dependencies))

p, q, fa, ga, allXG, allYG :: L.Hl_formula
p = L.HL_Predicate "P" []
q = L.HL_Predicate "Q" []
fa = predicate "F" (L.HL_Const "a")
ga = predicate "G" (L.HL_Const "a")
allXG = L.HL_ForAll "x" (predicate "G" (L.HL_Var "x"))
allYG = L.HL_ForAll "y" (predicate "G" (L.HL_Var "y"))

predicate :: String -> L.Hl_term -> L.Hl_formula
predicate name term = L.HL_Predicate name [term]

closedBoxEscape, identityProof :: [L.Hl_fitch_item]
closedBoxEscape =
  [ L.HL_FSub (L.HL_Subproof (i 1) p [L.HL_FLine (i 2) p (L.HL_FReit (i 1))])
  , L.HL_FLine (i 3) p (L.HL_FReit (i 2))
  ]
identityProof =
  [ L.HL_FSub (L.HL_Subproof (i 1) p [])
  , L.HL_FLine (i 2) (L.HL_Implies p p) (L.HL_FCP (i 1, i 1))
  ]

lemDependencies :: [Integer] -> [L.Hl_line]
lemDependencies dependencies =
  [ line 1 p L.HL_Assumption [1]
  , line 2 (L.HL_Or q (L.HL_Not q)) L.HL_LEM dependencies
  ]

unusedPremise, inflatedLem, forallOuterPremise, existsOuterPremise :: [L.Hl_line]
unusedPremise = lemDependencies []
inflatedLem = lemDependencies [1]
forallOuterPremise =
  [ line 1 allXG L.HL_Assumption [1]
  , line 2 fa L.HL_Assumption [2]
  , line 3 ga (L.HL_ForallElim (i 1)) [1]
  , line 4 allYG (L.HL_ForallIntro (i 3)) [1]
  , line 5 (L.HL_And fa allYG) (L.HL_AndIntro (i 2) (i 4)) [1, 2]
  ]
existsOuterPremise =
  [ line 1 (L.HL_Exists "x" (predicate "G" (L.HL_Var "x"))) L.HL_Assumption [1]
  , line 2 (L.HL_ForAll "x" (L.HL_Implies (predicate "G" (L.HL_Var "x")) p))
      L.HL_Assumption [2]
  , line 3 fa L.HL_Assumption [3]
  , line 4 ga L.HL_Assumption [4]
  , line 5 (L.HL_Implies ga p) (L.HL_ForallElim (i 2)) [2]
  , line 6 p (L.HL_MP (i 5) (i 4)) [2, 4]
  , line 7 p (L.HL_ExistsElim (i 1) (i 4) (i 6)) [1, 2]
  , line 8 (L.HL_And fa p) (L.HL_AndIntro (i 3) (i 7)) [1, 2, 3]
  ]

preservesSequent :: [L.Hl_line] -> [L.Hl_fitch_item] -> Bool
preservesSequent source target =
  L.hlFitchCorrect target
  && L.hlFitchConclusion target == L.hlConclusion source
  && all (`elem` L.hlOpenPremises source) (L.hlFitchPremises target)

checkedTreePreserves :: [L.Hl_line] -> Bool
checkedTreePreserves source = case L.hlLemmonToFitchChecked source of
  L.Inr (L.HL_ViaTreeRoute, target) -> preservesSequent source target
  _ -> False

emittedTreePreserves :: [L.Hl_line] -> Bool
emittedTreePreserves source = case L.hlToDerivation source of
  Just derivation -> preservesSequent source (L.hlDerivationToFitch derivation)
  Nothing -> False

checks :: [(String, Bool)]
checks =
  [ ("Nat conversion roundtrip: " ++ show n,
      L.integer_of_nat (L.nat_of_integer n) == n)
  | n <- [0, 1, 42, 10 ^ (30 :: Integer)]
  ] ++
  [ ("negative Nat conversion clamps to zero", L.integer_of_nat (L.nat_of_integer (-9)) == 0)
  , ("legacy Fitch checker retains closed-box behavior", L.hlFitchWellFormed closedBoxEscape)
  , ("closed-box erasure still passes dependency checker", L.hlVerifiedCorrect (L.hlFitchToLemmon closedBoxEscape))
  , ("closed-box escape has no outer premises", null (L.hlFitchPremises closedBoxEscape))
  , ("closed-box escape rejected by verified checker", not (L.hlFitchVerified closedBoxEscape))
  , ("closed-box escape rejected by scope checker", not (L.hlFitchCorrect closedBoxEscape))
  , ("immediate assumption discharge accepted", L.hlFitchCorrect identityProof)
  , ("identity proof has no outer premises", null (L.hlFitchPremises identityProof))
  , ("identity proof concludes P implies P", L.hlFitchConclusion identityProof == Just (L.HL_Implies p p))
  , ("canonical LEM accepted by paper checker", L.hlPaperCorrect unusedPremise)
  , ("inflated LEM accepted by legacy checker", L.hlCorrect inflatedLem)
  , ("inflated LEM accepted by verified dependency checker", L.hlVerifiedCorrect inflatedLem)
  , ("inflated LEM rejected by paper checker", not (L.hlPaperCorrect inflatedLem))
  , ("unused premise is absent from source sequent", null (L.hlOpenPremises unusedPremise))
  , ("raw direct route retains the unused premise", case L.hlLemmonToFitchDirect unusedPremise of
       L.Inr target -> L.hlFitchPremises target == [p]
       _ -> False)
  , ("checked route drops the unused premise", case L.hlLemmonToFitchChecked unusedPremise of
       L.Inr (L.HL_ViaTreeRoute, target) -> null (L.hlFitchPremises target) && preservesSequent unusedPremise target
       _ -> False)
  , ("forall outer-premise source verified", L.hlVerifiedCorrect forallOuterPremise)
  , ("forall outer-premise checked repair", checkedTreePreserves forallOuterPremise)
  , ("forall outer-premise tree emitter repair", emittedTreePreserves forallOuterPremise)
  , ("exists outer-premise source verified", L.hlVerifiedCorrect existsOuterPremise)
  , ("exists outer-premise checked repair", checkedTreePreserves existsOuterPremise)
  , ("exists outer-premise tree emitter repair", emittedTreePreserves existsOuterPremise)
  ]

main :: IO ()
main = case [label | (label, False) <- checks] of
  [] -> putStrLn ("API regression: " ++ show (length checks) ++ " assertions passed")
  failures -> do
    mapM_ (hPutStrLn stderr . ("FAIL: " ++)) failures
    exitFailure
