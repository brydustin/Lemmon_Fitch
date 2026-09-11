-- | Drop-in replacement for Halvorson's LemmonChecker.
--
-- Same module name, same exports, same types.  Anything that imports
-- LemmonChecker gets this instead, and the checking is done by the
-- Isabelle-generated kernel rather than by the handwritten code.
module LemmonChecker
     ( checkProof
     , printReport
     , proofValid
     , LineReport(..)
     , ProofReport
     ) where

import qualified ProofTypes  as P
import qualified LemmonFitch as L
import           Adapter     (adaptProof, adaptLine)
import           Render      (renderCheckError)
import           Control.Monad (forM_)

data LineReport = LineReport
  { lrNum  :: Int
  , lrLine :: P.ProofLine
  , lrNote :: Either String ()
  }

type ProofReport = [LineReport]

-- | The verdict comes from Isabelle's hlLineOK, which is the generated
-- counterpart of his checkStructure-then-checkJustification.
checkProof :: P.Proof -> ProofReport
checkProof proof =
  let ours = adaptProof proof
  in [ LineReport (P.lineNumber ln) ln
         (case L.hlLineError ours (adaptLine ln) of
            Nothing -> Right ()
            Just e  -> Left (renderCheckError e))
     | ln <- proof ]

proofValid :: ProofReport -> Bool
proofValid = all (either (const False) (const True) . lrNote)

printReport :: ProofReport -> IO ()
printReport reps = do
  putStrLn ""
  putStrLn "Line   Result"
  putStrLn "-----  -------------------------"
  forM_ reps $ \r ->
    putStrLn (pad (show (lrNum r)) ++ either id (const "ok") (lrNote r))
  where pad s = s ++ replicate (max 1 (7 - length s)) ' '
