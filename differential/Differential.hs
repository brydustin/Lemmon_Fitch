-- | Differential test: does the Isabelle-generated checker return the same
-- verdict as Halvorson's handwritten one, on the same input?
--
-- Two phases.  The corpus phase reads his .pipe files, which are mostly valid
-- proofs and so exercise only the accept path -- a checker that always said
-- True would pass it.  The mutation phase corrupts every line of every corpus
-- proof in several ways and compares verdicts on each mutant, which exercises
-- the reject path and is where a real disagreement would show.
--
-- Comparison is PER LINE, through his public API (checkProof / LineReport),
-- never through internals.
module Main (main) where

import qualified ProofTypes    as P
import qualified LemmonChecker as C
import qualified LemmonFitch   as L
import qualified Data.Set      as S
import           Adapter       (adaptProof, adaptLine)
import           Extra         (extraProofs)

import Control.Monad     (forM, forM_)
import Data.Either       (isRight)
import Data.List         (sort)
import System.Directory  (listDirectory, doesDirectoryExist)
import System.Exit       (exitFailure, exitSuccess)
import System.FilePath   ((</>), takeExtension)
import PipeParse         (parsePipeProof)

data Tally = Tally { tLines :: !Int, tAcc :: !Int, tBad :: [String] }

instance Semigroup Tally where
  Tally a b c <> Tally d e f = Tally (a+d) (b+e) (c++f)
instance Monoid Tally where
  mempty = Tally 0 0 []

-- | One proof, compared line by line.
compareProof :: String -> P.Proof -> Tally
compareProof tag prf =
  let ours   = adaptProof prf
      hisRep = C.checkProof prf
      per    = [ ( P.lineNumber (C.lrLine r)
                 , isRight (C.lrNote r)
                 , L.hlLineOK ours (adaptLine (C.lrLine r)) )
               | r <- hisRep ]
      bad    = [ tag ++ " line " ++ show n ++ ": his=" ++ show h ++ " ours=" ++ show o
               | (n,h,o) <- per, h /= o ]
      whole  = [ tag ++ " WHOLE-PROOF: his=" ++ show (C.proofValid hisRep)
                     ++ " ours=" ++ show (L.hlCorrect ours)
               | C.proofValid hisRep /= L.hlCorrect ours ]
  in Tally (length per) (length [() | (_,h,_) <- per, h]) (bad ++ whole)

replaceAt :: Int -> a -> [a] -> [a]
replaceAt i x xs = take i xs ++ [x] ++ drop (i+1) xs

-- | Alternative justifications: shift each cited line number by one, and
-- degrade to Assumption.  Enough to make well-formed but wrong citations.
altJusts :: P.Justification -> [P.Justification]
altJusts j = case j of
  P.Assumption     -> [P.LEM, P.MP 1 2]
  P.MP a b         -> [P.MP b a, P.MP a (b+1), P.Assumption]
  P.MT a b         -> [P.MT b a, P.MP a b]
  P.DN a           -> [P.DN (a+1), P.Assumption]
  P.CP a b         -> [P.CP b a, P.CP a (b+1), P.RAA a b]
  P.AndIntro a b   -> [P.AndIntro b a, P.AndElim a]
  P.AndElim a      -> [P.AndElim (a+1), P.OrIntro a]
  P.OrIntro a      -> [P.OrIntro (a+1), P.AndElim a]
  P.OrElim a b c d e -> [P.OrElim b a c d e, P.OrElim a b c e d]
  P.RAA a b        -> [P.RAA b a, P.CP a b]
  P.ForallElim a   -> [P.ForallElim (a+1), P.ExistsIntro a]
  P.ExistsIntro a  -> [P.ExistsIntro (a+1), P.ForallElim a]
  P.ForallIntro a  -> [P.ForallIntro (a+1), P.ExistsIntro a]
  P.ExistsElim a b c -> [P.ExistsElim b a c, P.ExistsElim a b (c+1)]
  P.EqIntro        -> [P.LEM, P.Assumption]
  P.EqElim a b     -> [P.EqElim b a, P.EqElim a (b+1)]
  P.LEM            -> [P.EqIntro, P.Assumption]
  P.PropTaut ms    -> [P.PropTaut (map (+1) ms), P.PropTaut [], P.LEM]
  P.IffIntro a b   -> [P.IffIntro b a, P.IffElim a b]
  P.IffElim a b    -> [P.IffElim b a, P.IffIntro a b]
  P.QN a           -> [P.QN (a+1), P.DN a]

altFormulas :: P.PredFormula -> [P.PredFormula]
altFormulas f =
  [ P.Not f, P.Boolean True, P.Boolean False, P.And f f, P.Or f f ]

-- | Mutants of one proof: every line, mutated several ways.
mutants :: P.Proof -> [P.Proof]
mutants prf = concat
  [ [ replaceAt i l { P.references = S.insert k (P.references l) } prf | k <- [0,1,99] ]
    ++ [ replaceAt i l { P.references = S.drop 1 (P.references l) } prf
       | not (S.null (P.references l)) ]
    ++ [ replaceAt i l { P.references = S.empty } prf ]
    ++ [ replaceAt i l { P.lineNumber = n } prf | n <- [0, 99, P.lineNumber l + 1] ]
    ++ [ replaceAt i l { P.justification = j } prf | j <- altJusts (P.justification l) ]
    ++ [ replaceAt i l { P.formula = g } prf | g <- altFormulas (P.formula l) ]
  | (i,l) <- zip [0..] prf ]

collect :: FilePath -> IO [FilePath]
collect dir = do
  ok <- doesDirectoryExist dir
  if not ok then pure [] else do
    es <- listDirectory dir
    fmap concat . forM (sort es) $ \e -> do
      let p = dir </> e
      isDir <- doesDirectoryExist p
      if isDir then collect p else pure [p | takeExtension p == ".pipe"]

main :: IO ()
main = do
  files <- collect "reference/lemmon-checker-main/eval"
  parsed <- fmap concat . forM files $ \f -> do
    src <- readFile f
    case parsePipeProof src of
      Left _    -> pure []
      Right prf -> pure [(f, prf)]

  let allProofs = parsed ++ [ ("extra:" ++ n, pr) | (n,pr) <- extraProofs ]
      parsed'  = allProofs
      corpusT  = mconcat [ compareProof f prf | (f,prf) <- allProofs ]
      mutantsT = mconcat [ compareProof (f ++ " ~mut" ++ show k) m
                         | (f,prf) <- parsed'
                         , (k,m)   <- zip [(0::Int)..] (mutants prf) ]
      totalT   = corpusT <> mutantsT
      nMut     = sum [ length (mutants prf) | (_,prf) <- parsed' ]

  putStrLn $ "corpus files found:      " ++ show (length files)
  putStrLn $ "proofs parsed:           " ++ show (length parsed)
  putStrLn ""
  putStrLn $ "hand-written extras:     " ++ show (length extraProofs)
                 ++ " (covering the 8 rules his corpus never uses)"
  putStrLn ""
  putStrLn   "-- phase 1: his corpus + extras, unmodified --"
  putStrLn $ "  lines compared:        " ++ show (tLines corpusT)
  putStrLn $ "    his ACCEPTED:        " ++ show (tAcc corpusT)
  putStrLn $ "    his REJECTED:        " ++ show (tLines corpusT - tAcc corpusT)
  putStrLn $ "  disagreements:         " ++ show (length (tBad corpusT))
  putStrLn ""
  putStrLn   "-- phase 2: mutated proofs (exercises the reject path) --"
  putStrLn $ "  mutants generated:     " ++ show nMut
  putStrLn $ "  lines compared:        " ++ show (tLines mutantsT)
  putStrLn $ "    his ACCEPTED:        " ++ show (tAcc mutantsT)
  putStrLn $ "    his REJECTED:        " ++ show (tLines mutantsT - tAcc mutantsT)
  putStrLn $ "  disagreements:         " ++ show (length (tBad mutantsT))
  putStrLn ""
  putStrLn $ "TOTAL lines compared:    " ++ show (tLines totalT)
  putStrLn $ "TOTAL disagreements:     " ++ show (length (tBad totalT))
  forM_ (take 30 (tBad totalT)) $ \b -> putStrLn ("  " ++ b)
  if null (tBad totalT) then exitSuccess else exitFailure
