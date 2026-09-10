-- | Message-level differential test.  Verdicts already agree (see
-- Differential.hs); this measures how many of his exact message strings the
-- Isabelle-driven renderer reproduces byte for byte.
module Main (main) where

import qualified ProofTypes    as P
import qualified LemmonChecker as C     -- HIS checker (module search finds his src)
import qualified LemmonFitch   as L
import           Adapter       (adaptProof, adaptLine)
import           Render        (renderCheckError)

import Control.Monad    (forM, forM_)
import Data.List        (sort, nub, group)
import System.Directory (listDirectory, doesDirectoryExist)
import System.FilePath  ((</>), takeExtension)
import PipeParse        (parsePipeProof)
import Extra            (extraProofs)

groupOn :: Ord a => [a] -> [[a]]
groupOn = group . sort

-- his message for a line, if he rejects it
hisMsg :: P.Proof -> P.ProofLine -> Maybe String
hisMsg prf ln =
  case [ e | r <- C.checkProof prf, C.lrNum r == P.lineNumber ln
           , Left e <- [C.lrNote r] ] of
    (e:_) -> Just e
    []    -> Nothing

-- our message for the same line, if we reject it
ourMsg :: P.Proof -> P.ProofLine -> Maybe String
ourMsg prf ln =
  fmap renderCheckError (L.hlLineError (adaptProof prf) (adaptLine ln))

collect :: FilePath -> IO [FilePath]
collect dir = do
  ok <- doesDirectoryExist dir
  if not ok then pure [] else do
    es <- listDirectory dir
    fmap concat . forM (sort es) $ \e -> do
      let p = dir </> e
      d <- doesDirectoryExist p
      if d then collect p else pure [p | takeExtension p == ".pipe"]

replaceAt :: Int -> a -> [a] -> [a]
replaceAt i x xs = take i xs ++ [x] ++ drop (i+1) xs

-- mutations that provoke rejections, so messages actually fire
muts :: P.Proof -> [P.Proof]
muts prf = concat
  [ [ replaceAt i l { P.lineNumber = n } prf | n <- [0, 99, P.lineNumber l + 1] ]
    ++ [ replaceAt i l { P.justification = j } prf | j <- alts (P.justification l) ]
  | (i,l) <- zip [0..] prf ]
  where
    alts (P.MP a b)       = [P.MP (a+5) b, P.MP a (b+5)]
    alts (P.CP a b)       = [P.CP (a+5) b, P.CP b a]
    alts (P.AndIntro a b) = [P.AndIntro (a+5) b]
    alts (P.AndElim a)    = [P.AndElim (a+5)]
    alts (P.DN a)         = [P.DN (a+5)]
    alts j                = [P.MP 99 99, j]

main :: IO ()
main = do
  files <- collect "reference/lemmon-checker-main/eval"
  parsed <- fmap concat . forM files $ \f -> do
    src <- readFile f
    pure (either (const []) (\p -> [p]) (parsePipeProof src))
  let base = parsed ++ map snd extraProofs
      alls = base ++ concatMap muts base
      pairs = [ (hisMsg prf ln, ourMsg prf ln) | prf <- alls, ln <- prf ]
      rejected  = [ (h,o) | (Just h, o) <- pairs ]
      bothRej   = [ (h,o) | (h, Just o) <- rejected ]
      exact     = [ () | (h,o) <- bothRej, h == o ]
      mismatch  = [ (h,o) | (h,o) <- bothRej, h /= o ]
      onlyHis   = [ h | (h, Nothing) <- rejected ]
      falsePos  = [ o | (Nothing, Just o) <- pairs ]
  putStrLn $ "lines examined:              " ++ show (length pairs)
  putStrLn $ "he rejects:                  " ++ show (length rejected)
  putStrLn $ "  we also reject:            " ++ show (length bothRej)
  putStrLn $ "  he rejects, we accept:     " ++ show (length onlyHis) ++ "  (verdict disagreement!)"
  putStrLn $ "we reject, he accepts:       " ++ show (length falsePos) ++ "  (verdict disagreement!)"
  putStrLn ""
  putStrLn $ "message EXACT:               " ++ show (length exact)
  putStrLn $ "message differs:             " ++ show (length mismatch)
  putStrLn ""
  putStrLn "-- his unmatched messages, by frequency (template, count) --"
  let tmpl = id
      freq = reverse (sort [ (length g, head g)
                           | g <- groupOn (map (tmpl . fst) mismatch) ])
  forM_ (take 25 freq) $ \(c,m) -> putStrLn ("  " ++ show c ++ "x  " ++ m)
  putStrLn $ "(distinct templates: " ++ show (length freq) ++ ")"
