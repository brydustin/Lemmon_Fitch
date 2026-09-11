-- | Hand-written proofs exercising the eight rules his eval corpus never uses:
-- OrElim, EqIntro, EqElim, LEM, PropTaut, IffIntro, IffElim, QN.
--
-- These need not be VALID.  The differential test measures agreement between
-- the two checkers, so a proof both reject is as informative as one both
-- accept; what matters is that the rule's branch is reached in each.
module Extra (extraProofs) where

import qualified ProofTypes as P
import qualified Data.Set   as S

p_, q_, r_ :: P.PredFormula
p_ = P.Predicate "P" []
q_ = P.Predicate "Q" []
r_ = P.Predicate "R" []

pa, pb :: P.PredFormula
pa = P.Predicate "F" [P.Const "a"]
pb = P.Predicate "F" [P.Const "b"]

eqab, eqaa :: P.PredFormula
eqab = P.Predicate "=" [P.Const "a", P.Const "b"]
eqaa = P.Predicate "=" [P.Const "a", P.Const "a"]

fx :: P.PredFormula
fx = P.Predicate "F" [P.Var "x"]

ln :: Int -> P.PredFormula -> P.Justification -> [Int] -> P.ProofLine
ln n f j rs = P.ProofLine n f j (S.fromList rs)

extraProofs :: [(String, P.Proof)]
extraProofs =
  [ ("OrElim",   [ ln 1 (P.Or p_ p_) P.Assumption [1]
                 , ln 2 p_ P.Assumption [2]
                 , ln 3 p_ P.Assumption [3]
                 , ln 4 p_ (P.OrElim 1 2 2 3 3) [1] ])
  , ("EqIntro",  [ ln 1 eqaa P.EqIntro [] ])
  , ("EqElim",   [ ln 1 eqab P.Assumption [1]
                 , ln 2 pa   P.Assumption [2]
                 , ln 3 pb   (P.EqElim 1 2) [1,2] ])
  , ("LEM",      [ ln 1 (P.Or p_ (P.Not p_)) P.LEM [] ])
  , ("LEM-deps", [ ln 1 p_ P.Assumption [1]
                 , ln 2 (P.Or q_ (P.Not q_)) P.LEM [1,7] ])
  , ("PropTaut", [ ln 1 p_ P.Assumption [1]
                 , ln 2 (P.Or p_ q_) (P.PropTaut [1]) [1] ])
  , ("IffIntro", [ ln 1 (P.Implies p_ q_) P.Assumption [1]
                 , ln 2 (P.Implies q_ p_) P.Assumption [2]
                 , ln 3 (P.Iff p_ q_) (P.IffIntro 1 2) [1,2] ])
  , ("IffElim",  [ ln 1 (P.Iff p_ q_) P.Assumption [1]
                 , ln 2 p_ P.Assumption [2]
                 , ln 3 q_ (P.IffElim 1 2) [1,2] ])
  , ("QN",       [ ln 1 (P.Not (P.ForAll "x" fx)) P.Assumption [1]
                 , ln 2 (P.Exists "x" (P.Not fx)) (P.QN 1) [1] ])
  , ("QN2",      [ ln 1 (P.Not (P.Exists "x" fx)) P.Assumption [1]
                 , ln 2 (P.ForAll "x" (P.Not fx)) (P.QN 1) [1] ])
  , ("MTuse",    [ ln 1 (P.Implies p_ q_) P.Assumption [1]
                 , ln 2 (P.Not q_) P.Assumption [2]
                 , ln 3 (P.Not p_) (P.MT 1 2) [1,2] ])
  , ("Boolean",  [ ln 1 (P.Boolean True) P.Assumption [1]
                 , ln 2 (P.And (P.Boolean True) r_) P.Assumption [2] ])
  ]
