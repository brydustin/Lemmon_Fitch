-- | Translation between Halvorson's handwritten datatypes and the datatypes
-- Isabelle generates.  Every clause is forced: the two are isomorphic
-- constructor for constructor, so this file has no design freedom and any
-- mismatch would show up here as a type error rather than as a wrong answer.
module Adapter (adaptLine, adaptProof) where

import qualified ProofTypes  as P
import qualified LemmonFitch as L
import qualified Data.Set    as S

-- His line numbers are machine Int; Isabelle emits a newtype over Integer.
-- Not a cosmetic difference: his wraps on overflow, ours does not.
i :: Int -> L.Int
i = L.Int_of_integer . toInteger

term :: P.Term -> L.Hl_term
term (P.Var s)   = L.HL_Var s
term (P.Const s) = L.HL_Const s

formula :: P.PredFormula -> L.Hl_formula
formula (P.Predicate n ts) = L.HL_Predicate n (map term ts)
formula (P.Boolean b)      = L.HL_Boolean b
formula (P.Not p)          = L.HL_Not (formula p)
formula (P.And p q)        = L.HL_And (formula p) (formula q)
formula (P.Or p q)         = L.HL_Or (formula p) (formula q)
formula (P.Implies p q)    = L.HL_Implies (formula p) (formula q)
formula (P.Iff p q)        = L.HL_Iff (formula p) (formula q)
formula (P.ForAll v p)     = L.HL_ForAll v (formula p)
formula (P.Exists v p)     = L.HL_Exists v (formula p)

just :: P.Justification -> L.Hl_justification
just P.Assumption            = L.HL_Assumption
just (P.MP a b)              = L.HL_MP (i a) (i b)
just (P.MT a b)              = L.HL_MT (i a) (i b)
just (P.DN a)                = L.HL_DN (i a)
just (P.CP a b)              = L.HL_CP (i a) (i b)
just (P.AndIntro a b)        = L.HL_AndIntro (i a) (i b)
just (P.AndElim a)           = L.HL_AndElim (i a)
just (P.OrIntro a)           = L.HL_OrIntro (i a)
just (P.OrElim a b c d e)    = L.HL_OrElim (i a) (i b) (i c) (i d) (i e)
just (P.RAA a b)             = L.HL_RAA (i a) (i b)
just (P.ForallElim a)        = L.HL_ForallElim (i a)
just (P.ExistsIntro a)       = L.HL_ExistsIntro (i a)
just (P.ForallIntro a)       = L.HL_ForallIntro (i a)
just (P.ExistsElim a b c)    = L.HL_ExistsElim (i a) (i b) (i c)
just P.EqIntro               = L.HL_EqIntro
just (P.EqElim a b)          = L.HL_EqElim (i a) (i b)
just P.LEM                   = L.HL_LEM
just (P.PropTaut ms)         = L.HL_PropTaut (map i ms)
just (P.IffIntro a b)        = L.HL_IffIntro (i a) (i b)
just (P.IffElim a b)         = L.HL_IffElim (i a) (i b)
just (P.QN a)                = L.HL_QN (i a)

-- Data.Set.Set Int -> Isabelle's own Set representation.
refs :: S.Set Int -> L.Set L.Int
refs = L.Set . map i . S.toList

adaptLine :: P.ProofLine -> L.Hl_line
adaptLine l = L.HL_ProofLine (i (P.lineNumber l))
                             (formula (P.formula l))
                             (just (P.justification l))
                             (refs (P.references l))

adaptProof :: P.Proof -> [L.Hl_line]
adaptProof = map adaptLine
