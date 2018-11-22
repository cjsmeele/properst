{- |
Module      : Main
Description : Proposition logic REPL
Copyright   : (c) Chris Smeele, 2018
License     : GPL-3
Maintainer  : chris@cjsmeele.nl
Stability   : experimental

Properst is a command-line utility for working with propositions.
-}
module Main where

import qualified Data.Set as S
import           Data.Set (Set)
import           Data.Char (isSpace, toUpper)
import           Control.Arrow
import           Control.Monad
import           Data.Maybe
import           Data.List
import           Text.Polyglot
import           Text.Polyglot.Char
import           System.IO (stdout,
                            hSetBuffering,
                            BufferMode(NoBuffering))

-- * Types

-- | The proposition type.
data Prop = Basic   Bool
          | Atom    Char
          | Not     Prop
          | Prop  :/\:  Prop
          | Prop  :\/:  Prop
          | Prop  :^:   Prop -- XOR
          | Prop  :==>: Prop
          | Prop  :<==: Prop
          | Prop  :<=>: Prop
          deriving (Eq)

-- ** Type predicates

-- | A "composite" proposition is a binary operator.
isComposite :: Prop -> Bool
isComposite (Basic _) = False
isComposite (Atom  _) = False
isComposite (Not   _) = False
isComposite _         = True

isConjunction :: Prop -> Bool
isConjunction (_ :/\: _) = True
isConjunction _          = False

isDisjunction :: Prop -> Bool
isDisjunction (_ :\/: _) = True
isDisjunction _          = False

isImplication :: Prop -> Bool
isImplication (_ :==>: _) = True
isImplication _           = False

isRImplication :: Prop -> Bool
isRImplication (_ :<==: _) = True
isRImplication _           = False

isLogEqv :: Prop -> Bool
isLogEqv (_ :<=>: _) = True
isLogEqv _           = False

isArrow :: Prop -> Bool
isArrow p = isImplication p || isRImplication p || isLogEqv p

-- | This shows a proposition in canonical form.
-- The generated string representation is valid input for the proposition parser.
instance Show Prop where
    show (Basic True)  = "T"
    show (Basic False) = "F"
    show (Atom x)      = [x]
    show (Not p)       = '¬' : case p of
                                 Basic _ -> show p
                                 Atom  _ -> show p
                                 Not   _ -> show p
                                 _       -> "(" ++ show p ++ ")"

    show (p :/\:  q)  = maybeWrap p pred ++ " ∧ "  ++ maybeWrap q pred
        where pred p  =  isComposite p && not (isConjunction p)

    show (p :\/:  q)  = maybeWrap p pred ++ " ∨ "  ++ maybeWrap q pred
        where pred p  =  isComposite p && not (isDisjunction p)

    show (p :^:  q)   = show p ++ " ⊕ "   ++ show q

    show (p :==>: q) = maybeWrap p isArrow ++ " ==> " ++ maybeWrap q isArrow
    show (p :<==: q) = maybeWrap p isArrow ++ " <== " ++ maybeWrap q isArrow
    show (p :<=>: q) = maybeWrap p isArrow ++ " <=> " ++ maybeWrap q isArrow

-- | Show a proposition. Wrap it in parens if the given predicate holds.
-- This allows us to chain con/disjunction operators without redundant parens.
maybeWrap :: Prop -> (Prop -> Bool) -> String
maybeWrap q p | p q       = "(" ++ show q ++ ")"
              | otherwise = show q

-- | This is used in the pretty-printing of truth tables.
-- For now, we assume that the user has a nice color TTY.
showBool True  = "\x1b[92mT\x1b[0m" -- Bright green
showBool False = "\x1b[91mF\x1b[0m" -- Bright red
--showBool True  = "T"
--showBool False = "F"

-- * Checking propositions

-- | Determine if proposition holds with the given variable values.
-- If a proposition variable is missing from the variable map,
-- this will result in 'Nothing'.
tv :: [(Char, Bool)] -> Prop -> Maybe Bool
tv _ (Basic b)   = pure b
tv m (Atom c)    = lookup c m
tv m (Not p)     = not <$> tv m p
tv m (p :/\: q)  = (&&) <$> tv m p <*> tv m q
tv m (p :\/: q)  = (||) <$> tv m p <*> tv m q
tv m (p :^: q)   = xor  <$> tv m p <*> tv m q
    where True  `xor` False = True
          False `xor` True  = True
          _     `xor` _     = False
tv m (p :==>: q) = (||) <$> (not <$> tv m p) <*> tv m q
tv m (p :<==: q) = tv m (q :==>: p)
tv m (p :<=>: q) = (==) <$> tv m p <*> tv m q

-- | Get the set of variables from a proposition.
vars :: Prop -> Set Char
vars (Basic b)   = mempty
vars (Atom c)    = S.singleton c
vars (Not p)     = vars p
vars (p :/\:  q) = vars p <> vars q
vars (p :\/:  q) = vars p <> vars q
vars (p :^:   q) = vars p <> vars q
vars (p :==>: q) = vars p <> vars q
vars (p :<==: q) = vars p <> vars q
vars (p :<=>: q) = vars p <> vars q

-- | Generate all possible maps of variable assignments for the given proposition.
assigns :: Set Char -> [[(Char, Bool)]]
assigns = assigns' . S.toAscList
    where assigns' [ ]    = [[]]
          assigns' [c]    = [[(c, False)]
                            ,[(c, True )]]
          assigns' (c:cs) = concatMap (\p -> map (:p) (concat $ assigns' [c]))
                                      (assigns' cs)

-- | The truth table type.
data TruthTable = TT { ttProp :: Prop                     -- ^ its proposition
                     , ttTab  :: [([(Char, Bool)], Bool)] -- ^ mappings with corresponding truth value
                     }

-- | Pretty printing for truth tables
-- NB: This should not use the 'Show' class.
instance Show TruthTable where
    show (TT p tt) = let pv      = S.toAscList $ vars p
                         vlen    = length pv
                         prop    = show p
                         header  = " " ++ concatMap (:" ") pv ++ "| " ++ prop ++ " "
                         showLine (as, b) =  " " ++ concatMap ((++" ") . showBool . snd) as
                                          ++ "| "
                                          ++ replicate (length prop `div` 2) ' '
                                          ++ showBool b ++ "\n"
                      in header
                      ++ "\n" ++ ('-' <$ header) ++ "\n"
                      ++ if null tt
                            then "(this proposition can never hold)\n"
                            else concatMap showLine tt


-- | Generate a truth table for the given proposition.
truthTable :: Prop -> TruthTable
truthTable p = let pv = vars p
                   pa = assigns pv
                   -- NB: tv cannot fail here.
                in TT p ((\as -> (as, fromJust $ tv as p)) <$> pa)

--isTautology :: Prop -> Prop -> Bool
--isTautology p q = vars p == vars q
--               && (snd <$> truthTable p) == (snd <$> truthTable q)



-- * Manipulating propositions

-- | Perform a depth-first walk through the proposition structure.
walk :: (Prop -> Prop) -> Prop -> Prop
walk f (Basic b)          = f $ Basic b
walk f (Atom c)           = f $ Atom c
walk f (Not p)            = f $ Not (walk f p)
walk f (p :/\: q)         = f $ walk f p :/\:  walk f q
walk f (p :\/: q)         = f $ walk f p :\/:  walk f q
walk f (p :^: q)          = f $ walk f p :^:   walk f q
walk f (p :==>: q)        = f $ walk f p :==>: walk f q
walk f (p :<==: q)        = f $ walk f p :<==: walk f q
walk f (p :<=>: q)        = f $ walk f p :<=>: walk f q
--walk f p = f p

-- | Generic proposition normalizer.
-- Should be called from a walker function, so that the entire proposition is
-- normalized instead of just the tip.
normalize1 :: Prop -> Prop
normalize1 = norm
          -- Remove double negation.
    where norm (Not (Not p))       = p
          norm (Not (Basic b))     = Basic (not b)
          -- Implication into disjunction
          norm (p :==>: q)         = norm (norm (Not p)    :\/: q)
          -- Rotate backwards implication.
          norm (p :<==: q)         = norm (q :==>: p)
          -- Logical equivalence into disjunction
          norm (p :<=>: q)         = norm (p :/\: q)       :\/: norm (Not (p :\/: q))

          -- XOR into disjunction
          norm (p :^: q)           = norm
                                   $ norm (p :/\: norm (Not q))
                                     :\/:
                                     norm (q :/\: norm (Not p))

          -- FIXME: We can't yet look inside longer con/disjunction chains.

          -- De Morgan's laws.
          norm (Not (p :/\: q))    = norm (norm (Not p)    :\/: norm (Not q))
          norm (Not (p :\/: q))    = norm (norm (Not p)    :/\: norm (Not q))

          -- Simplify disjunction with familiar values.
          norm (Basic True  :\/: _)                  = Basic True
          norm (_           :\/: Basic True)         = Basic True
          norm (Basic False :\/: p)                  = p
          norm (p           :\/: Basic False)        = p
          norm (p :\/: q) |     p == q               = p
          norm (p :\/: q) | Not p == q || p == Not q = Basic True
                          | otherwise                = p :\/: q

          -- Simplify conjunction with familiar values.
          norm (Basic False :/\: _)                  = Basic False
          norm (_           :/\: Basic False)        = Basic False
          norm (Basic True  :/\: p)                  = p
          norm (p           :/\: Basic True)         = p
          norm (p :/\: q) |       p == q             = p
          norm (p :/\: q) | Not p == q || p == Not q = Basic False
                          | otherwise                = p :/\: q

          norm p = p

-- | Normalize a proposition into conjunctive normal form.
-- (WIP - not yet correctly implemented)
toConjunctiveNormalForm :: Prop -> Prop
toConjunctiveNormalForm = walk (norm . normalize1)
          -- Distribute disjunction over conjunction.
    where norm (p :\/: (q :/\: r)) = norm' (norm' (q :\/: p) :/\: norm' (r :\/: p))
          norm ((q :/\: r) :\/: p) = norm' (norm' (q :\/: p) :/\: norm' (r :\/: p))
          norm p = p
          norm' = norm . normalize1

-- | Normalize a proposition into disjunctive normal form.
-- (WIP - not yet correctly implemented)
toDisjunctiveNormalForm :: Prop -> Prop
toDisjunctiveNormalForm = walk (norm . normalize1)
          -- Distribute conjunction over disjunction.
    where norm (p :/\: (q :\/: r)) = norm' (norm' (q :/\: p) :\/: norm' (r :/\: p))
          norm ((q :\/: r) :/\: p) = norm' (norm' (q :/\: p) :\/: norm' (r :/\: p))
          norm p = p
          norm' = norm . normalize1

-- * Parser

-- | Parser for propositions.
pprop :: SParser Prop
pprop =  token
      $  pbasic
     <|> patom
     <|> pnot
     <|> psubprop
     <|> pconjunction
     <|> pdisjunction
     <|> pxdisjunction
     <|> pimplication
     <|> primplication
     <|> plogeqv

-- | Parser for any proposition element that is not a binary operator.
pnoncomposite = pbasic <|> patom <|> pnot <|> psubprop

pbasic        =  (Basic True  <$ char 'T')
             <|> (Basic False <$ char 'F')
patom         = Atom . toUpper <$> (noneOf "tTfF" <&> alpha)
pnot          = Not     <$> (pstrnot *> token pnoncomposite)
psubprop      = char '(' *> pprop <* char ')'
pconjunction  = (:/\:)  <$> token pnoncomposite
                        <*> (pstrcon *> token (pnoncomposite <|> pconjunction))
pdisjunction  = (:\/:)  <$> token pnoncomposite
                        <*> (pstrdis *> token (pnoncomposite <|> pdisjunction))

pxdisjunction = (:^:)   <$> token pnoncomposite
                        <*> (pstrxdis *> token pnoncomposite)

pstrcon    = string "&"   <|> string "∧" <|> string "/\\"
pstrdis    = string "|"   <|> string "∨" <|> string "\\/"
pstrxdis   = string "x|"  <|> string "⊕" <|> string "⊻" <|> string "^"
pstrnot    = string "!"   <|> string "¬" <|> string "not "
pstrimpl   = string "=>"  <|> string "⇒" <|> string "==>" <|> string "→"
pstrrimpl  = string "<="  <|> string "⇐" <|> string "<==" <|> string "←"
pstrlogeqv = string "<=>" <|> string "⇔" <|> string " iff "

pimplication  = (:==>:) <$> token phigher
                        <*> (pstrimpl *> token phigher)
    where phigher = pnoncomposite <|> pconjunction <|> pdisjunction <|> pxdisjunction

primplication = (:<==:) <$> token phigher
                        <*> (pstrrimpl *> token phigher)
    where phigher = pnoncomposite <|> pconjunction <|> pdisjunction <|> pxdisjunction

plogeqv      = (:<=>:) <$> token phigher
                       <*> (pstrlogeqv *> token phigher)
    where phigher = pnoncomposite <|> pconjunction <|> pdisjunction <|> pxdisjunction

-- * Command-line interface

-- | Run an action with a succesfully parsed proposition.
-- On parser error, a usage text is printed via 'putUsage'.
withParsed :: String -> (Prop -> IO ()) -> IO ()
withParsed s act
  = case parse' pprop s of
      Just prop -> act prop
      Nothing   -> putUsage

-- | Print a truth table for the given proposition.
putTt :: Prop -> IO ()
putTt p = putStr (show $ truthTable p)

main :: IO ()
main = forever $ do
    hSetBuffering stdout NoBuffering
    putStr "** "
    line   <- getLine
    case dropWhile isSpace line of
      ""       -> pure ()
      't':xs   -> case xs of
                    '!':ys -> withParsed ys putTt
                    _      -> withParsed xs
                            $ \p -> let tt  = truthTable p
                                        tt' = tt { ttTab = filter snd (ttTab tt) }
                                     in print tt'
      'c':xs   -> case xs of
                    '!':ys -> withParsed ys (\x -> putTt (toConjunctiveNormalForm x :<=>: x))
                    _      -> withParsed xs (toConjunctiveNormalForm >>> print)
      'd':xs   -> case xs of
                    '!':ys -> withParsed ys (\x -> putTt (toDisjunctiveNormalForm x :<=>: x))
                    _      -> withParsed xs (toDisjunctiveNormalForm >>> print)
      'h':_    -> putUsage
      "syntax" -> putSyntax
      _        -> withParsed line print


putUsage :: IO ()
putUsage = putStr
         $ unlines
         ["usage: (replace PROP with your proposition expression)"
         ," PROP     - prints proposition in canonical syntax"
         ," t  PROP  - shows for what variable values the proposition holds"
         ," t! PROP  - prints a complete truth table for the given proposition"
         ," c  PROP  - prints the proposition's conjunctive normal form"
         ," c! PROP  - II, also prints truth table showing logical equivalence"
         ," d  PROP  - prints the proposition's disjunctive normal form"
         ," d! PROP  - II, also prints truth table showing logical equivalence"
         ,""
         ,"type `syntax' to get information on the grammar used for parsing,"
         ,"              and which symbols to use"
         ,""
         , "example: t !(P & Q) <=> (!P | !Q)"
         ]

putSyntax :: IO ()
putSyntax = putStr
          $ unlines
          ["Syntax elements are:"
          ," variables: any single letter excluding T and F (e.g. P, Q, ζ, x)"
          ," booleans:  T and F"
          ," negation:  ¬P, !P, or not P"
          ," disjunction: P ∨ Q, P | Q, or P \\/ Q"
          ," conjunction: P ∧ Q, P & Q, or P /\\ Q"
          ," exclusive disjunction (XOR): P ⊻ Q, P ⊕ Q, or P x| Q"
          ," implication: P ⇒ Q, P → Q, P => Q, or P ==> Q"
          ,"   -> the same characters in reverse direction may be used"
          ,"      for converse implication"
          ," logical equivalence: P ⇔ Q, P <=> Q, or P iff Q"
          ,""
          ,"Any proposition may be grouped with parentheses () to indicate precedence"
          ,"Built-in precedence is as follows, from highest to lowest:"
          ,"1. negation"
          ,"2. conjunction, disjunction and exclusive disjunction"
          ,"3. implication, converse implication and logical equivalence"
          ,""
          ,"NB: Except for chains of conjunctions and chains of disjunctions,"
          ,"    any two binary operators with the same precedence may not occur next"
          ,"    to eachother without the use of parens to denote precedence."
          ]
