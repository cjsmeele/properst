{- |
Module      : Text.Polyglot.Char
Description : Primitive parsers for working with textual strings
Copyright   : (c) Chris Smeele, 2018
License     : GPL-3
Maintainer  : chris@cjsmeele.nl
Stability   : experimental

This module provides primitive parsers for working with textual strings.
-}
module Text.Polyglot.Char where

import           Text.Polyglot
import           Data.Char

cr   = char '\r'
lf   = char '\n'
crlf = string "\r\n"

digit = sat isDigit
alpha = sat isAlpha
alnum = sat isAlphaNum
space = sat isSpace
upper = sat isUpper
lower = sat isLower

word = many space *> some (sat (not . isSpace)) <* many space

token p = many space *> p <* many space
