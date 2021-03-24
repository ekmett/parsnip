{-# language MagicHash #-}
{-# language BlockArguments #-}
{-# language UnboxedTuples #-}
{-# language BangPatterns #-}
{-# language TypeApplications #-}
{-# language NegativeLiterals #-}
{-# language UnliftedFFITypes #-}
{-# language ScopedTypeVariables #-}
{-# language ForeignFunctionInterface #-}
module Text.Parsnip.Char8
( satisfy
, char
, notChar
, anyChar
, digit
, space
, skipSpace
, letter_ascii
, letter_iso8859_15
, while, whileSome
, till, tillSome, tillChar
, skipWhile, skipWhileSome
, skipTill, skipTillSome, skipTillChar
, previousChar, previousChar'
, nextChar, nextChar'
) where

import Control.Applicative
import qualified Data.Attoparsec.ByteString.Char8 as A
import Data.ByteString (ByteString)
import Data.Word
import GHC.Char
import GHC.Prim
import GHC.Ptr
import GHC.Types
import Text.Parsnip.Internal.Parser
import Text.Parsnip.Internal.Private
import Text.Parsnip.Parser

--------------------------------------------------------------------------------
-- * Char parsers
--------------------------------------------------------------------------------

satisfy :: (Char -> Bool) -> Parser s e Char
satisfy f = Parser \p s -> case readCharOffAddr# p 0# s of
  (# t, c #) -> if isTrue# (chr# 0# `neChar#` c) && f (C# c)
    then OK (C# c) (plusAddr# p 1#) t
    else Fail p t
{-# inline satisfy #-}

char :: Char -> Parser s e Char
char '\0' = empty
char r@(C# c) = Parser \p s -> case readCharOffAddr# p 0# s of
  (# t, c' #) -> if isTrue# (eqChar# c c')
    then OK r (plusAddr# p 1#) t
    else Fail p t
{-# inline char #-}

notChar :: Char -> Parser s e Char
notChar '\0' = anyChar
notChar (C# c) = Parser \p s -> case readCharOffAddr# p 0# s of
  (# t, c' #) -> if isTrue# (chr# 0# `neChar#` c') && isTrue# (neChar# c c')
    then OK (C# c') (plusAddr# p 1#) t
    else Fail p t
{-# inline notChar #-}

nextChar :: Parser s e (Maybe Char)
nextChar = Parser \p s -> case readCharOffAddr# p 0# s of
  (# t, c #) -> OK (if isTrue# (chr# 0# `neChar#` c) then Just (C# c) else Nothing) p t
{-# inline nextChar #-}

nextChar' :: Parser s e Char
nextChar' = Parser \p s -> case readCharOffAddr# p 0# s of
  (# t, c #) -> if isTrue# (chr# 0# `neChar#` c)
    then OK (C# c) p t
    else Fail p t
{-# inline nextChar' #-}

anyChar :: Parser s e Char
anyChar = Parser \p s -> case readCharOffAddr# p 0# s of
  (# t, c #) -> if isTrue# (chr# 0# `neChar#` c)
    then OK (C# c) (plusAddr# p 1#) t
    else Fail p t
{-# inline anyChar #-}

digit :: Parser s e Char
digit = satisfy A.isDigit 
{-# inline digit #-}

space :: Parser s e Char
space = satisfy A.isSpace
{-# inline space #-}

skipSpace :: Parser s e ()
skipSpace = skipWhile A.isSpace
{-# inline skipSpace #-}

letter_ascii :: Parser s e Char
letter_ascii = satisfy A.isAlpha_ascii
{-# inline letter_ascii #-}

letter_iso8859_15:: Parser s e Char
letter_iso8859_15 = satisfy A.isAlpha_iso8859_15
{-# inline letter_iso8859_15 #-}

scan :: (Char -> Bool) -> Addr# -> State# s -> (# State# s, Addr# #)
scan f = go where
  go p s = case readCharOffAddr# p 0# s of
    (# t, c #) -> if isTrue# (chr# 0# `neChar#` c) && f (C# c)
      then (# t, p #)
      else scan f (plusAddr# p 1#) t
{-# inline scan #-}

skipWhile :: (Char -> Bool) -> Parser s e ()
skipWhile f = Parser \p s -> case scan f p s of
  (# t, q #) -> OK () q t
{-# inline [1] skipWhile #-}  

{-# RULES
"skipWhile (x/=)" forall x.
  skipWhile (x `neChar`) = skipTillChar x
"skipWhile (/=x)" forall x.
  skipWhile (`neChar` x) = skipTillChar x
  #-}

skipTill :: (Char -> Bool) -> Parser s e ()
skipTill p = skipWhile (not . p)
{-# inline [1] skipTill #-}

{-# RULES
"skipTill (x==)" forall x.
  skipTill (x `eqChar`) = skipTillChar x
"skipWhile (==x)" forall x.
  skipWhile (`eqChar` x) = skipTillChar x
  #-}

skipTillSome :: (Char -> Bool) -> Parser s e ()
skipTillSome p = skipWhileSome (not . p)
{-# inline skipTillSome #-}

foreign import ccall "parsnip.h" strchr0 :: Addr# -> Char# -> IO (Ptr Word8)

skipTillChar :: Char -> Parser s e ()
skipTillChar (C# c) = Parser $ \p s -> case io (strchr0 p c) s of
  (# t, Ptr q #) -> OK () q t
{-# inline skipTillChar #-}

skipWhileSome :: (Char -> Bool) -> Parser s e ()
skipWhileSome p = satisfy p *> skipWhile p
{-# inline skipWhileSome #-}

while :: KnownBase s => (Char -> Bool) -> Parser s e ByteString
while f = snipping (skipWhile f)
{-# inline while #-}  

till :: KnownBase s => (Char -> Bool) -> Parser s e ByteString
till p = snipping (skipTill p)
{-# inline till #-}

tillChar :: KnownBase s => Char -> Parser s e ByteString
tillChar c = snipping (skipTillChar c)
{-# inline tillChar #-}

whileSome :: KnownBase s => (Char -> Bool) -> Parser s e ByteString
whileSome p = snipping (skipWhileSome p)
{-# inline whileSome #-}

tillSome :: KnownBase s => (Char -> Bool) -> Parser s e ByteString
tillSome p = snipping (skipTillSome p)
{-# inline tillSome #-}

-- Peek at the previous character. Always succeeds. 
previousChar :: forall s e. KnownBase s => Parser s e (Maybe Char)
previousChar = case reflectBase @s of
  !(Base _ _ l _) -> Parser \p s ->
    if isTrue# (ltAddr# l p)
    then case readCharOffAddr# p (-1#) s of
      (# t, c #) -> OK (Just (C# c)) p t
    else OK Nothing p s

-- Peek at the previous character. Fails if we're at the start of input.
previousChar' :: forall s e. KnownBase s => Parser s e Char
previousChar' = case reflectBase @s of
  !(Base _ _ l _) -> Parser \p s ->
    if isTrue# (ltAddr# l p)
    then case readCharOffAddr# p (-1#) s of
      (# t, c #) -> OK (C# c) p t
    else Fail p s
