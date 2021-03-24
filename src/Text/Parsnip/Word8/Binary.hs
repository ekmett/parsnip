{-# language MagicHash #-}
{-# language BlockArguments #-}
{-# language UnboxedTuples #-}
{-# language BangPatterns #-}
{-# language TypeApplications #-}
{-# language NegativeLiterals #-}
{-# language UnliftedFFITypes #-}
{-# language ScopedTypeVariables #-}
{-# language ForeignFunctionInterface #-}

-- | These combinators allow handling of embedded null characters.
--
-- However, they do assume that the string is null terminated to
-- accelerate access, and to properly intermix with other combinators
-- which means we still have to do an initial copy.
--
-- Use 'binaryEof' instead of 'eof' to check for end-of-file, as
-- it understands embdded nulls.
module Text.Parsnip.Word8.Binary
( satisfy
, word8
, notWord8
, anyWord8
, while, whileSome
, till, tillSome, tillWord8
, skipWhile, skipWhileSome
, skipTill, skipTillSome, skipTillWord8
, previousWord8, previousWord8'
, nextWord8, nextWord8'
, binaryEof
) where

import Data.ByteString (ByteString)
import Data.Word
import Foreign.C.Types
import GHC.Prim
import GHC.Ptr
import GHC.Types
import GHC.Word
import Text.Parsnip.Internal.Parser
import Text.Parsnip.Internal.Private
import Text.Parsnip.Parser

--------------------------------------------------------------------------------
-- * Word8 parsers that handle embedded nulls
--------------------------------------------------------------------------------

satisfy :: forall s e. KnownBase s => (Word8 -> Bool) -> Parser s e Word8
satisfy f = Parser \p s -> case readWord8OffAddr# p 0# s of
  (# t, c #) -> if f (W8# c) 
    then if isTrue# (0## `neWord#` c) || isTrue# (neAddr# p (end @s))
         then OK (W8# c) (plusAddr# p 1#) t
         else Fail p t
    else Fail p t
{-# inline satisfy #-}

notWord8 :: forall s e. KnownBase s => Word8 -> Parser s e Word8
notWord8 (W8# c) = Parser \p s -> case readWord8OffAddr# p 0# s of
  (# t, c' #) -> 
    if isTrue# (c `neWord#` c') 
    then if isTrue# (0## `neWord#` c') || isTrue# (neAddr# p (end @s))
         then OK (W8# c') (plusAddr# p 1#) t
         else Fail p t
    else Fail p t
{-# inline notWord8 #-}

nextWord8 :: forall s e. KnownBase s => Parser s e (Maybe Word8)
nextWord8 = Parser \p s -> case readWord8OffAddr# p 0# s of
  (# t, c #) -> OK 
    ( if isTrue# (0## `neWord#` c) || isTrue# (neAddr# p (end @s)) 
      then Just (W8# c) 
      else Nothing
    ) 
    p 
    t
{-# inline nextWord8 #-}

nextWord8' :: forall s e. KnownBase s => Parser s e Word8
nextWord8' = Parser \p s -> case readWord8OffAddr# p 0# s of
  (# t, c #) -> 
    if isTrue# (0## `neWord#` c) || isTrue# (neAddr# p (end @s))
    then OK (W8# c) p t
    else Fail p t
{-# inline nextWord8' #-}

anyWord8 :: forall s e. KnownBase s => Parser s e Word8
anyWord8 = Parser \p s -> case readWord8OffAddr# p 0# s of
  (# t, c #) -> 
    if isTrue# (0## `neWord#` c) || isTrue# (neAddr# p (end @s))
    then OK (W8# c) (plusAddr# p 1#) t
    else Fail p t
{-# inline anyWord8 #-}

scan :: forall s. KnownBase s => (Word8 -> Bool) -> Addr# -> State# s -> (# State# s, Addr# #)
scan f = go where
  go p s = case readWord8OffAddr# p 0# s of
    (# t, c #) -> 
      if (isTrue# (0## `neWord#` c) || isTrue# (neAddr# p (end @s))) && f (W8# c)
      then (# t, p #)
      else scan f (plusAddr# p 1#) t
{-# inline scan #-}

skipWhile :: KnownBase s => (Word8 -> Bool) -> Parser s e ()
skipWhile f = Parser \p s -> case scan f p s of
  (# t, q #) -> OK () q t
{-# inline [1] skipWhile #-}

{-# RULES
"skipWhile (x/=)" forall x.
  skipWhile (x `neWord8`) = skipTillWord8 x
"skipWhile (/=x)" forall x.
  skipWhile (`neWord8` x) = skipTillWord8 x
  #-}

skipTill :: KnownBase s => (Word8 -> Bool) -> Parser s e ()
skipTill p = skipWhile (not . p)
{-# inline [1] skipTill #-}

{-# RULES
"skipTill (x==)" forall x.
  skipTill (x `eqWord8`) = skipTillWord8 x
"skipWhile (==x)" forall x.
  skipWhile (`eqWord8` x) = skipTillWord8 x
  #-}

skipTillSome :: KnownBase s => (Word8 -> Bool) -> Parser s e ()
skipTillSome p = skipWhileSome (not . p)
{-# inline skipTillSome #-}

foreign import ccall "string.h" memchr :: Addr# -> CInt -> CSize -> IO (Ptr Word8)

skipTillWord8 :: forall s e. KnownBase s => Word8 -> Parser s e ()
skipTillWord8 w = Parser $ \p s -> case io (memchr p (fromIntegral w) (fromIntegral $ I# (minusAddr# (end @s) p))) s of
  (# t, Ptr q #) -> OK () q t
{-# inline skipTillWord8 #-}

skipWhileSome :: KnownBase s => (Word8 -> Bool) -> Parser s e ()
skipWhileSome p = satisfy p *> skipWhile p
{-# inline skipWhileSome #-}

while :: KnownBase s => (Word8 -> Bool) -> Parser s e ByteString
while f = snipping (skipWhile f)
{-# inline while #-}

till :: KnownBase s => (Word8 -> Bool) -> Parser s e ByteString
till p = snipping (skipTill p)
{-# inline till #-}

tillWord8 :: KnownBase s => Word8 -> Parser s e ByteString
tillWord8 c = snipping (skipTillWord8 c)
{-# inline tillWord8 #-}

whileSome :: KnownBase s => (Word8 -> Bool) -> Parser s e ByteString
whileSome p = snipping (skipWhileSome p)
{-# inline whileSome #-}

tillSome :: KnownBase s => (Word8 -> Bool) -> Parser s e ByteString
tillSome p = snipping (skipTillSome p)
{-# inline tillSome #-}

-- | Peek at the previous character. Always succeeds.
previousWord8 :: forall s e. KnownBase s => Parser s e (Maybe Word8)
previousWord8 = case reflectBase @s of
  !(Base _ _ l _) -> Parser \p s ->
    if isTrue# (ltAddr# l p)
    then case readWord8OffAddr# p (-1#) s of
      (# t, c #) -> OK (Just (W8# c)) p t
    else OK Nothing p s
{-# inline previousWord8 #-}

-- | Peek at the previous character. Fails if we're at the start of input.
previousWord8' :: forall s e. KnownBase s => Parser s e Word8
previousWord8' = case reflectBase @s of
  !(Base _ _ l _) -> Parser \p s ->
    if isTrue# (ltAddr# l p)
    then case readWord8OffAddr# p (-1#) s of
      (# t, c #) -> OK (W8# c) p t
    else Fail p s
{-# inline previousWord8' #-}

-- This version of 'eof' is not fooled by embedded nulls.
binaryEof :: forall s e. KnownBase s => Parser s e ()
binaryEof = Parser \p s -> case readWord8OffAddr# p 0# s of
  (# t, c #) -> 
    if isTrue# (0## `eqWord#` c) && isTrue# (eqAddr# p (end @s))
    then OK () p t
    else Fail p t
{-# inline binaryEof #-}
