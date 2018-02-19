{-# Language DeriveDataTypeable #-}
{-# Language DeriveGeneric #-}
{-# Language NamedFieldPuns #-}

module EVM.Assembly where

import Prelude hiding (not, and, or, exp, return, div, log)

import Data.Aeson (ToJSON (..), object, (.=))
import Data.Bits
import Data.List (unfoldr, mapAccumL)
import Data.Word
import Text.Printf

import GHC.Generics
import GHC.Stack

import Control.Monad.State (get, modify, execState)
import qualified Control.Monad.State as Monad

type Assembler i a = Monad.State ([i], Integer) a
type Assembly = Assembler Instr ()

bytecode :: Assembly -> String
bytecode = concatMap (printf "%02x") . compile . assemble

emit :: CallStack -> Instr' -> Assembly
emit cs x =
  modify $
    \(xs, i) ->
      (Instr Nothing cs x : xs, succ i)

assemble :: Assembly -> [Instr]
assemble x = reverse y
  where (y, _) = execState x ([], 0)

as :: String -> Assembler Instr a -> Assembler Instr a
as s m =
  do r <- m
     modify $
       \(Instr _ cs x : xs, i) -> (Instr (Just s) cs x : xs, i)
     pure r

(?) :: Assembler Instr a -> String -> Assembler Instr a
(?) = flip as

infix 0 ?

data Label = Label Integer
  deriving (Show, Generic)

label :: HasCallStack => Assembler Instr Label
label = do
  (_, i) <- get
  emit callStack Jumpdest
  pure (Label i)

data Instr = Instr
  { instrAnnotation :: Maybe String
  , instrCallstack :: CallStack
  , op :: Instr'
  } deriving (Show, Generic)

data Instr'
  = Push Int Integer
  | PushLabel Label
  | Dup Int
  | Pop
  | Swap Int
  | Log Int
  | Caller
  | Eq
  | Jumpi
  | Stop
  | Mstore
  | Mstore8
  | Mload
  | Calldatasize
  | Gt
  | Lt
  | Sgt
  | Slt
  | Calldataload
  | Sload
  | Sstore
  | Byte
  | Calldatacopy
  | Msize
  | Keccak256
  | Timestamp
  | Gas
  | Call
  | Sub
  | Add
  | Mul
  | Not
  | And
  | Or
  | Exp
  | Callvalue
  | Iszero
  | Div
  | Revert
  | Return
  | Jump
  | Jumpdest
  deriving (Show, Generic)

instance ToJSON Label
instance ToJSON Instr'
instance ToJSON Instr where
  toJSON (Instr ann _ op) =
    object
      [ "instrAnnotation" .= toJSON ann
      , "op" .= toJSON op
      ]

push1 :: HasCallStack => Integer -> Assembly; push1 = emit callStack . Push 1
push2 :: HasCallStack => Integer -> Assembly; push2 = emit callStack . Push 2
push20 :: HasCallStack => Integer -> Assembly; push20 = emit callStack . Push 20
push32 :: HasCallStack => Integer -> Assembly; push32 = emit callStack . Push 32
refer :: HasCallStack => Label -> Assembly; refer = emit callStack . PushLabel
dup :: HasCallStack => Int -> Assembly; dup = emit callStack . Dup
mstore :: HasCallStack => Assembly; mstore = emit callStack Mstore
mstore8 :: HasCallStack => Assembly; mstore8 = emit callStack Mstore8
mload :: HasCallStack => Assembly; mload = emit callStack Mload
msize :: HasCallStack => Assembly; msize = emit callStack Msize
pop :: HasCallStack => Assembly; pop = emit callStack Pop
eq :: HasCallStack => Assembly; eq = emit callStack Eq
stop :: HasCallStack => Assembly; stop = emit callStack Stop
swap :: HasCallStack => Int -> Assembly; swap = emit callStack . Swap
caller :: HasCallStack => Assembly; caller = emit callStack Caller
jumpi :: HasCallStack => Assembly; jumpi = emit callStack Jumpi
sload :: HasCallStack => Assembly; sload = emit callStack Sload
sstore :: HasCallStack => Assembly; sstore = emit callStack Sstore
byte :: HasCallStack => Assembly; byte = emit callStack Byte
calldatasize :: HasCallStack => Assembly; calldatasize = emit callStack Calldatasize
calldataload :: HasCallStack => Assembly; calldataload = emit callStack Calldataload
calldatacopy :: HasCallStack => Assembly; calldatacopy = emit callStack Calldatacopy
timestamp :: HasCallStack => Assembly; timestamp = emit callStack Timestamp
gas :: HasCallStack => Assembly; gas = emit callStack Gas
gt :: HasCallStack => Assembly; gt = emit callStack Gt
lt :: HasCallStack => Assembly; lt = emit callStack Lt
sgt :: HasCallStack => Assembly; sgt = emit callStack Sgt
slt :: HasCallStack => Assembly; slt = emit callStack Slt
add :: HasCallStack => Assembly; add = emit callStack Add
mul :: HasCallStack => Assembly; mul = emit callStack Mul
sub :: HasCallStack => Assembly; sub = emit callStack Sub
not :: HasCallStack => Assembly; not = emit callStack Not
call :: HasCallStack => Assembly; call = emit callStack Call
keccak256 :: HasCallStack => Assembly; keccak256 = emit callStack Keccak256
exp :: HasCallStack => Assembly; exp = emit callStack Exp
and :: HasCallStack => Assembly; and = emit callStack And
or :: HasCallStack => Assembly; or = emit callStack Or
div :: HasCallStack => Assembly; div = emit callStack Div
return :: HasCallStack => Assembly; return = emit callStack Return
iszero :: HasCallStack => Assembly; iszero = emit callStack Iszero
jump :: HasCallStack => Assembly; jump = emit callStack Jump
revert :: HasCallStack => Assembly; revert = emit callStack Revert
callvalue :: HasCallStack => Assembly; callvalue = emit callStack Callvalue
log :: HasCallStack => Int -> Assembly; log = emit callStack . Log

unroll :: Integer -> [Word8]
unroll = unfoldr f
  where
    f 0 = Nothing
    f i = Just (fromIntegral i, i `shiftR` 8)

word :: [Word8] -> Integer
word xs = sum [ fromIntegral x `shiftL` (8*n)
              | (n, x) <- zip [0..] (reverse xs) ]

pad :: Int -> a -> [a] -> [a]
pad n x xs =
  if length xs > n
  then error "too big"
  else replicate (length xs - n) x ++ xs

compile :: [Instr] -> [Word8]
compile xs =
  let
    pass1 :: [Pass1]
    pass1 = map (compile1 . op) xs

    pass2 :: [Int]
    pass2 = snd (mapAccumL f 0 pass1)
      where
        f i (Bytecode code) = (i + length code, i)
        f i (Unresolved _)  = (i + 3, i)

    stupid :: Pass1 -> [Word8]
    stupid (Bytecode code) = code
    stupid (Unresolved i) =
      0x62 : pad 2 0 (unroll (fromIntegral (pass2 !! i)))
  in
    concatMap stupid pass1

data Pass1 = Bytecode [Word8] | Unresolved Int

parse :: [Word8] -> Maybe [Instr]
parse [] = Just []
parse (b:bs) = do
  let k x = (Instr Nothing callStack x :) <$> parse bs
  case b of
    x | x >= 0x60 && x <= 0x7f -> do
      let n = fromIntegral x - 0x60 + 1
          w = word (take n bs)
      (Instr Nothing callStack (Push n w) :) <$> parse (drop n bs)
    x | x >= 0x80 && x <= 0x8f ->
      k (Dup (fromIntegral x - 0x80 + 1))
    x | x >= 0x90 && x <= 0x9f ->
      k (Swap (fromIntegral x - 0x90 + 1))
    x | x >= 0xa0 && x <= 0xa4 ->
      k (Log (fromIntegral x - 0xa0 + 1))
    0x00 -> k Stop
    0x01 -> k Add
    0x02 -> k Mul
    0x03 -> k Sub
    0x04 -> k Div
    0x10 -> k Lt
    0x11 -> k Gt
    0x12 -> k Slt
    0x13 -> k Sgt
    0x14 -> k Eq
    0x15 -> k Iszero
    0x16 -> k And
    0x17 -> k Or
    0x19 -> k Not
    0x1a -> k Byte
    0x20 -> k Keccak256
    0x33 -> k Caller
    0x34 -> k Callvalue
    0x35 -> k Calldataload
    0x36 -> k Calldatasize
    0x37 -> k Calldatacopy
    0x42 -> k Timestamp
    0x50 -> k Pop
    0x51 -> k Mload
    0x52 -> k Mstore
    0x53 -> k Mstore8
    0x54 -> k Sload
    0x55 -> k Sstore
    0x56 -> k Jump
    0x57 -> k Jumpi
    0x59 -> k Msize
    0x5a -> k Gas
    0x5b -> k Jumpdest
    0x0a -> k Exp
    0xf1 -> k Call
    0xf3 -> k Return
    0xfd -> k Revert
    _ -> Nothing

compile1 :: Instr' -> Pass1
compile1 = \case
  Push n x ->
    let
      bytes = unroll x
      count = length bytes
    in
      if count == 0
      then Bytecode [0x60, 0]
      else Bytecode $ fromIntegral (0x60 + count - 1) : bytes
  PushLabel (Label x) -> Unresolved (fromIntegral x)
  Dup x -> Bytecode [fromIntegral $ 0x80 + x - 1]
  Swap x -> Bytecode [fromIntegral $ 0x90 + x - 1]
  Log x -> Bytecode [fromIntegral $ 0xa0 + x]
  Pop -> Bytecode [0x50]
  Caller -> Bytecode [0x33]
  Eq -> Bytecode [0x14]
  Jumpi -> Bytecode [0x57]
  Stop -> Bytecode [0x00]
  Mstore -> Bytecode [0x52]
  Mstore8 -> Bytecode [0x53]
  Mload -> Bytecode [0x51]
  Calldatasize -> Bytecode [0x36]
  Gt -> Bytecode [0x11]
  Lt -> Bytecode [0x10]
  Sgt -> Bytecode [0x13]
  Slt -> Bytecode [0x12]
  Calldataload -> Bytecode [0x35]
  Sload -> Bytecode [0x54]
  Sstore -> Bytecode [0x55]
  Byte -> Bytecode [0x1a]
  Calldatacopy -> Bytecode [0x37]
  Msize -> Bytecode [0x59]
  Keccak256 -> Bytecode [0x20]
  Timestamp -> Bytecode [0x42]
  Gas -> Bytecode [0x5a]
  Call -> Bytecode [0xf1]
  Add -> Bytecode [0x01]
  Mul -> Bytecode [0x02]
  Sub -> Bytecode [0x03]
  Not -> Bytecode [0x19]
  And -> Bytecode [0x16]
  Or -> Bytecode [0x17]
  Exp -> Bytecode [0x0a]
  Callvalue -> Bytecode [0x34]
  Iszero -> Bytecode [0x15]
  Div -> Bytecode [0x04]
  Revert -> Bytecode [0xfd]
  Return -> Bytecode [0xf3]
  Jump -> Bytecode [0x56]
  Jumpdest -> Bytecode [0x5b]
