{-# Language DeriveGeneric #-}
{-# Language OverloadedStrings #-}
{-# Language NamedFieldPuns #-}
{-# Language LambdaCase #-}

import GHC.Generics
import Data.Aeson hiding (Null, Value)
import System.Environment (getArgs)

import Data.Word
import Data.Bits
import Data.Text (Text, pack, unpack)
import Data.Text.Encoding (encodeUtf8, decodeUtf8)

import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Base16 as BS16

data Op
  = Push Int Integer
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

word :: [Word8] -> Integer
word xs = sum [ fromIntegral x `shiftL` (8*n)
              | (n, x) <- zip [0..] (reverse xs) ]

parse :: [Word8] -> Maybe [Op]
parse [] = Just []
parse (b:bs) = do
  let k x = (x :) <$> parse bs
  case b of
    x | x >= 0x60 && x <= 0x7f -> do
      let n = fromIntegral x - 0x60 + 1
          w = word (take n bs)
      (Push n w :) <$> parse (drop n bs)
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

instance ToJSON Op
instance ToJSON Value
instance ToJSON Memory
instance ToJSON State
instance ToJSON Possibility
instance ToJSON Path
instance ToJSON Outcome
instance ToJSON Tree

data Value
  = Actual Integer
  | TheCaller
  | TheCalldatasize
  | TheCallvalue
  | TheCalldataWord Value
  | TheTimestamp
  | TheGas
  | SomeCallResult
  | TheByte Value Value
  | SetByte Integer Value Value
  | Size Memory
  | Equality Value Value
  | IsGreaterThan Value Value
  | IsLessThan Value Value
  | IsGreaterThanSigned Value Value
  | IsLessThanSigned Value Value
  | Negation Value
  | Minus Value Value
  | Plus Value Value
  | Times Value Value
  | DividedBy Value Value
  | TheHashOf Value Value Memory
  | MemoryAt Value Memory
  | StorageAt Value Memory
  | Max Value Value
  | Conjunction Value Value
  | Disjunction Value Value
  | Exponentiation Value Value
  | SetBit Value Value
  | IsBitSet Value Value
  | IsZero Value
  deriving (Show, Eq, Generic)

-- dependsOnCall :: Value -> Bool
-- dependsOnCall = elem SomeCallResult . universe . value

type PC = Int
type Stack = [Value]
type Code = [Op]

findJumpdest :: Code -> Int -> Int
findJumpdest (Jumpdest : _) 0 = 0
findJumpdest _ 0 = error "jumpdest error"
findJumpdest (Push n x : k) i =
  1 + findJumpdest k (i - 1 - n)
findJumpdest (o : k) i =
  1 + findJumpdest k (i - 1)
findJumpdest [] i = error ("crazy " ++ show i)

data Memory
  = Null
  | With Value Value Memory
  | WithByte Value Value Memory
  | WithCalldata (Value, Value, Value) Memory
  | WithCallResult (Value, Value) Memory
  | ArbitrarilyAltered Memory
  deriving (Show, Eq, Generic)

data State = State
  { stack   :: Stack
  , pc      :: PC
  , memory  :: Memory
  , storage :: Memory
  } deriving (Show, Generic)

data Possibility
  = Step State
  | Fork Value State State
  | StackUnderrun Op
  | Done
  | Reverted
  | Returned Value Value
  deriving (Show, Generic)

exec :: State -> Code -> Possibility
exec (State { pc }) c | pc >= length c =
  Done
exec (state @ State { stack, pc, memory, storage }) c =
  let instr = c !! pc
  in case instr of
    Stop ->
      Done

    Jumpdest ->
      Step $ state
        { pc = succ pc }

    Push _ x ->
      Step $ state
        { stack = Actual x : stack
        , pc = succ pc }

    Jumpi ->
      case stack of
        (Actual j : x : stack') ->
          Fork x
            (state { stack = stack', pc = findJumpdest c (fromIntegral j) })
            (state { stack = stack', pc = succ pc })
        (_ : _ : _) ->
          error "symbolic jump"
        _ ->
          StackUnderrun instr

    Jump ->
      case stack of
        (Actual j : stack') ->
          Step $
            (state { stack = stack', pc = findJumpdest c (fromIntegral j) })
        (_ : _) ->
          error "symbolic jump"
        _ ->
          StackUnderrun instr

    Dup n ->
      if length stack >= n
      then Step $ state
        { stack = stack !! (n - 1) : stack
        , pc = succ pc }
      else StackUnderrun instr

    Pop ->
      case stack of
        (_:stack') ->
          Step $ state
            { stack = stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Swap n ->
      -- swap 5
      -- 1 2 3 4 5 6 7 8 9 10
      -- 6 : 1 2 3 4 5 : 7 8 9 10
      -- #n : take n : drop (n + 1)
      if length stack >= n + 1
      then
        let stack' = (stack !! n) :
                       (take n stack ++ drop (n + 1) stack)
        in Step $ state
          { stack = stack'
          , pc = succ pc }
      else
        StackUnderrun instr

    Log n ->
      if length stack >= n + 2
      then
        Step $ state
          { stack = drop (n + 2) stack
          , pc = succ pc }
      else
        StackUnderrun instr

    Iszero ->
      case stack of
        (x:xs) ->
          Step $ state
            { stack = IsZero x : xs
            , pc = succ pc
            }
        _ ->
          StackUnderrun instr

    Caller ->
      Step $ state
        { stack = TheCaller : stack
        , pc = succ pc }

    Eq ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = Equality x y : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Mstore ->
      case stack of
        (x : y : stack') ->
          Step $ state
            { stack = stack'
            , pc = succ pc
            , memory = With x y memory }
        _ ->
          StackUnderrun instr

    Mstore8 ->
      case stack of
        (x : y : stack') ->
          Step $ state
            { stack = stack'
            , pc = succ pc
            , memory = WithByte x y memory }
        _ ->
          StackUnderrun instr

    Mload ->
      case stack of
        (x:stack') ->
          Step $ state
            { stack = MemoryAt x memory : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Sstore ->
      case stack of
        (x : y : stack') ->
          Step $ state
            { stack = stack'
            , pc = succ pc
            , storage = With x y storage }
        _ ->
          StackUnderrun instr

    Sload ->
      case stack of
        (x:stack') ->
          Step $ state
            { stack = StorageAt x storage : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Calldatasize ->
      Step $ state
        { stack = TheCalldatasize : stack
        , pc = succ pc }

    Callvalue ->
      Step $ state
        { stack = TheCallvalue : stack
        , pc = succ pc }

    Gt ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = (x `IsGreaterThan` y) : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Sgt ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = (x `IsGreaterThanSigned` y) : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Slt ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = (x `IsLessThanSigned` y) : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Div ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = (x `DividedBy` y) : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Revert ->
      Reverted

    Return ->
      case stack of
        (x:y:_) ->
          Returned x y
        _ ->
          StackUnderrun instr

    Lt ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = (x `IsLessThan` y) : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Calldataload ->
      case stack of
        (x:stack') ->
          Step $ state
            { stack = (TheCalldataWord x) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Byte ->
      case stack of
        (i:x:stack') ->
          Step $ state
            { stack = (TheByte i x) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Calldatacopy ->
      case stack of
        (xTo:xFrom:xSize:stack') ->
          Step $ state
            { stack = stack'
            , pc = succ pc
            , memory = WithCalldata (xSize, xFrom, xTo) memory
            }
        _ -> StackUnderrun instr

    Msize ->
      Step $ state
        { stack = (Size memory) : stack
        , pc = succ pc }

    Keccak256 ->
      case stack of
        (xOffset:xSize:stack') ->
          Step $ state
            { stack = (TheHashOf xOffset xSize memory) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Timestamp ->
      Step $ state
        { stack = TheTimestamp : stack
        , pc = succ pc }

    Gas ->
      Step $ state
        { stack = TheGas : stack
        , pc = succ pc }

    Sub ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = (Minus x y) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Add ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = (Plus x y) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Mul ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = (Times x y) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Exp ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = (Exponentiation x y) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    And ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = (Conjunction x y) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Or ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = (Disjunction x y) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Call ->
      case stack of
        (_:_xTo:_xValue:_xInOffset:_xInSize:xOutOffset:xOutSize:stack') -> do
          Step $ (state
              { stack = (Actual 1) : stack'
              , pc = succ pc
              , memory = WithCallResult (xOutOffset, xOutSize) memory
              , storage = ArbitrarilyAltered storage
              })
          -- Fork (SomeCallResult)
          --   (state
          --     { stack = (Actual 1) : stack'
          --     , pc = succ pc
          --     , memory = WithCallResult (xOutOffset, xOutSize) memory
          --     , storage = ArbitrarilyAltered storage
          --     })
          --   (state
          --     { stack = (Actual 0) : stack'
          --     , pc = succ pc
          --     })
        _ -> StackUnderrun instr
    Not ->
      case stack of
        (x:stack') ->
          Step $ state
            { stack = (Negation x) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

data Outcome = Good | Bad String
  deriving (Show, Generic)

data Path = Path [Value] State Outcome
  deriving (Generic, Show)

data Tree = One State Outcome | Two Value Tree Tree
  deriving Generic

step' :: Code -> State -> Tree
step' c state =
  case exec state c of
    Done -> One state Good
    Reverted -> One state (Bad "reverted")
    Returned _ _ -> One state Good
    StackUnderrun x -> One state (Bad (show x))
    Step s' -> step' c s'
    Fork p s1 s2 ->
      Two p (step' c s1) (step' c s2)

step :: Code -> State -> [Path]
step c state =
  case exec state c of
    Done -> [Path [] state Good]
    StackUnderrun x -> [Path [] state (Bad (show x))]
    Reverted -> [Path [] state (Bad "reverted")]
    Returned _ _ -> [Path [] state Good]
    Step s' -> step c s'
    Fork p s1 s2 ->
      map (\(Path ps s' o) -> Path (p : ps) s' o) (step c s1)
        ++ map (\(Path ps s' o) -> Path (Negation p : ps) s' o) (step c s2)

-- pathDoesCall :: Path -> Bool
-- pathDoesCall (Path x _ _) = any dependsOnCall x

-- class Optimize a where
--   optimize :: a -> Maybe a
--
-- memorySize :: Memory -> Value
-- memorySize = \case
--   Null ->
--     Actual 0
--   WithCalldata (n, _, dst) m ->
--     Max (As Nothing (memorySize m)) (As Nothing (Plus dst n))
--   x ->
--     Size x
--
-- instance Optimize Value where
--   optimize (instr) = case instr of
--     Size x -> Just ((memorySize x))
--     Max (As _ (Actual 0)) x -> Just x
--     Plus (As _ (Actual 0)) x -> Just x
--     MemoryAt x mem -> resolveMemory a x mem
--     Disjunction (As _ (Exponentiation (As _ (Actual 2)) (As _ (Actual x)))) y ->
--       Just ((SetBit (As Nothing (Actual (x + 1))) y))
--     Conjunction (As _ (Exponentiation (As _ (Actual 2)) (As _ (Actual x)))) y ->
--       Just ((IsBitSet (As Nothing (Actual (x + 1))) y))
--     _ -> Nothing
--
-- resolveMemory :: Maybe String -> Value -> Memory -> Maybe Value
-- resolveMemory a _ Null = Just ((Actual 0))
-- resolveMemory a x (With y z m) =
--   if value x == value y then Just z else resolveMemory a x m
-- resolveMemory a (As _ (Actual i)) (WithByte (As _ (Actual j)) z m) =
--   if i == Prelude.div j 32
--   then
--     -- We have information about one byte of the requested word.
--     case resolveMemory a (As Nothing (Actual i)) m of
--       Nothing -> Nothing
--       Just (As a' x') -> Just (As Nothing (SetByte j z (As a' x')))
--   else
--     -- This byte is unrelated to the requested word.
--     resolveMemory a (As Nothing (Actual i)) m
-- resolveMemory _ _ _ = Nothing

isArbitrarilyAltered :: Memory -> Bool
isArbitrarilyAltered m =
  case m of
    Null -> False
    With _ _ x -> isArbitrarilyAltered x
    WithByte _ _ x -> isArbitrarilyAltered x
    WithCalldata _ x -> isArbitrarilyAltered x
    WithCallResult _ x -> isArbitrarilyAltered x
    ArbitrarilyAltered _ -> True

emptyState :: State
emptyState = State
  { stack = []
  , pc = 0
  , memory = Null
  , storage = Null
  }

run :: Code -> [Path]
run code = step code emptyState

parseString :: String -> Maybe [Op]
parseString = parse . BS.unpack . fst . BS16.decode . encodeUtf8 . pack

main :: IO ()
main = do
  [x] <- getArgs
  case parseString x of
    Nothing -> error "error"
    Just ops -> putStrLn . unpack . decodeUtf8 . LBS.toStrict . encode $ run ops
