{-# Language DeriveDataTypeable #-}
{-# Language DeriveGeneric #-}
{-# Language RecursiveDo #-}
{-# Language NamedFieldPuns #-}

module EVM.Symbex where

import Prelude hiding (not, and, or, exp, return, div, log)
import qualified Prelude

import Data.Generics.Uniplate.Data
import Data.Data (Data)
import Data.Typeable (Typeable)
import GHC.Generics
import Data.Aeson (ToJSON ())

import EVM.Assembly

example :: [Instr]
example = assemble $ mdo
  caller
  dup 1; push 1; eq; refer x; swap 1; jumpi
  dup 1; push 2; eq; refer y; swap 1; jumpi
  dup 1; push 3; eq; refer z; swap 1; jumpi
  pop; push 0; push 1; mstore; push 0; mload; stop
  x <- label; pop; push 10; stop
  y <- label; pop; push 11; stop
  z <- label; pop; push 12; stop

multisig2 :: [Instr]
multisig2 = assemble $ mdo

  let
    allow s i j = do
      as ("id of " ++ s)      (push i)
      as ("address of " ++ s) (push j)
      caller; eq; refer confirm; jumpi; pop

  allow "bob" 8 10
  allow "pam" 9 11
  allow "tom" 10 12
  allow "ken" 11 13
  allow "liz" 12 14
  allow "joe" 13 15
  nope <- label; stop

  confirm <- label
  as "size of action hash" (push 32); calldatasize; gt; refer trigger; jumpi
  push 0; as "action hash" calldataload; dup 1; as "old action state" sload
  push 2; dup 4; as "confirmation flag bitmask" exp
  dup 1; dup 3; as "user confirmation bit" and; refer nope; jumpi
  dup 2; or
  push 255; not; as "new confirmation state" and
  swap 1; push 255; as "old confirmation count" and
  push 1; as "new confirmation count" add
  as "new action state" or; swap 1; sstore; stop

  trigger <- label
  calldatasize; push 0; push 0; as "full action" calldatacopy
  calldatasize; push 0; as "action hash" keccak256
  as "quorum" (push 2); dup 2; as "action state" sload;
  push 255; as "confirmation count" and; lt; refer nope; jumpi
  push 0; as "deadline" calldataload; timestamp; gt; refer nope; jumpi
  push 255; as "trigger state" not; swap 1; sstore
  push 0; push 0; push 96; calldatasize; sub; push 96
  push 64; calldataload; push 32; calldataload
  gas; call; pop
instance ToJSON Value
instance ToJSON AValue
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
  | TheCalldataWord AValue
  | TheTimestamp
  | TheGas
  | SomeCallResult
  | TheByte AValue AValue
  | SetByte Integer AValue AValue
  | Size Memory
  | Equality AValue AValue
  | IsGreaterThan AValue AValue
  | IsLessThan AValue AValue
  | IsGreaterThanSigned AValue AValue
  | IsLessThanSigned AValue AValue
  | Negation AValue
  | Minus AValue AValue
  | Plus AValue AValue
  | Times AValue AValue
  | DividedBy AValue AValue
  | TheHashOf AValue AValue Memory
  | MemoryAt AValue Memory
  | StorageAt AValue Memory
  | Max AValue AValue
  | Conjunction AValue AValue
  | Disjunction AValue AValue
  | Exponentiation AValue AValue
  | SetBit AValue AValue
  | IsBitSet AValue AValue
  | IsZero AValue
  deriving (Show, Eq, Data, Typeable, Generic)

data AValue = As
  { annotation :: Maybe String
  , value :: Value
  }
  deriving (Show, Eq, Data, Typeable, Generic)

dependsOnCall :: AValue -> Bool
dependsOnCall = elem SomeCallResult . universe . value

type PC = Integer
type Stack = [AValue]
type Code = [Instr]

findJumpdest :: Code -> Integer -> PC
findJumpdest (Instr _ _ Jumpdest : _) 0 = 0
findJumpdest _ 0 = error "jumpdest error"
findJumpdest (Instr _ _ (Push n x) : k) i =
  1 + n + findJumpdest (i - 1 - n)

data Memory
  = Null
  | With AValue AValue Memory
  | WithByte AValue AValue Memory
  | WithCalldata (AValue, AValue, AValue) Memory
  | WithCallResult (AValue, AValue) Memory
  | ArbitrarilyAltered Memory
  deriving (Show, Eq, Data, Typeable, Generic)

data State = State
  { stack   :: Stack
  , pc      :: PC
  , memory  :: Memory
  , storage :: Memory
  } deriving (Show, Generic)

data Possibility
  = Step State
  | Fork AValue State State
  | StackUnderrun Instr
  | Done
  | Reverted
  | Returned AValue AValue
  deriving (Show, Generic)

exec :: State -> Code -> Possibility
exec (State { pc }) c | fromInteger pc >= length c =
  Done
exec (state @ State { stack, pc, memory, storage }) c =
  let instr = c !! fromInteger pc
      a = instrAnnotation instr
  in case op instr of
    Stop ->
      Done

    Jumpdest ->
      Step $ state
        { pc = succ pc }

    Push _ x ->
      Step $ state
        { stack = As a (Actual x) : stack
        , pc = succ pc }

    PushLabel (Label x) ->
      Step $ state
        { stack = As a (Actual x) : stack
        , pc = succ pc }

    Jumpi ->
      case stack of
        (As _ (Actual j) : x : stack') ->
          Fork x
            (state { stack = stack', pc = (findJumpdest c j) })
            (state { stack = stack', pc = succ pc })
        (_ : _ : _) ->
          error "symbolic jump"
        _ ->
          StackUnderrun instr

    Jump ->
      case stack of
        (As _ (Actual j) : stack') ->
          Step $
            (state { stack = stack', pc = j })
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
            { stack = As a (IsZero x) : xs
            , pc = succ pc
            }
        _ ->
          StackUnderrun instr

    Caller ->
      Step $ state
        { stack = As a TheCaller : stack
        , pc = succ pc }

    Eq ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = As a (Equality x y) : stack'
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
            { stack = As a (MemoryAt x memory) : stack'
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
            { stack = As a (StorageAt x storage) : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Calldatasize ->
      Step $ state
        { stack = As a TheCalldatasize : stack
        , pc = succ pc }

    Callvalue ->
      Step $ state
        { stack = As a TheCallvalue : stack
        , pc = succ pc }

    Gt ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = As a (x `IsGreaterThan` y) : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Sgt ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = As a (x `IsGreaterThanSigned` y) : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Slt ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = As a (x `IsLessThanSigned` y) : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Div ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = As a (x `DividedBy` y) : stack'
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
            { stack = As a (x `IsLessThan` y) : stack'
            , pc = succ pc }
        _ ->
          StackUnderrun instr

    Calldataload ->
      case stack of
        (x:stack') ->
          Step $ state
            { stack = As a (TheCalldataWord x) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Byte ->
      case stack of
        (i:x:stack') ->
          Step $ state
            { stack = As a (TheByte i x) : stack'
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
        { stack = As a (Size memory) : stack
        , pc = succ pc }

    Keccak256 ->
      case stack of
        (xOffset:xSize:stack') ->
          Step $ state
            { stack = As a (TheHashOf xOffset xSize memory) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Timestamp ->
      Step $ state
        { stack = As a TheTimestamp : stack
        , pc = succ pc }

    Gas ->
      Step $ state
        { stack = As a TheGas : stack
        , pc = succ pc }

    Sub ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = As a (Minus x y) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Add ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = As a (Plus x y) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Mul ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = As a (Times x y) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Exp ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = As a (Exponentiation x y) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    And ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = As a (Conjunction x y) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Or ->
      case stack of
        (x:y:stack') ->
          Step $ state
            { stack = As a (Disjunction x y) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

    Call ->
      case stack of
        (_:_xTo:_xValue:_xInOffset:_xInSize:xOutOffset:xOutSize:stack') -> do
          Step $ (state
              { stack = As a (Actual 1) : stack'
              , pc = succ pc
              , memory = WithCallResult (xOutOffset, xOutSize) memory
              , storage = ArbitrarilyAltered storage
              })
          -- Fork (SomeCallResult)
          --   (state
          --     { stack = As a (Actual 1) : stack'
          --     , pc = succ pc
          --     , memory = WithCallResult (xOutOffset, xOutSize) memory
          --     , storage = ArbitrarilyAltered storage
          --     })
          --   (state
          --     { stack = As a (Actual 0) : stack'
          --     , pc = succ pc
          --     })
        _ -> StackUnderrun instr
    Not ->
      case stack of
        (x:stack') ->
          Step $ state
            { stack = As a (Negation x) : stack'
            , pc = succ pc }
        _ -> StackUnderrun instr

-- !

data Outcome = Good | Bad String
  deriving (Show, Generic)

data Path = Path [AValue] State Outcome
  deriving Generic

data Tree = One State Outcome | Two AValue Tree Tree
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
        ++ map (\(Path ps s' o) -> Path (As Nothing (Negation p) : ps) s' o) (step c s2)

pathDoesCall :: Path -> Bool
pathDoesCall (Path x _ _) = any dependsOnCall x

class Optimize a where
  optimize :: a -> Maybe a

memorySize :: Memory -> Value
memorySize = \case
  Null ->
    Actual 0
  WithCalldata (n, _, dst) m ->
    Max (As Nothing (memorySize m)) (As Nothing (Plus dst n))
  x ->
    Size x

instance Optimize AValue where
  optimize (As a instr) = case instr of
    Size x -> Just (As a (memorySize x))
    Max (As _ (Actual 0)) x -> Just x
    Plus (As _ (Actual 0)) x -> Just x
    MemoryAt x mem -> resolveMemory a x mem
    Disjunction (As _ (Exponentiation (As _ (Actual 2)) (As _ (Actual x)))) y ->
      Just (As a (SetBit (As Nothing (Actual (x + 1))) y))
    Conjunction (As _ (Exponentiation (As _ (Actual 2)) (As _ (Actual x)))) y ->
      Just (As a (IsBitSet (As Nothing (Actual (x + 1))) y))
    _ -> Nothing

resolveMemory :: Maybe String -> AValue -> Memory -> Maybe AValue
resolveMemory a _ Null = Just (As a (Actual 0))
resolveMemory a x (With y z m) =
  if value x == value y then Just z else resolveMemory a x m
resolveMemory a (As _ (Actual i)) (WithByte (As _ (Actual j)) z m) =
  if i == Prelude.div j 32
  then
    -- We have information about one byte of the requested word.
    case resolveMemory a (As Nothing (Actual i)) m of
      Nothing -> Nothing
      Just (As a' x') -> Just (As Nothing (SetByte j z (As a' x')))
  else
    -- This byte is unrelated to the requested word.
    resolveMemory a (As Nothing (Actual i)) m
resolveMemory _ _ _ = Nothing

isArbitrarilyAltered :: Memory -> Bool
isArbitrarilyAltered m =
  case m of
    Null -> False
    With _ _ x -> isArbitrarilyAltered x
    WithByte _ _ x -> isArbitrarilyAltered x
    WithCalldata _ x -> isArbitrarilyAltered x
    WithCallResult _ x -> isArbitrarilyAltered x
    ArbitrarilyAltered _ -> True
