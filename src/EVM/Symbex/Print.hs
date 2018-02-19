module EVM.Symbex.Print where

import EVM.Symbex

import Data.SCargot.Repr.Basic
import Data.SCargot.Print
import Data.Text (pack, unpack)

class SDisplay a where
  s :: a -> SExpr String

display :: SDisplay a => a -> String
display = unpack . encodeOne (basicPrint pack) . s

instance SDisplay Integer where
  s = A . show

instance SDisplay Value where
  s (Actual x) = A (show x)
  s TheCaller = A "caller" ::: Nil
  s TheCallvalue = A "callvalue" ::: Nil
  s TheCalldatasize = A "calldatasize" ::: Nil
  s TheTimestamp = A "timestamp" ::: Nil
  s TheGas = A "gas" ::: Nil
  s SomeCallResult = A "some-call-result" ::: Nil
  s (TheCalldataWord a) = A "calldataload" ::: s a ::: Nil
  s (TheByte a b) = A "byte" ::: s a ::: s b ::: Nil
  s (SetByte a b c) = A "set-byte" ::: s a ::: s b ::: s c ::: Nil
  s (Equality a b) = A "eq?" ::: s a ::: s b ::: Nil
  s (Minus a b) = A "-" ::: s a ::: s b ::: Nil
  s (Plus a b) = A "+" ::: s a ::: s b ::: Nil
  s (Times a b) = A "*" ::: s a ::: s b ::: Nil
  s (a `IsGreaterThan` b) = A ">" ::: s a ::: s b ::: Nil
  s (a `IsLessThan` b) = A "<" ::: s a ::: s b ::: Nil
  s (a `IsGreaterThanSigned` b) = A ">s" ::: s a ::: s b ::: Nil
  s (a `IsLessThanSigned` b) = A "<s" ::: s a ::: s b ::: Nil
  s (a `DividedBy` b) = A "div" ::: s a ::: s b ::: Nil
  s (IsZero a) = A "iszero" ::: s a ::: Nil
  s (Negation a) = A "not" ::: s a ::: Nil
  s (Size a) = A "size" ::: s a ::: Nil
  s (TheHashOf a b m) = A "keccak256" ::: s a ::: s b ::: s m ::: Nil
  s (MemoryAt x m) = A "mload" ::: s x ::: s m ::: Nil
  s (StorageAt x m) = A "sload" ::: s x ::: s m ::: Nil
  s (Max a b) = A "max" ::: s a ::: s b ::: Nil
  s (Conjunction a b) = A "and" ::: s a ::: s b ::: Nil
  s (Disjunction a b) = A "or" ::: s a ::: s b ::: Nil
  s (Exponentiation a b) = A "exp" ::: s a ::: s b ::: Nil
  s (SetBit a b) = A "set-bit" ::: s a ::: s b ::: Nil
  s (IsBitSet a b) = A "bit-set?" ::: s a ::: s b ::: Nil

instance SDisplay AValue where
  s (As Nothing x) = s x
  s (As (Just a) x) = L [A (show a), s x]

instance SDisplay Memory where
  s Null = A "initial" ::: Nil
  s (With x y m) = L [A "set", s x, s y, s m]
  s (WithByte x y m) = L [A "set-byte", s x, s y, s m]
  s (WithCalldata (n, x, y) m) =
    L [A "set-calldata", s n, s x, s y, s m]
  s (WithCallResult (x, y) m) =
    L [A "set-call-result", s x, s y, s m]
  s (ArbitrarilyAltered m) =
    L [A "arbitrarily-altered", s m]
