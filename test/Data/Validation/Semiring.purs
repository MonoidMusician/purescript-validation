module Test.Data.Validation.Semiring where

import Prelude

import Control.Alt (class Alt, (<|>))
import Control.Alternative (class Alternative, class Plus)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log, logShow)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Control.Monad.Gen (choose)
import Data.Bifunctor (class Bifunctor)
import Data.Newtype (class Newtype)
import Data.Validation.Semiring as V
import Test.QuickCheck (class Arbitrary, (===))
import Test.QuickCheck as QC
import Test.QuickCheck.Gen (resize)
import Test.QuickCheck.Laws.Control as QCLC
import Type.Proxy (Proxy2(..))

newtype V e a = V (V.V e a)
derive instance newtypeV :: Newtype (V e a) _
derive newtype instance eqV :: (Eq e, Eq a) => Eq (V e a)
derive newtype instance showV :: (Show e, Show a) => Show (V e a)
derive newtype instance functorV :: Functor (V e)
derive newtype instance bifunctorV :: Bifunctor V
derive newtype instance applyV :: Semiring e => Apply (V e)
derive newtype instance applicativeV :: Semiring e => Applicative (V e)
derive newtype instance altV :: Semiring e => Alt (V e)
derive newtype instance plusV :: Semiring e => Plus (V e)
derive newtype instance alternativeV :: Semiring e => Alternative (V e)

instance arbitraryV :: (Semiring e, Arbitrary e, Arbitrary a) =>
  Arbitrary (V e a) where
    arbitrary = V <$> choose
      (V.invalid <$> resize 3 QC.arbitrary)
      (pure <$> QC.arbitrary)

data V2 e a = V1 e | V2 e a
derive instance eqV2 :: (Eq e, Eq a) => Eq (V2 e a)
derive instance functorV2 :: Functor (V2 e)
instance bifunctorV2 :: Bifunctor V2 where
  bimap f _ (V1 e) = V1 (f e)
  bimap f g (V2 e a) = V2 (f e) (g a)
instance applyV2 :: Semiring e => Apply (V2 e) where
  apply (V1 e1) (V1 e2) = V1 (e1 * e2)
  apply (V1 e1) (V2 e2 _) = V1 (e1 * e2)
  apply (V2 e1 _) (V1 e2) = V1 (e1 * e2)
  apply (V2 e1 fa) (V2 e2 a) = V2 (e1 * e2) (fa a)
instance applicativeV2 :: Semiring e => Applicative (V2 e) where
  pure = V2 one
instance altV2 :: Semiring e => Alt (V2 e) where
  alt (V1 e1) (V1 e2) = V1 (e1 + e2)
  alt (V1 e1) (V2 e2 a) = V2 (e1 + e2) a
  alt (V2 e1 a) (V1 e2) = V2 (e1 + e2) a
  alt (V2 e1 a) (V2 e2 _) = V2 (e1 + e2) a
instance plusV2 :: Semiring e => Plus (V2 e) where
  empty = V1 zero
instance showV2 :: (Show e, Show a) => Show (V2 e a) where
  show (V1 e) = "(V1 " <> show e <> ")"
  show (V2 e a) = "(V2 " <> show e <> " " <> show a <> ")"
instance alternativeV2 :: Semiring e => Alternative (V2 e)

instance arbitraryV2 :: (Arbitrary e, Arbitrary a) =>
  Arbitrary (V2 e a) where
    arbitrary = choose
      (V1 <$> QC.arbitrary)
      (V2 <$> QC.arbitrary <*> QC.arbitrary)

distR :: forall f a b. Alternative f => f (a -> b) -> f (a -> b) -> f a -> f b
distR f g x = (f <|> g) <*> x
distR' :: forall e a b. Semiring e => V e (a -> b) -> V e (a -> b) -> V e a -> V e b
distR' (V f) (V g) (V x) = V case f, g, x of
  V.Invalid err1, V.Invalid err2, _ -> case x of
    V.Valid _ -> V.Invalid (err1 + err2)
    V.Invalid err3 -> V.Invalid ((err1 + err2) * err3) -- == err1 * err3 + err2 * err3
  V.Valid fa, _, _ -> case x of
    V.Valid a -> V.Valid (fa a)
    V.Invalid err -> V.Invalid err
  V.Invalid _, _, _ -> case g, x of
    V.Invalid err1, V.Invalid err2 -> V.Invalid (err1 * err2)
    V.Invalid err, V.Valid _ -> V.Invalid err
    V.Valid _, V.Invalid err -> V.Invalid err
    V.Valid fa, V.Valid a -> V.Valid (fa a)
distL :: forall f a b. Alternative f => f (a -> b) -> f (a -> b) -> f a -> f b
distL f g x = (f <*> x) <|> (g <*> x)
distL' :: forall e a b. Semiring e => V e (a -> b) -> V e (a -> b) -> V e a -> V e b
distL' (V f) (V g) (V x) = V case x of
  V.Invalid err3 ->
    case f, g of
      V.Invalid err1, V.Invalid err2 ->
        V.Invalid ((err1 * err3) + (err2 * err3)) -- == ((err1 + err2) * err3)
      V.Invalid err1, V.Valid _ -> V.Invalid ((err1 * err3) + err3)
      V.Valid _, V.Invalid err2 -> V.Invalid (err3 + (err2 * err3))
      V.Valid _, V.Valid _ -> V.Invalid (err3 + err3)
  V.Valid a -> case f, g of
    V.Invalid err1, V.Invalid err2 -> V.Invalid (err1 + err2)
    V.Invalid _, V.Valid ga -> V.Valid (ga a)
    V.Valid fa, _ -> V.Valid (fa a)

main :: forall e. Eff ( console :: CONSOLE, exception :: EXCEPTION, random :: RANDOM | e ) Unit
main = do
  let vInt = Proxy2 :: Proxy2 (V Int)
  let v2Int = Proxy2 :: Proxy2 (V2 Int)
  let logErroring v = logShow (V v :: V Int Unit)
  QCLC.checkApply vInt
  QCLC.checkApplicative vInt
  QCLC.checkAlt vInt
  QCLC.checkPlus vInt
  logErroring $ V.invalid 2 -- Invalid (2)
  logErroring $ V.invalid 2 <|> V.invalid 3 -- Invalid (5)
  logErroring $ V.invalid 2 <*> V.invalid 3 -- Invalid (6)
  -- this seems okay:
  logErroring $ (V.invalid 2 <|> V.invalid 3) <*> V.invalid 7 -- Invalid (35)
  logErroring $ (V.invalid 2 <*> V.invalid 7) <|> (V.invalid 3 <*> V.invalid 7) -- Invalid (35)
  -- QCLC.checkAlternative (Proxy2 :: Proxy2 (V Int))
  -- verify we expanded the definition correctly
  QC.quickCheck' 1000 (\f g (x :: V Int Ordering) -> distR f g x === (distR' f g x :: V Int Ordering))
  QC.quickCheck' 1000 (\f g (x :: V Int Ordering) -> distL f g x === (distL' f g x :: V Int Ordering))
  let ppu = pure (pure unit)
  logErroring $ (ppu <|> ppu) <*> V.invalid 2
  logErroring $ (ppu <*> V.invalid 2) <|> (ppu <*> V.invalid 2)

  let
    distributivity :: V Int (Ordering -> Ordering) -> V Int (Ordering -> Ordering) -> V Int Ordering -> QC.Result
    distributivity f g x = ((f <|> g) <*> x) === ((f <*> x) <|> (g <*> x))
  --QC.quickCheck' 1000 distributivity
  pure unit

  log "---------- V2 -----------"
  QCLC.checkApply v2Int
  QCLC.checkApplicative v2Int
  QCLC.checkAlt v2Int
  QCLC.checkPlus v2Int
  QCLC.checkAlternative v2Int
