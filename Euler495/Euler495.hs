{-# LANGUAGE 
  ViewPatterns,
  NoMonomorphismRestriction,
  MultiParamTypeClasses,
  TypeSynonymInstances,
  FlexibleInstances,
  FlexibleContexts,
  AllowAmbiguousTypes
  #-}

import Prelude hiding (length, replicate, take)
import Data.List hiding (length, replicate, take)
import Data.Ratio
import Data.Function.Memoize
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Poly
import Data.Vector.Generic((!?))

default ()

-- We hide the originals of these functions and import the versions which operate on Integer rather than Int
length = genericLength
replicate = genericReplicate
take = genericTake

index = genericIndex

type Natural = Integer
type PositiveInteger = Natural
type Prime = PositiveInteger
type Fraction = Ratio Natural

primes = 2 : filter isPrime [3..]

smallestPrimeFactor' n = searchThrough primes where 
  searchThrough (p:ps)
    | n `mod` p == 0 = p
    | p * p > n = n
    -- We rely in the above case on the fact that every prime n > 2 has a smaller prime p such that 
    -- p^2 > n. This follows from Bertrand's postulate.
    | otherwise = searchThrough ps

smallestPrimeFactor = memoize smallestPrimeFactor'

primeFactorization :: PositiveInteger -> [Prime]
primeFactorization = memoFix (\recurse n -> 
  if n == 1
  then []
  else let p = smallestPrimeFactor n
       in insert p (recurse (n `div` p))
  )

isPrime n = smallestPrimeFactor n == n

multiplicityCompress list = 
  [(value, multiplicity) | valueRepeated <- group list, 
    let value = head valueRepeated,
    let multiplicity = length valueRepeated]

primeAndExponentFactorization = memoize (\n -> multiplicityCompress (primeFactorization n))

-- All ways to write n as a sum of a sequence of positive integers, each ≤ the previous, and 
-- the first being ≤ bound.
boundedFallingPartitions n bound
 | n < 0 = []
 | n == 0 = [[]]
 | n > 0 = 
  [firstPart:remainingPart | 
    firstPart <- [1..bound], 
    remainingPart <- boundedFallingPartitions (n - firstPart) firstPart
  ]

-- All ways to write n as a sum of a sequence of positive integers, each ≤ the previous
fallingPartitions n = boundedFallingPartitions n n

fallingPartitionsWithAtLeastOneOne n = map (++[1]) (fallingPartitions (n - 1))

lookupMultiplicity partMultiplicities part = fromMaybe 0 (lookup part partMultiplicities)

divisorsPrimePower :: (Integer, Integer) -> [Integer]
divisorsPrimePower (prime, exponent) = take (exponent + 1) (iterate (prime*) 1)

-- All divisors of n, sorted lexicographically by exponents on the ordered prime factors
divisors :: Integer -> [Integer]
divisors = memoize (\n -> map product $ sequence $ map divisorsPrimePower $ primeAndExponentFactorization n)

expandMultiplicities multiplicities = concat [replicate multiplicity value | (value, multiplicity) <- multiplicities]

boundedColoredPartitions = memoFix2 (\recurse fallingTileSizes n -> 
  if n < 0 then  {-# SCC "negative" #-} 0
  else if n == 0 then  {-# SCC "1" #-} 1
  else if n < 10 then {-# SCC "under10" #-} sum [(recurse cut (n - tileSize)) | cut <- tails fallingTileSizes, not (null cut), let tileSize = head cut]
  else if n < 50 then {-# SCC "under50" #-} sum [(recurse cut (n - tileSize)) | cut <- tails fallingTileSizes, not (null cut), let tileSize = head cut]
  else if n < 500 then {-# SCC "under500" #-} sum [(recurse cut (n - tileSize)) | cut <- tails fallingTileSizes, not (null cut), let tileSize = head cut]
  else if n < 1000 then {-# SCC "under1000" #-} sum [(recurse cut (n - tileSize)) | cut <- tails fallingTileSizes, not (null cut), let tileSize = head cut]
  else {-# SCC "Over1000" #-} sum [(recurse cut (n - tileSize)) | cut <- tails fallingTileSizes, not (null cut), let tileSize = head cut]
  )

-- The number of ways to choose bars + 1 distinguishable natural numbers which sum to stars, is the same as the number 
-- of ways to arrange stars and bars, which is (stars + bars) choose (stars; bars)
starsAndBars stars bars = 
  let j = min stars bars
      numerator = product $ take j $ iterate (subtract 1) (stars + bars)
      denominator = factorial j
  in numerator `div` denominator

boundedColoredPartitions2 :: [(Integer, Integer)] -> Integer -> Integer
boundedColoredPartitions2 = memoFix2 (\recurse tileMultiplicities n -> 
  if n < 0 then 0
  else if n == 0 then 1
  else if null tileMultiplicities then 0
  else sum [(recurse remainingTileMultiplicities (n - numberUses * tileSize)) * numColorings 
         | cut <- tails tileMultiplicities,
           not (null cut),
           let (tileSize, multiplicity) = head cut,
           let remainingTileMultiplicities = tail cut,
           numberUses <- [1..(n `div` tileSize)],
           let numColorings = starsAndBars numberUses (multiplicity - 1)
         ]
  )

coloredPartitions3 :: [(Integer, Integer)] -> Integer -> Integer
coloredPartitions3 multiplicities = memoize (\n -> boundedColoredPartitions2 (reverse multiplicities) n)

coloredPartitions2 :: [(Integer, Integer)] -> Integer -> Integer
coloredPartitions2 fallingMultiplicities =
  let risingTileSizes = expandMultiplicities (reverse fallingMultiplicities)
  in memoize (\n -> boundedColoredPartitions risingTileSizes n)

{-
coloredPartitions4 :: [(Integer, Integer)] -> Integer -> Integer
coloredPartitions4 multiplicities =
  let risingTileSizes = expandMultiplicities multiplicities
  in memoize (\n -> boundedColoredPartitions risingTileSizes n)
-}

coloredPartitions1 :: [(Integer, Integer)] -> Integer -> Integer
coloredPartitions1 (lookupMultiplicity -> multiplicityFunc) = 
  let gamma = memoize (\n -> sum [divisor * (multiplicityFunc divisor) | divisor <- divisors n])
  in 
    memoFix (\recurse n ->
     if n == 1 
     then multiplicityFunc 1
     else (gamma n + sum [(gamma k) * (recurse (n - k)) | k <- [1..n-1]]) `div` n
    )

-- We assume for now that the polynomial to be inverted has lowest-order term 1
invertPoly :: (VPoly Integer) -> Integer -> Integer
invertPoly p =
  let coeff d = fromMaybe 0 $ (unPoly p) !? (fromIntegral d)
  in
    memoFix (\recurse n -> 
    if n == 0
    then 1
    else - sum [(recurse k) * (coeff (n - k)) | k <- [0..n-1]]
    )

coloredPartitions5 :: [(Integer, Integer)] -> Integer -> Integer
coloredPartitions5 m = invertPoly $ product [(1 - X^a)^b | (a, b) <- m]

coloredPartitions beta 1 = fromMaybe 0 (lookup 1 beta)
coloredPartitions beta n = coloredPartitions2 beta n -- Empirically, this is better than coloredPartitions1 or coloredPartitions3
-- Test: coloredPartitions [(2, 1), (3, 1), (5, 1), (7, 2)] 1000 = 29727907

theta partMultiplicities = sum [(1 + i) * multiplicity | (i, multiplicity) <- partMultiplicities]
parityTheta partMultiplicities = case (theta partMultiplicities `mod` 2) of 
  0 -> id
  1 -> negate

factorials = scanl (*) 1 [1..]
factorial n = factorials `index` n

reciprocalH partMultiplicities = product [i^multiplicity * (factorial multiplicity) | (i, multiplicity) <- partMultiplicities]

vectorPartitions k vector = 
  sum [parityTheta beta (vectorPartitionsDuplicatePattern beta vector)
        | alpha <- fallingPartitionsWithAtLeastOneOne k, let beta = multiplicityCompress alpha
      ]

class Divide a b where 
  divide :: a -> a -> b

instance Divide Integer Modular where
  divide m n = (toModular m) / (toModular n)

instance Divide Integer Fraction where
  divide m n = (fromIntegral m) % (fromIntegral n)

vectorPartitionsDuplicatePattern :: Divide Integer b => [(Integer, Integer)] -> [Integer] -> b
vectorPartitionsDuplicatePattern beta vector =
  let numerator = product [coloredPartitions beta component | component <- vector]
      denominator = reciprocalH beta
  in numerator `divide` denominator

-- The number of ways in which n can be written as the product of k distinct positive integers
w n k = vectorPartitions k (map snd $ primeAndExponentFactorization n)

-- Computes n/p + n/p^2 + n/p^3 + ..., where all divisions are rounded down to whole numbers
legendre n p | n < p = 0
             | otherwise = firstTerm + legendre firstTerm p where firstTerm = n `div` p

-- Returns primeAndExponentFactorization (n!), quickly using Legendre's theorem
factorialPrimeAndExponentFactorization n = [(p, legendre n p) | p <- takeWhile (<= n) primes]

newtype Modular = Modular Integer deriving Show
modulus = 1000000007 :: Integer -- Note that this is a prime modulus!
checkPrimeModulus = isPrime modulus
toModular a = Modular (a `mod` modulus)

instance Num Modular where
  fromInteger n = toModular (fromIntegral n)
  (Modular a) + (Modular b) = toModular (a + b)
  (Modular a) * (Modular b) = toModular (a * b)
  negate (Modular a) = toModular (negate a)

inverse :: Integral a => a -> a -> a
inverse q 1 = 1
inverse q p = (n * q + 1) `div` p
    where n = p - inverse p (q `mod` p)

instance Fractional Modular where
  recip (Modular a) = if not checkPrimeModulus then error "Non prime modulus!" else (Modular (inverse modulus a))

-- Returns w (n!) k modulo the fixed modulus.
genericAnswer :: Integer -> Integer -> Modular
genericAnswer n k = vectorPartitions k (map snd (factorialPrimeAndExponentFactorization n))

answer = genericAnswer 100 30

main2 = putStrLn $ show answer