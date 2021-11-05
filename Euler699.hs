import Prelude hiding (length, replicate)
import Data.List hiding (length, replicate)
import Data.Ratio
import Data.Function.Memoize
import qualified Data.Map.Strict as Map

-- We hide the originals of these functions and import the versions which operate on Integer rather than Int
length = genericLength
replicate = genericReplicate
index = genericIndex

type Natural = Integer
type PositiveInteger = Natural
type Prime = PositiveInteger
type Fraction = Ratio Natural

primes = 2 : filter isPrime [3..]

isPrime n = searchThrough primes where 
  searchThrough (p:ps)
   | n `mod` p == 0 = False
   | p^2 > n = True
   -- We rely in the above case on the fact that every prime n > 2 has a smaller prime p such that 
   -- p^2 > n. This follows from Bertrand's postulate.
   | otherwise = searchThrough ps

-- Returns the prime factorization as a list of primes with multiplicity, sorted in increasing order
{-
primeFactorization n = primeFactorization' n primes where 
  primeFactorization' 1 _ = []
  primeFactorization' n remainingPrimes@(candidatePrime : furtherPrimes) =
    let (quotient, modulus) = n `divMod` candidatePrime
    in if modulus == 0
       then candidatePrime : primeFactorization' quotient remainingPrimes
       else primeFactorization' n furtherPrimes

primeAndExponentFactorization n = 
  [(prime, exponent) | primeRepeated <- group (primeFactorization n), 
    let prime = head primeRepeated,
    let exponent = length primeRepeated]
-}
primeFactorization' :: (PositiveInteger -> [Prime]) -> PositiveInteger -> [Prime]
primeFactorization' recurse 1 = emptyFactorization
primeFactorization' recurse n = 
  head [addFactor p (recurse quotient) | p <- primes, let (quotient, modulus) = n `divMod` p, modulus == 0]

emptyFactorization :: [Prime]
emptyFactorization = []

addFactor :: Prime -> [Prime] -> [Prime]
addFactor p factorization = p : factorization

primeFactorization = memoFix primeFactorization'

primeAndExponentFactorization = memoize (\n ->
  [(prime, exponent) | primeRepeated <- group (primeFactorization n), 
    let prime = head primeRepeated,
    let exponent = length primeRepeated])

sigmaOverPrimePower :: Prime -> Natural -> Fraction
sigmaOverPrimePower = memoize2 (\prime exponent -> ((prime^(exponent + 1) - 1) `div` (prime - 1)) % (prime^exponent))

sigmaOver' recurse 1 = 1
sigmaOver' recurse n = let
  (p, e) = last (primeAndExponentFactorization n)
  quotient = n `div` (p^e)
  in (sigmaOverPrimePower p e) * (recurse quotient)

sigmaOver :: PositiveInteger -> Fraction
sigmaOver = memoFix sigmaOver'

powerOfThree n = case primeAndExponentFactorization n of
  [(3, _)] -> True -- Note that we do not include the case where the denominator is 3^0 = 1
  _ -> False

acceptable n = powerOfThree $ denominator (sigmaOver n)