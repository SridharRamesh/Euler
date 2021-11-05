import Prelude hiding (length, replicate)
import Data.List hiding (length, replicate)
import Data.Ratio

-- We hide the originals of these functions and import the versions which operate on Integer rather than Int
length = genericLength
replicate = genericReplicate

-- Some convenient type names. 
-- The underlying types do not actually enforce that values of these types be >= 0, but that is our intention.
type Natural = Integer
type Fraction = Ratio Natural

-- partialProduct list returns a function which sends n to the product of the first n elements of list.
-- Once this function is called for a given n, its values for all arguments up through that n are
-- memoized for future calls.
partialProduct list = genericIndex $ scanl (*) 1 list

-- factorial n = n!, straightforwardly enough.
factorial = partialProduct [1..]

-- Number of elements of n^k in which x items appear once and y items appear twice, over all x + 2y = k.
-- For any particular x and y, this comes out to n! k! divided by (n - x - y)! x! y! 2^y.
noItemHasThreeDefectsCount :: Natural -> Natural -> Natural
noItemHasThreeDefectsCount k n = let 
  -- nFallingProduct r = n! / (n - r)!
  nFallingProduct = partialProduct $ iterate (subtract 1) n
  
  -- chooser x y = n! / ((n - x - y)! x! y!). This is guaranteed to be a whole number, as it is a 
  -- multinomial coefficient.
  chooser x y = nFallingProduct (x + y) `div` ((factorial x) * (factorial y))

  -- Term x y is the number of elements of n^k in which x items appear once and y items appear twice.
  -- This comes out to n! k! divided by (n - x - y)! x! y! 2^y, which is thus guaranteed to be a whole 
  -- number.
  term x y = (chooser x y) * (factorial k) `div` 2^y

  -- We do not consider values of y above yCutoff. The right cut-off is k/2. However, because the 
  -- contribution decays exponentially as y increases, we can cut off even earlier and obtain 
  -- good enough results for our purposes. We impose an early cut-off of 300 here. This cut-off 
  -- value of 300 has been observed empirically to be in the regime where the result we are 
  -- ultimately interested in stabilizes.
  yCutoff = min (k `div` 2) 300

  in sum [term x y | y <- [0..yCutoff], let x = k - 2 * y]

noItemHasThreeDefectsProbability :: Natural -> Natural -> Fraction
noItemHasThreeDefectsProbability k n = (noItemHasThreeDefectsCount k n) % (n^k)

someItemHasThreeDefectsProbability :: Natural -> Natural -> Fraction
someItemHasThreeDefectsProbability k n = 1 - (noItemHasThreeDefectsProbability k n)

-- The input is presumed to be a fraction in the range [0, 1)
showFractionToNumDigits :: Natural -> Fraction -> String
showFractionToNumDigits numDigits q = 
  let core = show $ (numerator q) * 10^numDigits `div` (denominator q)
      leadingZeros = replicate (numDigits - (length core)) '0'
  in "0." ++ leadingZeros ++ core

main :: IO ()
main = putStrLn $ showFractionToNumDigits 10 $ someItemHasThreeDefectsProbability (2 * 10^4) (10^6)