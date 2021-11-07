{-# LANGUAGE 
  #-}

{-
Fix an integer m. Let us consider a random walk where, with probability 1/2^n, you add to your
position -m + n, for positive integers n. Let p(z) be the probability you will ever reach the 
range of values R, starting from position z. By fiat, we have p(z) = 1 for z in R, but at all 
other z, we have the recurrence p(z) = sum over all positive integers n of 1/2^n * p(z - m + n).



1/2 p(z - m + 1) + 1/4 p(z - m + 2) + 1/8 p(z - m + 3) + ... = p(z) [for z not in R]
                   1/2 p(z - m + 2) + 1/4 p(z - m + 3) + ... = p(z + 1) [for z not in R - 1]
Subtract the former from the latter and we get:
-1/2 p(z - m + 1) + 1/4 p(z - m + 2) + 1/8 p(z - m + 3) + ... =
-1/2 p(z - m + 1) + 1/2 p(z + 1).

Thus, p(z + 1) - p(z) = -1/2 p(z - m + 1) + 1/2 p(z + 1), when z is not in R or R - 1.
Which is to say, 1/2 p(z + 1) - p(z) + 1/2 p(z - m + 1) = 0 when z is not in R or R - 1.
Which is to say, p(z + 1) - 2p(z) + p(z - m + 1) = 0 when z is not in R or R - 1.
Which is to say, p(z) - 2p(z - 1) + p(z - m) = 0 when z is not in R + 1 or R.

This is a simple recurrence: to determine any value of p, it suffices to know that m prior or 
m later values. We simply need to find m values in a row to start with whose initial values 
we know.

We are ultimately interested in the probability of bankruptcy, of ending up at any value below 
m. Note that there are m adjacent values from 0 through m - 1, all below m. Furthermore, since 
we can move down by at most m - 1 in any given turn, if we ever arrive ANYWHERE below m, starting 
from an initial value >= m, we must along the way do so by passing through one of the values from 
1 through m - 1, which at any rate is one of the values from 0 through m - 1. So we can take our 
R of interest to be 0 through m - 1, granting us m adjacent values at which p's value is known 
(to be 1). To say that we ever pass through R is the same as to say that we ever pass through a 
value less than m, so long as our starting value is >= 0.

Ah, but we also have this business of z not being in R + 1 OR R. But we can deal with that, I think 
by our also having this mismatch by one in the previous paragraph, this slack.

....

BUT

Oh no, I've misread the problem. The pot DOUBLES with each coin flip, it doesn't increment by one.
-}