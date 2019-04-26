sieve :: [Int] -> [Int]
sieve (p : xs) = p : sieve (filter (\ a -> a `mod` p /= 0) xs)

primes :: [Int]
primes = sieve [2..]

main =
  print (sum (take 2000 primes))
