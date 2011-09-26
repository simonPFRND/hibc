\section{The Random Module}

The Random module provides functions for the generation of pseudo random values. Those are used to introduce secrets in encryption and signing operations and for primality testing. The random functions too require a high level of randomness to assure the security of our system.

\begin{code}

module Random(randomInteger,
              randomString,
              randomByteString,
              findNextPrime,
              getPrime,
              getPrime') where

import Hash
import Crypto.Random
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as L

\end{code}

\subsection{Random Data}

To generate random bytestrings we use the CryptoRandomGen typeclass provided by the Crypto.Random module. It's interface is more suitable cryptographical purposes, since the Haskell's System.Random module is limited to the generation of \cc{Int} values. We will use the \cc{SystemRandom} datatype as an implementation of CryptoRandomGen. On unix-like system an instance of SystemRandom lazily reads an infinite stream of bytes from the dev/urandom file. Even though the content of dev/urandom is not purely random, it is considered suitable for most cryptographical purposes. We write a wrapper function that returns an empty bytestring if the random data can not be generated. 

\begin{code}

genBytes' :: (CryptoRandomGen g) => Int -> g -> (B.ByteString,g)
genBytes' n g = 
  let err = (\x -> (error "Could not generate random data."))
      r  = genBytes n g
  in (either err id r)


\end{code}

The \cc{randomInteger n g} generates a random number in the range $[0,n-1]$. It obtains a random $\lceil \log_{256} n \rceil$-byte number from g and maps it to the range $[0,n-1]$. 

\begin{code}

randomInteger :: (CryptoRandomGen g) => Integer -> g -> (Integer,g)
randomInteger n g =  
  let m = ceiling (logBase 256 (fromIntegral n))
      (bs,g') = genBytes' m g
      r  = mod (decodeInteger bs) n
  in (r,g')

decodeInteger :: B.ByteString -> Integer
decodeInteger b =
  let f x y = x*256 + (fromIntegral y)
  in B.foldl f 0 b

\end{code} 
 
 The \cc{randomString} function generates a random string of a given length n. It uses the \cc{genBytes'} function to generate a random bytestring of length n and decodes it as a unicode string. 
\begin{code}                    

randomString :: (CryptoRandomGen g) => Int -> g -> (String,g)
randomString n g = 
  let (bs,g') = genBytes' n g
      s = take n (decodeStr bs)
  in  (s,g')

decodeStr :: B.ByteString -> String
decodeStr b 
  | B.null b = ""
  | otherwise = (toEnum (fromEnum (B.head b))):(decodeStr (B.tail b))

\end{code}

The \cc{decodeStr} takes a \cc{ByteString} and decodes it as a unicode string. \\

Further, we define the randomByteString function that generates a random 32-byte bytestring. We will use during encryption to generate masks to hide the plaintext.

\begin{code}
                    
randomByteString :: (CryptoRandomGen g) => g -> (B.ByteString,g)
randomByteString g  = genBytes' 32 g
                     
\end{code}

\subsection{Primality Testing}

For the generation of system parameters we need to generate very large primes. We use the \emph{Miller-Rabin}
test to test a given integer for primality.

\begin{code}

isPrime :: (CryptoRandomGen g) => Integer -> Int -> g -> (Bool,g)
isPrime n m g = 
  let rek 0 g = (True,g)
      rek i g
        | r = rek (i-1) g'
        | otherwise = (False, g')
          where (n',g') = randomInteger (n-2) g
                r =  millerRabinPrimality n (n'+2) 
  in rek m g
     
\end{code}

\cc{isPrime n m g} tests \cc{n} for primality by testing it \cc{m}-times for primality using the Miller-Rabin test.
The random numbers for the test are generated using \cc{g} and  \cc{randomInteger}. The implementation of the Miller-Rabin test was taken from \citep{haskellwiki}. Applied to a composite number the Miller-Rabin test declares it a prime with probability of at most $4^{-1}$.

\ignore{
\begin{code}
--------------------------------------------------------------------------------------------------
-- Implementation of Miller-Rabin test. Takne from www.haskell.org/haskellwiki/Testing_primality--
--------------------------------------------------------------------------------------------------

find2km :: Integral a => a -> (a,a)
find2km n = f 0 n
    where 
        f k m
            | r == 1 = (k,m)
            | otherwise = f (k+1) q
            where (q,r) = quotRem m 2        
 

millerRabinPrimality :: Integer -> Integer -> Bool
millerRabinPrimality n a
    | n < 2 = False
    | even n = False
    | b0 == 1 || b0 == n' = True
    | otherwise = iter (tail b)
    where
        n' = n-1
        (k,m) = find2km n'
        b0 = expMod n a m
        b = take (fromIntegral k) $ iterate (square n) b0
        iter [] = False
        iter (x:xs)
            | x == 1 = False
            | x == n' = True
            | otherwise = iter xs
 
        
expMod :: Integer -> Integer -> Integer -> Integer
expMod p x n
  | n < 1 = 1
  | otherwise = 
    let rek _ 0 y = y
        rek x n y 
          | even n = rek (square p x) (div n 2) y 
          | otherwise = rek (square p x) (div n 2) (mul p y x)
    in rek x n 1
  
mul :: Integer -> Integer -> Integer -> Integer
mul a b c = (b * c) `mod` a

square :: Integer -> Integer -> Integer
square a b = (b * b) `mod` a
 
\end{code}}

To generate a prime of a given size we define the \cc{getPrime} function. \cc{getPrime n g} starts with a random number $r \approx 2^n$ and returns the next prime. Each number is tested 20 times using Miller-Rabin test before declaring it a prime. 

\begin{code}

getPrime :: (CryptoRandomGen g) => Int -> g -> (Integer,g)
getPrime n g = 
  let (m,g') = randomInteger (2^(n-1)) g
      m' = 2^(n-1) + m
  in findNextPrime m' g' 
                
findNextPrime :: (CryptoRandomGen g) =>  Integer -> g -> (Integer,g)
findNextPrime n g
  | (even n) = findNextPrime (n+1) g
  | r = (n,g')
  | otherwise = findNextPrime (n+2) g'
    where (r,g') = isPrime n 20 g
        
\end{code}
 
 Finally we define the \cc{getPrime'} function. \cc{getPrime' n l g} returns a prime $p \approx 2^n$ that satisfies the following properties:
\begin{itemize}
\item $l | p+1$
\item $p \equiv 11 \mod 12 $
\item $l^2 \not | p+1$
\end{itemize}

 \begin{code}
getPrime' :: (CryptoRandomGen g) => Int -> Integer -> g -> (Integer,g)
getPrime' n l g =
  let m = (div (2^(n-1)) l)
      m' = (l*(m+1))
      mod12 = (11 == ).( `mod`  12) 
      divl2 = (0 /= ) . ( `mod` (l^2))
      addL n g
        | mod12 (n-1), divl2 (n-1), r  = ((n-1),g')
        | otherwise = addL (n+l) g'
          where (r,g') = isPrime (n-1) 20 g
  in addL m' g
                      
\end{code}



