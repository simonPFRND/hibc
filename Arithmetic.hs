{-| 
The 'Arithmetic'-module provides functionality for finite field arithmetic. 
-}

module Arithmetic (Field(..),
                   F_p2(..),
                   fp2) where

{-|
 The 'Field' class provides a common interface for elements of a finite field K.
 We represent K as an extension fields over the field of intergers modulo a prime p.
 -}
class Field a where
-- | The 'zero' function returns the zero-element in K
        zero :: a
-- | The 'one' function returns the one-element in K 
        one :: a
-- | Embeds an Integer value in K
        lift :: Integer -> a
-- | Addition in K
        add_p :: Integer -- ^ the characteristic of K 
		-> a     -- ^ a in K
		-> a     -- ^ b in K
                -> a     -- ^ a+b in K
-- | Subtraction in K
        sub_p :: Integer -- ^ the characteristic of K
		-> a     -- ^ a in K
		-> a     -- ^ b in K
                -> a     -- ^ a+b in K
-- | Multiplication in K
        mul_p :: Integer -- ^ the characteristic of K
		-> a     -- ^ a in K
		-> a     -- ^ b in K
                -> a     -- ^ a+b in K
-- | Repeated addition in K
        mul'_p :: Integer  -- ^ the characteristic of K
		-> Integer -- ^ a positive integer n
                -> a       -- ^ a in K 
                -> a       -- ^ a+...+a in K
-- |  Division in K 
        div_p :: Integer -- ^ the characteristic of K 
                -> a     -- ^ a in K 
                -> a     -- ^ b in K 
                -> a     -- ^ a*b^(-1) in K
-- | Repeated multiplication in K
        exp_p :: Integer   -- ^ the characteristic of K 
                -> a       -- ^ a in K  
                -> Integer -- ^ an integer n
                -> a       -- ^ a^n in K


instance Field Integer where
        zero = 0
        one = 1
        lift = id
        add_p p x y = mod (x+y) p
        sub_p p x y = mod (x-y) p
        mul_p p x y = mod (x*y) p
        mul'_p = mul_p
        div_p p x y = let (_,y',_) = extendedEukl y p
                      in mod (x*y') p
        exp_p p x n = let ex x n z 
		              | n == 0 = mod z p
		              | even n = ((ex $! (mod (x*x) p)) $! (n `div` 2)) $! z
		              | otherwise = ((ex $! (mod (x*x) p)) $! (n `div` 2)) $! (x*z)
	              in ex x n 1
{-|
The 'F_p2' data type represents elements of the Field F_p^2 as ordered pairs over F_p. 
-}
data F_p2 = F_p2 Integer Integer
        deriving (Eq,Show)

instance Field F_p2 where
        zero = (F_p2 0 0)
        one = (F_p2 1 0)
        lift x = (F_p2 x 0)
        add_p p (F_p2 ax ay) (F_p2 bx by) = F_p2 (mod (ax+bx) p) (mod (ay + by) p)
        sub_p p (F_p2 ax ay) (F_p2 bx by) = F_p2 (mod (ax-bx) p) (mod (ay - by) p)
        mul_p p (F_p2 ax ay) (F_p2 bx by) = F_p2 (mod (ax*bx-ay*by) p) (mod (ax*by+ay*bx) p)
        mul'_p p a (F_p2 bx by) = F_p2 (mod (a*bx) p) (mod (a*by) p)
        div_p p (F_p2 ax ay) (F_p2 bx by) = let (_,z,_) = extendedEukl (bx*bx + by*by) p
                                  in F_p2 (mod ((ax*bx + ay*by)*z) p) (mod ((ay*bx-by*ax)*z) p)
        exp_p p a n = let square (F_p2 x y) = F_p2 (mod (x*x -y*y) p) (mod (2*x*y) p)
		          exp a 0 z = z
                          exp a n z 
                               | (even n) = ((exp $! (square a)) $! (div n 2))  z   
                               | otherwise = ((exp $! (square a)) $! (div n 2)) $! (mul_p p z a)
                      in exp a (mod n (p^2-1)) one


fp2 :: Integer -> Integer -> F_p2
fp2 x y = F_p2 x y

-- | recursive implementation of the extended Euclidean algorithm.
extendedEukl :: Integer -> Integer -> (Integer,Integer,Integer)
extendedEukl x 0 = (x,1,0)
extendedEukl x y = let (d,s,t) = extendedEukl y (mod x y)
		   in (d,t,s-(div x y)*t)
