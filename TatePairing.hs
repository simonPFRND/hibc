{-# Language FlexibleContexts #-}

module TatePairing (bkls,
		    miller,
		    bklsPre,
		    bkls') where

import Arithmetic
import EllipticCurve
import Data.Bits

-- computes the slope of the line through two points on an elliptic curve.
slope ::(Point a b) => EllipticCurve -> a -> a -> b
slope (EC p _ _) a b = div_p p (sub_p p (getY b) (getY a)) (sub_p p (getX b) (getX a))

-- computes the tangent on an point on an elliptic curve
tangent :: (Point a b) => EllipticCurve -> a -> b
tangent (EC p ca _) a =  div_p p (add_p p (mul'_p p 3 (mul_p p (getX a) (getX a))) (lift ca)) (mul'_p p 2 (getY a))
  
-- evaluation function for the bkls algorithm
evaluate :: (Point a Integer) => Integer -> Integer -> a -> a -> F_p2
evaluate p m a b = let ax = getX a
		       ay = getY a
		       bx = getX b
		       by = getY b 
		   in fp2 (sub_p p ay (mul_p p m (add_p p bx ax))) (sub_p p p by)

{- | 
The 'bkls'-function implements the bkls algorithm. It provides an optimized computation of the Tate pairing
on elliptic curves E: y^2 = x^3 + x. The computed value will only be correct if the parameters satisfy the following properties: p = 3 mod 4, a is a l-torsion point on E, b is a point on E. We will refer to parameters that satisfy those properties as valid parameters. 
-}
bkls :: (Point a Integer) => Integer -- ^ p
                          -> Integer -- ^ l
                          -> a       -- ^ a
                          -> a       -- ^ b
                          -> F_p2    
bkls p l a b = let rek m z n 
                     | n < 0 = m	
   		     | testBit (l) n = ((rek  $! m'') $! z2') $! (n-1)
		     | otherwise = ((rek $! m') $! z2) $! (n-1)
		             where z2 =  pdbl c z 
				   z2' = padd c z2 a
			           m' = mul_p p (mul_p p m m) fzz
				   fzz 
				   	| (getY z) == 0 = one
					| otherwise = evaluate p (tangent c z) z b
				   m'' = mul_p p m' fza
				   fza 
					| (getX z2) == (getX a) = one
					| otherwise = evaluate p (slope c z2 a) z2 b
		   c = (EC p 1 0)
                   n = (floor (logBase 2 (fromIntegral l))) - 1
                   res = rek one a n
	       in exp_p p res (div (p^2-1) l)

{- |
The 'bklsPre'-function is similar to the 'bkls' function but the result is a pair that contains the
value of the reduced tate pairing e(a,b) and precomputation parameters for fast computation of e(a,c)
for an arbitrary point c on the elliptic curve E: y^2  = x^3 + x. The 'bklsPre'-function is applied to valid parameters, it will produce a correct Tate pairing value as well as valid precomputation parameters.
-}
bklsPre :: (Point a Integer) => Integer -- ^ p
                             -> Integer -- ^ l 
                             -> a       -- ^ a
                             -> a       -- ^ b
                             -> (F_p2,[(Integer,Integer,a)])
bklsPre p l a b = let rek m z n xs
                      	| n < 0 = (m,xs)	
   		      	| testBit (l) n = (((rek  $! m'') $! z2') $! (n-1)) xxs'
		      	| otherwise = (((rek $! m') $! z2) $! (n-1)) xxs
		             where z2 =  pdbl c z 
				   z2' = padd c z2 a
			           m' = mul_p p (mul_p p m m) fzz
				   mzz = (tangent c z)
				   fzz
				   	| (getY z) == 0 = one
					| otherwise = evaluate p mzz z b
				   m'' = mul_p p m' fza
				   mza = (slope c z2 a)
				   fza 
					| (getX z2) == (getX a) = one
					| otherwise = evaluate p mza z2 b
				   xxs = if ((getY z) == 0) then xs else (2,mzz,z):xs
			           xxs' = if ((getX z2) == (getX a)) then xxs else (1,mza,z2):xxs
		      c = (EC p 1 0)
                      n = (floor (logBase 2 (fromIntegral l))) - 1
                      (res,xs) = rek one a n []
	          in (exp_p p res (div (p^2-1) l),xs)

{-|
Uses valid precomputed parameters for fast computation of the Tate pairing. The computed value can only be correct
if p and l are identical to the values used to precompute the parameters.
-}
bkls' :: (Point a Integer) => Integer               -- ^ p 
                           -> Integer               -- ^ l
                           -> a                     -- ^ c
                           -> [(Integer,Integer,a)] -- the precomputed parameters 
                           -> F_p2
bkls' p l c xs = let cof = div (p^2 - 1) l 
                 in (exp_p p (foldr (\(e,s,z) m -> mul_p p (exp_p p m e) (evaluate p s z c)) one xs) cof)

{-
 Evaluates the line through a and b at c. Does not work for a and b both the point at infinity. If a and b are equal the evaluated function is the tangent on a. If one of a and b ist the point at infinity, then the evaluated line is the vertival line through the point that is not the point at infinity.
-}
fun :: (Point a b) => EllipticCurve -> a -> a -> a -> b
fun e@(EC p _ _) a b c 
	| (eq inf a) && (eq inf b) = (lift 1)
	| eq inf b = vert a c
	| eq inf a = vert b c
	| eq a b = if ((getY a) == zero) then vert a c else eval (tangent e a) a c
	| (getX a) == (getX b) = vert a c
	| otherwise = eval (slope e a b) a c
	where vert a b = sub_p p (getX b) (getX a)
	      eval m a b = add_p p (mul_p p m (sub_p p (getX b) (getX a))) (sub_p p (getY a) (getY b))



{-| 
Generic implementation of Miller's algorithm. Computes the reduced Tate pairing on the curve e defined over a field of characteristic p. The result is a root of unity in the underlying field of e. For a successful computation of the Tate pairing the parameters have to satisfy the following properties: a is a l-torsion point on e, p is a prime, b and c are linearily independent from a. The choice of c does not influence the result.
|-}
miller :: (Point a b) => EllipticCurve -- ^ e
                      -> Integer       -- ^ l
                      -> a             -- ^ a
                      -> a             -- ^ b 
                      -> a             -- ^ c
                      -> b
miller e@(EC p _ _) l a b c = let rek m z n
			                | n < 0 = m
                                        | testBit l n = ((rek  $! m'') $! z2') $! (n-1)
                                        | otherwise = ((rek  $! m') $! z2) $! (n-1)
                                        where z2 = pdbl e z
                                              z2' = padd e z2 a
                                              m' = mul_p p (mul_p p m m) (div_p p fzz f2z)
                                              fzz = eval (fun e z z)
                                              f2z = eval (fun e z2 inf)
                                              m'' = mul_p p m' (div_p p fza faz)
					      fza = eval (fun e z2 a)
					      faz = eval (fun e z2' inf)
                                              eval f = div_p p (f (padd e b c)) (f c)
                                  m = (floor (logBase 2 (fromIntegral l))) - 1
			          res = rek one a m
                              in exp_p p res (div (p^2-1) l)
                                        


