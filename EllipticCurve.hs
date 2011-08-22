{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}


module EllipticCurve( EllipticCurve(..),
		      Point(..),
		      Affine(..),
		      pmul) where

import Arithmetic

{-|
The 'EllipticCurve' data type represents elliptic curves of the form E: y^2 = x^3 + ax + b over 
the finites field of characteristic p.
-}
data EllipticCurve = EC Integer Integer Integer -- ^ EC p a b

{-|
The 'Point' typeclass represents points on an Elliptic Curve E. 
-}
class (Field b, Eq b) => Point a b | a -> b where
	inf :: a -- ^ Returns the point at infinity on E
	getX :: a -> b -- ^ Returns the x-coordinate of the point in affine coordinates
	getY :: a -> b -- ^ Returns the y-coordinate of the point in affine coordinates
	eq :: a -> a -> Bool -- ^ Checks whether two points on E are equal
	pdbl :: EllipticCurve -> a -> a -- ^ Doubles a point on E
	padd :: EllipticCurve -> a -> a -> a -- ^ Computes the sum of two points on E
 	neg :: EllipticCurve -> a -> a -- ^ Computes the inverse of an element on E

{-|
The Affine data type represents a point on an elliptic curve in affine coordinates.
-}
data Affine a
	 = A a a -- ^ A x y represents the point (x,y) on an elliptic curve E
         | InfA  -- ^ Special constructor to represent the point at infinity


instance (Field a, Eq a) => Point (Affine a) a  where
	inf = InfA
	getX InfA = zero
	getX (A ax ay) = ax
	getY InfA = undefined
	getY (A ax ay) = ay
	eq InfA InfA = True
	eq (A ax ay) (A bx by) = (ax == bx) && (ay == by)
	eq _ _ = False
	pdbl _ InfA = InfA
	pdbl (EC p ca cb) (A ax ay) 
		| ay == zero = InfA
		| otherwise = let u = div_p p (add_p p (mul'_p p 3 (mul_p p ax ax)) (lift ca)) (mul'_p p 2 ay)
		    		  x' = sub_p p (mul_p p u u) (mul'_p p 2 ax) 
		                  y' = sub_p p (mul_p p u (sub_p p ax x')) ay
			      in A x' y'
	padd _ InfA a = a
	padd _ a InfA = a
	padd  c@(EC p _ _) a@(A ax ay) b@(A bx by)
		| eq a b = pdbl c a 
		| ax == bx = InfA
		| otherwise = let u = div_p p (sub_p p by ay) (sub_p p bx ax)
				  x'' = sub_p p (mul_p p u u) (add_p p ax  bx) 
				  y'' = sub_p p (mul_p p u (sub_p p ax  x''))  ay
			      in A x'' y''	
	neg (EC p _ _) (A x y) = A x (sub_p p (lift p) y)

pmul :: (Point a b) => EllipticCurve -> Integer -> a -> a
pmul e n a = let mul x n s
		        | (n == 0) = s
	                | (even n) = ((mul $! (pdbl e x)) $! (n `div` 2)) $! s
			| otherwise = ((mul $! (pdbl e x)) $! (n `div` 2)) $! (padd e s x)
      	     in if (n < 0) then (neg e (mul a (negate n) inf)) else (mul a n inf)

