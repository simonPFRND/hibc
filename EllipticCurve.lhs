\subsection{EllipticCurve}
 


The \cc{EllipticCurve} module contains datatypes for elliptic curves and affine points as well as functions
for elliptic curve arithmetic.

\begin{code}

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, PatternGuards #-} 
-- |  The Elliptic Curve module contains datatypes for the representation of 
-- |  elliptic curves and elliptic curve points and functions for arithmetic 
-- |  operations over elliptic curves. 
module EllipticCurve( EC(..),
		      Aff(..),
                      padd,
                      pdbl,
                      neg,
                      pmul) where
			
import Arithmetic

\end{code}

Elliptic curves over fields with a characteristic $p > 3$ are represented by equation of the  form $ E : y^2 = x^3 + ax +b $. We define the \cc{EC} datatype to represent 
elliptic curves over \mb{F}{p}.

\begin{code}

-- | The EC datatype represents elliptic curves E: y^2 = x^3 + ax +b defined over a prime field F_p with p>3. 
-- | The curve E: y^2 = x^3 + ax + b is represented by EC p a b 
data EC = EC Integer Integer Integer

\end{code}

For example, \cc{EC p a b} represents the curve $E : y^2 = x^3 + ax +b$  defined over \mb{F}{p}. We will represent 
points on elliptic curves in affine coordinates, i.e. as pairs over a field \mb{F}{q}. We define the type constructor \cc{Aff} that takes a \cc{Field} value \cc{a} and produces the type \cc{Aff a}.

\begin{code}

-- | The @Aff@ typeconstructor represents affine points as a pair of @'Field'@ values. 
data Aff a  = A a a | InfA  
            deriving (Eq)

instance (Show a) => Show (Aff a) where
  show InfA = "inf"
  show (A ax ay) = "[" ++ (show  ax) ++ "," ++ (show ay) ++ "]"

\end{code}


\cc{Aff} offers two constructors. \cc{A} takes two \cc{Field} values and represents an affine point over that field and \cc{InfA} represents the point at infinity. We use Haskell's \cc{deriving} function to make \cc{Aff} an instance of \cc{Eq} so that we can check points for equaliy. Further, we declare \cc{Aff} an instance of show manually, to prettify the output in GHCi. We will also use this later for string based IO. \\

We can now use the methods of the \cc{Field} typeclass to implement arithmetic operation on elliptic curves.


 \subsubsection{Point Doubling}
 
 To double an affine point on an elliptic curve we use the equation for point doubling given in theorem \ref{group}. However, the equation is only well-defined for $A = (a_x,a_y)$ and $a_y \neq 0$. When $a_0 = 0$ then the tangent in $A$ is vertical. In that case doubling A results in the point at infinity. The \cc{pdbl} function needs an additional argument that represents the underlying elliptic curve.

\begin{code}
-- | @pdbl ec a@ doubles the point @a@ on the elliptic curve @ec@ -}
pdbl :: (Field a) => EC -> (Aff a) -> (Aff a)
pdbl (EC p ca _) (A ax ay)
  | ay == (zero) = InfA
  | otherwise = let u = div_p p (add_p p (mul'_p p 3 (mul_p p ax ax)) (lift p ca)) (mul'_p p 2 ay)
                    x' = sub_p p (mul_p p u u) (mul'_p p 2 ax) 
                    y' = sub_p p (mul_p p u (sub_p p ax x')) ay
                in A x' y'
pdbl _ _ = InfA 

\end{code}
 


 
 \subsubsection{Point Addition}
 

To implement addition of ellitpic curve points we can also use the formula given in theorem \ref{group}. Note that the equation holds only for two distinct points $A = (a_x,a_y),B = (b_x,b_y)$ with $a_x \neq b_x$. When $a_x = b_x$ then $A+B = \infty$. We further have to consider the cases where the points are equal and where one or both of them are the point at infinity.
 
\begin{code}
-- | @add ec a b@ add the two point @a@ and @b@ on the elliptic curve @ec@ 
padd :: (Field a) => EC -> (Aff a) -> (Aff a) -> (Aff a)
padd _ InfA a = a
padd _ a InfA = a
padd  c@(EC p _ _) a@(A ax ay) b@(A bx by)
        | a == b = pdbl c a 
	| ax == bx = InfA
	| otherwise = let u = div_p p (sub_p p by ay) (sub_p p bx ax)
			  x'' = sub_p p (mul_p p u u) (add_p p ax  bx) 
			  y'' = sub_p p (mul_p p u (sub_p p ax  x''))  ay
		      in A x'' y''	

\end{code}

Additionally, we define the function neg that computes the additional inverse of an elliptic curve point. Given an elliptic curve point $A = (a_x,a_y)$ it's inverse $-A$ is the point $-A = (a_x,-a_y)$.

\begin{code}
-- | @neg ec a@ computes the inverse of the point @a@ on the elliptic curve @ec@ 
neg :: (Field a) => EC -> (Aff a) -> (Aff a)
neg (EC p _ _) (A ax ay) = (A ax (sub_p p zero ay))
neg _ _ = InfA

\end{code}

\subsubsection{Point Multiplication}

Point multiplication is implement using a double-and-add method. In standard elliptic curve cryptographic systems point multiplication dominates the execution time. However, for the computation of the  Tate  pairing  point multiplication plays a minor part. 

\begin{code}

-- | @pmul ec n a@ computes the scalar product @na@ of an integer n and the point a on the elliptic curve @ec@
pmul :: (Field a) => EC -> Integer -> (Aff a) -> (Aff a)
pmul e n a = 
  let mul x n s
        | (n == 0) = s
        | (even n) = mul (pdbl e x) (n `div` 2)  s
        | otherwise = mul (pdbl e x) (n `div` 2) (padd e s x)
  in if (n < 0) then (neg e (mul a (negate n) InfA)) else (mul a n InfA)

\end{code}

Finally, we add a function that determines whether a point lies on a given curve or not. We do not directly need it for the Tate pairing computation, but it is very useful for debugging and testing.

\begin{code}

-- | @isOnCurve ec a@ checks whether the point @a@ lies on the elliptic curve @ec@.
isOnCurve :: (Field a) => EC -> (Aff a) -> Bool
isOnCurve (EC p ca cb) (A ax ay) = l == r
  where l = mul_p p ay ay
        r = add_p p (exp_p p ax 3) (add_p p (mul'_p p ca ax) (lift p cb))

\end{code}

\begin{exampleth}
We can use the \cc{EllipticCurve} in GHCi to perform the sample computations given in example \ref{exea}. 

\begin{example1}
*EllipticCurve> let ec = EC 29 4 20
*EllipticCurve> padd ec (A 2 6) (A 5 22)
[15,2]
*EllipticCurve> pdbl ec (A 27 2)
[20,26]
*EllipticCurve> pmul ec 3 (A 10 4)
[15,27]
*EllipticCurve> padd ec (A 0 7) (A 0 22)
inf
\end{example1}
\end{exampleth}

