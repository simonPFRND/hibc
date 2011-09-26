%include polycode.fmt 
The Arithmetic module contains the basic arithmetic operations for our cryptosystem. Those are the field operation of the field \mb{F}{p} and its quadratic extension \mb{F}{p^2}. 

\ignore{
\begin{code}
{-# LANGUAGE FlexibleInstances#-}
-- | Provides an interface for arithmetic in finite fields as well as 
-- | implementations for the prime field F_p and F_p^2 with p = 3 mod 4.
module Arithmetic (Field(..),
                   Fp2) where

\end{code}
 }
 We define the \cc{Field} that provides a generic interface for arithmetic in finite fields \mb{F}{q} with characteristic p. Note that most function require a third parameter  of type \cc{Integer} that contains the characteristic $p$ of the underlying field. 

\begin{code}

-- |  The @Field@ class provides a generic interface for arithmetic 
-- |  in a finite field F_q with characteristic p m.
class (Eq a) => Field a where
  -- | the neutral element of addition  
  zero :: a
  -- | the neutral element of multiplication  
  one :: a 
  -- | @add_p p a b@ computes the sum of two field elements @a@,@b@    
  add_p :: Integer -> a -> a -> a 
  -- | @sub_p p a b@ computes the difference of two field elements @a@,@b@
  sub_p :: Integer -> a -> a -> a
  -- | @mul_p p a b@ computes the product of two field elements @a@,@b@ 
  mul_p :: Integer -> a -> a -> a 
  -- | @div_p p a b@ computes the quotient of two field elements @a@,@b@
  div_p :: Integer -> a -> a -> a
  -- | @mul'_p p n a@ computes the scalar product of @n@ and a field element @a@ 
  mul'_p :: Integer -> Integer -> a -> a
  -- | @exp_p p n a@                                                           
  exp_p :: Integer -> a -> Integer -> a 
  -- | @lift p a@ returns the corresponding field element in the extension field F_q of F_p   
  lift :: Integer -> Integer -> a 

\end{code}

The \cc{zero} function returns the identity element in the additive group of \mb{F}{q}. Alike, \cc{one} returns the
identity element of the multiplicative group of \mb{F}{q}. The basic field operations are implemented by \cc{add_p} and \cc{mul_p}. The functions \cc{sub_p} and \cc{div_p} compute their inversions, subtraction and division. 
 To make writing complex equations  more confortable the interface contains the additional functions \cc{mul'\_p},\cc{exp_p} and \cc{lift}.  \cc{mul'\_p p n a} computes the scalar product of $n \in \mb{F}{q}$ . Similarily, \cc{exp\_p} computes the nth power of an element $a \in \mb{F}{q}$.  The function \cc{lift} maps an \cc{Integer} to the corresponding element of \mb{F}{q}.

 \subsubsection{The field \mb{F}{p}}

We represent the field \mb{F}{p} as the field of integers modulo a prime p. Haskell's \cc{Integer} type is very comfortable for our purposes since it can be used to represent numbers of arbitrary size. To compute the multiplicative inverse of an element of the multiplicative group of \mb{F}{p} we use the extended Euklidean algorithm. Given two integers a and b it computes their greatest common divisor $\gcd(a,b)$ and integers
x and y so that $ax + by = \gcd(a,b)$. 

\begin{code}
extendedEukl :: Integer -> Integer -> (Integer,Integer,Integer)
extendedEukl x 0 = (x,1,0)
extendedEukl x y = let (d,s,t) = extendedEukl y (mod x y)
		   in (d,t,s-(div x y)*t)
\end{code}

Using this, we declare the \cc{Integer} datatype an instace of the \cc{Field} typeclass: 

\begin{code}

-- |  Implementation of arithmetic in the field F_p for a prime p using Haskells 
-- |  Integer datatype using addition/multiplication modulo p and the extended Euklidean algorithm.
instance Field Integer where
  zero = 0 
  one = 1
  add_p p a b = mod (a+b) p 
  sub_p p a b = mod (a-b) p
  mul_p p a b = mod (a*b) p
  div_p p a b = let (_,y,_) = extendedEukl b p
                in mod (a*y) p
  mul'_p = mul_p
  exp_p p a n = 
    let ex x n z 
          | n == 0 = mod z p
          | even n = ex (mod (x*x) p) (n `div` 2)  z
          | otherwise = ex (mod (x*x) p) (n `div` 2) (x*z)
    in ex a n 1
  lift p a = mod a p
\end{code}

The implementation of \cc{add_p},\cc{sub_p},\cc{mul_p} and \cc{sub_p} is trivial. To compute the divide the quotient of two field element $a$ and $b$ we use the extended Euklidean algorithm to compute $b^{-1}$ and return $ab^-1 \mod p$. For exponentiation in \mb{F}{p} we use a square and multiply algorithm.

 \subsubsection{The field \mb{F}{p^2}}

The field \mb{F}{p^2} is the quadratic extension field of \mb{F}{p}. We can construct \mb{F}{p^2} from \mb{F}{p} by adjoining an element i which is the square root of an element in \mb{F}{p}. We can think of the resulting Field as a vector space over
  \mb{F}{p} with basis $b = \{1,i\}$. The resulting vector space contains $p^2$ elements. Of course, this presupposes that $i$ and $1$ are linearly independent, i.e. that $i$ is not an element of \mb{F}{p}.  The finite field \mb{F}{p} for $p \equiv 3 \mod 4$ does not contain a square root of -1. So we can represent \mb{F}{p^2} as a vector space over \mb{F}{p} with basis $\{1,i=\sqrt{-1}\}$. We represent its elements as ordered pairs over \mb{F}{p}:
\begin{eqnarray*}
 a & = & (a_x,a_y)
\end{eqnarray*}
Each element of \mb{F}{p^2} can also be represented as a linear combination of 1 and i:
  \begin{eqnarray*}
  a & = & a_x + a_y i
    \end{eqnarray*}
    We can use this to derive formulas for the arithmetic operations in \mb{F}{p^2} in terms of arithmetic operations in \mb{F}{p}.
\begin{eqnarray*}
a+b & = & (a_x+b_x,a_y+b_y) \\
a-b & = & (a_x-b_y,a-a_y) \\
ab & = & (a_xb_x-a_yb_y,a_xb_y+a_yb_x) \\
a/b & = & (a_x^2+a_y^2)^{-1}(a_xb_x+a_yb_y,a_yb_x-a_xb_y) \\
\end{eqnarray*}

We represent elements of \mb{F}{p^2} as a pair of \cc{Integers}
\begin{code}

-- |  The @Fp2@ datatype represents element the field F_p^2 for p = 3 mod 4. 
-- |  F_p^2 is constructed by adjoining i with  i^2 = -1. @(a,b)@ represents 
-- |  the element a + bi.          -}
type Fp2 = (Integer,Integer) 

\end{code}
  
  Standard Haskell allows only instance declarations of the form \cc{(T a1 ... an)} where \cc{(a1,...,an)} are type variables. To make \cc{Fp2} an instance of Field we use the FlexibleInstances language extension.

\begin{code}

instance Field (Integer,Integer) where
  zero = (0,0)
  one = (1,0)
  add_p p (ax,ay) (bx,by) = ((mod (ax+bx) p),(mod (ay + by) p))
  sub_p p (ax,ay) (bx,by) = ((mod (ax-bx) p),(mod (ay - by) p))
  mul_p p (ax,ay) (bx,by) = ((mod (ax*bx-ay*by) p),(mod (ax*by+ay*bx) p))
  div_p p (ax,ay) (bx,by) = let (_,z,_) = extendedEukl (bx*bx + by*by) p
		                cx = mod ((ax*bx+ay*by)*z) p
                                cy = mod ((ay*bx-ax*by)*z) p
                            in (cx, cy)
  lift p x = (mod x p,0)
  mul'_p p a (bx,by) = ((mod (a*bx) p),(mod (a*by) p))
  exp_p p a n = 
    let square (x,y) = ((mod (x*x -y*y) p),(mod (2*x*y) p))
        exp a 0 z = z
        exp a n z 
          | (even n) = ((exp $! (square a)) $! (div n 2)) $! z   
          | otherwise = ((exp $! (square a)) $! (div n 2)) $! (mul_p p z a)
    in exp a n one
\end{code}



