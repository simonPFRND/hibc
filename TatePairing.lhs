\section{The Tate Pairing}

\subsection{Building a bilinear map}

The Arithmetic and the EllipticCurve Module provide us with the necessary functions to perfom finite field and elliptic curve arithmetic. Based on them we will now implement two algorithms for the computation of the Tate pairing. 

\begin{code}
{-# LANGUAGE PatternGuards #-} 
-- | The @TatePairing@ module contains implementations of the BKLS algorithm as well as Miller's 
-- | algorithm to compute the Tate pairing over elliptic curves.
module TatePairing (FunParam,
                    miller,
                    modTateMiller,
                    modTateBKLS,
		    modTateBKLSPre,
		    modTateBKLS') where

import Arithmetic
import EllipticCurve
import Data.Bits
\end{code}


Throughout the following, let E be an elliptic curve defined over a finite field \mb{F}{q}$. Let l be a prime that is coprime to $q$ with $l | \#E(\mb{F}{q}). Let $k$ be the embedding degree of E, i.e. the smallest integer k so that $l | q^k - 1$. The Tate pairing over E is a function
\begin{eqnarray}
 \langle , \rangle \ &:& E(\mb{F}{p^2})[l] \times E(\mb{F}{p^2}) \to \mb{F}{p^2}^* 
\end{eqnarray}

As showed in section \ref{tatecomp} we can compute the Tate pairing $\langle A,B \rangle$ for $A \in E[l]$ and $B \in E(\mb{F}{q^k})$ using Miller's algorithm. Miller's successively computes the Miller function $f_{A,m}$ by performing in each step a doubling operation
\begin{eqnarray*}
    f_{A,2m} & = & f_{A,m}^2 \frac{h_{mA,mA}}{h_{2mA}} \\
\end{eqnarray*}
and if necessary an addition operation.
\begin{eqnarray*}
   f_{A,m+1} & = & f_{A,m} \frac{h_{mA,A}}{h_{(m+1)A}} \\
\end{eqnarray*}

The functions $h_{A,B}$ and $h_{A}$ are defined as in section \ref{tatecomp}. We begin with defining the functions \cc{vertLine} and \cc{line}. \cc{vertLine} computes the function of a vertical line through a given point. \cc{line} computes the function of a line through two given points that do not lie on a vertical line.

\begin{code}

vertLine :: (Field a) => EC -> (Aff a) -> (Aff a) -> a
vertLine (EC p _ _) (A ax _) (A bx _) = sub_p p bx ax  

line :: (Field a) => EC -> (Aff a) -> (Aff a) -> (Aff a) -> a
line ec@(EC p _ _ ) a@(A ax ay) b@(A bx by) c@(A cx cy) 
  | a == b = fun (tangent ec a)          
  | otherwise = fun (slope ec a b)         
 where fun m = (add_p p (mul_p p m x') y')  
       x' = sub_p p cx ax
       y' = sub_p p ay cy
\end{code}

%We use partial evaluation to represent functions on elliptic curves. \cc{vertLine ec (A ax ay) (A bx by) } computes $h_A(B) = b_x -a_x$ over the elliptic curve given by \cc{ec}. \cc{line ec a b} either computes the tangent on the given curve in \cc{a} or the line running through \cc{a} and \cc{b}, depending on whether \cc{a} and \cc{b} are equal. \cc{vertLine} returns a function of the form $f_{A,B}(x,y) = m(x - a_x) + a_y - y$. The adequate slope $m$ is computed by the \cc{slope} and \cc{tangent} functions.

\begin{code}

slope ::(Field a) => EC -> (Aff a) -> (Aff a) -> a
slope e@(EC p _ _) (A ax ay) (A bx by) = 
  let dx = (sub_p p bx ax)
      dy = (sub_p p by ay)
  in div_p p dy dx

tangent :: (Field a) => EC -> (Aff a) -> a
tangent e@(EC p ca _) (A ax ay) =  
  let y = add_p p ay ay
      x = add_p p (mul'_p p 3 (mul_p p ax ax)) (lift p ca)
  in div_p p x y

\end{code}

The \cc{slope} function computes the slope  $m = \frac{b_x-a_x}{b_y-a_y}$ of the line $h_{A,B}$. Alike, \cc{tangent} computes the slope of the tangent $m = \frac{3x^2 + a}{2y}$ where a is the coefficient of the simplified Weierstrass equation. \\ 

Using the \cc{line} and \cc{vertLine} functions we can now implement Miller's algorithm. 

\begin{code}
-- | The @miller ec l a b c@ function uses Miller's algorithm to compute the ordinary Tate pairing of @a@  
--   and @b@ over ec. @ec@ represents the underlying elliptic curve. @l@ is the order of the point @a@. 
--   @a@,@b@,@c@ have to be of equal type. @c@ can be an arbitrary point. Note that computation 
--   might fail when @b@ or @c@ is linearly dependent of @a@. 
miller :: (Field a) => EC -> Integer -> (Aff a) -> (Aff a) -> (Aff a) -> a
miller ec@(EC p _ _) l a b c = 
  let rek m z n
        | n == 0 = mul_p p m' (eval (vertLine ec a))
        | testBit l n = rek  m'' z2' (n-1)
        | otherwise = rek m' z2 (n-1)
          where z2 = pdbl ec z
                z2' = padd ec z2 a
                m' = mul_p p (mul_p p m m) (div_p p fzz f2z)
                fzz = eval (line ec z z)
                f2z = eval (vertLine ec z2)
                m'' = mul_p p m' (div_p p fza faz)
                fza = eval (line ec z2 a)
                faz = eval (vertLine ec z2')
                eval f = div_p p (f (padd ec b c)) (f c)
      n = (floor (logBase 2 (fromIntegral l))) - 1
  in rek one a n
\end{code}

\cc{miller ec a b c} computes the Tate pairing $\langle A,B \rangle = \frac{f_A(B+C)}{f_A(C)}$ where $A,B,C$ are the elliptic curve points represented by \cc{a,b,c}. To implement the modified Tate pairing we simply exponentiate the result of Miller's algorithm by $\frac{q^k-1}{l}$.

\begin{code}
-- | @modTateMiller ec k l a b c@ uses @'miller'@ to compute the modified TatePairing e(@a@,@b@).
--   @k@ is the embedding degree of @a@ in @E@ and dertermines the exponent of the final powering. 
--   @l@ is the order of @a@. @c@ is an arbitrary point on @ec@.
--   Note that computation might fail if @b@ or @c@ is linearly dependent of @a@.
modTateMiller :: (Field a) => EC -> Integer -> Integer -> (Aff a) -> (Aff a) -> (Aff a) -> a
modTateMiller ec@(EC p _ _) k l a b c = exp_p p (miller ec l a b c) (div (p^k-1) l)
\end{code}

\begin{exampleth}

We can use our implementation of Miller's algorithm to compute the Tate pairing for the curve given in example \ref{extate}. 

\begin{example1}
*TatePairing> let ec = EC 31 0 11
*TatePairing> miller ec 5 (A 2 9) (A 3 10) (A 3 10)
2
*TatePairing> modTateMiller ec 1 5 (A 2 9) (A 3 10) (A 3 10)
2
\end{example1}
\end{exampleth}

However, we can not use the modified Tate pairing alone as a bilinear map since $E[l]$ is not a cyclic group of order l. For the curve $E_p$ we can build a suitable bilinear map using the endomorphism $\phi$. 
\begin{eqnarray}
 \phi & : & E(\mb{F}{p}) \to E(\mb{F}{p^2}) \\
      & & (a_x,a_y) \mapsto (-a_x,a_yi).
\end{eqnarray}

 $\phi$ maps  maps an elliptic curve point in $E_0(\mb{F}{p})$ to a point in $E_0(\mb{F}{p^2})\backslash E_0(\mb{F}{p})$. Such a function is called distortion map. Finally, we obtain the following bilinear map $\hat{e}$ from the group of points of order l to the roots of unity in \mb{F}{p^2}.   
\begin{eqnarray*}
\hat{e} &:& E(\mb{F}{p})[l] \times E(\mb{F}{p})[l] \to \mb{F}{p^2} \\
        & & \hat{e}(A,B) \mapsto e(A,\phi(B)) 
	\end{eqnarray*}

\subsubsection{BKLS algorithm}
 
The pairing evaluation is a computationally expensive operation due to the arithmetic over elliptic curves and extensions of finite fields. However, over certain curves the computation can be considerably simplified. The following optimizations were presented in \citep{} by Barreto, Kim, Lynn, Scott. \\

Let $E_p$ be the curve defined in \ref{impl} Fruther, let $l$ be a prime that is coprime to $p$ and devides the order of $E(\mb{F}{p})$. Note that $p-1$ divides $p^2 - 1$ and since $p-1$ is coprime to l $p-1$ also divides $(p^2-1)/2$. Therefor, each element of \mb{F}{p} in the result of the Tate pairing is mapped to 1 and can be ommited. \\
The modified Tate pairing $\hat{e}$ is defined as  $\hat{e} = (f_A(D_B))^{\frac{p^2-1}{l}}$ where $D_B$ is a divisor $D_B \sim B - \infty$. Let A be a point in $E(\mb{F}{p})$ and $C \notin \{\infty,A\}$ be a point on $E(\mb{F}{p})$. We can choose any function for $f_A$ that has a divisor equivalent to $n(A) - n(\infty)$. Let's consider the case that $f_A$ is a function with $(f_A) = n(A + C) - n(C) \sim (f_A)$. $f_A$ is a rational function over $\mathbb{F}_p^*$ and does not have a zero or pole at $\infty$, thus $f_A(\infty)$ is an element of $\mathbb{F}_p^*$. That means $f_A(\infty)$ is an irrelevant factor in definition of the Tate pairing $e = f_A(D_B)^{\frac{p^2-1}{l}} = (\frac{f_A(B)}{f_A(\infty)}^{\frac{p^2-1}{l}} = f_A(B)^{\frac{p^2-1}{l}}$. This is a very useful property since we can use it to reduce the function evaluations that are performed during the computation of the Tate pairng. \\

We built the bilinear map $\hat{e}$ using the distortion map $\phi$. Hence, when computing $\hat{e}(A,B)$ point $\phi(B)$ is of formm $\phi(B) = (b_x,b_y)$ with $b_x \in \mathbb{F}_p$. That means when we evaluate a vertical line $h_{nA} = x - x_0$ at $\phi(B)$ the result is an element in \mb{F}{p}, that is mapped to 1 by the final powering. Consequently, we can omit all the denominators that occur in the doubling and addition formula of Miller's algorithm. \\

The omptimized version of Miller's algorithm is known as \emph{BKLS algorithm}, named after Barreto, Kim, Lynn and Scott. Note that all functions $h_{mA,mA},h_{mA,A},h_{mA}$, that occur during the computatio,n are rational functions over \mb{F}{p}. Since vertical lines do not contribute to the result of the Tate pairing we only have to consider functions of the form $g_{m,A}(x,y) = m(x - a_x) + a_y - y$ for a point $A=(a_x,a_y) \in E(\mb{F}{p})$. We define the \cc{evaluate} function that given an elliptic curve E, the slope m and the two points $A,B \in E(\mb{F}{p})$ evaluates the function $g_{m,A}$ at $\phi(B)$.

\begin{code}

evaluate :: EC -> Integer -> (Aff Integer) -> (Aff Integer) -> Fp2
evaluate e@(EC p _ _) m (A ax ay) (A bx by) =
  let cx = sub_p p ay (mul_p p m (add_p p bx ax))
      cy = sub_p p 0 by
  in (cx,cy)


\end{code}

Beneath we give an implementation of the BKLS algorithm. The equation of the elliptic curve is hardcoded in the algorithm since the properties mentioned above do not hold for arbitrary curves. Note that the BKLS algorithm computes the modified Tate pairing, i.e. it can not be used to compute the ordinary Tate pairing.

\begin{code}
-- | @modTateBKLS p l a b@ computes the modified Tate pairing e(@a@,@b@) over the curve E : y^2 = x^3 + x 
--   defined over \mb{F}{p} with embedding degree k = 2. @l@ is the prime order of @a@ and has to satisfy 
--   @l@ | p^2 - 1.
modTateBKLS ::  Integer -> Integer -> (Aff Integer) -> (Aff Integer) -> Fp2    
modTateBKLS p l a b = 
  let rek m z n 
        | n == 0 = m'	
        | testBit (l) n = ((rek  $! m'') $! z2') $! (n-1)
        | otherwise = ((rek $! m') $! z2) $! (n-1)
          where z2 =  pdbl e z 
                z2' = padd e z2 a
                m' = mul_p p (mul_p p m m) fzz
                m'' = mul_p p m' fza
                fzz = evaluate e (tangent e z) z b
                fza = evaluate e (slope e z2 a) z2 b
      e = (EC p 1 0)
      n = (floor (logBase 2 (fromIntegral l))) - 1
      res = rek one a n
  in exp' p l res 
                  
\end{code}

The \cc{exp'} function is explained in the following section.

\subsubsection{Speeding up the final powering}

Exploiting properties of the characteristic of the underlying prime field \mb{F}{p} we can speed up the final exponentiation. The exponent of the final powering is $z = \frac{p^2-1}{l} = (p-1)\frac{p+1}{l}$. Let x be an element of $mathbb{F}_{p^2}$. First, we compute $y = x^\frac{p+1}{l} = u + iv$. Using the linearity of exponentiation by p we obtain $(u + iv)^{p-1} = (u + iv)^p/(u+iv) = (u^p + (iv)^p) / (u+iv)$. As $p \equiv 3 \text{mod} 4$ we have that $i^p = -i$. Thus $(u^p + (iv)^p)/(u+iv) = (u - iv) / (u + iv) = \frac{u^2 - v^2 - 2uvi}{u^2+v^2}$. 

\begin{code}
exp' ::  Integer -> Integer -> Fp2 -> Fp2
exp' p l x  = 
  let (u,v) = exp_p p x (div (p+1) l) 
      u2 = mul_p p u u
      v2 = mul_p p v v
      u2v2 = add_p p u2 v2
  in (div_p p (sub_p p u2 v2) u2v2, div_p p (sub_p p 0 (mul'_p p 2 (mul_p p u v))) u2v2)
                 
\end{code}


\subsubsection{Precomputations}

As the functions that occur during the computation of $\hat{e}(A,B)$ only depend on the point A, we can store their parameters and use them to speed up the following Tate Pairing evaluation $\hat{e}(A,C)$. Therefor, we modify the BKLS algorithm to return the result of the computation and a list containing the precomputed parameters:  

\begin{code}
type FunParam = (Integer, Integer, Aff Integer)
-- | The same algorithm as 'modTateBKLS' but also returns a list of precomputed parameters that can be used 
--   with the @'modTateBKLS\''@ function
modTateBKLSPre :: Integer -> Integer -> Aff Integer -> Aff Integer -> (Fp2,[FunParam])
modTateBKLSPre p l a b = 
  let rek m z n xs
        | n == 0 = (m',xxs)	
        | testBit (l) n = (((rek  $! m'') $! z2') $! (n-1)) xxs'
        | otherwise = (((rek $! m') $! z2) $! (n-1)) xxs
          where z2 =  pdbl e z 
                z2' = padd e z2 a
                m' = mul_p p (mul_p p m m) fzz
                mzz = (tangent e z)
                fzz = evaluate e mzz z b
                m'' = mul_p p m' fza
                mza = (slope e z2 a)
                fza =  evaluate e mza z2 b
                xxs = (2,mzz,z):xs
                xxs'=(1,mza,z2):xxs
      e = (EC p 1 0)
      n = (floor (logBase 2 (fromIntegral l))) - 1
      (res,xs) = rek one a n []
  in (exp' p l res,xs)

\end{code}

The list of parameters contains tuples $(z,m,a)$ for every function doubling or addition that was performed during the computation. $z$ is either 1 or 2 and indicates whether the current operation was a doubling or an addition. $m$ contains the slope of the current line and a is a point on that line. With given parameters we can implement the BKLS algorithm as a simple fold operation:

\begin{code}
-- | @modTateBKLS' p l b xs@ computes the modified Tate pairing e(@a@,@b@) using the precomputed parameters @xs@
--   by @'modTateBKLSPre'@.
modTateBKLS' :: Integer -> Integer -> Aff Integer -> [FunParam] -> Fp2
modTateBKLS' p l b xs = 
  let ec = (EC p 1 0)
      f (z,m,a) x = mul_p p (exp_p p x z) (evaluate ec m a b)
      e = foldr f one xs
  in exp' p l e

\end{code}

