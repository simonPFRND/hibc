

\section{Hashfunctions}
 The \cc{Hash} module contains implementations of the hashfunction s $h_1,\ldots,h_5$ as defined in section \ref{ibc}. \\ 
Both, the Boneh-Franklin and the Hess scheme, were proven secure in the random oracle model. That means that we our system is only secure when our implementations of $h_1,\ldots,h_5$ statisfy the properties of a random oracle. A formal approach to the problem of replacing a random oracle by a concrete hashfunction can be found in \ref{ind}. Maurer, Renner and Holenstein introduce the notion of indifferentiability of two systems that can be used to prove the security of practical cryptosystems. However, in praxis random oracles are often replaced by cryptographic hashfunctions. Such a hashfunction should at least satisfy the following properties:

\begin{description}

\item[Preimage resistance:] It should be difficult to compute $x$ given $y = f(x)$
\item[Second-preimage resistance:] It should be difficult to compute $x'$ with $f(x') = y$ given $x$ with $f(x) = y$
\item[Collision resistance:] Is should be difficult to find $x$ and $x'$ with $f(x) = f(x')$
\end{description}
where $f : A \mapsto B$ is a hashfunction and $x,x' \in A$ and $y \in B$. \\

However, the implementations given beneath do \textbf{not} satisfy those properties, they are intened for prototypical use only.
\begin{code}
{-# LANGUAGE FlexibleContexts #-} 

module Hash (h1,
             h2,
             h3,
             h4,
             h5) where

\end{code}

We use the cryptographic hashfunction SHA256 and SHA384 to implement $h_1 \ldots h_5$. The SHA package provides pure implementations of SHA256 and SHA384 in the \cc{Data.Digest.Pure.SHA} module.


\begin{code}

import GHC.Int
import Arithmetic
import EllipticCurve
import Data.Binary
import qualified Data.Digest.Pure.SHA as H
import qualified Data.ByteString.Lazy as B


sha256' :: B.ByteString -> B.ByteString
sha256' = H.bytestringDigest .  H.sha256

sha384' :: B.ByteString -> B.ByteString
sha384' = H.bytestringDigest . H.sha384

\end{code}


 
\subsection{Indifferntial Hashing onto Elliptic Curve}

In the conrete context of an IBC system based on pairings on elliptic curves, the function $h_1$ maps an identification string to a point in a subgroup of an elliptic Curve E. In \citep{Bfibe}, Boneh and Franklin use a particular curve E, which gives rise to a one-to-one mapping from the field $\mathbb{F}_p$ to the points on the curve $E(\mathbb{F}_p)$.  Due to the lack of such a function for $E_p$, we will uses Icart's function to hash onto elliptic curves. Given an elliptic curve $E: y^2 = x^3 + ax +b$ defined over $\mb{F}{p}$ where $p = 2 \mod 3$,  Icart's function $f_{a,b}$ maps a value $u \in F_{p^n}$ to a point $A = (a_x,a_y)$ in $E(\mathbb{F}_{p^n}$. : 

\begin{eqnarray}
f_{a,b} & : & \mathbb{F}_{p^n} \to E_{a,b}(\mathbb{F}_{p^n}) \\
&& u \mapsto (a_x,a_y)
\end{eqnarray}

where

\begin{eqnarray}
a_x &=& (v^2-b-\frac{u^6}{27})^{\frac{1}{3}}+\frac{u^2}{3} \\
a_y &=& ux + v \\
v &=& \frac{3a-u^4}{6u}
\end{eqnarray}
and $f_{a,b}(0) = \infty$. The implementation of Icart's function is straight forward:

\begin{code}

icart :: (Field a)  => EC -> a -> (Aff a)
icart (EC p ca cb) n = A x y
  where u = sub_p p (mul_p p v v) (add_p p (lift p cb) (div_p p (exp_p p n 6) (lift p 27)))
        v = div_p p (sub_p p (mul'_p p 3 (lift p ca)) (exp_p p n 4)) (mul'_p p 6 n)
        y = add_p p (mul_p p n x)  v 
        x = add_p p x'  (div_p p (mul_p p n n) (lift p 3)) 
        x' = exp_p p u (div (2*p-1) 3)
 
\end{code}

As presented in \citep{indIc} we can use Icart's function to build an indifferentiable hash function onto an elliptic curve $E : y^2 = x^3 + ax + b$ defined over a field \mb{F}{p^r} where $r \equiv 2 \mod 3$. Let $g_0,g_1$ be two hashfunctions that hash strings into the finite field $\mathbb{F}_{p^r}$. The function $h(m) = f_{a,b}(g_0(m)) + f_{a,b}(g_1(m))$ that hashes a string into $E(\mb{F}{p^k})$ is indifferentiable from a random oracle. 

To build a hashfunction that hashes into an integer range we use a construction that can be found in the IBC standard by Boyen and Martin \citep{rfc}. \cc{hashToRange} takes a conventional hashfunction $h: \{0,1\}^* \to \{0,1\}^n$ as input and uses it to hash a bytestring into an integer range. hashToRange is provably as secure as the underlying hash function $h$ \citep{rfc}. However, this does not hold for arbitrary ranges. Therefor, the use of this function will have to be revised.

\begin{code}

hashToRange :: (B.ByteString -> B.ByteString) -> Int64 -> Integer -> B.ByteString -> Integer
hashToRange hash hashLen n bs  = 
  let h1 = hash(B.append (B.replicate hashLen 0) bs)
      a1 = decodeInteger h1 
      h2 = hash(B.append h1 bs)
      a2 = decodeInteger h2
      v = 256^hashLen*a1 + a2
  in mod v n
     
hashToRange256 :: Integer -> B.ByteString -> Integer
hashToRange256 = hashToRange sha256' 32
     
hashToRange384 :: Integer -> B.ByteString -> Integer
hashToRange384 = hashToRange sha256' 32
     
     
\end{code}

Further we define a function decodeInteger that takes a bytestring an decodes it as a big-endian unsigned integer and returns its value.

\begin{code}

decodeInteger :: B.ByteString -> Integer
decodeInteger b =
  let f x y = x*256 + (fromIntegral y)
  in B.foldl f 0 b

\end{code}

Icart's function does not necessarily return a point A of order l. To obtain a point of order l, we multiply the point with $(p+1)/l$. Given l is prime, the result is either the point at infinity or a point of order l on the curve. If the hashvalue of a string is not of order l we append a newline character to the identification string and hash it again onto the curve. Consequently, we have to forbid the newline characters in identification strings to avoid collisions.  

\begin{code}

h1 :: EC -> Integer -> String -> (Aff Integer)
h1 ec@(EC p _ _) l id =
  let p1 = icart ec (hashToRange256 p (encode id))
      p2 = icart ec (hashToRange384 p (encode id))
      p3 = padd ec p1 p2
      p3' = pmul ec  (div (p+1) l) p3
  in if (p3' == InfA) 
       then (h1 ec l (s ++ "\n")) 
       else  p3'
             
\end{code}
 \cc{h1} implements the method presented in \citep{InfIc} for indifferentiable hashing into elliptic curves. We build two hashfunctions into an integer range using \cc{hashToRange} based on SHA256 and SHA384. \cc{h1 ec l id} hashes the \cc{String} \cc{id} onto an elliptic curve. The hashvalue is a point of order l in $E(\mb{F}{p})$ where is is given by \cc{ec}. 


\subsection{$h_2$}

The hashfunction $h_2$ hashes an element of the codomain of the pairing function into the message space. For $E_p$ the codomain of the Tate pairing is a subset of $F_{p^2}^*$. We define the canonical representation of an element of $\mb{F}{p^2}$: Given $a=(a_x,a_y) \in \mb{F}{p^2}$, the canonical representation of $a$ is the concatenation of the two n-byte bytestring representing $a_x$ and $a_y$ as unsigned big-endian integers. $n$ is the smallest number of bytes needed to encode $p$. The canonical representation is necessary to avoid ambiguous encodings of elements of \mb{F}{p^2}. \\
\cc{encodeInteger p a} encodes the integer value as an unsigned big-endian integer. The result is a bytestring of length $\lceil \log_{256}(p) \lceil$.

\begin{code}

encodeInteger :: Integer -> Integer -> B.ByteString
encodeInteger p x = 
  let rek 1 = B.cons (fromIntegral x) B.empty 
      rek n = B.cons (fromIntegral (div x (256^(n-1)))) (rek (n-1))
      n = ceiling (logBase 256 (fromIntegral p))
  in rek n

\end{code}
 
\cc{h2 p (ax,ay)} uses SHA256 to compute the hashvalue of an \cc{Fp2} value \cc{(ax,ay)} in canonical representation.

\begin{code}

h2 :: Integer -> Fp2 -> B.ByteString
h2 p (ax,ay) = 
  let bs1 = encodeInteger p ax
      bs2 = encodeInteger p ay
  in sha256'(B.append bs1 bs2)

\end{code}


 
\subsection{$h_3$}

The hashfunction $h_3$ hashes two elements of the message space into the range $[1,l-1]$. Its implementation \cc{h3} uses the \cc{hashToRange} function to hash the two input bytestrings into the desired range.  

\begin{code}
     
h3 :: Integer -> B.ByteString ->  B.ByteString -> Integer
h3 l bs1 bs2 = (hashToRange256 (l-1) (B.append bs1 bs2)) + 1

\end{code}

\subsection{$h_4$}

The message space of our encryption scheme are 32-byte strings. Hence, we can use SHA256 to realize $h_4$.

\begin{code}

h4 :: B.ByteString -> B.ByteString
h4 = sha256'

\end{code}

\subsection{$h_5$} 

The implementation of $h_5$ is similar to $h_3$ and $h_2$. $h_5$ hashes an arbitrary-length message $m$ and an element $a$ of \mb{F}{p^2} into an integer range. \cc{h5} uses \cc{hashToRange} to map the concatenation of the canonical representation of a and the message $m$ to the desired range $[1,l-1]$.  


\begin{code}

h5 :: Integer -> Integer ->  B.ByteString -> Fp2 -> Integer
h5 p l bs (x,y) =
  let bs1 = encodeInteger p x
      bs2 = encodeInteger p y
  in  (hashToRange256 (l-1) (B.concat  [bs1,bs2,bs])) + 1 
      

                      
\end{code}
