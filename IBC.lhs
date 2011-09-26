The IBC module contains the actual implementations of the algorithms presented in chapter \ref{}.

\begin{code}

module IBC (Aff(..),
            Params(..),
            Cipher(..),
            Signature(..),
            setup,
            extract,
            encrypt,
            decrypt,
            encryptBlock,
            sign,
            verify) where 

import EllipticCurve
import Arithmetic
import TatePairing
import Random
import Hash
import Control.Monad
import Crypto.Random
import Data.Binary
import Data.Bits
import qualified Data.ByteString.Lazy as B
import Data.Numbers.Primes
import System.Random




\end{code}


\begin{code}
ep :: Integer -> EC
ep p = EC p 1 0

type G1 = Aff Integer
type G2 = Fp2

e :: Params -> G1 -> G1 -> G2
e (Params p l _ _) = modTateBKLS p l

\end{code}
\section{Parameter Generation}

The system parameters specify a concrete IBC system. A set of system parameters is the tuple $params = (p,l,A,B)$ where $p,l,A,B$ are defined as follows:  

\begin{itemize}

\item $p$ is the characteristic of \mb{F}{p} 
\item $l$ is the prime order of the l-torsion group 
\item $A$ is a point $A \in E(\mb{F}{p})[l]$
\item $B=k_mA$ is the product of $A$ and the master key $k_m$

\end{itemize}

The \cc{Params} datatype represent a set of system parameters.
\begin{code}

data Params  = Params Integer Integer (Aff Integer) (Aff Integer)
\end{code}

A valid set of parameters for the IBC system is generated as follows. At first we generat a random prime l. Based on that we find another prime p with $l | p+1,p \equiv 11 \text{mod} 12$ and $l^2 \nmid p+1$. Then we choose a random point A of order l on the elliptic curve and a random integer $k_m$ as master key. We compute $B = lA$ and issue the system parameters (p,l,A,B). \\

To choose a generator $A$ on $E$ we generate a random string and hash it into the curve using the \cc{h1} function of the Hash module. As l is prime that point is a generator of $E(\mathbb{F_p})[l]$. The \cc{setup} function takes two security parameters \cc{sp1} and \cc{sp2} as arguments and generates a valid set of parameters $params = (p,l,A,B)$ and the corresponding master key $k_m$ . $p$ and $l$ are randomly generated primes with $l \approx$ \cc{sp1} and $p \approx$ \cc{sp2}.

\begin{code}

setup :: (CryptoRandomGen g) => Int -> Int -> g -> (Params,Integer,g)
setup sp1 sp2 g = let (l,g1) = getPrime sp1 g 
                      (p,g2) = getPrime' sp2 l g1 
                      (s,g3) = randomString 10 g2 
                      (mk,g4) = randomInteger (l-1) g3
                      a = h1 (ep p) l s
                      b = pmul (ep p) mk a
                  in (Params p l a b,mk,g4)

\end{code}



\subsection{Private Key Extraction}

The private key of a user is generatd by hashing his \cc{id} onto the curve and multiplying in with the master key \cc{km}.

\begin{code}

extract :: Params -> Integer -> String -> G1
extract (Params p l _ _) km id = 
  let cid = h1 (ep p) l id
  in pmul (ep p) mk id 
     
\end{code}

\subsection{Encryption}

To encrypt an arbitrary-length message we divide the message into blocks of 32-bytes and apply the encryption algorithm presented in \ref{} to each of them. A ciphertext consists of an element of \mb{G}{1} and two bytestrings. 

\begin{code}

data Cipher = Cipher G1 B.ByteString B.ByteString

\end{code} 
 
 Each encryption operation requires one pairing evaluation, which is independent from the current message block. Thus, it suffices to evaluate the pairing once and use that value to encrypt the following blocks. \cc{encrypt params m id g} encrypts an arbitrary-length message \cc{m} using the public-key $id$. The result is a \cc{Cipher} value that contains the encrypted message m. 

\begin{code}

encrypt :: (CryptoRandomGen g) => Params -> B.ByteString -> String -> g -> ([Cipher],g)
encrypt params@(Params p l a b) m ids g=
  let id = h1 (e0 p) l ids
      val = e params id b
      encryptRek m g 
        | (B.null m) = ([],g)
        | otherwise = let (bs,g') = randomByteString  g
                          (m',m'') = B.splitAt 32 m
                          bs' = B.fromChunks [bs]
                          c = encryptBlock params val m' bs'
                          (cs,g'') = encryptRek m'' g'
                      in ((c:cs),g'')
  in encryptRek m g
                            

encryptBlock :: Params -> G2 -> B.ByteString -> B.ByteString -> Cipher
encryptBlock params@(Params p l a _) z m rb = 
  let rb' = B.take (B.length m) rb
      r = h3 l rb' m
      u = pmul (e0 p) r a
      v = xorBS rb' (h2 p (exp_p p z r))
      w = xorBS m (h4 rb')
  in (Cipher u v w)
     
xorBS :: B.ByteString -> B.ByteString -> B.ByteString
xorBS b = B.pack . (B.zipWith xor b)
     


\end{code}




\section{Decryption}

The decryption of a message block also requires a pairing evaluation. Here, the first parameter of the pairing is always the private key of the recipient, whereas the second parameter depends on the ciphertext that is decrypted. Thus we can precompute the parameters for the Tate pairing evaluation to speed-up the following decryption operations. Since decryption might fail we used the \cc{Maybe} monad.
     
\begin{code}

decrypt :: Params -> [Cipher] -> G1 -> Maybe B.ByteString
decrypt _ [] _ = Just B.empty
decrypt params@(Params  p l a b) (c:cs) pk = liftM2 B.append m1 m2
  where (m1,xs) = decryptBlock' params c pk    
        m2 = decryptRek cs
        decryptRek (c:cs) = let m = decryptBlock params c xs
                            in (liftM2 B.append m (decryptRek cs))
        decryptRek [] = Just B.empty

decryptBlock' :: Params -> Cipher -> G1 -> (Maybe B.ByteString, [FunParam])
decryptBlock' (Params p l a _) (Cipher u v w) pk = 
  let (z,xs) = modTateBKLSPre p l pk u 
      rb = (xorBS v (h2 p z))
      r = h3 l rb m
      pr = pmul (e0 p) r a
      m = xorBS w (h4 rb)
  in if (pr == u) then (Just m,xs) else (Nothing, xs)
                                               
\end{code}

The \cc{decryptBlock'} function is used for the first decryption. It returns the decrypted ciphertext  and the precomputed parameters. The \cc{decryptBlock} function performs a decryption using those parameters. 

\begin{code}

decryptBlock :: Params -> Cipher ->  [FunParam] -> Maybe B.ByteString
decryptBlock params@(Params p l a b) (Cipher u v w) xs =
  let z = modTateBKLS' p l u xs 
      rb = xorBS v (h2 p z)
      r = h3 l rb m
      pr = pmul (e0 p) r a
      m = xorBS w (h4 rb)
  in if (pr == u) 
       then (Just m) 
       else Nothing

\end{code}

\section{Signing}
 
 As opposed to encryption, we only produce one signature for an arbitrary-length message. This makes the signing and verification less time critical because we do not have to evaluate the Tate pairing for each message block. 
 
\begin{code}

data Signature = Signature (Aff Integer) Integer
                   
\end{code}

 The sign function produces a signature for a message given as a bytestring . The algorithm \ref{} uses an arbitrary point as parameter for the Tate pairing. For simplicity reasons we use the system parameter A. 
 
\begin{code}
     
sign :: (CryptoRandomGen g) => Params -> B.ByteString -> G1 -> g -> (Signature,g)
sign params@(Params p l a _) m pk g = 
  let (k,g') = randomInteger l g
      r = exp_p p (e params a a) k
      v = h5 p l m r
      u = padd (e0 p) (pmul (e0 p) v pk) (pmul (e0 p) k a)
  in ((Signature u v),g')
                                
       
\end{code}
 
 \section{Verification}
  
  The verify function is a straight-forward implementation of the algorithm \ref{}. Note that both operations, the signing and verification, require a pairing evaluation that can be precomputed, i.e. that does not depend on the current message or signature. This can be interesting if a large number of signatures or verifications are to be performed.
       
\begin{code}

verify :: Params -> B.ByteString -> Signature -> String -> Bool
verify params@(Params p l a b) m (Signature u v) id = 
  let cid = h1 (e0 p) l id
      w1 = e params u a
      w2 = e params cid (neg (e0 p) b) 
      w3 = exp_p p w2 v
      r = mul_p p w1 w3
  in (v == (h5 p l m r))

\end{code}