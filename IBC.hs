{-# LANGUAGE FlexibleInstances #-} 

module IBC (Params(..),
	    Cipher(..),
	    Affine(..),
	    Signature(..),
	    encrypt,
	    decrypt,
	    extract,	
	    sign,
	    verify,
	    zeroPadding,
	    h1) where

import Arithmetic
import EllipticCurve
import TatePairing
import Control.Monad
import qualified Crypto.Hash.SHA256 as SHA2
import qualified Crypto.Hash.SHA384 as SHA3
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8 as BC
import Data.Bits
import Data.Maybe
import Data.Binary
import Data.Binary.Get
import System.Random


{-| 
The 'Cipher' datatype represents a ciphertext in the Boneh-Franklin IBE scheme. It consists of an elliptic curve
point and two 32-byte bytestrings.
-}
data Cipher = Cipher (Affine Integer) B.ByteString B.ByteString
	deriving (Show)

{-| 
The 'Signature' datatype represents a signature in the Hess-IBS scheme. It consists of an elliptic curve point
and an integer in Z_p^*.
-}
data Signature = Signature (Affine Integer) Integer
	deriving (Show)

{-|
The 'Params' datatype encapsules the parameters of the IBC system. It contains a prime p, a prime q, and two elliptic curve point a and b. To represent a valid IBC system the parameters have to satisfy the following properties: p = 11 mod 12, l is prime and divides p+1, a = [km]b where km is the master key
-}
data Params = Params Integer Integer (Affine Integer) (Affine Integer) -- ^ Params p l a b
        deriving (Show)

instance Show a => Show (Affine a) where
	show InfA = "inf"
	show (A a b) = "(" ++ show a ++ "," ++ show b ++ ")"

ec :: Integer -> EllipticCurve
ec p = (EC p 1 0)

instance Binary (Affine Integer) where
	put InfA = putWord8 0
        put (A x y) = do putI x
			 putI y
	get = do let getAffine = do x <- getI
			            y <- getI
				    return (A x y)
		 l1 <- lookAhead getWord8
	         if (l1 == 0) then (return InfA) else getAffine

instance Binary F_p2 where
	put (F_p2 x y) = do putI x
	   	            putI y
		        
        get = do x <- getI
                 y <- getI
	         return (F_p2 x y)
      
-- | decodes a byte string as element in F_p that was serialized in the format specified by putI.
getI :: Get Integer
getI = do let getL 0 = liftM fromIntegral getWord8
   	      getL n = do x <- liftM fromIntegral getWord8
                          y <- getL (n-1)
		          return ((x*(256^n)) + y)
          getL (63)

{- | encodes x in F_p as ByteString. Works only for x > 0. The first byte indicates the number of bytes needeed to represent x. The following bytes represent x as unsigned big endian value. -}
putI :: Integer -> Put
putI x = do let putL 0 = putWord8 (fromIntegral x)
	        putL n = do putWord8 (fromIntegral (shiftR x (8*(fromIntegral n))))
                            putL (n-1)
            putL (63)


{- | Encrypts an arbitrary length byte string using the boneh franklin fullident scheme. The message is divided up into blocks of 32 bytes which are encrypted individually. If the length of the byte string is not a multiple of 32 
it will be extended using zero padding. -}
encrypt :: RandomGen a 
        => Params       -- ^ the system parameters
        -> B.ByteString -- ^ the plaintext
        -> String       -- ^ the identification string of the recipient
        -> a            
        -> Maybe ([Cipher],a)
encrypt params@(Params p q a b) m id gen = let (gen',gen'') = split gen
                                               cid = h1 p q id
				               s = bkls p q (fromJust cid) b
                                               m' = zeroPadding m 
		     		               encryptRek m g 
                                                       | (B.null m) = []
                                                       | otherwise = let (rb,g') = random256 g
						   	                 c = encryptBlock params s (B.take 32 m) rb
				                                     in c : (encryptRek (B.drop 32 m) g')
				           in if (isNothing cid) then Nothing else Just (encryptRek m' gen',gen'')


{- | Encrypts a single block using a precomputed tate pairing value. -}
encryptBlock :: Params        -- ^ the system parameters
             -> F_p2          -- ^ the precomputed pairing value
             -> B.ByteString  -- ^ the block
             -> B.ByteString  -- ^ a random 32 byte block 
             -> Cipher        -- ^ the ciphertext of a single block
encryptBlock (Params p q a _) z m rb = let r = h3 q rb m
                                           u = pmul (ec p) r a
                                           v = xorBS rb (h2 (exp_p p z r))
                                           w = xorBS m (h4 rb)
                                        in (Cipher u v w)


{- Takes a byte string b of arbitrary length and returns the smallest byte string c that contains b and whos size 
is a multiple of 32. Extension is done using zero padding.-} 
zeroPadding :: B.ByteString -- ^ b
            -> B.ByteString -- ^ c
zeroPadding b
        | (mod (B.length b) 32) == 0 = b
        | otherwise = B.append b (B.replicate (32 - (mod (B.length b) 32)) 0) 

{- |  Decrypts a list of Cipher to a contiguous bytestring. The decrypt function is consitent with encrypt:
   decrypt params (encrypt params m id g) pk = m , where pk is the private key corresponding to id. Will return Nothing if decryption fails. Decryption fails if the message was corrupted or the system parameters or the private key are invalid.  -} 
decrypt :: Params             -- ^ the system parameters
        -> [Cipher]           -- ^ the ciphertext
        -> Affine Integer              -- ^ the privatekey 
        -> Maybe B.ByteString -- ^ Just the decrypted ciphertext or Nothing if decryption failed
decrypt params@(Params p q a b) (c:cs) pk = let (m1,xs) = decryptBlock' params c pk
                                                decryptRek (c:cs) xs = let m = decryptBlock params c xs
                                                                       in  (liftM2 B.append m (decryptRek cs xs))
                                                decryptRek [] _ = Just B.empty
                                            in (liftM2 B.append m1 (decryptRek cs xs))


{- | Decrypts a single Block and precomputes parameters for faster tate pairing computation. Invoked by the decrypt 
function to decrypt the fist block. decryptBlock' returns (Just m, xs) when decryption was successful. Here m is the plaintext corresponding to the ciphertext decryptBlock' was applied to. xs contains the precomputation parameters for the tate pairing. Decryption might fail if the ciphertext was corrupted or if system parameters or private key are invalid. If decryption fails decryptBlock' returns (Nothing,xs).-}
decryptBlock' :: Params  -- ^ the system parameters
              -> Cipher  -- ^ a single ciphertext
              -> Affine Integer   -- the private key 
              -> (Maybe B.ByteString, [(Integer,Integer,Affine Integer)])
decryptBlock' (Params p q a _) (Cipher u v w) pk = let (z,xs) = bklsPre p q pk u 
                                                       rb = (xorBS v (h2 z))
                                                       r = h3 q rb m
                                                       pr = pmul (ec p) r a
                                                       m = xorBS w (h4 rb)
                                                in (if (eq pr u) then (Just m,xs) else (Nothing, xs))



{- | Decrypts a single Cipher to a 32 byte plaintext using precomputation parameters for faster tate pairing computation. Will return Just the plaintext if decryption is successful otherwise Nothing.-}
decryptBlock :: Params                    -- ^ the system parameters
             -> Cipher                    -- ^ a single ciphertext
             -> [(Integer,Integer,Affine Integer)] -- ^ the precomputation parameters 
             -> Maybe B.ByteString
decryptBlock (Params p q a b) (Cipher u v w) xs  = let z = bkls' p q u xs 
                                                       rb = (xorBS v (h2 z))
                                                       r = h3 q rb m
                                                       pr = pmul (ec p) r a
                                                       m = xorBS w (h4 rb)
                                                   in (if (eq pr u) then (Just m) else Nothing)

{- | Computes the private key corresponding to an identification string id. -} 
extract :: Params  -- ^ the system parameters 
        -> String  -- ^ the identification string   
        -> Integer -- ^ the master key
        -> Maybe (Affine Integer)   -- ^ the corresponding private key
extract (Params p q a _) s mk = liftM (pmul (ec p) mk)  (h1 p q s)


{- | Produces a Signatur for a message m. -}
sign :: RandomGen a 
     => Params        -- ^ the system parameters 
     -> B.ByteString  -- ^ the message
     -> Affine Integer         -- ^ the private key
     -> a 
     -> (Signature,a)
sign (Params p q a _) m pk gen = let (k,gen') = random gen
		                     r = exp_p p (bkls p q pk a) k
		                     v = h5 q r m
		                     u = padd (ec p) (pmul (ec p) v pk) (pmul (ec p) k pk)
	                         in ((Signature u v),gen')


{- | Verifies a message. Returns true if the message m is the same message as the message that was signed by the sender with the identification string id -}
verify :: Params       -- ^ The system parameters
       -> B.ByteString -- ^ the signed messaged
       -> Signature    -- ^ the corresponding signature
       -> String       -- ^ the identification string id of the alleged sender 
       -> Bool
verify (Params p q a b) m (Signature u v) id = let w1 = bkls p q u a
						   cid = h1 p q id
	                                           w2 = exp_p p (bkls p q (fromJust cid) (neg (ec p) b)) v
	                    	                   r = mul_p p w1 w2
		                               in if (isNothing cid) then False else (v == h5 q r m)
	       


-- | hashes an identification string id onto a point a with order l on E. 
h1 :: Integer -- ^ p
   -> Integer -- ^ l 
   -> String  -- ^ id
   -> Maybe (Affine Integer) -- ^ a
h1 p q id = let cof = div (p+1) q
	        i = max (div p (2^256)) 1
	        t1 =  i* (bsToInteger (SHA2.hash (BC.pack id)))
	        t2 = i* (bsToInteger  (SHA3.hash (BC.pack id)))
	        rek _ _ 0 = Nothing
	        rek t1 t2 n = let a = pmul (ec p) cof (padd (ec p) (mapToPoint (ec p) t1) (mapToPoint (ec p) t2))
                              in if (eq a inf) then (rek (t1+1) (t2+1) (n-1)) else (Just a)
	    in rek t1 t2 16


{- hashes a F_p2 a value onto {0,1}^256. Uses the encode function of the Data.Binary class to encode F_p2 and maps the result onto {0,1}^256 using SHA256-}
h2 :: F_p2       -- ^ a
   -> B.ByteString -- a 256 bit digest of a
h2 = SHA2.hash . B.concat . BL.toChunks . encode

 
{- hashes two 256 bit byte strings onto {1,..,(l-1)}. Uses SHA256. -}
h3 :: Integer    -- ^ l
   -> B.ByteString -- a
   -> B.ByteString -- b
   -> Integer -- digest
h3 l a b = (hashToRange (l-2) (B.append a b)) + 1


{- simply uses SHA256 to compute the hash of a byte string. -}
h4 :: B.ByteString -> B.ByteString
h4 = SHA2.hash


{- takes an F_p2 value a and a byte string b and hashes them onto {1,..,(l-1)} using SHA256 -}
h5 :: Integer       -- ^ l
   -> F_p2          -- ^ a
   -> B.ByteString  -- ^ b
   -> Integer       -- digest
h5 l a b = (hashToRange (l-2) (B.concat (b : (BL.toChunks (encode a))))) + 1


mapToPoint :: EllipticCurve -> Integer -> Affine Integer 
mapToPoint (EC p ca cb) n = A x y 
	where v = div_p p (3*ca - n^4) (6*n)
	      y = mod (n*x + v) p
	      x = mod (x' + (div_p p (n*n) 3)) p
	      x' = exp_p p  (v*v - cb - (div_p p (n^6) 27)) ((2*p-1) `div` 3)

-- | Hashes a byte string b onto the field F_p. p should have at least 256 bits.
hashToRange :: Integer -- ^ p
            -> B.ByteString  -- ^ id
	    -> Integer -- ^ n
hashToRange p b = let i = max (div p (2^256)) 1
		      h = bsToInteger (SHA2.hash b)
		   in h*i+(h `mod` i) 

-- | Interprets a B.ByteString bs as unsigned big endian integer a returns its value v.
bsToInteger :: B.ByteString -- ^ bs
            -> Integer      -- ^ v
bsToInteger = B.foldl (\x y -> x*256 + (fromIntegral y)) 0 


-- | Computes bytewise XOR of two B.ByteStrings
xorBS :: B.ByteString -> B.ByteString -> B.ByteString
xorBS b = B.pack . (B.zipWith xor b)

{- | generates a random 32 byte string -}
random256 :: (RandomGen a) => a -> (B.ByteString,a)
random256 a = (BC.pack  (Prelude.take 32 (randoms a')),a'')
	where (a',a'') = System.Random.split a

