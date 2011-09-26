



import EllipticCurve
import TatePairing
import IBC
import Control.Monad
import qualified Control.Exception as C
import Crypto.Random
import qualified Data.Binary as B

import Data.Maybe
import System.IO.Error
import System

                     
instance (Read a) => Read (Aff a) where
  readsPrec _ x = [(A ax ay, xs) | ((ax,ay),xs) <- reads x]            
                  ++
                  [(InfA, t) | ("inf", t) <- lex x     ]
                  
instance (Show a) => Show (Aff a) where
  show (A ax ay) = show (ax,ay)
  show InfA = "inf" 
  
instance Read Cipher where
  readsPrec _ x = [(Cipher u v w,xs) | ((u,v,w),xs) <- reads x]
  
instance Show Cipher where
  show (Cipher u v w) = show (u,v,w)
  
instance Read Signature where
  readsPrec _ x = [(Signature u v,xs) | ((u,v),xs) <- reads x]
  
instance Show Signature where
  show (Signature u v) = show (u,v)
                          
instance Read Params  where
  readsPrec _ x = [(Params p l a b,xs) | ((p,l,a,b),xs) <- reads x]
  
instance Show Params where
  show (Params p l a b) =  show (p,l,a,b)

errEncr = "Usage: hibc -e <message> <userid> (<output>)"
errDecr = "Usage: hibc -d <cipher> <key> (<output>)"
errSign = "Usage: hibc -s <message> <key> (<output>)"
errVer = "Usage: hibc -v <message> <signature> <userid>"
errSetup = "Usage: hibc -setup <securityparameter1> <securityparameter2>"
errGen = "Usage: hibc [-e,-d,-s,-v,-setup] <param1> <param2> (<param3>)"
errExtr = "Usage: hibc -extract <masterkey> <id> (<output>)"
                 
err :: String ->  C.SomeException -> IO a
err s e = ioError (userError s)     
          
readf :: (Read a) => String -> IO a
readf s = 
  C.catch (do s' <- readFile s
              return (read s'))
        (err ("could not read file " ++ s))
          
writef :: (Show a) => String -> a -> IO ()
writef s f = 
  C.catch (writeFile s (show f))
          (err  ("Could not write file " ++ s))
  
readS :: String -> IO String
readS s = 
  C.catch (readFile s)
          (err ("Could not write file " ++ s))
        
writeS :: String -> String -> IO ()
writeS s f = 
  C.catch (do writeFile s f) 
          (err ("Could not write file " ++ s))
  
encrypt' :: [String] -> IO()
encrypt' s =
  C.catch (do g <- newGenIO :: IO SystemRandom
              params <- readf "params.conf"
              message <- liftM B.encode (readS (s !! 0))
              let o = if ((length s) > 2)
                        then s !! 2
                        else suffix (s !! 0) ".ci"
                  id = s !! 1
                  (c,_) = encrypt params message id g
              writef o c)
          (err errEncr)

decrypt' :: [String] -> IO()
decrypt' s =
  C.catch (do params <- readf "params.conf"
              cipher <- readf (s !! 0) 
              key <- readf (s !! 1) 
              let o = s !! 2
                  m =  decrypt params cipher key
              if (isNothing m) 
                then (ioError (userError "decryption failed!"))
                else writeS o ((B.decode (fromJust m)) :: String))     
          (err errDecr)

sign' :: [String] -> IO()
sign' s =
  C.catch (do g <- newGenIO :: IO SystemRandom
              params <- readf "params.conf"
              message <- liftM B.encode (readS (s !! 0)) 
              key <- readf (s !! 1) 
              let o = if (length s) > 2
                        then s !! 2
                        else suffix (s !! 0) ".sgn"
                  (sig,_) = sign params message key g
              writef o sig)     
          (err errSign)
                         
verify' :: [String] -> IO()
verify' s = 
  C.catch (do params <- readf "params.conf"
              message <- liftM B.encode (readS (s !! 0))
              sign <- readf (s !! 1)
              let id = s !! 2
                  r  =  verify params message sign id
              if r 
                then putStrLn "valid signature"
                else putStrLn "invalid signature")  
          (err errVer)     
  
extract' :: [String] -> IO()
extract' s =
  C.catch (do params <- readf "params.conf"
              mk <- readf (s !! 0)
              let id = (s !! 1)
                  o = if (length s) > 2 
                        then s !! 2
                        else suffix (s !! 1) ".k"     
                  k = extract params mk id
              writef o k)
          (err errExtr)     
            
setup' :: [String] -> IO()
setup'  s = 
  C.catch (do g <- newGenIO :: IO SystemRandom
              let sp1 = read (s !! 0) :: Int
                  sp2 = read (s !! 1) :: Int
                  (params,mk,_) = setup sp1 sp2 g
              writef "params.conf" params
              writef "master.k" mk)
          (err errSetup)     

readParams :: String -> IO Params
readParams s =
  C.catch (do params <- readf s
              return params)
          (err "Could not read parameters") 
          
suffix :: String -> String -> String
suffix s s' = (takeWhile (/= '.') s) ++  s'

dispatch :: [String] -> IO()
dispatch (s:xs) = 
  do case s of 
                "-e" -> encrypt' xs
                "-d" -> decrypt' xs
                "-s" -> sign' xs
                "-v" -> verify' xs 
                "-setup" -> setup' xs
                "-extract" -> extract' xs
                _ -> ioError (userError errGen)
dispatch _ = ioError (userError errGen)
  
             
main =
  do args <- getArgs
     C.catch (dispatch args)
             (\err -> putStrLn (ioeGetErrorString err))   

 
\end{code}