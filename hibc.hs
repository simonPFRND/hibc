
import IBC
import qualified Data.Binary as B
import qualified Data.ByteString as BS
import Data.Maybe
import System
import System.Random
import System.IO.Error

instance B.Binary Cipher where
	put (Cipher a b c) = do B.put a
				B.put b
			 	B.put c
	get = do a <- B.get
		 b <- B.get
		 c <- B.get
		 return (Cipher a b c)

instance B.Binary Signature where 
	put (Signature a b) = do B.put a
		                 B.put b
	get = do a <- B.get
	         b <- B.get	
	 	 return (Signature a b)

params = getParams "params.conf"

main = do
	args <- getArgs
	catch (dispatch (args !! 0) (tail args)) err 
	

dispatch :: String -> [String] -> IO()
dispatch s xs = do params <- getParams "params.conf"
		   putStrLn "params"
		   gen <- getStdGen
		   case s of
		   	"-e" -> encr params (xs !! 0) (xs !! 1) gen  
	           	"-d" -> decr params (xs !! 0) (xs !! 1)
	           	"-s" -> sgn params (xs !! 0) (xs !! 1) gen
                   	"-v" -> vrf params (xs !! 0) (xs !! 1) (xs !! 2)  

err :: IOError -> IO ()
err e = putStrLn errmsg

errmsg = "Usage: \n hibc -e MESSAGEFILE PUBLICKEY \n hibc -d CIPHER PRIVATEKEY \n hibc -s MESSAGE PRIVATEKEY \n hibc -v MESSAGE SIGNATURE PUBLICKEY \n"

sgn :: (RandomGen a) => Params -> String -> String -> a -> IO ()
sgn params ms ks gen = do m <- BS.readFile ms
			  pk <- getKey ks
                          let (s,gen') = sign params m pk gen
		              name = (takeWhile ('.'/=) ms) ++ ".sgn"
	                  B.encodeFile name s
			

vrf :: Params -> String -> String -> String -> IO ()
vrf params ms s id = do m <- BS.readFile ms
		        sg <- B.decodeFile s
                        let t = verify params m sg id		
                     	if t then putStrLn "Valid signature" else putStrLn "Invalid signature"


encr :: (RandomGen a) => Params -> String -> String -> a -> IO ()
encr params s id gen = do m <- BS.readFile s
	                  let (c,gen') = fromJust (encrypt params m id gen)
		              name = (takeWhile ('.'/=) s) ++ ".ci"
	                  B.encodeFile name c
                           

decr :: Params -> String -> String -> IO ()
decr params cs ks = do c <- B.decodeFile cs
                       pk <- getKey ks
		       let m = fromJust (decrypt params c pk)
		           name = (takeWhile ('.'/=) cs) ++ "2.txt"
		       BS.writeFile name m
	    
getKey :: String -> IO (Affine Integer)
getKey s = do cont <- readFile s
	      let lns = lines cont
	          ax = read (lns !! 0)
		  ay = read (lns !! 1)
	      return (A ax ay)

getParams :: String -> IO Params
getParams s = do cont <- readFile s
		 let lns = lines cont
		     p = read (lns !! 0)
		     q = read (lns !! 1)
		     ax = read (lns !! 2)
		     ay = read (lns !! 3)
		     bx = read (lns !! 4)
		     by = read (lns !! 5)
		 return (Params p q (A ax ay) (A bx by))


