{-# LANGUAGE OverloadedStrings #-}

import Datatypes
import FreeCheck
import Parser
import System.Environment (getArgs)

main = do
  [filename] <- getArgs
  s <- readFile filename
  case parseModule filename s of
    Left err -> putStrLn (show err)
    Right (Module sig trs) -> print (checkTRS sig trs)
    --(getReachable sig (Appl "cons" [(Appl "list" [Var "l1"]) , (Var "l2")]) (TypeName "Expr"))

--import Data.Set as S
--import Data.Vector as V
--import Data.List
--
--main = do
--  let l1 = V.replicate 5 (S.singleton 5)
--  let l2 = [0..4]
--  let l = V.imap (foo l1) (V.fromList l2)
--  putStrLn (show l)
--    where foo li i n = accum add li [(i,n)]
--          add s n = S.insert n s
