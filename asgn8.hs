{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}


module Main where


import Data.List (find)
import Text.Read (readMaybe)


-- Value types
data Value
 = NumV Double
 | BoolV Bool
 | StringV String
 | PrimV String
 | ClosV [String] ExprC Env
 deriving (Show)


-- Expression types
data ExprC
 = NumVC Value
 | IdC String
 | StringVC Value
 | LamC [String] ExprC
 | AppC ExprC [ExprC]
 | IfC ExprC ExprC ExprC
 deriving (Show)


-- Standalone deriving due to errors in putting it above
deriving instance Eq Value
deriving instance Eq ExprC


-- Binding and Environment
type Binding = (String, Value)
type Env = [Binding]


-- Initial top-level environment
topEnv :: Env
topEnv =
 [ ("false", BoolV False)
 , ("true", BoolV True)
 , ("+", PrimV "+")
 , ("*", PrimV "*")
 , ("-", PrimV "-")
 , ("/", PrimV "/")
 , ("<=", PrimV "<=")
 , ("equal?", PrimV "equal?")
 , ("error", PrimV "error")
 ]


-- Lookup a symbol in the environment
lookup' :: String -> Env -> Value
lookup' sym env =
 case find ((== sym) . fst) env of
   Just (_, val) -> val
   Nothing -> error $ "[AAQZ] Id out of bounds: " ++ sym


-- Check if a symbol is valid
validId :: String -> String
validId s
 | s `elem` ["if", "=>", "bind", "="] = error $ "[AAQZ] Id not permitted: " ++ s
 | otherwise = s


-- Check argument uniqueness
checkArgs :: [String] -> [String]
checkArgs [] = []
checkArgs (f:r)
 | f `elem` r = error $ "[AAQZ] Duplicate argument names: " ++ f
 | otherwise = f : checkArgs r


-- Parse an S-Expression represented as a list
parse :: [String] -> ExprC
parse expr = case expr of
 -- Numeric values
 [n] | Just num <- readMaybe n -> NumVC (NumV num)


 -- Bool values
 ["true"] -> NumVC (BoolV True)
 ["false"] -> NumVC (BoolV False)


 -- String values
 [s] | head s == '"' && last s == '"' -> StringVC (StringV (init (tail s)))


 -- Variable ID
 [s] -> IdC (validId s)


 -- If expr
 ("if" : test : then' : else' : []) ->
   IfC (parse [test]) (parse [then']) (parse [else'])


 -- Bind expr
 ("bind" : bindings : body : []) ->
   let bindingPairs = parseBindings (words bindings)
   in AppC (LamC (map fst bindingPairs) (parse [body]))
           (map (parse . (:[])) (map snd bindingPairs))


 -- Lambda
 (argList : "=>" : body : []) ->
   LamC (checkArgs (words argList)) (parse [body])


 -- Function with args
 (f : args) ->
   AppC (parse [f]) (map (parse . (:[])) args)


 -- ERROR: Invalid syntax
 _ -> error $ "[AAQZ] Syntax error: " ++ show expr


-- Parse bindings
parseBindings :: [String] -> [(String, String)]
parseBindings [] = []
parseBindings (name : "=" : value : rest) =
 (validId name, value) : parseBindings rest
parseBindings _ = error "[AAQZ] Invalid binding syntax"


-- Handle primitive operations
handlePrims :: String -> [Value] -> Value
handlePrims op args = case (op, args) of
 ("error", [x]) -> error $ "[AAQZ] User error: " ++ show x
 ("equal?", [x, y]) -> BoolV $ case (x, y) of
   (PrimV _, PrimV _) -> False
   (ClosV _ _ _, ClosV _ _ _) -> False
   _ -> x == y
 (arith, [NumV x, NumV y]) ->
   case arith of
     "+" -> NumV (x + y)
     "-" -> NumV (x - y)
     "*" -> NumV (x * y)
     "/" -> if y > 0
            then NumV (x / y)
            else error "[AAQZ] Division by zero"
     "<=" -> BoolV (x <= y)
     _ -> error $ "[AAQZ] Unknown arithmetic operation: " ++ arith
 _ -> error $ "[AAQZ] Invalid primitive operation: " ++ op


-- Interpreter
interp :: ExprC -> Env -> Value
interp expr env = case expr of
 NumVC v -> v
 IdC s -> lookup' s env
 StringVC v -> v
 LamC args body -> ClosV args body env
 IfC test then' else' ->
   case interp test env of
     BoolV True -> interp then' env
     BoolV False -> interp else' env
     _ -> error "[AAQZ] Non-boolean test in if statement"
 AppC f args ->
   case interp f env of
     ClosV params body cenv ->
       if length params == length args
       then interp body newEnv
       else error $ "[AAQZ] Wrong arity: " ++ show f
       where
         newEnv =
           zip params (map (\arg -> interp arg env) args) ++ cenv
     PrimV op -> handlePrims op (map (\arg -> interp arg env) args)
     _ -> error $ "[AAQZ] Application of non-closure: " ++ show f


-- Serialize a value to a string representation
serialize :: Value -> String
serialize val = case val of
 NumV n -> show n
 BoolV True -> "true"
 BoolV False -> "false"
 StringV s -> show s
 ClosV {} -> "#<procedure>"
 PrimV {} -> "#<primop>"


-- Top-level interpreter
topInterp :: [String] -> String
topInterp expr = serialize (interp (parse expr) topEnv)


-- Main function to test
main :: IO ()
main = do
 let sExpr = ["bind", "x = 42", "x"]
 putStrLn $ topInterp sExpr

