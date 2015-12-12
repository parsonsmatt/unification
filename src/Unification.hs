{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Unification where

import Control.Monad.State
import Control.Monad.Except
import Data.Map (Map)
import qualified Data.Map.Strict as Map
     
data Expr
  = Lit String
  | Var String
  | List [Expr]
  | Expr :=> Expr
  deriving (Eq, Ord, Show)
infixr 4 :=>

newtype Unification a
  = Unification 
  { unUnification :: ExceptT UnificationError (State Theta) a 
  } deriving (Functor, Applicative, Monad, MonadState Theta, MonadError UnificationError)

data UnificationError
  = VariableOccursCheck
  | IncompatibleUnification Expr Expr
  | InexplicableFailure
  | OccursCheckWithNotVar
  | UnifyVarWithNotVar
  deriving Show

type Theta = Map Expr Expr

runUnify :: Expr -> Expr -> Either UnificationError Theta
runUnify a b = evalState (runExceptT (unUnification (unify a b))) mempty

unify :: Expr -> Expr -> Unification Theta
unify a b | a == b = get
unify (Var a) b = 
  unifyVar (Var a) b
unify a (Var b) =
  unifyVar (Var b) a
unify (opX :=> argsX) (opY :=> argsY) = do
  unify opX opY
  unify argsX argsY
unify (List as) (List bs) =
  last <$> zipWithM unify as bs
unify (Lit _) (Lit _) = get
unify a b =
  throwError $ IncompatibleUnification a b

unifyVar :: Expr -> Expr -> Unification Theta
unifyVar var@(Var _) x = do
  theta <- get
  case Map.lookup var theta of
       Just val -> unify val x
       Nothing ->
         case Map.lookup x theta of
              Just val -> unify var val
              Nothing -> do
                occursCheck var x
                let x' = Map.foldrWithKey replace x theta
                modify (Map.insert var x')
                updateVariables var x'
                get
unifyVar _ _ = throwError UnifyVarWithNotVar

occursCheck :: Expr -> Expr -> Unification ()
occursCheck var@(Var a) expr = do
  theta <- get
  case expr of
       Var b -> do
         when (a == b) throwOccurs
         gets (Map.lookup expr) >>= mapM_ (occursCheck var)
       Lit _ -> return ()
       List xs -> mapM_ (occursCheck var) xs
       op :=> arg -> do
         occursCheck var op
         occursCheck var arg
  where throwOccurs = throwError VariableOccursCheck
occursCheck _ _ = throwError OccursCheckWithNotVar


replace :: Expr -> Expr -> Expr -> Expr
replace source replacement target 
  | source == target = replacement
  | otherwise =
    case target of
         List xs -> List $ map (replace source replacement) xs
         op :=> arg -> replace source replacement op :=> replace source replacement arg
         a -> a

updateVariables :: Expr -> Expr -> Unification ()
updateVariables var@(Var a) replacement =
  modify (Map.map (replace var replacement))


ex :: Int -> (Expr, Expr)
ex 1 = 
  ( Var "P" :=> Var "X"
  , Var "P" :=> Lit "a"
  )
ex 2 =
  ( Var "P" :=> Lit "f" :=> List [ Var "Y", Lit "g" :=> Var "Y"]
  , Var "P" :=> Lit "f" :=> List [ Lit "a", Var "X" ]
  )
ex 3 =
  ( Var "P" :=> List [ Var "Y", Var "Y" ]
  , Var "P" :=> List [ Lit "f" :=> Lit "a", Lit "a" ]
  )
ex 4 =
  ( Var "P" :=> List [ Var "Y", Lit "f" :=> Var "Y" ]
  , Var "P" :=> List [ Var "X", Var "X" ]
  )

main :: IO ()
main = forM_ [1..4] (print . uncurry runUnify . ex)
