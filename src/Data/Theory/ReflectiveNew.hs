

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Theory.ReflectiveNew (
          reflective
        , mirReflective
        -- , reflectiveWithAxioms
        , GoedelEncodable(..)
        , rForm
        , (~~>)
        , (<~>)
        , (<~~)
        , (&&&)
        , (|||)
        , rEmpty
        , tEmpty
        , rPush
        , tPush
        , rVar0
        , tVar0
        , rForall
        , tForall
        , (|=)
        , Refl(..)
        , dot
        ) where


import Util
import Data.Formula hiding (subs)
import Data.Formula.Mir
import Data.Formula.Reflective
import Data.Theory.Interpreted
import Data.Signature
--
import Data.List
import Control.Monad
import Data.Maybe
import Data.HashMap hiding ((!))
import Data.Theory (theoryInf, formulaInf, toMir)
import qualified Data.HashMap as Map
import Control.Lens hiding (element, to)
import Debug.Trace

class Refl a where 
  refl :: a -> a

instance Refl MirBenchmark where 
  refl (Benchmark t c) = Benchmark (refl t) c

instance Refl MirTheory where 
  refl = mirReflective


instance Refl MirForm where
  refl phi = tEmpty |= goedel varMapping phi
    where 
      varMapping :: (VarId, SortId) -> Int
      varMapping (v,s) = fromJust $ elemIndex v (varsOfSort s)
      varsOfSort s = fmap fst . Data.List.filter ((== s).snd) $ allVs phi

dot :: Id a -> FunId
dot ( Id a ) | isOperator (Id a) = dot (Id $ transOp opName a)
             | otherwise         = Id ( a ++ "R" )

Id a `append` Id b = Id (a ++ "_" ++ b)


------------------- symbol ids

-- functions
rVar0    sort = Id "v0"     `append` sort :: FunId
rNextVar sort = Id "next"   `append` sort :: FunId
rInj     sort = Id "inj"    `append` sort :: FunId
rEq      sort = Id "eq"     `append` sort :: FunId
rBot          = Id "falseR"               :: FunId
rOr           = Id "orR"                  :: FunId
rNot          = Id "notR"                 :: FunId
rEmpty        = Id "empty"                :: FunId
rPush    sort = Id "push"   `append` sort :: FunId
rEvalV   sort = Id "evalV"  `append` sort :: FunId
rEval    sort = Id "eval"   `append` sort :: FunId
rForall  sort = Id "forallR"`append` sort :: FunId

-- predicates
rModels       = Id "|=" :: PredId

-- sorts
rVar    sort = Id "var"    `append` sort :: SortId
rTerm   sort = Id "term"   `append` sort :: SortId
rForm        = Id "form"                 :: SortId
rEnv         = Id "env"                  :: SortId
--
----------------------------

-- functions
tVar0    sort     = BaseFun (rVar0    sort ) [   ] (rVar sort)
tNextVar sort x   = BaseFun (rNextVar sort ) [ x ] (rVar sort)
tInj     sort v   = BaseFun (rInj     sort ) [ v    ] (rTerm sort)
tEq      sort l r = BaseFun (rEq      sort ) [ l, r ] (rTerm sort)
tBot                    = BaseFun rBot             [          ] rForm 
tNot            phi     = BaseFun rNot             [ phi      ] rForm
tOr             phi psi = BaseFun rOr              [ phi, psi ] rForm
tForall  sort v phi     = BaseFun (rForall  sort ) [ v,   phi ] rForm
tEmpty              = BaseFun (rEmpty        ) [       ] rEnv
tPush    sort e v t = BaseFun (rPush    sort ) [ e,v,t ] rEnv
tEvalV   sort e v = BaseFun (rEvalV   sort ) [ e, v ] sort
tEval    sort e t = BaseFun (rEval    sort ) [ e, t ] sort

-- sugar
(|||) = tOr
a &&& b  = tNot ( tNot a ||| tNot b )
a ~~> b =         tNot a |||      b  
a <~~ b =              a ||| tNot b  
a <~> b =    ( a &&& b ) ||| ( tNot a &&& tNot b )

infixl 3 |=
(|=) ::  SortAnnotation s => BaseTerm s -> BaseTerm s -> BaseForm BaseAtom s
e |= phi = BaseAtom $ BasePred rModels [e, phi] 


------------------- signature

reflSig :: [SymDec] -> [SymDec] 
reflSig sig  = [] 
    -- Syntax
   ++ [ coerse ( rVar0    s ) :::: [        ] :-> rVar  s | s <- sorts ]
   ++ [ coerse ( rNextVar s ) :::: [ rVar s ] :-> rVar  s | s <- sorts ]
   ++ [ coerse ( rInj     s ) :::: [ rVar s ] :-> rTerm s | s <- sorts ]

   ++ [ coerse ( dot f ) :::: fmap rTerm as :-> rTerm a | f :::: as :-> a    <- sig ]
   ++ [ coerse ( dot p ) :::: fmap rTerm as :-> rForm   | p :::: Pred as     <- sig ]

   ++ [ coerse ( rEq s     ) :::: [ rTerm s, rTerm s ] :-> rForm  | s <- sorts ]
   ++ [ coerse ( rBot      ) :::: [                  ] :-> rForm  ]
   ++ [ coerse ( rOr       ) :::: [ rForm  , rForm   ] :-> rForm  ]
   ++ [ coerse ( rNot      ) :::: [ rForm            ] :-> rForm  ]
   ++ [ coerse ( rForall s ) :::: [ rVar s, rForm    ] :-> rForm  | s <- sorts ]

    -- Semantics
   ++ [ coerse ( rEmpty   ) :::: [ ] :-> rEnv ] 
   ++ [ coerse ( rPush s  ) :::: [ rEnv, rVar s, s ] :-> rEnv | s <- sorts ] 
   ++ [ coerse ( rEvalV s ) :::: [ rEnv, rVar s    ] :-> s    | s <- sorts ] 
   ++ [ coerse ( rEval  s ) :::: [ rEnv, rTerm s   ] :-> s    | s <- sorts ] 
   ++ [ coerse ( rModels  ) :::: Pred [ rEnv, rForm ]         ]

    where 
       sorts = [ Id s | Id s :::: Srt <- sig ] :: [SortId]
       coerse :: Id a -> Id ()
       coerse (Id a) = Id a


class GoedelEncodable a where
  goedel :: ((VarId, SortId) -> Int) -> a -> MirTerm

instance GoedelEncodable MirForm where 
  goedel vs (BaseCon0 Bot) = tBot
  goedel vs (BaseCon0 Top) = goedel vs (BaseNot (BaseCon0 Bot) :: MirForm)
  goedel vs (BaseNot  phi) = tNot (goedel vs phi)
  goedel vs (BaseAtom a) = goedel vs a
  goedel vs (BaseCon c phi psi) = c' ( goedel vs phi ) ( goedel vs psi  )
    where c' = case c of 
                 -- primary connective
                 Or      -> (|||) 
                 -- defined connectives
                 And     -> (&&&)
                 If      -> (<~~)
                 Implies -> (~~>)
                 Iff     -> (<~>)
  goedel vs (BaseQuant q v s phi) = 
        case q of 
           -- primary 
          Universal -> tForall s (goedel vs (v,s)) (goedel vs phi)
           -- defined
          Existential -> goedel vs $ lnot (BaseQuant Universal v s (lnot phi))


instance GoedelEncodable (VarId, SortId) where
  goedel vs (var,srt) = (tNextVar srt ^ i) (tVar0 srt)
    where i = vs (var, srt)
          f ^ 0 = id
          f ^ n = f . (f ^ ( n - 1 ))

instance GoedelEncodable MirAtom where
  goedel vs (BasePred p ts) = BaseFun (dot p) (goedel vs <$> ts) rForm
  goedel vs (BaseEq pol lhs rhs) = 
    case pol of 
      -- primary
      Pos -> tEq (btSort lhs) (goedel vs lhs) (goedel vs rhs)
      -- defined
      Neg -> goedel vs $ lnot $ BaseAtom ( BaseEq Pos lhs rhs )

instance GoedelEncodable MirTerm where
  goedel vs (BaseFun f ts srt) = BaseFun (dot f) (goedel vs <$> ts) (rTerm srt)
  goedel vs (BaseVar v    srt) = tInj srt ( goedel vs (v, srt) )


reflAxioms :: [SymDec]  -> [MirForm]
reflAxioms sig = unwrap $ sequence [ inferTypes (mkSig $ reflSig sig ++ sig) phi | phi <- reflUnsorted sig ]

  where
    -- inferTypes = toMir
    inferTypes = formulaInf
    reflUnsorted :: [SymDec] -> [Formula]
    reflUnsorted sig = fmap universalClosure $ [] 
        ------------------ Reflective variable interpretation
        -- evalV0
        ++ [             rEvalV s ![ rPush s ![env,v,x], v ] === x                    | s <- sorts ]
        -- evalV1
        ++ [ v =/= w --> rEvalV s ![ rPush s ![env,w,x], v ] === rEvalV s ![ env, v ] | s <- sorts ] 
        -- evalV2
        ++ [             rEvalV s ![ rPush t ![env,w,x], v ] === rEvalV s ![ env, v ] | s <- sorts , t <- sorts , s /= t ] 

        ------------------ Reflective evaluation
        -- evalVar
        ++ [ rEval s ![ env, rInj s ![ v ] ] === rEvalV s ![env, v]         | s <- sorts ]
        -- evalFun
        ++ [ rEval s ![ env, dot f ! [                 t i   | (_, i) <- zip as [0..] ]  ]
                             === f ! [ rEval a ![ env, t i ] | (a, i) <- zip as [0..] ]  | (Id f_ :::: as :-> s)    <- sig , let f = Id f_ :: FunId                  ]
        ------------------ Reflective satisfaction
        -- eqR
        ++ [ ( env |= rEq s ![ x, y ] ) <-> (rEval s ![env, x] ===  rEval s ![env, y] )       | s <- sorts ]
        -- pred
        ++ [ ( env |= dot p ! [                 t i   | (_, i) <- zip as [0..] ]  ) 
                   <-> (  p ! [ rEval a ![ env, t i ] | (a, i) <- zip as [0..] ]  ) | (Id p_ :::: Pred as) <- sig 
                                                                                    , let p = Id p_ :: PredId  ]
        ++ [ ( env |= rBotT )               <-> BaseCon0 Bot                       ] -- bot
        ++ [ ( env |= (rNot ![ phi ]) )     <-> lnot (env |= phi)                  ] -- not
        ++ [ ( env |= (rOr ![ phi, psi ]) ) <-> ( (env |= phi) \/ (env |= psi) )   ] -- or
        ++ [ ( env |= (rForall s ! [ v, phi ] ))  -- forall
                  <-> (oForall s x ( rPush s ![ env, v, x ] |= phi ) ) | s <- sorts]
        
      where x   = BaseVar ( Id "x"   ) Nothing :: Term
            y   = BaseVar ( Id "y"   ) Nothing :: Term
            env = BaseVar ( Id "env" ) Nothing :: Term
            s   = BaseVar ( Id "s"   ) Nothing :: Term
            phi = BaseVar ( Id "phi" ) Nothing :: Term
            psi = BaseVar ( Id "psi" ) Nothing :: Term
            v   = BaseVar ( Id "v"   ) Nothing :: Term
            w   = BaseVar ( Id "w"   ) Nothing :: Term
            sorts = [ Id s | Id s :::: Srt <- sig ] 
            rBotT = rBot ! ([] :: [BaseTerm (Maybe SortId)])
            a +~ Id b = a ++ "_" ++ b
            t i =  BaseVar ( Id $ "t" ++ (show i) ) Nothing :: BaseTerm (Maybe SortId)
            oForall :: SortId -> BaseTerm (Maybe SortId) -> Formula -> Formula
            oForall s (BaseVar x Nothing) = forallS [x] s



reflective = unwrap . safeReflective

trace' x = trace (show x) x
mirReflective :: MirTheory -> MirTheory
mirReflective t =  Theory {
        thName      = thName t      
      , thAxioms    = thAxioms t    ++ reflAxioms (thSignature t)
      , thSignature = toDecls $  mkSig $ thSignature t ++ reflSig    (thSignature t)
      , thDataTypes = thDataTypes t 
      }

safeReflective :: Theory -> Result MirTheory
safeReflective t = do 
  t' <- theoryInf t
  return (mirReflective t')
