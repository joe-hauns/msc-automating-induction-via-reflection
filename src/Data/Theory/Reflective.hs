

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

module Data.Theory.Reflective (
          form
        , term
        , reflective
        , reflectiveWithAxioms
        , safeReflective 
        , eval
        , dot
        , trueR
        , true
        , forallR
        , eqR
        , notR
        , botR
        , subsFR
        , subsTR
        , v0R
        , nVarR 
        , vTermR
        , orR
        , reflForm
        , Refl(..)
        ) where


import Util
import Data.Formula hiding (subs)
import Data.Formula.Mir
import Data.Formula.Reflective
import Data.Theory
import Data.Signature
--
import Data.List
import Control.Monad
import Data.Maybe
import Data.HashMap hiding ((!))
import qualified Data.HashMap as Map
import Control.Lens hiding (element, to)

fun id ts = BaseFun id ts Nothing

funDecl id ts t = (Id id, Function ts t)

reflFuns :: Sig -> Decls Function
reflFuns sig = decls $ [ (dot  id, Function [term a | a <- f^.funArgs] (term $ f ^.funSort))   | (id, f) <- declList sgFuns sig ]

pushId :: String -> SortId -> Id a
pushId x (Id s) =  Id $ join [ s, "_", x ]

connectives :: [(FunId, Formula -> Formula -> Formula)]
connectives = [ 
    (orR, (\/))
  ]
-- additional funs
-- implR   =     Id "implies"::           FunId
botR    =     Id "bot"    ::           FunId
orR     =     Id "or"     ::           FunId
-- andR    =     Id "and"    ::           FunId
notR    =     Id "not"    ::           FunId
forallR = pushId "forall" :: SortId -> FunId
subsFR = pushId "subs"     :: SortId -> FunId
subsTR :: SortId -> SortId -> FunId 
subsTR (Id f) (Id i)  = Id ("subs_" ++ f ++ "_in_" ++ i ) 
eqR     = pushId "eq"     :: SortId -> FunId
eval    = pushId "eval"   :: SortId -> FunId
nVarR   = pushId "nv"   :: SortId -> FunId
vTermR  = pushId "trm"    :: SortId -> FunId
-- cTerm   = pushId "cTerm"  :: SortId -> FunId

-- additional sorts
form = Id "formula"  ::           SortId 
term = pushId "term" :: SortId -> SortId 
var  = pushId "var"  :: SortId -> SortId 

-- additional consts
v0R  =  pushId "v0" ::  SortId -> FunId

-- additional preds
trueR = Id "true" :: PredId


true :: BaseTerm s -> BaseAtom s
true f = BasePred trueR [f] 

dot_ :: Id a -> Id b
dot_ (Id s) = Id $ s ++ "_"

class Refl a r | a -> r where 
   refl :: Sig -> a -> r

instance Refl FunId FunId where 
  refl = const dot_

instance Refl PredId FunId where 
  refl = const dot_

instance Refl Connective (MirTerm -> MirTerm -> MirTerm) where 
  refl _ Or  a b = BaseFun orR [ a, b ] form
  refl _ And a b = notR![ orR![ notR![a], notR![b] ] ]
    where f!a = BaseFun f a form
  refl s Implies a b = refl s Or (BaseFun notR [a] form) b
  refl s If a b = refl s Implies b a
  refl s Iff a b = (refl s And) (refl s Implies a b :: MirTerm) (refl s Implies b a :: MirTerm)

reflForm :: Sig -> MirForm -> Result MirForm
reflForm s x = trace $ typeChecked s (BaseAtom (BasePred trueR [refl s x]))
  where trace = pushTrace ( "generating reflection of: " ++ show x ) 

instance Refl MirForm MirTerm where
  refl s = refl' Map.empty
    where 
      fn sym args = BaseFun sym args form

      refl' :: Map SortId [VarId] -> MirForm -> MirTerm
      refl' vs (BaseAtom (BaseEq Pos a1 a2) ) = fn (eqR $ mirSort a1) [ reflT vs a1,  reflT vs a2 ]
      refl' vs (BaseAtom (BaseEq Neg a1 a2) ) = refl' vs (BaseNot (BaseAtom (BaseEq Pos a1 a2) ))
      refl' vs (BaseCon   c a1 a2)   = (refl s c) (refl' vs a1) (refl' vs a2)
      refl' vs (BaseAtom (BasePred p ts) )       = fn (refl s p) [ reflT vs t | t <- ts ]
      refl' vs (BaseNot   f)         = fn notR        [ refl' vs  f ]  
      refl' vs (BaseQuant q v s f)   = fn (forallR s) [ refl' vs' f ] 
         where vs' = alter addV s vs
               addV Nothing   = Just $ [v]
               addV (Just vs) = Just $ v:vs
        

      reflT :: Map SortId [VarId] -> MirTerm -> MirTerm
      reflT vs (BaseFun f ts s) = BaseFun (dot f) [reflT vs t | t <- ts] (term s)
      reflT vs (BaseVar v s) = 
        case Map.lookup s vs >>= findIndex (== v) of 
          Nothing -> error "open formulas are not supported yet"
          Just i  -> BaseFun (vTermR s)  [varFrom i] (term s)
            where varFrom 0 = vfn (v0R s) [] 
                  varFrom x = vfn (nVarR s) [varFrom (x-1)] 
                  vfn sym args = BaseFun sym args (var s)
                              

dot :: Id a -> FunId
dot = dot_

reflAxioms :: Sig -> [Axiom Formula]
reflAxioms sig = [] 

              ++ [ axiom ("Sem"++show c)  (tr(phi * psi) <-> (tr phi . tr psi)) | (c, (.)) <- connectives 
                                                                                , let (*) = binary c      ]
               
              -- truth predicate
              ++ [ axiom "Eq"         ( tr( s ~~~ t ) <-> ev a s === ev a t ) | a <- sorts 
                                                                             , let x ~~~ y = (eqR a)!(x,y) ]
              ++ [ axiom "Bot"        ( lnot(tr bot))                      ]
              ++ [ axiom "Not"        ( tr(not' phi ) <-> lnot (tr phi))   ]
              ++ [ axiom "Q"          ( tr(forall' a phi) <-> forall [t] ( tr(sbs a phi (v0 a) t) ) )  | a <- sorts ]
              ++ [ axiom (show p)     ( tr(p'!xs) <-> p![ eval b ! x | (x,b) <- xs `zip` bs ])  
                                                                                  | p_ :::: Pred bs <- toDecls sig 
                                                                                  , let xs = take (length bs) infVars
                                                                                  , let p = coerse p_ :: PredId
                                                                                  , let p' = dot p_                ]

              
               -- formula substitution
              ++ [ axiom "SubsQ1"     ( sbs a (forall' a phi) (v0 a) t    === forall' a phi             ) | a <- sorts ]
              ++ [ axiom "SubsQ2"     ( sbs a (forall' a phi) (nxt a v) t === forall' a (sbs a phi v t) ) | a <- sorts ]
              ++ [ axiom "SubsQ1"     ( sbs a (forall' b phi) v t         === forall' b (sbs a phi v t) ) | a <- sorts 
                                                                                                         , b <- sorts 
                                                                                                         , a /= b ]
              ++ [ axiom ("Subs"++show c)    ( sbs a ((to phi ) * (to psi )) v t === (sbs a phi v t * sbs a psi v t)) 
                                                                        | (c, _) <- connectives 
                                                                        , let (*) = binary c 
                                                                        , a <- sorts ]
              ++ [ axiom "SubsBot"    ( sbs a bot  v t === bot )                                   | a <- sorts ]
              ++ [ axiom "SubsNot"    ( sbs a (not' phi)  v t === not' (sbs a phi v t) )           | a <- sorts ]
              ++ [ axiom "SubsEq"     ( sbs a (to s ~~~ to u)   v t === (sbs' a b s v t ~~~ sbs' a b u v t)) | a <- sorts 
                                                                                                        , b <- sorts
                                                                                                        , let x ~~~ y = (eqR b)!(x,y) ]
               -- -- term substitution
              ++ [ axiom "Subst_Var0"  ( sbs' a a (trm a v) v t === t ) | a <- sorts ]
              ++ [ axiom "Subst_Var1"  ( sbs' a a (trm a w) v t === (trm a w) <-- v =/= w ) | a <- sorts ]
              ++ [ axiom "Subst_Var2"  ( sbs' a b (trm b w) v t === (trm b w) ) | a <- sorts 
                                                                               , b <- sorts 
                                                                               , a /= b     ]
              ++ [ axiom ( "Subst_" ++ show f) ( sbs' a b (f'![ a | (a,_) <- ts ]) v t === f'![ sbs' a srt x v t | (x, srt) <- ts ] ) 
                                                   | b <- sorts
                                                   , a <- sorts
                                                   , decl @ (f, fd) <- declList sgFuns sig
                                                   , let f' = dot f
                                                   , b == fd ^. funSort
                                                   , let ts =  [ Id ("arg" ++ show i) :: VarId | i <- [0..] ] `zip` ( fd ^. funArgs ) ]
              ++ [ axiom ("Subs"++show p)  ( sbs a (p'!xs) v t === p'![ sbs' a b x v t | (x, b) <- xs `zip` bs  ] ) 
              -- ( tr(p'!xs) <-> p![ eval b ! x | (x,b) <- xs `zip` bs ])  
                                                                                  | p_ :::: Pred bs <- toDecls sig 
                                                                                  , a <- sorts
                                                                                  , let xs = take (length bs) infVars
                                                                                  , let p = coerse p_ :: PredId
                                                                                  , let p' = dot p_                ]

              ++ [ axiom ( "eval_" ++ show f) 
                       ( ev a ( f'![ t'          | (t', _   ) <- ts ] ) 
                             === f![ ev b t'  | (t', b) <- ts ] ) | a <- sorts 
                                                                          , decl @ (f, fd) <- declList sgFuns sig
                                                                          , a == fd ^. funSort
                                                                          , let f' = dot f
                                                                          , let ts =  [ Id ("arg" ++ show i) :: VarId | i <- [0..] ] `zip` ( fd ^. funArgs ) ]
               ++ [ axiom ("eval_" ++ show v) undefined | (v, decl) <- declList sgVars sig ]  -- TODO
            where sorts = fmap fst $ declList sgSorts sig
                  nxt s v = nVarR s![to v]

                  eq s a b = eqR s![to a, to b]

                  infVars :: [VarId]
                  infVars = [ Id $ "a" ++ show i | i <- [0..] ]
                  sbs  s = ternary (subsFR  s) 
                  sbs' s t = ternary (subsTR  s t) 
                  forall' s = unary (forallR s) 
                  v0 s      = nullary (v0R s) 
                  ev s x = (eval s)![x]
                  trm s x = vTermR s![x]


                  coerse (Id a) = Id a
                  
                  --
                  -- preds
                  tr      x       = BaseAtom $ BasePred trueR [ to x ]
                  -- consts
                  -- vars
                  not'    :: forall a . ToTerm a => a -> Term
                  not'    = unary notR 
                  axiom n f = Axiom n (universalClosure f)
                  -- a  &  b = andR!(a,b)
                  -- a  ~~>  b = implR!(a,b)
                  bot = botR!()
                  -- variables
                  x   = Id "x"   :: VarId 
                  s   = Id "s"   :: VarId 
                  s'  = Id "s_"  :: VarId 
                  t   = Id "t"   :: VarId 
                  u   = Id "u"   :: VarId 
                  phi = Id "phi" :: VarId 
                  psi = Id "psi" :: VarId 
                  v   = Id "v"   :: VarId 
                  w   = Id "w"   :: VarId 
         
reflSorts :: Sig -> Decls Sort
reflSorts sig = decls $ fmap ( \s -> (s, Sort) ) 
                      $ [term s | (s, _) <- declList sgSorts sig ] 
                     ++ [var  s | (s, _) <- declList sgSorts sig ] 
                     ++ [form] 

  
sig' :: [SymDec] -> [SymDec] 
sig' sig  = sig 

         ++ [ tid ( form   ) :::: Srt               ]
         ++ [ tid ( term s ) :::: Srt  | s <- sorts ]
         ++ [ tid ( var  s ) :::: Srt  | s <- sorts ]

         ++ [ tid ( trueR        ) :::: Pred [form]                                                    ]

         ++ [ tid ( eval    s   ) :::: [term  s] :-> s                   | s <- sorts                 ]

         -- formulas
         ++ [ tid ( dot p       ) :::: [ term a | a <- as ]      :-> form   | p :::: Pred as <- sig   ]
         ++ [ tid ( eqR     s   ) :::: [term  s, term s]         :-> form   | s <- sorts              ]
         ++ [ tid ( notR        ) :::: [form]                    :-> form                             ]
         ++ [ tid ( con         ) :::: [form, form]              :-> form   | (con, _) <- connectives ]
         ++ [ tid ( forallR s   ) :::: [form]                    :-> form   | s <- sorts              ]
         ++ [ tid ( botR        ) :::: []                        :-> form                             ]

         ++ [ tid ( dot f       ) :::: [ term a | a <- as ] :-> term b   | f :::: as :-> b <- sig     ]

         -- variables
         ++ [ tid ( nVarR   s   ) :::: [var   s] :-> var s               | s <- sorts                 ]
         ++ [ tid ( v0R     s   ) :::: [ ]       :-> var s               | s <- sorts                 ]

         -- terms
         ++ [ tid ( vTermR   s  ) :::: [var   s] :-> term s              | s <- sorts                 ]

         -- substitutions
         ++ [ tid ( subsTR  a b ) :::: [term  b, var  a, term a] :-> term b | a <- sorts
                                                                    , b <- sorts              ]

         ++ [ tid ( subsFR  s   ) :::: [form   , var  s, term s] :-> form   | s <- sorts              ]

          where sorts = [ Id s | Id s :::: Srt <- sig ]

reflSig = mkSig . sig' . toDecls

reflective = unwrap . safeReflective

reflectiveWithAxioms :: [Axiom Formula] -> Theory -> Either [String] Theory
reflectiveWithAxioms as th = theory ("Reflective "++ n) (reflSig sig) (a ++ reflAxioms sig ++ as)
  where n   = th ^.thName 
        sig = th ^.thSig 
        a   = ( fromMir <$>) <$> th ^.thAxioms 

safeReflective :: Theory -> Either [String] Theory
safeReflective = reflectiveWithAxioms []
-- safeReflective th = theory ("Reflective "++ n) (reflSig sig) (a ++ reflAxioms sig)
--   where n   = th ^.thName 
--         sig = th ^.thSig 
--         a   = ( fromMir <$>) <$> th ^.thAxioms 
