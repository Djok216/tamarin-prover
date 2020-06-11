{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- MaNumainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- AC-unification of DH terms using Maude as a backend.
module Term.Maude.Process (
  -- * Handle to a maude process
    MaudeHandle(..)
  , startMaude
  , getMaudeStats

  -- * Unification using Maude
  , unifyViaMaude

  -- * Matching using Maude
  , matchViaMaude

  -- * Variants using Maude
  , variantsViaMaude

  -- * Normalization using Maude
  , normViaMaude

  -- * Managing the persistent Maude process
  , WithMaude
) where

-- import Data.Traversable hiding ( mapM )
import qualified Data.Map as M

import Term.Term
import Term.LTerm
import Term.Rewriting.Definitions
import Term.Maude.Signature
import Term.Maude.Types
import Term.Maude.Parser
import Term.Substitution

-- import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Fresh
import Control.Concurrent
import Control.Exception (onException, evaluate)
import Control.DeepSeq   (rnf)
import Control.Monad.Bind

import qualified Data.ByteString as B
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BC

import System.Process
import System.IO

import Utils.Misc

import Foreign.C.Types
import Foreign.Ptr
import Foreign.Marshal.Array

-- import Extension.Data.Monoid

-- import Debug.Trace


-- Unification using a persistent Maude process
-----------------------------------------------------------------------

-- | A handle to a Maude process. It requires the Maude path for Signatures to
-- be serializable. If we also add the string for the Maude config file, then
-- it would even be serializable on its own.
data MaudeHandle = MaudeHandle { mhFilePath :: FilePath
                               , mhMaudeSig :: MaudeSig
                               , mhProc     :: MVar MaudeProcess }

-- | @getMaudeStats@ returns the maude stats formatted as a string.
getMaudeStats :: MaudeHandle -> IO String
getMaudeStats (MaudeHandle {mhProc = maude}) =
    withMVar maude $ \mp -> do
      let mc = matchCount mp
          uc = unifCount mp
      return $ "Maude has been called "++show (mc+uc)++ " times ("
                 ++show uc++" unifications and "++show mc++" matchings)."

data MaudeProcess = MP {
      mIn        :: !Handle
    , mOut       :: !Handle
    , _mErr      :: !Handle
    , mProc      :: !ProcessHandle
    , unifCount  :: !Int
    , matchCount :: !Int
    , normCount  :: !Int
    , varCount   :: !Int
    }

-- | @startMaude@ starts a new instance of Maude and returns a Handle to it.
startMaude :: FilePath -> MaudeSig -> IO MaudeHandle
startMaude maudePath maudeSig = do
    mv <- newMVar =<< startMaudeProcess maudePath maudeSig
    -- Add a finalizer to the MVar that stops maude.
    _  <- mkWeakMVar mv $ withMVar mv $ \mp -> do
        terminateProcess (mProc mp) <* waitForProcess (mProc mp)      
    -- return the maude handle
    return (MaudeHandle maudePath maudeSig mv)

-- | Start a Maude process.
startMaudeProcess :: FilePath -- ^ Path to Maude
                  -> MaudeSig
                  -> IO (MaudeProcess)
startMaudeProcess maudePath maudeSig = do
    (hin,hout,herr,hproc) <- runInteractiveCommand maudeCmd
    _ <- getToDelim hout
    -- set maude flags
    mapM_ (executeMaudeCommand hin hout) setupCmds
    -- input the maude theory
    executeMaudeCommand hin hout (ppTheory maudeSig)
    return (MP hin hout herr hproc 0 0 0 0)
  where
    maudeCmd
      | dEBUGMAUDE = "sh -c \"tee /tmp/maude.input | "
                     ++ maudePath ++ " -no-tecla -no-banner -no-wrap -batch "
                     ++ "\" | tee /tmp/maude.output"
      | otherwise  =
          maudePath ++ " -no-tecla -no-banner -no-wrap -batch "
    executeMaudeCommand hin hout cmd =
        B.hPutStr hin cmd >> hFlush hin >> getToDelim hout >> return ()
    setupCmds = [ "set show command off .\n"
                , "set show timing off .\n"
                , "set show stats off .\n" ]
    dEBUGMAUDE = envIsSet "DEBUG_MAUDE"



-- | Restart the Maude process on this handle.
restartMaude :: MaudeHandle -> IO ()
restartMaude (MaudeHandle maudePath maudeSig mv) = modifyMVar_ mv $ \mp -> do
    terminateProcess (mProc mp) <* waitForProcess (mProc mp)
    startMaudeProcess maudePath maudeSig

-- | @getToDelim ih@ reads input from @ih@ until the Maude delimitier is encountered.
--   It returns the 'ByteString' up to (not including) the delimiter.
getToDelim :: Handle -> IO ByteString
getToDelim ih =
    go BC.empty
  where
    go !acc = do
        bs <- BC.append acc <$> B.hGetSome ih 8096
        case BC.breakSubstring mDelim bs of
            (before, after) | after == mDelim -> return before
            (_,      after) | after == ""     -> go bs
            _  -> error $ "Too much maude output" ++ BC.unpack bs
    mDelim = "Maude> "

-- | @callMaude cmd@ sends the command @cmd@ to Maude and returns Maude's
-- output up to the next prompt sign.
callMaude :: MaudeHandle
          -> (MaudeProcess -> MaudeProcess) -- ^ Statistics updater.
          -> ByteString -> IO ByteString
callMaude hnd updateStatistics cmd = do
    -- Ensure that the command is fully evaluated and therefore does not depend
    -- on another call to Maude anymore. Otherwise, we could end up in a
    -- deadlock.
    evaluate (rnf cmd)
    -- If there was an exception, then we might be out of sync with the current
    -- persistent Maude process: restart the process.
    (`onException` restartMaude hnd) $ modifyMVar (mhProc hnd) $ \mp -> do
        let inp = mIn  mp
            out = mOut mp
        B.hPut inp cmd
        hFlush  inp
        mp' <- evaluate (updateStatistics mp)
        res <- getToDelim out
        return (mp', res)

-- | Compute a result via Maude.
computeViaMaude ::
       MaudeHandle
    -> (MaudeProcess -> MaudeProcess)                                 -- ^ Update statistics
    -> (a -> BindT (Lit c LVar) MaudeLit Fresh ByteString)            -- ^ Conversion to Maude command
    -> (M.Map MaudeLit (Lit c LVar) -> ByteString -> Either String b) -- ^ Conversion from Maude reply
    -> a
    -> IO b
computeViaMaude hnd updateStats toMaude fromMaude inp = do
    let (cmd, bindings) = runConversion $ toMaude inp
    reply <- callMaude hnd updateStats cmd
    case fromMaude bindings reply of
        Right res -> return res
        Left    e -> fail $ "\ncomputeViaMaude:\nParse error: `" ++ e ++"'"++
                            "\nFor Maude Output: `" ++ BC.unpack reply ++"'"++
                            "\nFor query: `" ++ BC.unpack cmd++"'"

------------------------------------------------------------------------------
-- Unification modulo AC
------------------------------------------------------------------------------

-- | @unifyCmd eqs@ returns the Maude command to solve the unification problem @eqs@.
--   Expects a nonempty list of equations
unifyCmd :: [Equal MTerm] -> ByteString
unifyCmd []  = error "unifyCmd: cannot create cmd for empty list of equations."
unifyCmd eqs =
    "unify in MSG : " <> seqs <> " .\n"
  where
    ppEq (Equal t1 t2) = ppMaude t1 <> " =? " <> ppMaude t2
    seqs = B.intercalate " /\\ " $ map ppEq eqs

getNodeLists 
    :: (IsConst c)
    => VTerm c LVar
    -> ([VTerm c LVar], [VTerm c LVar], [VTerm c LVar])
getNodeLists root = 
  case root of
    (LIT a) -> 
      case a of
        (Con c) -> ([LIT (Con c)], [], [])
        (Var v) -> ([], [LIT (Var v)], [])
    (FAPP x []) -> ([], [], [(FAPP x [])])
    (FAPP x (y:z)) -> (consy ++ consz, varsy ++ varsz, funcsy ++ funcsz)
      where
        (consy, varsy, funcsy) = getNodeLists y
        (consz, varsz, funcsz) = getNodeLists (FAPP x z)

mapConsVarsFuncs
    :: (IsConst c)
    => M.Map (VTerm c LVar) CInt
    -> [VTerm c LVar] -> M.Map (VTerm c LVar) CInt
mapConsVarsFuncs mapper [] = mapper
mapConsVarsFuncs mapper (x:y) = 
    if M.member x mapper2 then mapper2
    else M.insert x map2Size mapper2
  where
    mapper2 = mapConsVarsFuncs mapper y
    map2Size = (fromIntegral (M.size mapper2))

getMapperTerms 
    :: (IsConst c)
    => M.Map (VTerm c LVar) CInt
    -> VTerm c LVar
    -> VTerm c LVar
    -> M.Map (VTerm c LVar) CInt
getMapperTerms mapper root1 root2 = mapConsVarsFuncs mapper $ constList ++ varsList ++ funcsList
  where
    (constList1, varsList1, funcsList1) = getNodeLists root1
    (constList2, varsList2, funcsList2) = getNodeLists root2
    constList = constList1 ++ constList2
    varsList = varsList1 ++ varsList2
    funcsList = funcsList1 ++ funcsList2

getMapper
    :: (IsConst c)
    => [Equal (VTerm c LVar)]
    -> M.Map (VTerm c LVar) CInt
getMapper [] = M.empty
getMapper (x:xs) = 
    getMapperTerms mapper lhs rhs
  where
    lhs = eqLHS x
    rhs = eqRHS x
    mapper = getMapper xs

getTypes
    :: (IsConst c)
    => M.Map CInt (VTerm c LVar)
    -> [CInt]
    -> [CInt]
getTypes _ [] = []
getTypes mapper (-1:y) = -1:(getTypes mapper y)
getTypes mapper (-5:y) = -5:(getTypes mapper y)
getTypes mapper (x:y) = 
  case mapper M.! x of
    (LIT a) -> 
      case a of
        Con _ -> 0:tailTypes
        Var _ -> 1:tailTypes
    (FAPP z []) -> 
      case z of
        NoEq _ -> 2:tailTypes
        AC _ -> 3:tailTypes
        C _ -> 4:tailTypes
        List -> 5:tailTypes
    _ -> error "Something went wrong"
  where
    tailTypes = getTypes mapper y

getPreorder_
    :: (IsConst c)
    => M.Map (VTerm c LVar) CInt
    -> VTerm c LVar
    -> [CInt]
getPreorder_ mapper root =
  case root of
    (LIT a) -> [mapper M.! (LIT a), -1]
    (FAPP x y) -> rootFunc ++ concat childPreorder ++ [-1]
      where
        rootFunc = [mapper M.! (FAPP x [])]
        childPreorder = map (getPreorder_ mapper) y

getSorts
    :: (IsConst c)
    => (c -> LSort)
    -> VTerm c LVar
    -> [CInt]
getSorts sortOfConst root =
    case root of
      (LIT _) -> [encodedSort, -1]
      (FAPP _ y) -> [encodedSort] ++ concat (map (getSorts sortOfConst) y) ++ [-1]
  where
    encodedSort = 
        case sortOfLTerm sortOfConst root of
          LSortPub -> 7
          LSortFresh -> 8
          LSortMsg -> 9
          LSortNode -> 10

-- return ([preoder], [types], [sorts])
getPreorder2
    :: (IsConst c)
    => (c -> LSort)
    -> M.Map (VTerm c LVar) CInt
    -> M.Map CInt (VTerm c LVar)
    -> VTerm c LVar
    -> ([CInt], [CInt], [CInt])
getPreorder2 sortOfConst mapper invMapper root = 
    (preorder, types, sorts)
  where
    preorder = getPreorder_ mapper root
    types = getTypes invMapper preorder
    sorts = getSorts sortOfConst root

getPreorder
    :: (IsConst c)
    => (c -> LSort)
    -> M.Map (VTerm c LVar) CInt
    -> M.Map CInt (VTerm c LVar)
    -> [VTerm c LVar]
    -> ([CInt], [CInt], [CInt])
getPreorder _ _ _ [] = ([], [], [])
getPreorder sortOfConst mapper invMapper (x:xs) = 
    (ans1, ans2, ans3)
  where
    (preorder, types, sorts) = getPreorder2 sortOfConst mapper invMapper x
    (tailPreorder, tailTypes, tailSorts) = getPreorder sortOfConst mapper invMapper xs
    ans1 = preorder ++ [-5] ++ tailPreorder
    ans2 = types ++ [-5] ++ tailTypes
    ans3 = sorts ++ [-5] ++ tailSorts
  
cppFuncCall 
    :: [CInt] -> [CInt] -> [CInt] 
    -> [CInt] -> [CInt] -> [CInt]
    -> IO (Ptr CInt)
cppFuncCall a1 b1 c1 a2 b2 c2 = 
    withArray a1 $ \arr1 ->
      withArray b1 $ \arr2 ->
        withArray c1 $ \arr3 ->
          withArray a2 $ \arr4 ->
            withArray b2 $ \arr5 ->
              withArray c2 $ \arr6 ->
                printSubstitutions len1 arr1 arr2 arr3 len2 arr4 arr5 arr6
  where
    len1 = fromIntegral $ length a1
    len2 = fromIntegral $ length a2

splitSubsts :: CInt -> [CInt] -> [CInt] -> [[CInt]]
splitSubsts _ [] [] = []
splitSubsts _ x [] = [x]
splitSubsts val y (x:xs) =
    if x == val then y : splitSubsts val [] xs
    else splitSubsts val (y ++ [x]) xs

combineTerms :: (VTerm c LVar, [VTerm c LVar]) -> VTerm c LVar
combineTerms (FAPP x _, terms) = FAPP x terms
combineTerms (LIT a, _) = LIT a

constructTermFromPreorder
    :: (IsConst c)
    => M.Map CInt (VTerm c LVar)
    -> [(VTerm c LVar, [VTerm c LVar])]
    -> [CInt]
    -> VTerm c LVar
constructTermFromPreorder _ _ [] = error "Construct Term From Preorder Error"
constructTermFromPreorder _ stk (-1:[]) = combineTerms $ head stk
constructTermFromPreorder mapper [] (x:(-1):_) =
    if M.member x mapper then 
      case M.lookup x mapper of
        (Just a) -> a
        _ -> error "something is wrong"
    else freshVar
  where
    varId = NameId $ show x
    name = show $ Name FreshName varId
    freshVar = LIT $ Var $ LVar name LSortMsg $ toInteger x
constructTermFromPreorder _ (y:[]) (-1:_) = combineTerms y
constructTermFromPreorder mapper stk (-1:xs) = 
    constructTermFromPreorder mapper nstk xs
  where
    (y:ys) = stk
    t = combineTerms y
    (z:zs) = ys
    nstk = (fst z, (snd z) ++ [t]) : zs
constructTermFromPreorder mapper [] (x:xs) = 
    constructTermFromPreorder mapper nstkFAPP xs
  where
    root =
      if M.member x mapper then 
        case M.lookup x mapper of
          (Just a) -> a
          _ -> error "something is wrong"
      else freshVar
    varId = NameId $ show x
    name = show $ Name FreshName varId
    freshVar = LIT $ Var $ LVar name LSortMsg $ toInteger x
    nstkFAPP = [(root, [])]
constructTermFromPreorder mapper stk (x:xs) = 
    case root of
      (LIT _) -> constructTermFromPreorder mapper nstkLIT $ tail xs
      _ -> constructTermFromPreorder mapper nstkFAPP xs
  where
    root =
      if M.member x mapper then 
        case M.lookup x mapper of
          (Just a) -> a
          _ -> error "something is wrong"
      else freshVar
    varId = NameId $ show x
    name = show $ Name FreshName varId
    freshVar = LIT $ Var $ LVar name LSortMsg $ toInteger x
    (y:ys) = stk
    nstkLIT = (fst y, (snd y) ++ [root]) : ys
    nstkFAPP = (root, []) : stk

applyMapper
    :: (IsConst c)
    => M.Map CInt (VTerm c LVar)
    -> [(CInt, [CInt])]
    -> [(LVar, VTerm c LVar)]
applyMapper _ [] = []
applyMapper mapper (x:xs) = 
    (var, term) : applyMapper mapper xs
  where
    var =
      if M.member (fst x) mapper then 
        case M.lookup (fst x) mapper of
          (Just (LIT (Var a))) -> a
          _ -> error "something is wrong"
      else freshVar
    varId = NameId $ show (fst x)
    name = show $ Name FreshName varId
    freshVar = LVar name LSortMsg (toInteger $ fst x)
    term = constructTermFromPreorder mapper [] (snd x)

decodeSubst 
    :: (IsConst c)
    => M.Map CInt (VTerm c LVar) 
    -> [[CInt]]
    -> [(LVar, VTerm c LVar)]
decodeSubst mapper x =
    applyMapper mapper subst
  where
    splitListFunc [] = error "something is wrong"
    splitListFunc (y:ys) = (y, ys)
    subst = map splitListFunc x

-- | @unifyViaMaude hnd eqs@ computes all AC unifiers of @eqs@ using the
--   Maude process @hnd@.
unifyViaMaude
    :: (IsConst c)
    => MaudeHandle
    -> (c -> LSort) -> [Equal (VTerm c LVar)] -> IO [SubstVFresh c LVar]
unifyViaMaude _   _      []  = return [emptySubstVFresh]
unifyViaMaude hnd sortOf eqs = 
  do
    ptrSubstSet <- cppFuncCall lhsPreorder lhsTypes lhsSorts rhsPreorder rhsTypes rhsSorts
    substSetEncoded <- peekArray0 (-4 :: CInt) ptrSubstSet
    let encodedSubstsList = map (splitSubsts (-3 :: CInt) []) $ splitSubsts (-2 :: CInt) [] substSetEncoded
    let listSubst = map (decodeSubst invMapper) encodedSubstsList
    let listVFreshSubst = map substFromListVFresh listSubst
    x <- computeViaMaude hnd incUnifCount toMaude fromMaude eqs
    print "+++++++++++++++++++++++++++++++"
    print $ length listVFreshSubst
    print $ length x
    print "_______________________________"
    --error "ceva"
    return listVFreshSubst
    --return x
  where
    mapper = getMapper eqs
    invMapper = M.fromList $ map (\(x, y) -> (y, x)) $ M.toList mapper
    (lhsPreorder, lhsTypes, lhsSorts) = getPreorder sortOf mapper invMapper $ map (\x -> eqLHS x) eqs
    (rhsPreorder, rhsTypes, rhsSorts) = getPreorder sortOf mapper invMapper $ map (\x -> eqRHS x) eqs
    msig = mhMaudeSig hnd
    toMaude          = fmap unifyCmd . mapM (traverse (lTermToMTerm sortOf))
    fromMaude bindings reply =
        map (msubstToLSubstVFresh bindings) <$> parseUnifyReply msig reply
    incUnifCount mp  = mp { unifCount = 1 + unifCount mp }

------------------------------------------------------------------------------
-- Matching modulo AC
------------------------------------------------------------------------------

-- | @matchCmd p t@ returns the Maude command to match the terms @t@ to the
-- pattern @p@.
matchCmd :: [Equal MTerm] -> ByteString
matchCmd eqs =
    "match in MSG : " <> ppTerms t2s <> " <=? " <> ppTerms t1s <> " .\n"
  where
    (t1s,t2s) = unzip [ (a,b) | Equal a b <- eqs ]
    ppTerms = ppMaude . fAppList

-- | @matchViaMaude (t, p)@ computes a complete set of AC matchers of the term
-- @t@ to the pattern @p@ via Maude.
matchViaMaude :: (IsConst c)
              => MaudeHandle
              -> (c -> LSort)
              -> Match (VTerm c LVar)
              -> IO [Subst c LVar]
matchViaMaude hnd sortOf matchProblem =
    case flattenMatch matchProblem of
      Nothing -> return []
      Just [] -> return [emptySubst]
      Just ms -> computeViaMaude hnd incMatchCount toMaude fromMaude
                                 (uncurry Equal <$> ms)
  where
    msig = mhMaudeSig hnd
    toMaude  = fmap matchCmd . mapM (traverse (lTermToMTerm sortOf))
    fromMaude bindings reply =
        map (msubstToLSubstVFree bindings) <$> parseMatchReply msig reply
    incMatchCount mp = mp { matchCount = 1 + matchCount mp }



------------------------------------------------------------------------------
-- Getting variants
------------------------------------------------------------------------------
variantsCmd :: MTerm -> ByteString
variantsCmd tm = "get variants in MSG : " <> ppMaude tm <> " .\n"

variantsViaMaude :: (IsConst c)
                 => MaudeHandle
                 -> (c -> LSort)
                 -> VTerm c LVar
                 -> IO [SubstVFresh c LVar]
variantsViaMaude hnd sortOf t =
    computeViaMaude hnd incVarCount toMaude fromMaude t
  where
    msig = mhMaudeSig hnd
    toMaude = fmap variantsCmd . (lTermToMTerm sortOf)
    fromMaude bindings reply =
        map (msubstToLSubstVFresh bindings) <$> parseVariantsReply msig reply
    incVarCount mp = mp {varCount = 1 + varCount mp }

------------------------------------------------------------------------------
-- Normalization of terms
------------------------------------------------------------------------------

-- | @normCmd t@ returns the Maude command to normalize the term @t@
-- pattern @p@.
normCmd :: MTerm -> ByteString
normCmd tm = "reduce " <> ppMaude tm <> " .\n"

-- | @normViaMaude t@ normalizes the term t via Maude.
normViaMaude :: (IsConst c)
             => MaudeHandle
             -> (c -> LSort)
             -> VTerm c LVar
             -> IO (VTerm c LVar)
normViaMaude hnd sortOf t =
    computeViaMaude hnd incNormCount toMaude fromMaude t
  where
    msig = mhMaudeSig hnd
    toMaude = fmap normCmd . (lTermToMTerm sortOf)
    fromMaude bindings reply =
        (\mt -> (mTermToLNTerm "z" mt `evalBindT` bindings) `evalFresh` nothingUsed)
            <$> parseReduceReply msig reply
    incNormCount mp = mp { normCount = 1 + normCount mp }


-- Passing the Handle to Maude via a Reader monad
-------------------------------------------------

-- | Values that depend on a 'MaudeHandle'.
type WithMaude = Reader MaudeHandle

foreign import ccall unsafe "CppApi.h"
    printSubstitutions 
        :: CInt -> Ptr CInt -> Ptr CInt -> Ptr CInt 
        -> CInt -> Ptr CInt -> Ptr CInt -> Ptr CInt
        -> IO (Ptr CInt)