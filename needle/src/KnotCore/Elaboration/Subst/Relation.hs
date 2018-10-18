{-# LANGUAGE DataKinds #-}

module KnotCore.Elaboration.Subst.Relation where

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core
import KnotCore.Elaboration.Eq

import Control.Applicative
import Control.Arrow
import Control.Monad ((>=>))
import Data.Maybe
import Data.Traversable (for, traverse, sequenceA)

--------------------------------------------------------------------------------

lemmas :: Elab m => [RelationGroupDecl] -> m [Sentence]
lemmas rgds = concat <$> traverse eRelationGroupDecl rgds

eRelationGroupDecl :: Elab m => RelationGroupDecl -> m [Sentence]
eRelationGroupDecl (RelationGroupDecl (Just _etn) rds) = do
  ntns <- getEnvNamespaces
  for ntns $ \ntn -> do
    bodies <- for rds $ \rd -> localNames $ do
      RelationDecl (Just ev) rtn fds _roots _outputs rules <- freshen rd
      eRelationDecl rtn ev fds rules ntn
    pure (SentenceFixpoint (Fixpoint bodies))
eRelationGroupDecl (RelationGroupDecl Nothing _) = pure []

eRelationDecl :: Elab m => RelationTypeName -> EnvVariable -> [FieldDecl 'WOMV] ->
  [Rule] -> NamespaceTypeName -> m FixpointBody
eRelationDecl rtn ev1 fds rules ntn = localNames $ do
  let etn = typeNameOf ev1
  fds' <- freshen fds
  fs' <- eFieldDeclFields fds'

  jmv <- freshJudgementVariable rtn
  outFnEtns <- lookupRelationOutputs rtn
  outFnEvs <- for outFnEtns $ \(fn,etn) -> (,) fn <$> freshEnvVariable etn

  let jmt = Judgement rtn
              (Just (SymEnvVar ev1))
              (map (fieldDeclToSymbolicField Nil) fds')
              (map (second SymEnvVar) outFnEvs)
  (stn,cn) <- getNamespaceCtor ntn
  subSv <- freshTraceVar ntn
  subSv <- freshSubtreeVar stn
  ev0   <- freshEnvVariable etn
  ev2   <- freshEnvVariable etn

  insert <-
    SubstEnvHyp
      <$> freshHypothesis
      <*> pure (SubstEnv (EVar ev0) (CVar cv) (EVar ev1) (EVar ev2))

  result <-
    TermForall
    <$> sequenceA [toBinder cv, toBinder ev2, toBinder insert]
    <*> toTerm
        (PJudgement
           rtn
           (JudgementEnvTerm (EVar ev2))
           (map (shiftField (CVar cv)) fs')
           (map (EShift' (CVar cv) . EVar . snd) outFnEvs)
        )

  equations <- for rules $ \rule ->
     runElabRuleT
       (eRule rtn cv ev1 ev2 insert rule)
       (makeElabRuleEnv (rulePremises rule))

  FixpointBody
    <$> idLemmaShiftRelation etn ntn rtn
    <*> sequenceA
        (toBinder ev1 :
         eFieldDeclBinders fds' ++
         map (toBinder.snd) outFnEvs ++
         [jvBinder jmv jmt]
        )
    <*> pure Nothing
    <*> pure result
    <*> (TermMatch
         <$> (MatchItem
              <$> toRef jmv
              <*> pure Nothing
              <*> (Just <$> toTerm (PJudgement rtn
                                    JudgementEnvUnderscore
                                    fs' (map (EVar . snd) outFnEvs)))
             )
         <*> pure (Just result)
         <*> pure equations
        )

--------------------------------------------------------------------------------

eRule :: ElabRuleM m => RelationTypeName -> CutoffVar -> EnvVariable -> EnvVariable ->
  InsertEnvHyp -> Rule -> m Equation
eRule rtn cv ev1 ev2 ins r = case r of
  RuleVar cn rmbs etn fv sfs jm -> do
    lkv   <- freshLookupVar (SymEnvVar ev1) fv sfs
    wfs   <- catMaybes <$> traverse (eRuleMetavarWellFormed (Just ev1)) rmbs
    ids1  <- catMaybes <$> traverse eRuleMetavarId rmbs
    ids2  <- sequenceA [toId lkv]
    ids3  <- traverse (toId . snd) wfs

    lemma <- idLemmaInsertLookup etn (typeNameOf cv) (typeNameOf fv)
    proof <- TermApp
               <$> toRef lemma
               <*> sequenceA [toRef ins, toRef lkv]
    shiftedFields <- catMaybes <$> traverse (shiftRuleMetavarBinder cv) rmbs
    shiftedWf     <- traverse (uncurry (shiftWellFormedHyp ins)) wfs

    body <-
      TermApp
      <$> toRef cn
      <*> ((:)
           <$> toRef ev2
           <*> pure (shiftedFields ++ [proof] ++ shiftedWf)
          )

    Equation
      <$> (PatCtor <$> toQualId cn <*> pure (ids1 ++ ids2 ++ ids3))
      <*> (TermAbs
           <$> sequenceA
               [ toBinder cv
               , toBinder ev2
               , toBinder ins
               ]
           <*> pure body
          )


  RuleReg cn rmbs premises (Judgement _ _ sfs outFnSes) outFnRbs -> do

    wfs   <- catMaybes <$> traverse (eRuleMetavarWellFormed (Just ev1)) rmbs

    ids1  <- catMaybes <$> traverse eRuleMetavarId rmbs
    ids2  <- traverse eFormulaId premises
    ids3  <- traverse (toId . snd) wfs

    proofs        <- traverse (eFormulaProof cv ev2 ins) premises
    shiftedFields <- catMaybes <$> traverse (shiftRuleMetavarBinder cv) rmbs
    shiftedWf     <- traverse (uncurry (shiftWellFormedHyp ins)) wfs


    body <-
      TermApp
      <$> toRef cn
      <*> ((:)
           <$> toRef ev2
           <*> pure (shiftedFields ++ proofs ++ shiftedWf)
          )

    eqts   <- map (eqtSimplify . EqtSym)
                <$> sequenceA (eSymbolicFieldEqs (CVar cv) sfs)
    eqOuts <- for outFnRbs $ \(_fn,rbs) ->
                eqeSimplify . EqeSym
                  <$> eqhvlRuleBindSpecShift (CVar cv) (ENil (typeNameOf ev1)) rbs
    fs <- catMaybes <$> traverse symbolicFieldToField sfs

    eqrefl <- toRef (ID "eq_refl")
    cast <-
      if Prelude.all isEqtRefl eqts && Prelude.all isEqeRefl eqOuts
      then pure body
      else
        TermApp
          <$> (idLemmaRelationCast rtn >>= toRef)
          <*> (sequenceA . concat $
               [ [toRef ev2]
               , -- TODO: The first terms are the ones where the meta-variables
                 -- have been substituted for shifted values. We should eventually
                 -- elaborate into those.
                 map (const (pure TermUnderscore)) fs
               , map (const (pure TermUnderscore)) outFnSes
               , [toRef ev2]
               , map (toTerm . shiftField (CVar cv)) fs
               , map (const (pure TermUnderscore)) outFnSes
                 -- map (symbolicEnvToETerm . snd >=> toTerm) outFnSes -- EShift' ?
               , [pure eqrefl]
               , map toTerm eqts
               , map toTerm eqOuts
               , [pure body]
               ]
              )

    Equation
      <$> (PatCtor <$> toQualId cn <*> pure (ids1 ++ ids2 ++ ids3))
      <*> (TermAbs
           <$> sequenceA
               [ toBinder cv
               , toBinder ev2
               , toBinder ins
               ]
           <*> pure cast
          )

--------------------------------------------------------------------------------

shiftRuleMetavarBinder :: ElabRuleM m => CutoffVar -> RuleMetavarBinder -> m (Maybe Term)
shiftRuleMetavarBinder cv (RuleMetavarSort bs sv _ _) =
  Just <$> toTerm (SShift' (CWeaken (CVar cv) (evalBindSpec HV0 bs)) (SVar sv))
shiftRuleMetavarBinder cv (RuleMetavarFree fv _) = do
  iv <- toIndex fv
  Just <$> toTerm (IShift' (CVar cv) (IVar iv))
shiftRuleMetavarBinder _ (RuleMetavarBinding _ _) =
  pure Nothing
shiftRuleMetavarBinder cv (RuleMetavarOutput rbs ev) = do
  delta <- evalRuleBindSpec (ENil (typeNameOf ev)) rbs
  Just <$> toTerm (EShift' (CWeaken (CVar cv) (HVDomainEnv delta)) (EVar ev))

shiftWellFormedHyp :: Elab m => InsertEnvHyp -> BindSpec -> WellFormedHyp -> m Term
shiftWellFormedHyp ins@(InsertEnvHyp _hyp (InsertEnv _c _et1 et2)) bs wf = case wf of
  WellFormedHypSort hyp -> do
    let stn       = typeNameOf hyp
        (ntn,etn) = typeNameOf ins
    call <-
      toTerm $ WellFormedSortShift
        (InsertHvlWeaken (InsertHvlEnv (InsertEnvVar ins)) (evalBindSpec HV0 bs))
        (WellFormedSortVar hyp)

    eqh <-
      eqhSimplify
      <$> (EqhCongAppend (EqhRefl (HVDomainEnv et2))
           <$> (EqhCongAppend (EqhRefl HV0)
                <$> (EqhSym <$> eqhvlEvalBindspecShift ntn bs)
               )
          )

    if isEqhRefl eqh
      then pure call
      else TermApp
           <$> (idLemmaWellFormedTermCast stn >>= toRef)
           <*> sequenceA
               [ pure TermUnderscore
               , pure TermUnderscore
               , pure TermUnderscore
               , pure TermUnderscore
               , toTerm eqh
               , toTerm (EqtRefl stn)
               , pure call
               ]
  WellFormedHypIndex hyp ->
    toTerm $ WellFormedIndexShift
      (InsertHvlWeaken (InsertHvlEnv (InsertEnvVar ins)) (evalBindSpec HV0 bs))
      (WellFormedIndexVar hyp)


eFormulaProof :: ElabRuleM m => CutoffVar -> EnvVariable -> InsertEnvHyp -> Formula -> m Term
eFormulaProof cv _ ins (FormLookup lkv ev mv _)   = do
  lemma <- idLemmaInsertLookup (typeNameOf ev) (typeNameOf cv) (typeNameOf mv)
  TermApp
    <$> toRef lemma
    <*> sequenceA [toRef ins, toRef lkv]
eFormulaProof cv ev2 ins (FormJudgement jmv rbs (Judgement rtn' (Just se1) sfs outFnSes) _fnRbs) = do
  e1  <- symbolicEnvToETerm se1
  let etn = typeNameOf e1

  ex  <- evalRuleBindSpec (ENil etn) rbs
  lem <- idLemmaShiftRelation etn (typeNameOf cv) rtn'

  body <- TermApp
    <$> toRef lem
    <*> (fmap concat . sequenceA $
         [ sequenceA [toTerm e1]
         , traverse symbolicFieldToField sfs
             >>= pure . catMaybes
             >>= traverse toTerm
         , traverse (symbolicEnvToETerm . snd >=> toTerm) outFnSes
         , sequenceA
           [ toRef jmv
           , toTerm . simplifyCutoff $
             CWeaken
             (CVar cv)
             (HVDomainEnv ex)
           , toTerm $ EAppend (EVar ev2) (EShift' (CVar cv) ex) -- TODO: Weaken cv?
           , toTerm $ InsertEnvWeaken (InsertEnvVar ins) ex
           ]
         ]
        )

  eqrefl <- toRef (ID "eq_refl")

  eqe <- eqeSimplify . EqeCongAppend (EqeRefl (EVar ev2))
          <$> eqhvlRuleBindSpecShift (CVar cv) (ENil (typeNameOf ev2)) rbs
  eqh <- eqhvlRuleBindSpecDomain etn rbs
  eqts <-
      map (\eqt ->eqtSimplify $
               EqtTrans
                 (EqtCongShift
                   (EqcCongWeaken (EqcRefl (typeNameOf cv)) eqh)
                   (EqtRefl (typeNameOf eqt))
                 )
                 eqt
          ) <$> sequenceA (eSymbolicFieldEqs (CVar cv) sfs)
  fs <- catMaybes <$> traverse symbolicFieldToField sfs

  if isEqeRefl eqe && Prelude.all isEqtRefl eqts
    then pure body
    else TermApp
         <$> (idLemmaRelationCast rtn' >>= toRef)
         <*> (sequenceA . concat $
              [ [pure TermUnderscore]
              , -- TODO: The first terms are the ones where the meta-variables
                -- have been substituted for shifted values. We should eventually
                -- elaborate into those.
                map (const (pure TermUnderscore)) fs
              , map (const (pure TermUnderscore)) outFnSes
              , [pure TermUnderscore]
              , map (const (pure TermUnderscore)) fs
              , map (const (pure TermUnderscore)) outFnSes
                -- map (symbolicEnvToETerm . snd >=> toTerm) outFnSes -- EShift' ?
              , [toTerm eqe]
              , map toTerm eqts
              , map (const (pure eqrefl)) outFnSes
              , [pure body]
              ]
             )

eFormulaProof _ _ _ (FormJudgement _ _ (Judgement _ Nothing _ _) _) =
  error "NOT IMPLEMENTED: Shift.Relation.eFormula"

--------------------------------------------------------------------------------

eSymbolicTermEq :: Elab m => Cutoff -> SymbolicTerm -> m EqTerm
eSymbolicTermEq _ (SymSubtree _ sv)            = pure (EqtRefl (typeNameOf sv))
eSymbolicTermEq _ (SymCtorVarFree _ cn _)      = EqtRefl <$> getCtorSort cn
eSymbolicTermEq _ (SymCtorVarBound _ cn _ _ _) = EqtRefl <$> getCtorSort cn
eSymbolicTermEq c (SymCtorReg _ cn sfs) =
  EqtCongCtor
    <$> getCtorSort cn
    <*> pure cn
    <*> sequenceA (eSymbolicFieldEqs c sfs)
eSymbolicTermEq c (SymWeaken _ _ st bs)      = do
  st'  <- symbolicTermToSTerm st
  EqtTrans
    <$> pure (EqtSym (EqtCommWeakenShift (evalBindSpec HV0 bs) c st'))
    <*> (EqtCongWeaken
         <$> eSymbolicTermEq c st
         <*> (EqhCongAppend
              <$> pure (EqhRefl HV0)
              <*> (EqhSym <$> eqhvlEvalBindspecShift (typeNameOf c) bs)
             )
        )
eSymbolicTermEq c (SymSubst _ mv st ste)   = do
  ste' <- symbolicTermToSTerm ste
  st'  <- symbolicTermToSTerm st
  deps <- getSortNamespaceDependencies (typeNameOf ste')
  if (typeNameOf c `elem` deps) && (typeNameOf mv `elem` deps)
    then pure (EqtCommShiftSubst0 ste' c (typeNameOf mv) st')
    else pure (EqtRefl (typeNameOf ste'))

eSymbolicFieldEqs :: Elab m => Cutoff -> [SymbolicField w] -> [m EqTerm]
eSymbolicFieldEqs c = mapMaybe (eSymbolicFieldEq c)

eSymbolicFieldEq :: Elab m => Cutoff -> SymbolicField w -> Maybe (m EqTerm)
eSymbolicFieldEq c (SymFieldSort _scp bs st)  =
  Just (eSymbolicTermEq (CWeaken c (evalBindSpec HV0 bs)) st)
eSymbolicFieldEq _c (SymFieldEnv _scp _bs _se)  = error "NOT IMPLEMENTED"
eSymbolicFieldEq _c (SymFieldBinding{}) = Nothing
eSymbolicFieldEq _c (SymFieldReferenceFree{}) = error "NOT IMPLEMENTED"
eSymbolicFieldEq _c (SymFieldReferenceBound{}) = error "NOT IMPLEMENTED"
