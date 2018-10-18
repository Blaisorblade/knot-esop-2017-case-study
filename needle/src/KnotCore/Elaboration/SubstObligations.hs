
module KnotCore.Elaboration.SubstObligations where

import Coq.StdLib
import Coq.Syntax

import KnotCore.Syntax
import KnotCore.Elaboration.Core

import Control.Applicative

obligations :: Elab m => [EnvDecl] -> [RelationDecl] -> m [Coq.Sentence]
obligations eds rds = sequenceA
  [ eEnvDecl (typeNameOf bv) (typeNameOf ed)
  | ed <- eds
  , EnvCtorCons _cn bv _fds _mbRtn <- edCtors ed
  ]

eEnvDecl :: Elab m => NamespaceTypeName -> EnvTypeName -> m Coq.Sentence


 class SubObligations : Prop :=
   { Sub_var :
       forall G X T, lookup_etvar G X T -> Sub G (tvar X) T;
     subst_etvar_SA_Refl_TVar :
       forall G TX, wfTy (domainEnv G) TX -> Sub G TX TX;
     subst_etvar_SA_Trans_TVar :
       forall G T U TX,
         wfTy (domainEnv G) TX -> Sub G TX U -> Sub G U T -> Sub G TX T
   }.


eWeakenClass :: Elab m => m [Sentence]
eWeakenClass = localNames $
  do
    setA <- freshVariable "A" (TermSort Type)
    a1   <- freshVariable "a" =<< toRef setA
    a2   <- freshVariable "a" =<< toRef setA
    k1   <- freshHVarlistVar
    k2   <- freshHVarlistVar
    append       <- idAppendHVarlist
    weaken       <- idMethodWeaken
    weakenInj    <- idMethodWeakenInj
    weakenAppend <- idMethodWeakenAppend

    declWeaken    <-
      MethodDeclaration weaken
      <$> sequenceA [toBinder a1, toBinder k1]
      <*> toRef setA

    declWeakenInj <-
      MethodDeclaration weakenInj
      <$> sequenceA [toBinder k1, toBinder a1, toBinder a2]
      <*> (TermFunction
           <$> (eq
                <$> (TermApp
                     <$> toRef weaken
                     <*> sequenceA [toRef a1,toRef k1]
                    )
                <*> (TermApp
                     <$> toRef weaken
                     <*> sequenceA [toRef a2,toRef k1]
                    )
               )
           <*> (eq
                <$> toRef a1
                <*> toRef a2
               )
          )

    declWeakenAppend <-
      MethodDeclaration weakenAppend
      <$> sequenceA [toBinder a1, toBinder k1, toBinder k2]
      <*> (eq
           <$> (TermApp
                <$> toRef weaken
                <*> sequenceA
                    [TermApp
                     <$> toRef weaken
                     <*> sequenceA [toRef a1, toRef k1],
                     toRef k2
                    ]
               )
           <*> (TermApp
                <$> toRef weaken
                <*> sequenceA
                    [toRef a1,
                     TermApp
                     <$> toRef append
                     <*> sequenceA [toRef k1, toRef k2]
                    ]
               )
          )

    classDecl <-
      ClassDeclaration
      <$> idClassWeaken
      <*> sequenceA [toBinder setA]
      <*> pure (Just Type)
      <*> pure [declWeaken, {- declWeakenInj, -} declWeakenAppend ]

    return [SentenceClassDecl classDecl]
