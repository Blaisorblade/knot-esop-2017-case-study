
module KnotCore.Elaboration.Shift where

import Control.Applicative
import Coq.Syntax

import KnotCore.Syntax

import KnotCore.Elaboration.Monad
import KnotCore.Elaboration.Shift.Cutoff
import KnotCore.Elaboration.Shift.ShiftIndex
import KnotCore.Elaboration.Shift.ShiftTerm

eShift :: Elab m => TermSpec -> m Sentences
eShift ts =
  concat <$> sequenceA
    [ eCutoff (tsNamespaceDecls ts),
      traverse eShiftIndex (tsNamespaceDecls ts),
      eSortGroupDecls (tsSortGroupDecls ts)
    ]
