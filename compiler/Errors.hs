-- Errors emitted during parsing or typechecking
module Errors where

import Src
import JavaUtils
import PrettyUtils

import Text.PrettyPrint.ANSI.Leijen

import Control.Monad.Error

data TypeError
  = General Doc
  | ConflictingDefinitions Name
  | ExpectJClass
  | IndexTooLarge
  | TypeMismatch Type Type
  | KindMismatch Kind Kind
  | MissingRHSAnnot
  | NotInScope Name
  | ProjectionOfNonTupleType
  | NotWellKinded Type
  | NotMember Name Type
  | NotAFunction Type

  -- Java-specific type errors
  | NoSuchClass       ClassName
  | NoSuchConstructor ClassName [ClassName]
  | NoSuchMethod      (JReceiver ClassName) MethodName [ClassName]
  | NoSuchField       (JReceiver ClassName) FieldName
  deriving (Show)

instance Pretty TypeError where
  pretty (General doc)      = prettyError <+> doc
  pretty (NotInScope x)  = prettyError <+> code (text x) <+> text "is not in scope"
  pretty (NotWellKinded t)  = prettyError <+> code (pretty t) <+> text "is not well-kinded"
  pretty (KindMismatch expected actual) =
    prettyError <+> text "kind mismatch" <> colon <$>
    indent 2 (text "expected:" <+> code (pretty expected) <$>
              text "  actual:" <+> code (pretty actual))
  pretty (TypeMismatch expected actual) =
    prettyError <+> text "type mismatch" <> colon <$>
    indent 2 (text "expected:" <+> code (pretty expected) <$>
              text "  actual:" <+> code (pretty actual))

  pretty (NoSuchClass c)  = prettyError <+> text "no such class:" <+> code (text c)
  pretty (NotMember x t)  = prettyError <+> code (text x) <+> text "is not a member of the type" <+> code (pretty t)
  pretty (NotAFunction t) = prettyError <+> code (pretty t) <+> text "is not a function; it cannot be applied"

  -- Java-specific type errors
  pretty (NoSuchMethod (NonStatic c) m cs) =
    prettyError <+> text "no such method" <+> code (text m) <+>
    text "on" <+> code (pretty (JType (JClass c))) <+>
    text "with parameters of type" <+> commas (map (code . pretty . JType . JClass) cs)
  pretty (NoSuchMethod (Static c) m cs) =
    prettyError <+> text "no such static method" <+> code (text m) <+>
    text "on" <+> code (pretty (JType (JClass c))) <+>
    text "with parameters of type" <+> commas (map (code . pretty . JType . JClass) cs)

  pretty (NoSuchField (NonStatic c) f) =
    prettyError <+> text "no such field" <+> code (text f) <+>
    text "on" <+> code (pretty (JType (JClass c)))
  pretty (NoSuchField (Static c) f) =
    prettyError <+> text "no such static field" <+> code (text f) <+>
    text "on" <+> code (pretty (JType (JClass c)))

  pretty e = prettyError <+> text (show e)

instance Error TypeError where
  -- strMsg
