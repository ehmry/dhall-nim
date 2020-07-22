# SPDX-License-Identifier: MIT

import
  bigints

import
  std / options, std / strutils, std / tables

type
  UniverseKind* = enum
    uType = "Type", uKind = "Kind", uSort = "Sort"
  BuiltinKind* = enum
    bNaturalBuild = "Natural/build", bNaturalFold = "Natural/fold",
    bNaturalIsZero = "Natural/isZero", bNaturalEven = "Natural/even",
    bNaturalOdd = "Natural/odd", bNaturalToInteger = "Natural/toInteger",
    bNaturalShow = "Natural/show", bNaturalSubtract = "Natural/subtract",
    bIntegerDouble = "Integer/toDouble", bIntegerShow = "Integer/show",
    bIntegerNegate = "Integer/negate", bIntegerClamp = "Integer/clamp",
    bDoubleShow = "Double/show", bListBuild = "List/build",
    bListFold = "List/fold", bListLength = "List/length",
    bListHead = "List/head", bListLast = "List/last",
    bListIndexed = "List/indexed", bListReverse = "List/reverse",
    bOptionalBuild = "Optional/build", bOptionalFold = "Optional/fold",
    bTextShow = "Text/show", bBool = "Bool", bOptional = "Optional",
    bNatural = "Natural", bInteger = "Integer", bDouble = "Double",
    bText = "Text", bList = "List", bTrue = "True", bFalse = "False",
    bNone = "None", bType = "Type", bKind = "Kind", bSort = "Sort"
  OpKind* = enum
    opBoolOr = (0, "||"), opBoolAnd = (1, "&&"), opBoolEquality = (2, "=="),
    opBoolInequality = (3, "!="), opNaturalAdd = (4, "+"),
    opNaturalMultiplication = (5, "*"), opTextAppend = (6, "++"),
    opListAppend = (7, "#"), opRecordRecursiveMerge = (8, "∧"),
    opRecordBiasedMerge = (9, "⫽"), opRecordTypeMerge = (10, "⩓"),
    opAlternateImport = (11, "?"), opEquivalience = (12, "≡"),
    opComplete = (13, "::")
  ImportKind* = enum
    iCode = 0, iText = 1, iLocation = 2
  TermKind* = enum
    tApp = 0, tLambda = 1, tPi = 2, tOp = 3, tList = 4, tSome = 5, tMerge = 6,
    tRecordType = 7, tRecordLiteral = 8, tField = 9, tProject = 10,
    tUnionType = 11, tIf = 14, tNaturalLiteral = 15, tIntegerLiteral = 16,
    tTextLiteral = 18, tAssert = 19, tImport = 24, tLet = 25, tAnnotation = 26,
    tToMap = 27, tEmptyList = 28, tVar, tBuiltin, tUniverse, tProjectType,
    tBoolLiteral, tDoubleLiteral, tEntry, tTextChunk, tBinding
  Term* = ref object
    case kind*: TermKind
    of tVar:
        varName*: string
        varIndex*: int

    of tBuiltin:
        builtin*: BuiltinKind

    of tUniverse:
        universe*: UniverseKind

    of tApp:
        appFun*: Term
        appArgs*: seq[Term]

    of tLambda:
        lambdaLabel*: string
        lambdaType*, lambdaBody*: Term

    of tPi:
        piLabel*: string
        piType*, piBody*: Term

    of tOp:
        op*: OpKind
        opL*, opR*: Term

    of tList:
        listType*: Term
        list*: seq[Term]

    of tSome:
        someType*, someVal*: Term

    of tMerge:
        mergeHandler*, mergeUnion*, mergeAnn*: Term

    of tRecordType:
        recordType*: Table[string, Term]

    of tRecordLiteral:
        recordLiteral*: Table[string, Term]

    of tField:
        fieldRecord*: Term
        fieldName*: string

    of tProject:
        projectRecord*: Term
        projectNames*: seq[string]

    of tProjectType:
        projectTypeRecord*: Term
        projectTypeSelector*: Term

    of tUnionType:
        union*: Table[string, Term]

    of tBoolLiteral:
        bool*: bool

    of tIf:
        ifCond*, ifTrue*, ifFalse*: Term

    of tNaturalLiteral:
        natural*: BigInt

    of tIntegerLiteral:
        integer*: BigInt

    of tDoubleLiteral:
        double*: BiggestFloat

    of tTextLiteral:
        textChunks*: seq[Term]
        textSuffix*: string

    of tAssert:
        assertAnn*: Term

    of tImport:
        importCheck*: seq[byte]
        importKind*: ImportKind
        importScheme*: uint8
        importHeaders*: Term
        importElements*: seq[string]
        importQuery*: Option[string]

    of tLet:
        letBinds*: seq[Term]
        letBody*: Term

    of tAnnotation:
        annExpr*, annAnn*: Term

    of tToMap:
        toMapBody*, toMapAnn*: Term

    of tEmptyList:
        emptyListType*: Term

    of tEntry:
        entryKey*: string
        entryVal*: Term

    of tTextChunk:
        textPrefix*: string
        textExpr*: Term

    of tBinding:
        key*: string
        val*, ann*: Term

  
func parseBuiltin*(s: string): BuiltinKind =
  case s
  of "Natural/build":
    bNaturalBuild
  of "Natural/fold":
    bNaturalFold
  of "Natural/isZero":
    bNaturalIsZero
  of "Natural/even":
    bNaturalEven
  of "Natural/odd":
    bNaturalOdd
  of "Natural/toInteger":
    bNaturalToInteger
  of "Natural/show":
    bNaturalShow
  of "Natural/subtract":
    bNaturalSubtract
  of "Integer/toDouble":
    bIntegerDouble
  of "Integer/show":
    bIntegerShow
  of "Integer/negate":
    bIntegerNegate
  of "Integer/clamp":
    bIntegerClamp
  of "Double/show":
    bDoubleShow
  of "List/build":
    bListBuild
  of "List/fold":
    bListFold
  of "List/length":
    bListLength
  of "List/head":
    bListHead
  of "List/last":
    bListLast
  of "List/indexed":
    bListIndexed
  of "List/reverse":
    bListReverse
  of "Optional/build":
    bOptionalBuild
  of "Optional/fold":
    bOptionalFold
  of "Text/show":
    bTextShow
  of "Bool":
    bBool
  of "Optional":
    bOptional
  of "Natural":
    bNatural
  of "Integer":
    bInteger
  of "Double":
    bDouble
  of "Text":
    bText
  of "List":
    bList
  of "True":
    bTrue
  of "False":
    bFalse
  of "None":
    bNone
  of "Type":
    bType
  of "Kind":
    bKind
  of "Sort":
    bSort
  else:
    raise newException(ValueError, "invalid builtin " & s)
