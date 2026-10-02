-- Author: Jesse Comer
import Whiel.Guard.Syntax
import Whiel.Concrete.Data

/-
  Restricted surface parsing for submitted Framework-II
  clauses.

  `SurfaceParser.parse` accepts a relation-name codec and
  constructs the existing proof-free `RawGuard` syntax. It
  does not invoke Lean's term parser or elaborator.
  The parser imposes no bound of its own on what may be
  submitted: `Limits` is absent by default and, when a run
  sets the host limit `clause_text_bytes`, carries exactly
  that. Recursive-descent work is guarded by a fuel derived
  from the token count, which no submitted clause can reach.

  Key declarations include:
    * `Whiel.Synthesis.FrameworkII.SurfaceParser.Limits`
    * `Whiel.Synthesis.FrameworkII.SurfaceParser.Error`
    * `Whiel.Synthesis.FrameworkII.SurfaceParser.parse`
    * `SurfaceParser.parseWithLimits`
-/

------------------------------------------------------------
-- Public Results
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace SurfaceParser

open Concrete

/- Name parsing supplied by one concrete carrier. -/
class NameCodec (A : Type) where
  parseName : String -> Except String A
  emptyName? : Option A := none

/- One proof-free submitted clause over a name carrier. -/
abbrev Clause (A : Type) [RelationNames A] :=
  RawGuard A Data

/-
  Optional host bounds for one parse.

  Both fields are absent by default, and absent means
  unbounded: the parser applies no bound of its own to what
  a proposer may submit. A run that sets the host limit
  `clause_text_bytes` passes it here through
  `Limits.ofClauseTextBytes?`, which drives both fields from
  that one value. Reaching either bound is a disagreement
  with the host, which refuses an oversized clause before it
  is ever submitted, and never a defect of the clause.
-/
structure Limits where
  maxChars? : Option Nat := none
  maxTokens? : Option Nat := none
deriving DecidableEq, Repr

/-
  The parse bounds one host `clause_text_bytes` limit
  induces.

  A character occupies at least one UTF-8 byte and a token
  consumes at least one character, so the byte budget bounds
  both counts. The derivation is deliberately conservative:
  it can only ever admit input the host already admitted.
-/
def Limits.ofClauseTextBytes? : Option Nat -> Limits
| none => {}
| some bytes => { maxChars? := some bytes, maxTokens? := some bytes }

/- Closed classes of parser failure. -/
inductive ErrorKind where
| inputLimit
| tokenLimit
| lexical
| syntax
| parserFuel
deriving DecidableEq, Repr

/- One sanitized failure at a character offset. -/
structure Error where
  kind : ErrorKind
  offset : Nat
  message : String
deriving DecidableEq, Repr

/- Render one failure without including submitted text. -/
def Error.pretty (error : Error) : String :=
  "at character " ++ toString error.offset ++
    ": " ++ error.message

end SurfaceParser
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Lexical Tokens
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace SurfaceParser

private inductive TokenKind where
| leftParen
| rightParen
| leftBracket
| rightBracket
| leftBrace
| rightBrace
| comma
| hash
| equal
| top
| empty
| select
| project
| product
| union
| difference
| subset
| notEqual
| conjunction
| disjunction
| negation
| number (value : Nat)
| string (value : String)
| identifier (value : String)
deriving DecidableEq, Repr

private structure Token where
  kind : TokenKind
  offset : Nat
deriving DecidableEq, Repr

private inductive LexerMode where
| ready
| identifier (start : Nat) (charsRev : List Char)
| number (start : Nat) (value : Nat)
| string (start : Nat) (charsRev : List Char)
| escape
    (start escapeOffset : Nat)
    (charsRev : List Char)
| hexSecond
    (start escapeOffset first : Nat)
    (charsRev : List Char)
deriving Repr

private structure LexerState where
  mode : LexerMode := .ready
  tokensRev : List Token := []
  remainingTokens? : Option Nat

private def lexicalError
    (offset : Nat)
    (message : String) : Error :=
  { kind := .lexical
    offset := offset
    message := message }

private def LexerState.emit
    (state : LexerState)
    (kind : TokenKind)
    (offset : Nat) : Except Error LexerState :=
  match state.remainingTokens? with
  | none =>
      .ok
        { state with
          tokensRev := { kind, offset } :: state.tokensRev }
  | some 0 =>
      .error
        { kind := .tokenLimit
          offset := offset
          message := "token limit exceeded" }
  | some (remaining + 1) =>
      .ok
        { state with
          tokensRev := { kind, offset } :: state.tokensRev
          remainingTokens? := some remaining }

private def isDigit (c : Char) : Bool :=
  '0' <= c && c <= '9'

private def digitValue (c : Char) : Nat :=
  c.toNat - '0'.toNat

private def isIdentifierRest (c : Char) : Bool :=
  c.isAlpha || isDigit c || c = '_' || c = '∞'

private def hexValue? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then
    some (c.toNat - '0'.toNat)
  else if 'a' <= c && c <= 'f' then
    some (10 + c.toNat - 'a'.toNat)
  else if 'A' <= c && c <= 'F' then
    some (10 + c.toNat - 'A'.toNat)
  else
    none

private def simpleToken? (c : Char) : Option TokenKind :=
  match c with
  | '(' => some .leftParen
  | ')' => some .rightParen
  | '[' => some .leftBracket
  | ']' => some .rightBracket
  | '{' => some .leftBrace
  | '}' => some .rightBrace
  | ',' => some .comma
  | '#' => some .hash
  | '=' => some .equal
  | '⊤' => some .top
  | '∅' => some .empty
  | 'σ' => some .select
  | 'π' => some .project
  | '×' => some .product
  | '∪' => some .union
  | '∖' => some .difference
  | '⊆' => some .subset
  | '≠' => some .notEqual
  | '∧' => some .conjunction
  | '∨' => some .disjunction
  | '¬' => some .negation
  | _ => none

private def consumeReady
    (state : LexerState)
    (offset : Nat)
    (c : Char) : Except Error LexerState :=
  if c.isWhitespace then
    .ok state
  else if c.isAlpha || c = '_' || c = '∞' then
    .ok
      { state with
        mode := .identifier offset [c] }
  else if isDigit c then
    .ok
      { state with
        mode := .number offset (digitValue c) }
  else if c = '"' then
    .ok
      { state with
        mode := .string offset [] }
  else
    match simpleToken? c with
    | some kind => state.emit kind offset
    | none =>
        .error
          (lexicalError offset
            "unsupported surface character")

private def finishIdentifier
    (state : LexerState)
    (start : Nat)
    (charsRev : List Char) :
    Except Error LexerState :=
  state.emit
    (.identifier (String.ofList charsRev.reverse))
    start

private def finishLexer
    (state : LexerState)
    (_endOffset : Nat) : Except Error (List Token) := do
  let state <-
    match state.mode with
    | .ready => .ok state
    | .identifier start charsRev =>
        finishIdentifier
          { state with mode := .ready }
          start charsRev
    | .number start value =>
        ({ state with mode := .ready }).emit
          (.number value) start
    | .string start _ =>
        .error
          (lexicalError start
            "unterminated string literal")
    | .escape _ escapeOffset _ =>
        .error
          (lexicalError escapeOffset
            "unterminated string escape")
    | .hexSecond _ escapeOffset _ _ =>
        .error
          (lexicalError escapeOffset
            "incomplete hexadecimal string escape")
  pure state.tokensRev.reverse

private def lexChars :
    List Char -> Nat -> LexerState ->
      Except Error (List Token)
  | [], offset, state => finishLexer state offset
  | c :: chars, offset, state => do
      let next <-
        match state.mode with
        | .ready => consumeReady state offset c
        | .identifier start charsRev =>
            if isIdentifierRest c then
              .ok
                { state with
                  mode := .identifier start
                    (c :: charsRev) }
            else do
              let emitted <- finishIdentifier
                { state with mode := .ready }
                start charsRev
              consumeReady emitted offset c
        | .number start value =>
            if isDigit c then
              .ok
                { state with
                  mode := .number start
                    (10 * value + digitValue c) }
            else if c.isAlpha || c = '_' then
              .error
                (lexicalError offset
                  "numeric literal must be delimited")
            else do
              let emitted <-
                ({ state with mode := .ready }).emit
                  (.number value) start
              consumeReady emitted offset c
        | .string start charsRev =>
            if c = '"' then
              ({ state with mode := .ready }).emit
                (.string
                  (String.ofList charsRev.reverse))
                start
            else if c = '\\' then
              .ok
                { state with
                  mode := .escape start offset charsRev }
            else if c.toNat <= 31 || c.toNat = 127 then
              .error
                (lexicalError offset
                  "control character must be escaped")
            else
              .ok
                { state with
                  mode := .string start
                    (c :: charsRev) }
        | .escape start escapeOffset charsRev =>
            let escaped? :=
              if c = 'n' then some '\n'
              else if c = 't' then some '\t'
              else if c = '\\' then some '\\'
              else if c = '"' then some '"'
              else none
            match escaped? with
            | some escaped =>
                .ok
                  { state with
                    mode := .string start
                      (escaped :: charsRev) }
            | none =>
                if c = 'x' then
                  .ok
                    { state with
                      mode := .hexSecond start
                        escapeOffset 256 charsRev }
                else
                  .error
                    (lexicalError escapeOffset
                      "unsupported string escape")
        | .hexSecond start escapeOffset first
            charsRev =>
            match hexValue? c with
            | none =>
                .error
                  (lexicalError offset
                    "expected hexadecimal digit")
            | some value =>
                if first = 256 then
                  .ok
                    { state with
                      mode := .hexSecond start
                        escapeOffset value charsRev }
                else
                  .ok
                    { state with
                      mode := .string start
                        (Char.ofNat (16 * first + value) ::
                          charsRev) }
      lexChars chars (offset + 1) next

private def withinLimit : Nat -> List Char -> Bool
  | _, [] => true
  | 0, _ :: _ => false
  | limit + 1, _ :: chars => withinLimit limit chars

private def tokenize
    (limits : Limits)
    (text : String) : Except Error (List Token) :=
  let chars := text.toList
  match limits.maxChars? with
  | some maxChars =>
      if withinLimit maxChars chars then
        lexChars chars 0
          { remainingTokens? := limits.maxTokens? }
      else
        .error
          { kind := .inputLimit
            offset := maxChars
            message := "character limit exceeded" }
  | none =>
      lexChars chars 0
        { remainingTokens? := limits.maxTokens? }

end SurfaceParser
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Parser Support
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace SurfaceParser

open Concrete

private abbrev RelExpr
    (A : Type) [RelationNames A] :=
  RawRAExpr A Data

private abbrev Selection := Sel Data

private structure Cursor where
  tokens : List Token
  endOffset : Nat

private abbrev Parsed (alpha : Type) :=
  alpha × Cursor

private def Cursor.offset (cursor : Cursor) : Nat :=
  match cursor.tokens with
  | [] => cursor.endOffset
  | token :: _ => token.offset

private def syntaxError
    (cursor : Cursor)
    (message : String) : Error :=
  { kind := .syntax
    offset := cursor.offset
    message := message }

private def fuelError (cursor : Cursor) : Error :=
  { kind := .parserFuel
    offset := cursor.offset
    message := "parser fuel exhausted" }

private def Error.isResource (error : Error) : Bool :=
  error.kind = .parserFuel

private def preferError
    (first second : Error) : Error :=
  if first.isResource then
    first
  else if second.isResource then
    second
  else if second.offset < first.offset then
    first
  else
    second

private def takeToken
    (cursor : Cursor) : Option (Token × Cursor) :=
  match cursor.tokens with
  | [] => none
  | token :: tokens =>
      some (token, { cursor with tokens := tokens })

private def tokenMatches
    (expected actual : TokenKind) : Bool :=
  match expected, actual with
  | .leftParen, .leftParen
  | .rightParen, .rightParen
  | .leftBracket, .leftBracket
  | .rightBracket, .rightBracket
  | .leftBrace, .leftBrace
  | .rightBrace, .rightBrace
  | .comma, .comma
  | .hash, .hash
  | .equal, .equal
  | .top, .top
  | .empty, .empty
  | .select, .select
  | .project, .project
  | .product, .product
  | .union, .union
  | .difference, .difference
  | .subset, .subset
  | .notEqual, .notEqual
  | .conjunction, .conjunction
  | .disjunction, .disjunction
  | .negation, .negation => true
  | _, _ => false

private def hasToken
    (cursor : Cursor)
    (kind : TokenKind) : Bool :=
  match cursor.tokens with
  | [] => false
  | token :: _ => tokenMatches kind token.kind

private def expect
    (cursor : Cursor)
    (kind : TokenKind)
    (description : String) :
    Except Error (Parsed Unit) :=
  match takeToken cursor with
  | some (token, rest) =>
      if tokenMatches kind token.kind then
        .ok ((), rest)
      else
        .error
          (syntaxError cursor
            ("expected " ++ description))
  | none =>
      .error
        (syntaxError cursor
          ("expected " ++ description))

private def parseNumber
    (cursor : Cursor) : Except Error (Parsed Nat) :=
  match takeToken cursor with
  | some ({ kind := .number value, .. }, rest) =>
      .ok (value, rest)
  | _ =>
      .error
        (syntaxError cursor
          "expected natural-number literal")

private def parseData
    (cursor : Cursor) : Except Error (Parsed Data) :=
  match takeToken cursor with
  | some ({ kind := .number value, .. }, rest) =>
      .ok (.num value, rest)
  | some ({ kind := .string value, .. }, rest) =>
      .ok (.str value, rest)
  | some ({ kind := .identifier "true", .. }, rest) =>
      .ok (.bool true, rest)
  | some ({ kind := .identifier "false", .. }, rest) =>
      .ok (.bool false, rest)
  | _ =>
      .error
        (syntaxError cursor
          "expected number, string, or Boolean literal")

private def parseRelationName
    {A : Type}
    [RelationNames A]
    [NameCodec A]
    (cursor : Cursor) :
    Except Error (Parsed A) :=
  match takeToken cursor with
  | some ({ kind := .identifier raw, .. }, rest) =>
      match NameCodec.parseName raw with
      | .ok name => .ok (name, rest)
      | .error message =>
          .error (syntaxError cursor message)
  | _ =>
      .error
        (syntaxError cursor "expected relation name")

private inductive Comparator where
| equal
| subset
| notEqual

private def parseComparator
    (cursor : Cursor) :
    Except Error (Parsed Comparator) :=
  match takeToken cursor with
  | some ({ kind := .equal, .. }, rest) =>
      .ok (.equal, rest)
  | some ({ kind := .subset, .. }, rest) =>
      .ok (.subset, rest)
  | some ({ kind := .notEqual, .. }, rest) =>
      .ok (.notEqual, rest)
  | _ =>
      .error
        (syntaxError cursor
          "expected =, ⊆, or ≠")

/- Tokens that force a preceding primary into RA context. -/
private def startsRelationalContinuation
    (cursor : Cursor) : Bool :=
  hasToken cursor .equal ||
    hasToken cursor .subset ||
    hasToken cursor .notEqual ||
    hasToken cursor .product ||
    hasToken cursor .union ||
    hasToken cursor .difference

/-
  Delimiters at which the empty-base relation's printer has
  emitted no characters for one expected RA primary.
-/
private def startsEmptyRelation
    (cursor : Cursor) : Bool :=
  match cursor.tokens with
  | [] => true
  | token :: _ =>
      tokenMatches .equal token.kind ||
        tokenMatches .subset token.kind ||
        tokenMatches .notEqual token.kind ||
        tokenMatches .product token.kind ||
        tokenMatches .union token.kind ||
        tokenMatches .difference token.kind ||
        tokenMatches .rightParen token.kind ||
        tokenMatches .conjunction token.kind ||
        tokenMatches .disjunction token.kind

end SurfaceParser
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Recursive-Descent Grammar
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace SurfaceParser

open Concrete

variable {A : Type}
variable [RelationNames A] [NameCodec A]

private def comparison
    (operator : Comparator)
    (left right : Option (RelExpr A)) :
    Option (Clause A) :=
  let positive :=
    match operator, left, right with
    | .equal, some left, some right =>
        some (.eq left right)
    | .equal, some left, none =>
        some (.eqEmptyRight left)
    | .equal, none, some right =>
        some (.eqEmptyLeft right)
    | .subset, some left, some right =>
        some (.subset left right)
    | .subset, some left, none =>
        some (.subsetEmptyRight left)
    | .subset, none, some right =>
        some (.subsetEmptyLeft right)
    | .notEqual, some left, some right =>
        some (.eq left right)
    | .notEqual, some left, none =>
        some (.eqEmptyRight left)
    | .notEqual, none, some right =>
        some (.eqEmptyLeft right)
    | _, none, none => none
  match operator, positive with
  | .notEqual, some formula => some (.not formula)
  | _, result => result

mutual
  private def parseGuardOr :
      Nat -> Cursor -> Except Error (Parsed (Clause A))
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor => do
        let (left, rest) <- parseGuardAnd fuel cursor
        parseGuardOrTail fuel left rest

  private def parseGuardOrTail :
      Nat -> Clause A -> Cursor ->
        Except Error (Parsed (Clause A))
    | 0, _, cursor => .error (fuelError cursor)
    | fuel + 1, left, cursor =>
        if hasToken cursor .disjunction then do
          let (_, afterOperator) <-
            expect cursor .disjunction "∨"
          let (right, rest) <-
            parseGuardAnd fuel afterOperator
          parseGuardOrTail fuel (.or left right) rest
        else
          .ok (left, cursor)

  private def parseGuardAnd :
      Nat -> Cursor -> Except Error (Parsed (Clause A))
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor => do
        let (left, rest) <- parseGuardUnary fuel cursor
        parseGuardAndTail fuel left rest

  private def parseGuardAndTail :
      Nat -> Clause A -> Cursor ->
        Except Error (Parsed (Clause A))
    | 0, _, cursor => .error (fuelError cursor)
    | fuel + 1, left, cursor =>
        if hasToken cursor .conjunction then do
          let (_, afterOperator) <-
            expect cursor .conjunction "∧"
          let (right, rest) <-
            parseGuardUnary fuel afterOperator
          parseGuardAndTail fuel (.and left right) rest
        else
          .ok (left, cursor)

  private def parseGuardUnary :
      Nat -> Cursor -> Except Error (Parsed (Clause A))
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor =>
        if hasToken cursor .negation then do
          let (_, rest) <- expect cursor .negation "¬"
          let (formula, afterFormula) <-
            parseGuardUnary fuel rest
          .ok (.not formula, afterFormula)
        else
          parseGuardPrimary fuel cursor

  private def parseGuardPrimary :
      Nat -> Cursor -> Except Error (Parsed (Clause A))
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor =>
        match cursor.tokens with
        | { kind := .identifier "true", .. } :: tokens =>
            let rest := { cursor with tokens := tokens }
            if startsRelationalContinuation rest then
              parseGuardAtom fuel cursor
            else
              .ok (.«true», rest)
        | { kind := .identifier "false", .. } :: tokens =>
            let rest := { cursor with tokens := tokens }
            if startsRelationalContinuation rest then
              parseGuardAtom fuel cursor
            else
              .ok (.«false», rest)
        | { kind := .leftParen, .. } :: _ =>
            let grouped :
                Except Error (Parsed (Clause A)) := do
              let (_, afterOpen) <-
                expect cursor .leftParen "("
              let (formula, afterFormula) <-
                parseGuardOr fuel afterOpen
              let (_, rest) <-
                expect afterFormula .rightParen ")"
              .ok (formula, rest)
            match grouped with
            | .ok (formula, rest) =>
                if startsRelationalContinuation rest then
                  parseGuardAtom fuel cursor
                else
                  .ok (formula, rest)
            | .error groupedError =>
                if groupedError.isResource then
                  .error groupedError
                else
                  match parseGuardAtom fuel cursor with
                  | .ok result => .ok result
                  | .error atomError =>
                      .error
                        (preferError groupedError atomError)
        | _ => parseGuardAtom fuel cursor

  private def parseGuardAtom :
      Nat -> Cursor -> Except Error (Parsed (Clause A))
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor => do
        let (left, afterLeft) <-
          parseMaybeBareEmpty fuel cursor
        let (comparator, afterComparator) <-
          parseComparator afterLeft
        let (right, rest) <-
          parseMaybeBareEmpty fuel afterComparator
        match comparison comparator left right with
        | some formula => .ok (formula, rest)
        | none =>
            .error
              (syntaxError cursor
                "both operands cannot be bare empty")

  private def parseMaybeBareEmpty :
      Nat -> Cursor ->
        Except Error (Parsed (Option (RelExpr A)))
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor =>
        match cursor.tokens with
        | { kind := .empty, .. } :: next :: tokens =>
            if tokenMatches .leftBracket next.kind then
              let parsed := parseRelUnion fuel cursor
              parsed.map fun (formula, rest) =>
                (some formula, rest)
            else
              .ok
                (none,
                  { cursor with tokens := next :: tokens })
        | [{ kind := .empty, .. }] =>
            .ok (none, { cursor with tokens := [] })
        | _ =>
            let parsed := parseRelUnion fuel cursor
            parsed.map fun (formula, rest) =>
              (some formula, rest)

  private def parseRelUnion :
      Nat -> Cursor -> Except Error (Parsed (RelExpr A))
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor => do
        let (left, rest) <- parseRelProduct fuel cursor
        parseRelUnionTail fuel left rest

  private def parseRelUnionTail :
      Nat -> RelExpr A -> Cursor ->
        Except Error (Parsed (RelExpr A))
    | 0, _, cursor => .error (fuelError cursor)
    | fuel + 1, left, cursor =>
        if hasToken cursor .union then do
          let (_, afterOperator) <-
            expect cursor .union "∪"
          let (right, rest) <-
            parseRelProduct fuel afterOperator
          parseRelUnionTail fuel (.union left right) rest
        else if hasToken cursor .difference then do
          let (_, afterOperator) <-
            expect cursor .difference "∖"
          let (right, rest) <-
            parseRelProduct fuel afterOperator
          parseRelUnionTail fuel (.diff left right) rest
        else
          .ok (left, cursor)

  private def parseRelProduct :
      Nat -> Cursor -> Except Error (Parsed (RelExpr A))
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor => do
        let (left, rest) <- parseRelPrefix fuel cursor
        parseRelProductTail fuel left rest

  private def parseRelProductTail :
      Nat -> RelExpr A -> Cursor ->
        Except Error (Parsed (RelExpr A))
    | 0, _, cursor => .error (fuelError cursor)
    | fuel + 1, left, cursor =>
        if hasToken cursor .product then do
          let (_, afterOperator) <-
            expect cursor .product "×"
          let (right, rest) <-
            parseRelPrefix fuel afterOperator
          parseRelProductTail fuel (.prod left right) rest
        else
          .ok (left, cursor)

  private def parseRelPrefix :
      Nat -> Cursor -> Except Error (Parsed (RelExpr A))
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor =>
        if hasToken cursor .select then do
          let (_, afterSelect) <-
            expect cursor .select "σ"
          let (_, afterOpen) <-
            expect afterSelect .leftBracket "["
          let (selection, afterSelection) <-
            parseSelectionOr fuel afterOpen
          let (_, afterClose) <-
            expect afterSelection .rightBracket "]"
          let (formula, rest) <-
            parseRelPrefix fuel afterClose
          .ok (.select selection formula, rest)
        else if hasToken cursor .project then do
          let (_, afterProject) <-
            expect cursor .project "π"
          let (_, afterOpen) <-
            expect afterProject .leftBracket "["
          let (indices, afterIndices) <-
            parseIndexList fuel afterOpen
          let (formula, rest) <-
            parseRelPrefix fuel afterIndices
          .ok (.proj indices formula, rest)
        else
          parseRelPrimary fuel cursor

  private def parseRelPrimary :
      Nat -> Cursor -> Except Error (Parsed (RelExpr A))
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor =>
        match cursor.tokens with
        | { kind := .top, .. } :: tokens =>
            .ok (.top, { cursor with tokens := tokens })
        | { kind := .empty, .. } :: tokens => do
            let afterEmpty :=
              { cursor with tokens := tokens }
            let (_, afterOpen) <-
              expect afterEmpty .leftBracket "["
            let (arity, afterArity) <-
              parseNumber afterOpen
            let (_, rest) <-
              expect afterArity .rightBracket "]"
            .ok (.empty arity, rest)
        | { kind := .leftBrace, .. } :: tokens => do
            let afterOpen :=
              { cursor with tokens := tokens }
            let (value, afterValue) <- parseData afterOpen
            let (_, rest) <-
              expect afterValue .rightBrace "}"
            .ok (.single value, rest)
        | { kind := .leftParen, .. } :: tokens => do
            let afterOpen :=
              { cursor with tokens := tokens }
            let (formula, afterFormula) <-
              parseRelUnion fuel afterOpen
            let (_, rest) <-
              expect afterFormula .rightParen ")"
            .ok (formula, rest)
        | { kind := .identifier _, .. } :: _ =>
            let parsed := parseRelationName cursor
            parsed.map fun (name, rest) =>
              (RawRAExpr.rel name, rest)
        | _ =>
            if startsEmptyRelation cursor then
              match NameCodec.emptyName? (A := A) with
              | some name =>
                  .ok (RawRAExpr.rel name, cursor)
              | none =>
                  .error
                    (syntaxError cursor
                      "expected relational expression")
            else
              .error
                (syntaxError cursor
                  "expected relational expression")

  private def parseIndexList :
      Nat -> Cursor ->
        Except Error (Parsed (List Nat))
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor =>
        if hasToken cursor .rightBracket then do
          let (_, rest) <-
            expect cursor .rightBracket "]"
          .ok ([], rest)
        else do
          let (index, rest) <- parseNumber cursor
          parseIndexListTail fuel [index] rest

  private def parseIndexListTail :
      Nat -> List Nat -> Cursor ->
        Except Error (Parsed (List Nat))
    | 0, _, cursor => .error (fuelError cursor)
    | fuel + 1, indicesRev, cursor =>
        if hasToken cursor .comma then do
          let (_, afterComma) <-
            expect cursor .comma ","
          let (index, rest) <- parseNumber afterComma
          parseIndexListTail fuel
            (index :: indicesRev) rest
        else do
          let (_, rest) <-
            expect cursor .rightBracket "]"
          .ok (indicesRev.reverse, rest)

  private def parseSelectionOr :
      Nat -> Cursor -> Except Error (Parsed Selection)
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor => do
        let (left, rest) <- parseSelectionAnd fuel cursor
        parseSelectionOrTail fuel left rest

  private def parseSelectionOrTail :
      Nat -> Selection -> Cursor ->
        Except Error (Parsed Selection)
    | 0, _, cursor => .error (fuelError cursor)
    | fuel + 1, left, cursor =>
        if hasToken cursor .disjunction then do
          let (_, afterOperator) <-
            expect cursor .disjunction "∨"
          let (right, rest) <-
            parseSelectionAnd fuel afterOperator
          parseSelectionOrTail fuel (.or left right) rest
        else
          .ok (left, cursor)

  private def parseSelectionAnd :
      Nat -> Cursor -> Except Error (Parsed Selection)
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor => do
        let (left, rest) <-
          parseSelectionUnary fuel cursor
        parseSelectionAndTail fuel left rest

  private def parseSelectionAndTail :
      Nat -> Selection -> Cursor ->
        Except Error (Parsed Selection)
    | 0, _, cursor => .error (fuelError cursor)
    | fuel + 1, left, cursor =>
        if hasToken cursor .conjunction then do
          let (_, afterOperator) <-
            expect cursor .conjunction "∧"
          let (right, rest) <-
            parseSelectionUnary fuel afterOperator
          parseSelectionAndTail fuel (.and left right) rest
        else
          .ok (left, cursor)

  private def parseSelectionUnary :
      Nat -> Cursor -> Except Error (Parsed Selection)
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor =>
        if hasToken cursor .negation then do
          let (_, rest) <- expect cursor .negation "¬"
          let (selection, afterSelection) <-
            parseSelectionUnary fuel rest
          .ok (.not selection, afterSelection)
        else
          parseSelectionPrimary fuel cursor

  private def parseSelectionPrimary :
      Nat -> Cursor -> Except Error (Parsed Selection)
    | 0, cursor => .error (fuelError cursor)
    | fuel + 1, cursor =>
        if hasToken cursor .leftParen then do
          let (_, afterOpen) <-
            expect cursor .leftParen "("
          let (selection, afterSelection) <-
            parseSelectionOr fuel afterOpen
          let (_, rest) <-
            expect afterSelection .rightParen ")"
          .ok (selection, rest)
        else do
          let (_, afterHash) <- expect cursor .hash "#"
          let (left, afterLeft) <- parseNumber afterHash
          let (_, afterEqual) <-
            expect afterLeft .equal "="
          if hasToken afterEqual .hash then do
            let (_, afterRightHash) <-
              expect afterEqual .hash "#"
            let (right, rest) <-
              parseNumber afterRightHash
            .ok (.eqIdx left right, rest)
          else do
            let (value, rest) <- parseData afterEqual
            .ok (.eqConst left value, rest)
end

end SurfaceParser
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Public Entry Points
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace SurfaceParser

variable {A : Type}
variable [RelationNames A] [NameCodec A]

/-
  Structural fuel for one recursive-descent parse over
  `tokens`.

  This is a termination guard on the mutual block below, not
  a bound on submitted input: the grammar descends through
  fewer than sixteen non-consuming levels between two token
  consumptions, so `32 * n + 64` cannot be reached by any
  token list the lexer produces. Exhausting it therefore
  reports a fault of this parser and never a defect of the
  clause, and admission maps it to an infrastructure failure.

  Making the parser fuel-free would need a lexicographic
  well-founded measure over the whole twenty-function mutual
  block; the guard is derived from the input instead so that
  no fixed number bounds what may be submitted.
-/
private def parserFuelFor (tokens : List Token) : Nat :=
  32 * tokens.length + 64

/- Parse one submitted clause under optional host bounds. -/
def parseWithLimits
    (limits : Limits)
    (text : String) : Except Error (Clause A) := do
  let tokens <- tokenize limits text
  let cursor : Cursor :=
    { tokens := tokens
      endOffset := text.length }
  let (formula, rest) <-
    parseGuardOr (parserFuelFor tokens) cursor
  match rest.tokens with
  | [] => .ok formula
  | _ =>
      .error
        (syntaxError rest
          "unexpected trailing surface input")

/- Parse one clause under no host bound at all. -/
def parse (text : String) : Except Error (Clause A) :=
  parseWithLimits {} text

end SurfaceParser
end FrameworkII
end Synthesis
end Whiel
