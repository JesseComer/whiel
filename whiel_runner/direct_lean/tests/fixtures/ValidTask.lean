import Whiel.Concrete.Notation
import Whiel.Hoare.Concrete

namespace DirectLeanTask

open Whiel Whiel.Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![{R} (arity: 1)]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![true]

def inputCmd : Cmd Data inputSchema := .skip

def inputPost : AssertExpr Data inputSchema :=
  programAssert![true]

def goal : Prop :=
  HoareValid inputPre inputCmd inputPost

end DirectLeanTask
