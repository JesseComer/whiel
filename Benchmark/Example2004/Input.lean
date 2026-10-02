-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  A magic-set transformation of a right-linear path
  program, against the program it was derived from.

  Schema `{Root, MPath}` (unary) and `{Edge, PathBF,
  Path}` (binary). `Edge` is the edge relation and `Root`
  the set of sources the query is asked about; `MPath` is
  the demand set the transformation introduces, `PathBF`
  the transformed program's answers on demanded sources,
  and `Path` the original program's answers. `MPath_aux`,
  `PathBF_aux` and `Path_aux` are the snapshots the
  compiler generates; `Edge` and `Root` are only read and
  have none.

  The transformed program is
    `MPath(x) :- Root(x)`
    `MPath(y) :- MPath(x), Edge(x, y)`
    `PathBF(x, y) :- MPath(x), Edge(x, y)`
    `PathBF(x, z) :- MPath(x), Edge(x, y), PathBF(y, z)`
  and the original one is
    `Path(x, y) :- Edge(x, y)`
    `Path(x, z) :- Edge(x, y), Path(y, z)`

  The command is the two compiled programs run one after
  the other. The single loop the tool verifies is computed
  from that sequence by the generic preprocessor.

  The precondition seeds the query at the single source
  `"root"`, `Root = { "root" }`. The postcondition is
  completeness and soundness of the transformation on the
  demanded sources: every answer of the original program
  whose source is demanded is an answer of the transformed
  one, and every answer of the transformed one is an
  answer of the original. Each computed relation starts
  empty and accumulates its program's immediate
  consequences, and each loop exits only when every output
  equals its snapshot, so on exit `MPath`, `PathBF` and
  `Path` hold the least fixpoints of the two programs; the
  postcondition relates those fixpoints.

  That precondition is the corpus's only assertion that
  fixes a relation to a constant set: it pins the query to
  one source, and relaxing it to `true` would be a sound
  generalisation of the same problem over an arbitrary
  demand seed.

  Expected verdict: valid. The demand set is closed under
  edges out of the seed, so restricting the original
  program to it loses nothing and adds nothing.
-/

namespace Whiel
namespace Benchmark
namespace Example2004

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Root, MPath, MPath_aux} (arity: 1),
    {Edge, PathBF, PathBF_aux, Path, Path_aux}
      (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ (Root = { "root" }) ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      MPath_aux := ∅[1];
      PathBF_aux := ∅[2];
      MPath :=
        (Root ∪
          (π[2] (σ[#0 = #1] (MPath_aux × Edge))));
      PathBF :=
        ((π[0, 2]
            (σ[#0 = #1] (MPath_aux × Edge))) ∪
          (π[0, 4]
            (σ[(#0 = #1) ∧ (#2 = #3)]
              (MPath_aux × (Edge × PathBF_aux)))));
      WHILE
          (¬ ((MPath = MPath_aux) ∧
            (PathBF = PathBF_aux))) DO
        MPath_aux := MPath;
        PathBF_aux := PathBF;
        MPath :=
          (MPath ∪
            (Root ∪
              (π[2]
                (σ[#0 = #1] (MPath_aux × Edge)))));
        PathBF :=
          (PathBF ∪
            ((π[0, 2]
                (σ[#0 = #1] (MPath_aux × Edge))) ∪
              (π[0, 4]
                (σ[(#0 = #1) ∧ (#2 = #3)]
                  (MPath_aux ×
                    (Edge × PathBF_aux))))))
      END;
      Path_aux := ∅[2];
      Path :=
        (Edge ∪
          (π[0, 3] (σ[#1 = #2] (Edge × Path_aux))));
      WHILE (¬ (Path = Path_aux)) DO
        Path_aux := Path;
        Path :=
          (Path ∪
            (Edge ∪
              (π[0, 3]
                (σ[#1 = #2] (Edge × Path_aux)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((π[1, 2] (σ[#0 = #1] (MPath × Path)))
      ⊆ PathBF) ∧
    (PathBF ⊆ Path)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example2004
end Benchmark
end Whiel
