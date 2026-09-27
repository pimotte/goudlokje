import Goudlokje.Expectations

/-!
# Worksheets

Finds the worksheets the CLI works on, by asking Lake, and runs Lake on them. A worksheet is a Lean
source file that is a module of a library in the Lake workspace.
-/

namespace Goudlokje.Cli

open System

/-- The Lean source files among `paths`; directories are searched recursively, skipping hidden
    directories such as `.lake`. -/
partial def findLeanFiles (paths : Array FilePath) : IO (Array FilePath) :=
  paths.foldlM (init := #[]) fun acc path => do
    if ← path.isDir then
      let entries ← path.readDir
      let children := entries.filterMap fun e =>
        if e.fileName.startsWith "." then none else some e.path
      return acc ++ (← findLeanFiles (children.qsort (·.toString < ·.toString)))
    else if path.extension == some "lean" then
      return acc.push path
    else return acc

/-- Runs `lake` with `args`, capturing its output. -/
def lakeOutput (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "lake", args }

/-- Whether all `files` are modules of the workspace. Lake resolves the `lean` facet (the source
    file) without building anything, and fails for files that are not modules. -/
private def areModules (files : Array FilePath) : IO Bool :=
  return (← lakeOutput (#["query", "--no-build"] ++ files.map (s!"{·}:lean"))).exitCode == 0

/-- Runs `f` on every element of `xs`, at most `jobs` at a time. -/
def parallelMap (xs : Array α) (f : α → IO β) (jobs := 8) : IO (Array β) := do
  let mut results := #[]
  for i in [0:(xs.size + jobs - 1) / jobs] do
    let tasks ← (xs.extract (i * jobs) ((i + 1) * jobs)).mapM fun x => IO.asTask (f x)
    for task in tasks do
      results := results.push (← IO.ofExcept task.get)
  return results

/-- The worksheets among `paths` (files and directories). Files that are not modules of the
    workspace are left out; they are reported if named explicitly. -/
def findWorksheets (paths : Array FilePath) : IO (Array FilePath) := do
  let files ← findLeanFiles paths
  if files.isEmpty then return #[]
  -- Usually all files are modules and one query suffices.
  if ← areModules files then return files
  let modules ← parallelMap files fun file => areModules #[file]
  let mut worksheets := #[]
  for file in files, isModule in modules do
    if isModule then
      worksheets := worksheets.push file
    else if paths.contains file then
      IO.eprintln s!"warning: {file} is not a module of a library in this Lake workspace; skipped"
  return worksheets

/-- Runs `lake build` on the worksheets, with output going to the terminal; returns whether the
    build succeeded. -/
def build (worksheets : Array FilePath) : IO Bool := do
  let child ← IO.Process.spawn { cmd := "lake", args := #["build"] ++ worksheets.map toString }
  return (← child.wait) == 0

/-- Elaborates `worksheet` again with `lake lean`, which uses the worksheet's configuration but,
    unlike `lake build`, leaves the build state alone. This writes a new results file. -/
def elaborate (worksheet : FilePath) : IO IO.Process.Output :=
  lakeOutput #["lean", worksheet.toString]

end Goudlokje.Cli
