namespace Goudlokje

/-- A discovered Lean source file paired with its optional test-file companion. -/
structure WorksheetEntry where
  sourcePath : System.FilePath
  testPath   : Option System.FilePath
  deriving Repr, Inhabited

/-- Recursively collect all `.lean` files under `root`. -/
private partial def collectLeanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut acc : Array System.FilePath := #[]
  let entries ← root.readDir
  for entry in entries do
    let path := root / entry.fileName
    let mdata ← path.metadata
    if mdata.type == .dir then
      acc := acc ++ (← collectLeanFiles path)
    else if path.extension == some "lean" then
      acc := acc.push path
  return acc

/-- Build a WorksheetEntry for each `.lean` file reachable from `paths`.
    Each path may be either a file or a directory to search recursively. -/
def discoverWorksheets (paths : Array System.FilePath) : IO (Array WorksheetEntry) := do
  let mut entries : Array WorksheetEntry := #[]
  for p in paths do
    let mdata ← p.metadata
    let leanFiles : Array System.FilePath ←
      if mdata.type == .dir then collectLeanFiles p else pure #[p]
    for leanFile in leanFiles do
      let tp := leanFile.withExtension "test.json"
      let hasTest ← tp.pathExists
      entries := entries.push {
        sourcePath := leanFile
        testPath   := if hasTest then some tp else none
      }
  return entries

end Goudlokje
