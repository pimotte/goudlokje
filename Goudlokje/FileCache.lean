import Std.Data.HashMap

/-!
# File cache

Memoises a value computed from a file, keyed on the file's path and modification time. Linters run
once per command, so a worksheet's companion files are otherwise re-read for every command; the
modification time keeps long-lived processes such as the language server up to date.
-/

namespace Goudlokje

/-- A cache of values computed from files. -/
abbrev FileCache (α : Type) := IO.Ref (Std.HashMap System.FilePath (IO.FS.SystemTime × α))

/-- Returns the cached value for `path`, recomputing it with `compute` if the file changed. A
    missing file has modification time zero. -/
def FileCache.get (cache : FileCache α) (path : System.FilePath) (compute : IO α) : IO α := do
  let mtime ← try pure (← path.metadata).modified catch _ => pure ⟨0, 0⟩
  if let some (cachedTime, value) := (← ST.Ref.get cache)[path]? then
    if cachedTime == mtime then return value
  let value ← compute
  cache.modify (·.insert path (mtime, value))
  return value

end Goudlokje
