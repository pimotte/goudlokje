import Lean
import Lean.Elab.Frontend
import Lean.Elab.Tactic
import Lean.Elab.Import
import Lean.Meta
import Goudlokje.Analysis
import Goudlokje.TestFile

/-!
  Goudlokje.Lint — Static lint checks for Lean Verbose worksheets.

  Implements three checks inspired by Lint1:

  * **CheckB1** — Raw Lean tactic detection: flags tactic positions whose syntax
    kind corresponds to a raw Lean or Mathlib tactic (e.g. `exact`, `constructor`,
    `simp`) rather than a Lean Verbose command.  Uses elaborated AST inspection
    (syntax kind of `TacticInfo` nodes).  `sorry`/`admit` are excluded from B1
    because they are handled by B3.

  * **CheckB2** — Type annotation detection (warning):
      1. `Fix <ident> : <Type>` — Fix commands with explicit type annotations.
         Detected via source-line pattern matching at tactic positions (fallback
         approach, since Verbose Fix syntax kind names may vary by library version).
      2. `(<expr> : <Type>)` — Parenthesised type-cast annotations in proof bodies.
         Detected via `TermInfo` nodes with kind `Lean.Parser.Term.typeAscription`
         that are not binder positions (`isBinder = false`).

  * **CheckB3** — Sorry detection (error): flags every use of `sorry` in proof
    bodies.  Detected via `TermInfo` nodes with kind `Lean.Parser.Term.sorry`.
    When the `sorry` tactic macro (`macro "sorry" : tactic => \`(tactic| exact sorry)`)
    is used, it expands to `exact sorry`; the inner `sorry` term generates a
    `TermInfo` that this check captures.
-/

namespace Goudlokje

open Lean Elab Meta

/-- A lint violation found in a source file. -/
structure LintResult where
  file    : String
  line    : Nat
  column  : Nat
  /-- Check identifier: "B1" (raw tactic), "B2" (type annotation), "B3" (sorry). -/
  check   : String
  message : String
  deriving Repr, BEq, Inhabited, Lean.ToJson, Lean.FromJson

-- ============================================================
-- Verbose Lean detection
-- ============================================================

/-- Return true if the tactic kind belongs to the Lean Verbose library.
    Covers step-boundary tactics, opaque Verbose subtrees, and proof wrappers
    (`withSuggestions`, `withoutSuggestions`).  Any of these in an InfoTree
    indicates the proof was written using Lean Verbose. -/
private def isVerboseTacticKind (kind : String) : Bool :=
  kind == "tacticLet'sFirstProveThat_"                             ||
  kind == "tacticLet'sNowProveThat_"                              ||
  kind == "tacticLet'sProveThat_Works_"                           ||
  kind == "tacticLet'sProveThat_"                                 ||
  kind == "Verbose.NameLess.tacticAssumeThat__"                   ||
  kind == "Verbose.English.tacticWeDiscussDependingOnWhether_Or_" ||
  kind == "tacticWeCompute_"                                      ||
  kind == "Verbose.English.withSuggestions"                       ||
  kind == "Verbose.French.withSuggestions"                        ||
  kind == "withoutSuggestions"                                    ||
  kind == "tacticStrg_assumption"

/-- Return true if `tree` contains at least one Verbose tactic node.
    Used to restrict B1 to Verbose Lean proofs only. -/
private partial def treeContainsVerbose (tree : InfoTree) : Bool :=
  match tree with
  | .context _ child => treeContainsVerbose child
  | .node info children =>
    (match info with
     | .ofTacticInfo ti => isVerboseTacticKind ti.stx.getKind.toString
     | _ => false) ||
    children.any treeContainsVerbose
  | .hole _ => false

-- ============================================================
-- CheckB3: sorry detection via TermInfo
-- ============================================================

/-- Collect all `TermInfo` nodes whose syntax kind is `Lean.Parser.Term.sorry`.
    These arise when the `sorry` term is elaborated, including inside the tactic
    macro expansion of `sorry` → `exact sorry`. -/
private partial def collectSorryTermInfos
    (ci? : Option ContextInfo) (tree : InfoTree)
    (acc : Array (ContextInfo × TermInfo)) : Array (ContextInfo × TermInfo) :=
  match tree with
  | .context pci child =>
    collectSorryTermInfos (pci.mergeIntoOuter? ci?) child acc
  | .node info children =>
    let acc' := match ci?, info with
      | some ci, .ofTermInfo ti =>
        if ti.stx.getKind.toString == "Lean.Parser.Term.sorry"
        then acc.push (ci, ti)
        else acc
      | _, _ => acc
    children.foldl (fun a c => collectSorryTermInfos ci? c a) acc'
  | .hole _ => acc

-- ============================================================
-- CheckB1: raw Lean tactic detection via TacticInfo
-- ============================================================

/-- Syntax kinds for raw Lean and Mathlib tactics that students in a Lean Verbose
    course should express using Verbose commands instead.

    Kind names are determined empirically from Lean 4 (`Init/Tactics.lean`,
    namespace `Lean.Parser.Tactic`) and Mathlib.  The list mirrors the keyword
    set from Lint1.CheckB1, minus `sorry`/`admit` (handled by B3).

    Note: some tactics are macros that expand to `exact` or similar primitives,
    so both the macro-invocation kind (e.g. `Lean.Parser.Tactic.rfl`) and the
    expanded kind (`Lean.Parser.Tactic.exact`) may appear at the same source
    position.  Position-based deduplication in `lintFile` keeps only the first
    violation per (check, line, column). -/
private def rawLeanTacticKinds : Array String := #[
  "Lean.Parser.Tactic.exact",
  "Lean.Parser.Tactic.apply",
  "Lean.Parser.Tactic.intro",
  "Lean.Parser.Tactic.introMatch",
  "Lean.Parser.Tactic.simp",
  "Lean.Parser.Tactic.simpAll",
  "Lean.Parser.Tactic.omega",
  "Lean.Parser.Tactic.constructor",
  "Lean.Parser.Tactic.cases",
  "Lean.Parser.Tactic.induction",
  "Lean.Parser.Tactic.rfl",
  "Lean.Parser.Tactic.rwTactic",
  "Lean.Parser.Tactic.tacticHave_",
  "Lean.Parser.Tactic.left",
  "Lean.Parser.Tactic.right",
  "Lean.Parser.Tactic.contradiction",
  "Lean.Parser.Tactic.trivial",
  "Lean.Parser.Tactic.decide",
  "Lean.Parser.Tactic.funext",
  "Lean.Parser.Tactic.congr",
  "Lean.Parser.Tactic.show",
  "Lean.Parser.Tactic.tacticSuffices_",
  "Lean.Parser.Tactic.refine",
  "Lean.Parser.Tactic.specialize",
  "Lean.Parser.Tactic.tacticUse_",
  "Lean.Parser.Tactic.obtain",
  "Lean.Parser.Tactic.ext",
  "Lean.Parser.Tactic.tacticExfalso",
  "Lean.Parser.Tactic.normNum",
  "Mathlib.Tactic.ring",
  "Mathlib.Tactic.linarith"
]

private def isRawLeanTacticKind (kind : String) : Bool :=
  rawLeanTacticKinds.contains kind

/-- True if the source line (after stripping leading whitespace / focus dots) starts
    with `sorry` or `admit`.  Used to exclude `sorry`-macro expansions from B1:
    when `sorry` is written as a tactic, the macro expands to `exact sorry`,
    producing a `TacticInfo` with kind `Lean.Parser.Tactic.exact` at the `sorry`
    source position.  Checking the source line prevents that expansion from being
    reported as a raw `exact` in B1 (it is handled by B3 instead). -/
private def isSorryLine (line : String) : Bool :=
  let stripped := line.trimAsciiStart.toString
  let cmd := if stripped.startsWith "· " then (stripped.drop 2).trimAsciiStart.toString
             else stripped
  cmd.startsWith "sorry" || cmd.startsWith "admit"

/-- Extract the leading tactic token from a source line (after stripping indentation
    and focus-dot prefix) for use in violation messages. -/
private def extractTacticToken (line : String) : String :=
  let stripped := line.trimAsciiStart.toString
  let cmd := if stripped.startsWith "· " then (stripped.drop 2).trimAsciiStart.toString
             else stripped
  match cmd.splitOn " " with
  | tok :: _ => tok
  | []       => "?"

/-- Source-level leading tokens that correspond to known raw Lean / Mathlib tactics
    in `rawLeanTacticKinds`.  If a tactic-info node's source line leads with a token
    NOT in this set, the node comes from a Verbose (or other) macro expansion rather
    than a directly-written raw Lean tactic and must not be flagged as B1.

    The set mirrors the tactic kinds in `rawLeanTacticKinds` at the source level. -/
private def rawLeanTacticSourceTokens : Array String := #[
  "exact", "apply", "intro", "simp", "simp_all", "omega", "constructor",
  "cases", "induction", "rfl", "rw", "rewrite", "have", "left", "right",
  "contradiction", "trivial", "decide", "funext", "congr", "show", "suffices",
  "refine", "specialize", "use", "obtain", "ext", "exfalso", "norm_num",
  "ring", "linarith"
]

/-- True if the leading tactic token extracted from `line` is a known raw Lean tactic
    source keyword.  Returns false for Verbose commands such as "Let's" or "Since",
    preventing macro-expansion artifacts from being reported as B1 violations. -/
private def isRawLeanTacticSourceLine (line : String) : Bool :=
  rawLeanTacticSourceTokens.contains (extractTacticToken line)

/-- Collect `(ContextInfo, TacticInfo)` pairs for raw Lean tactics.
    Only nodes with non-empty `goalsBefore` (real proof steps) are included. -/
private partial def collectRawTacticInfos
    (ci? : Option ContextInfo) (tree : InfoTree) (fileLines : Array String)
    (acc : Array (ContextInfo × TacticInfo)) : Array (ContextInfo × TacticInfo) :=
  match tree with
  | .context pci child =>
    collectRawTacticInfos (pci.mergeIntoOuter? ci?) child fileLines acc
  | .node info children =>
    let acc' := match ci?, info with
      | some ci, .ofTacticInfo ti =>
        if ti.goalsBefore.isEmpty then acc
        else if !isRawLeanTacticKind ti.stx.getKind.toString then acc
        else
          -- Exclude sorry/admit macro expansions (handled by B3)
          let pos := ci.fileMap.toPosition (ti.stx.getPos?.getD 0)
          let lineIdx := pos.line - 1
          let srcLine := if lineIdx < fileLines.size then fileLines[lineIdx]! else ""
          if isSorryLine srcLine then acc
          -- Exclude Verbose macro expansions: only flag lines whose leading token
          -- is an actual raw Lean tactic keyword (not "Let's", "Since", etc.)
          else if !isRawLeanTacticSourceLine srcLine then acc
          else acc.push (ci, ti)
      | _, _ => acc
    children.foldl (fun a c => collectRawTacticInfos ci? c fileLines a) acc'
  | .hole _ => acc

-- ============================================================
-- CheckB2: type annotation detection
-- ============================================================

/-- True if the source line matches the `Fix <ident> : <type>` pattern.
    This is a source-text fallback for Verbose Fix type annotations, used because
    the exact Verbose Fix tactic syntax kind names may vary across library versions. -/
private def isFixWithAnnotation (line : String) : Bool :=
  let stripped := line.trimAsciiStart.toString
  let cmd := if stripped.startsWith "· " then (stripped.drop 2).trimAsciiStart.toString
             else stripped
  if !cmd.startsWith "Fix " then false
  else
    -- "Fix x : T" contains " : " after "Fix "
    let afterFix := (cmd.drop 4).toString
    (afterFix.splitOn " : ").length > 1

/-- Collect `(ContextInfo, TacticInfo)` pairs for Verbose Fix commands that include
    explicit type annotations (`Fix x : T`).  Every tactic position is checked
    against the source line; only those whose source line matches the Fix-annotation
    pattern are included. -/
private partial def collectFixAnnotationInfos
    (ci? : Option ContextInfo) (tree : InfoTree) (fileLines : Array String)
    (acc : Array (ContextInfo × TacticInfo)) : Array (ContextInfo × TacticInfo) :=
  match tree with
  | .context pci child =>
    collectFixAnnotationInfos (pci.mergeIntoOuter? ci?) child fileLines acc
  | .node info children =>
    let acc' := match ci?, info with
      | some ci, .ofTacticInfo ti =>
        if ti.goalsBefore.isEmpty then acc
        else
          let pos := ci.fileMap.toPosition (ti.stx.getPos?.getD 0)
          let lineIdx := pos.line - 1
          let srcLine := if lineIdx < fileLines.size then fileLines[lineIdx]! else ""
          if isFixWithAnnotation srcLine then acc.push (ci, ti) else acc
      | _, _ => acc
    children.foldl (fun a c => collectFixAnnotationInfos ci? c fileLines a) acc'
  | .hole _ => acc

/-- Collect `(ContextInfo, TermInfo)` pairs for parenthesised type-cast annotations
    `(expr : T)` in proof bodies.  Uses `Lean.Parser.Term.typeAscription` kind and
    excludes binder positions (`isBinder = true`) to avoid flagging `(x : T)` in
    `intro` / `have` binders or theorem statement type annotations.

    Additionally, only nodes whose source position starts with `(` in the source file
    are included.  This filters out internally-synthesised `typeAscription` info-tree
    nodes that Lean / Lean Verbose inserts during elaboration but that do not
    correspond to any user-written `(expr : T)` in the proof body. -/
private partial def collectTypeAscriptionInfos
    (ci? : Option ContextInfo) (tree : InfoTree) (fileLines : Array String)
    (acc : Array (ContextInfo × TermInfo)) : Array (ContextInfo × TermInfo) :=
  match tree with
  | .context pci child =>
    collectTypeAscriptionInfos (pci.mergeIntoOuter? ci?) child fileLines acc
  | .node info children =>
    let acc' := match ci?, info with
      | some ci, .ofTermInfo ti =>
        if ti.stx.getKind.toString == "Lean.Parser.Term.typeAscription" && !ti.isBinder
        then
          -- Guard: the source character at the node's position must be '(' to
          -- confirm this is a user-written ascription and not a compiler-inserted one.
          let pos := ci.fileMap.toPosition (ti.stx.getPos?.getD 0)
          let lineIdx := pos.line - 1
          let srcLine := if lineIdx < fileLines.size then fileLines[lineIdx]! else ""
          -- pos.column is a 0-based offset; check the char at that position is '('.
          -- For ASCII source lines (typical Lean proofs) byte-offset == char-index.
          if (srcLine.drop pos.column).startsWith "(" then acc.push (ci, ti) else acc
        else acc
      | _, _ => acc
    children.foldl (fun a c => collectTypeAscriptionInfos ci? c fileLines a) acc'
  | .hole _ => acc

-- ============================================================
-- lintFile: main entry point
-- ============================================================

/-- Analyse a single Lean source file, returning all lint violations.

    Runs three checks:
    * B1 (raw Lean tactics): `TacticInfo` nodes whose syntax kind is in the
      `rawLeanTacticKinds` list.
    * B2 (type annotations): Fix+colon source-line pattern AND `TermInfo` nodes
      with `typeAscription` kind (non-binder).
    * B3 (sorry): `TermInfo` nodes with `Lean.Parser.Term.sorry` kind.

    Results are deduplicated by `(check, line, column)` so that macro expansions
    of a single source token do not produce multiple violations at the same position.

    If `envCache` is provided, the compiled environment is reused across files
    sharing the same import set (same semantics as `analyzeFile`). -/
def lintFile
    (filePath : System.FilePath)
    (envCache : Option EnvCache := none) :
    IO (Array LintResult) := do
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Lean.enableInitializersExecution
  let input ← IO.FS.readFile filePath
  let fileLines := input.splitOn "\n" |>.toArray
  let opts  := Elab.async.set Options.empty false
  let inputCtx := Parser.mkInputContext input filePath.toString
  let (header, parserState, _messages) ← Parser.parseHeader inputCtx
  let headerKey := "\n".intercalate
    (input.splitOn "\n" |>.takeWhile fun l =>
      l.startsWith "import " || l.startsWith "--" || l.isEmpty)
  let env ← match envCache with
    | some cache =>
      getOrBuildEnv cache headerKey do
        let (env, _) ← processHeader header opts {} inputCtx; pure env
    | none => do let (env, _) ← processHeader header opts {} inputCtx; pure env
  let initCmdState : Command.State := Command.mkState env {} opts
  let initState : Frontend.State := {
    commandState := initCmdState
    parserState  := parserState
    cmdPos       := 0
  }
  let ctx : Frontend.Context := { inputCtx }
  let (allTrees, finalState) ← processCommandsCollectTrees ctx initState #[]
  let assignment := finalState.commandState.infoState.assignment
  let resolvedTrees := allTrees.map fun t => t.substitute assignment
  let fileStr := filePath.toString
  let mut raw : Array LintResult := #[]
  for tree in resolvedTrees do
    -- CheckB3: sorry terms
    let sorryInfos := collectSorryTermInfos none tree #[]
    for (ci, ti) in sorryInfos do
      let pos := ci.fileMap.toPosition (ti.stx.getPos?.getD 0)
      raw := raw.push {
        file := fileStr, line := pos.line, column := pos.column,
        check := "B3", message := "sorry in proof body"
      }
    -- CheckB1: raw Lean tactics — only in Verbose Lean proofs.
    if treeContainsVerbose tree then
      let rawInfos := collectRawTacticInfos none tree fileLines #[]
      for (ci, ti) in rawInfos do
        let pos := ci.fileMap.toPosition (ti.stx.getPos?.getD 0)
        let lineIdx := pos.line - 1
        let srcLine := if lineIdx < fileLines.size then fileLines[lineIdx]! else ""
        let tacticToken := extractTacticToken srcLine
        raw := raw.push {
          file := fileStr, line := pos.line, column := pos.column,
          check := "B1", message := s!"Raw Lean tactic '{tacticToken}' in proof body"
        }
    -- CheckB2: Fix with type annotation
    let fixInfos := collectFixAnnotationInfos none tree fileLines #[]
    for (ci, ti) in fixInfos do
      let pos := ci.fileMap.toPosition (ti.stx.getPos?.getD 0)
      raw := raw.push {
        file := fileStr, line := pos.line, column := pos.column,
        check := "B2", message := "Fix command with explicit type annotation"
      }
    -- CheckB2: type-cast ascriptions
    let ascInfos := collectTypeAscriptionInfos none tree fileLines #[]
    for (ci, ti) in ascInfos do
      let pos := ci.fileMap.toPosition (ti.stx.getPos?.getD 0)
      raw := raw.push {
        file := fileStr, line := pos.line, column := pos.column,
        check := "B2", message := "Type cast annotation '(expr : T)' in proof body"
      }
  -- Deduplicate by (check, line, column) — keeps first occurrence per position.
  -- This prevents macro expansions (e.g. `rfl` → `exact HEq.rfl`) from producing
  -- multiple B1 violations at the same source position.
  return raw.foldl (fun acc r =>
    if acc.any (fun e => e.check == r.check && e.line == r.line && e.column == r.column)
    then acc
    else acc.push r) #[]

/-- Pretty-print a lint result to stdout. -/
def printLintResult (r : LintResult) : IO Unit :=
  match r.check with
  | "B3" | "B1" => IO.eprintln s!"ERROR [{r.check}] {r.file}:{r.line}:{r.column} — {r.message}"
  | _            => IO.eprintln s!"WARN  [{r.check}] {r.file}:{r.line}:{r.column} — {r.message}"

-- ============================================================
-- Lint classification: integrate with TestFile infrastructure
-- ============================================================

/-- Classification of a found lint violation against the documented lint entries. -/
inductive LintViolationResult where
  /-- Lint violation NOT documented in the test file — reported as error/warning. -/
  | unexpected (r : LintResult)
  /-- Lint violation documented in the test file — suppressed. -/
  | expected   (r : LintResult)
  deriving Repr, Inhabited

/-- A lint entry documented in the test file but the violation no longer occurs. -/
structure StaleLintEntry where
  entry : ExpectedLintViolation
  deriving Repr, Inhabited

structure LintClassificationResult where
  violations : Array LintViolationResult
  stale      : Array StaleLintEntry
  deriving Repr

/-- Match a lint result against an expected lint violation entry.
    Matches on (file, line, column, check); message is not used for matching
    so that documentation remains valid even if message text is updated. -/
private def lintMatchesEntry (r : LintResult) (e : ExpectedLintViolation) : Bool :=
  e.file == r.file && e.line == r.line && e.column == r.column && e.check == r.check

/-- Classify lint violations against the expected lint entries in the test file.

    B1 violations are always classified as `.unexpected` — they cannot be suppressed
    via the test file.  B1 entries in the test file are always considered stale
    (they should never have been added and must be removed). -/
def classifyLint (found : Array LintResult) (tf : TestFile) : LintClassificationResult :=
  let violations := found.map fun r =>
    -- B1 cannot be suppressed; it is always unexpected regardless of the test file.
    if r.check == "B1" then .unexpected r
    else if tf.lint.any (lintMatchesEntry r) then .expected r
    else .unexpected r
  let stale := tf.lint.filterMap fun e =>
    -- B1 entries are always stale: B1 violations cannot be documented in the test file.
    if e.check == "B1" then some { entry := e }
    else if found.any (fun r => lintMatchesEntry r e) then none
    else some { entry := e }
  { violations, stale }

/-- Pretty-print an unexpected lint violation. -/
def printLintViolationResult (r : LintViolationResult) : IO Unit :=
  match r with
  | .unexpected v =>
    match v.check with
    | "B3" | "B1" => IO.eprintln s!"ERROR: lint [{v.check}] {v.file}:{v.line}:{v.column} — {v.message}"
    | _            => IO.eprintln s!"WARN:  undocumented lint [{v.check}] {v.file}:{v.line}:{v.column} — {v.message}"
  | .expected v =>
    IO.println s!"OK: documented lint [{v.check}] {v.file}:{v.line}:{v.column} — {v.message}"

/-- Pretty-print a stale lint entry warning. -/
def printStaleLintEntry (s : StaleLintEntry) : IO Unit :=
  IO.eprintln s!"WARN: stale lint entry — [{s.entry.check}] {s.entry.file}:{s.entry.line}:{s.entry.column} no longer triggered"

end Goudlokje
