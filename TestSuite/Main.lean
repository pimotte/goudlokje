import TestSuite.Config
import TestSuite.TestFile
import TestSuite.Shortcuts
import TestSuite.Discovery
import TestSuite.Analysis
import TestSuite.Check

def main : IO UInt32 := do
  IO.println "=== Config tests ==="
  TestSuite.Config.runAll
  IO.println ""
  IO.println "=== TestFile tests ==="
  TestSuite.TestFile.runAll
  IO.println ""
  IO.println "=== Shortcuts tests ==="
  TestSuite.Shortcuts.runAll
  IO.println ""
  IO.println "=== Discovery tests ==="
  TestSuite.Discovery.runAll
  IO.println ""
  IO.println "=== Analysis integration tests ==="
  TestSuite.Analysis.runAll
  IO.println ""
  IO.println "=== Check end-to-end tests ==="
  TestSuite.Check.runAll
  IO.println ""
  IO.println "All tests passed."
  return 0
