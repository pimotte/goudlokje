The Goudlokje project provides a tool for teachers to maintain worksheets of mathematical exercises in Lean and Verbose Lean.

The idea is that we have a worksheet with reference solutions. Lean can check the correctness of the reference solutions, but for didactical reasons we want to be able to also check if no exercise is too easy; i.e. it can be completed by the specified tactic before the end of the proof. We call this a shortcut.

The way it works is as follows: The Mathlib Tactic Analysis framework is used to run tactics at every steps in a worksheet with reference solutions.
The tactics it should run are configured project-wide, as Lean options in the lakefile (`goudlokje.probes`).
Any file can have an optional accompanying test file (filename.lean goes with filename.test.json). This test file specifies any expected shortcuts (i.e. places where the given tactics succeed).

The tool has two modes of running: "check", in which the configuration is read and errors are reported for any shortcuts found. The other is "update", which by default interactively prompts any found shortcuts and asks the user if the shortcut is expected. If yes, it is written to the testfile, if no, it is not. "update" has a --all flag, which automatically accepts all shortcuts and writes them to the test files.

The tool supports vanilla Lean files (with or without Lean Verbose), but also files using the Waterproof Genre. 

The tool should be easily usable in other lean projects with the same toolchain version.

