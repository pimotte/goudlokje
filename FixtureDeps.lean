-- This file imports Verbose and Waterproof packages so their oleans are compiled
-- as part of `lake build`, ensuring `analyzeFile` can import them at runtime
-- when processing fixture files that depend on these packages.
import WaterproofGenre
import Verbose.English.All
