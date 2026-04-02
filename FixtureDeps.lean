-- This file ensures that Verbose and WaterproofGenre oleans are compiled
-- as part of `lake build`, so they are available at runtime when `analyzeFile`
-- processes fixture files that import these packages.
import WaterproofGenre
