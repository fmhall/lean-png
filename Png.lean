/-!
# lean-png

Verified PNG decoder/encoder in Lean 4.

Provides pure-Lean PNG parsing, scanline filtering, and image
encoding/decoding with formal correctness proofs. Uses lean-zip
for DEFLATE compression and CRC32 checksums.
-/

-- Re-export public API
-- import Png.Chunk
-- import Png.Decode
-- import Png.Encode
-- import Png.Types
