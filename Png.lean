-- Shared utilities
import Png.Util.ByteArray

-- Core types
import Png.Types

-- FFI bindings (libpng)
import Png.FFI

-- Native implementations
import Png.Native.Chunk
import Png.Native.Filter
import Png.Native.Idat
import Png.Native.Encode
import Png.Native.Decode
import Png.Native.Interlace

-- Specifications and proofs
import Png.Spec.ChunkCorrect
import Png.Spec.FilterCorrect
import Png.Spec.IdatCorrect
import Png.Spec.RoundtripCorrect
import Png.Spec.InterlaceCorrect

/-!
# lean-png

Verified PNG decoder/encoder in Lean 4.

Provides pure-Lean PNG parsing, scanline filtering, and image
encoding/decoding with formal correctness proofs. Uses lean-zip
for DEFLATE compression and CRC32 checksums.
-/
