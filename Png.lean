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
import Png.Native.ColorConvert

-- Specifications and proofs
import Png.Spec.BoundsCorrect
import Png.Spec.ChunkCorrect
import Png.Spec.ColorConvertCorrect
import Png.Spec.FilterCorrect
import Png.Spec.IdatCorrect
import Png.Spec.RoundtripCorrect
import Png.Spec.InterlaceCorrect
import Png.Spec.PngValid
import Png.Spec.InterlacedRoundtripCorrect
import Png.Spec.OverflowSafe
import Png.Spec.DecompBombSafe
import Png.Spec.SecurityClaims

/-!
# lean-png

Verified PNG decoder/encoder in Lean 4.

Provides pure-Lean PNG parsing, scanline filtering, and image
encoding/decoding with formal correctness proofs. Uses lean-zip
for DEFLATE compression and CRC32 checksums.
-/
