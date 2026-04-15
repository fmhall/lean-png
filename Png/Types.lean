/-!
# PNG Types

Core data types for PNG images: IHDR metadata, color types,
interlace methods, and decoded image representation.
-/

namespace Png

/-- PNG color type, matching the spec values. -/
inductive ColorType where
  | grayscale      -- 0
  | rgb            -- 2
  | palette        -- 3
  | grayscaleAlpha -- 4
  | rgba           -- 6
  deriving Repr, BEq, Inhabited

namespace ColorType

def ofUInt8 : UInt8 → Option ColorType
  | 0 => some .grayscale
  | 2 => some .rgb
  | 3 => some .palette
  | 4 => some .grayscaleAlpha
  | 6 => some .rgba
  | _ => none

def toUInt8 : ColorType → UInt8
  | .grayscale      => 0
  | .rgb            => 2
  | .palette        => 3
  | .grayscaleAlpha => 4
  | .rgba           => 6

end ColorType

/-- PNG interlace method. -/
inductive InterlaceMethod where
  | none  -- 0
  | adam7  -- 1
  deriving Repr, BEq, Inhabited

namespace InterlaceMethod

def ofUInt8 : UInt8 → Option InterlaceMethod
  | 0 => some .none
  | 1 => some .adam7
  | _ => Option.none

def toUInt8 : InterlaceMethod → UInt8
  | .none  => 0
  | .adam7  => 1

end InterlaceMethod

/-- IHDR chunk fields — the critical metadata at the start of every PNG. -/
structure IHDRInfo where
  width             : UInt32
  height            : UInt32
  bitDepth          : UInt8
  colorType         : ColorType
  compressionMethod : UInt8
  filterMethod      : UInt8
  interlaceMethod   : InterlaceMethod
  deriving Repr, BEq, Inhabited

/-! ## Palette and transparency -/

/-- A single palette entry: red, green, blue. -/
structure PaletteEntry where
  r : UInt8
  g : UInt8
  b : UInt8
  deriving Repr, BEq, DecidableEq, Inhabited

/-- PLTE chunk data: 1–256 RGB palette entries.
    Per PNG spec §11.2.3, the number of entries must not exceed
    `2^bitDepth` and the data length must be divisible by 3. -/
structure PLTEInfo where
  entries : Array PaletteEntry
  deriving Repr, BEq

/-- tRNS (transparency) chunk data.
    Per PNG spec §11.3.2, the format depends on the color type:
    - Grayscale (type 0): a single 16-bit gray sample value
    - RGB (type 2): three 16-bit R, G, B sample values
    - Palette (type 3): up to N alpha bytes (one per palette entry) -/
inductive TRNSInfo where
  | grayscale (gray : UInt16)
  | rgb (r g b : UInt16)
  | palette (alphas : ByteArray)

instance : BEq TRNSInfo where
  beq
    | .grayscale g1, .grayscale g2 => g1 == g2
    | .rgb r1 g1 b1, .rgb r2 g2 b2 => r1 == r2 && g1 == g2 && b1 == b2
    | .palette a1, .palette a2 => a1 == a2
    | _, _ => false

/-- A decoded PNG image: RGBA 8-bit pixels with dimensions. -/
structure PngImage where
  width  : UInt32
  height : UInt32
  pixels : ByteArray  -- RGBA, row-major, width*height*4 bytes
  deriving BEq, Inhabited

namespace PngImage

/-- Expected pixel buffer size for the given dimensions. -/
def expectedSize (w h : UInt32) : Nat :=
  w.toNat * h.toNat * 4

/-- Check that the pixel buffer has the right size. -/
def isValid (img : PngImage) : Bool :=
  img.pixels.size == expectedSize img.width img.height

end PngImage

end Png
