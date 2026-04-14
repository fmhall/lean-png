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
