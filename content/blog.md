# Proving PNG

*A formally verified PNG decoder in ~10,000 lines of Lean*

---

PNG is thirty years old and still shipping CVEs. Integer overflows in row allocation. Decompression bombs. Out-of-bounds reads in palette expansion. The format works, sort of, in the sense that billions of images load every day. It also keeps tripping up seasoned C programmers who have been staring at the same code for a decade.

So we wrote one where the compiler won't let us get it wrong.

`lean-png` is a PNG decoder and encoder in Lean 4, with machine-checked proofs of correctness. 332 theorems, 0 `sorry`s, 180 tests passing. That includes 162/162 valid files from PngSuite (the reference conformance suite) and all 14 corrupt files correctly rejected. There's no FFI on the verified path: the bytes in your image go through Lean from the file handle to the pixel buffer.

Here's what that actually buys you.

## Roundtrip, for real

The headline theorem:

```lean
theorem decodePng_encodePng (image : PngImage) (strategy : FilterStrategy) :
    decodePng (encodePng image strategy) = .ok image
```

For any `PngImage`, under any filter strategy, decoding the encoding gives you back the original. Not "we tested a thousand images." For all images, checked by the kernel.

This covers all 15 color-type × bit-depth combinations PNG supports (grayscale, RGB, palette, grayscale-alpha, RGBA, at 1/2/4/8/16 bits per channel), and it covers Adam7 interlaced images too.

## The parts that were actually hard

**Paeth.** PNG's Paeth filter is the one everyone gets wrong. It predicts each byte from its left, upper, and upper-left neighbors using a weird branch on absolute differences, and the reverse has to recover the original byte from the prediction and the residual. Invertibility isn't obvious by inspection. It's invertibility *modulo 256*, because PNG does everything in `UInt8`. We proved it by reducing to `BitVec 8` and letting `bv_decide` close the goal. The proof is short. Finding the right framing was not.

**Adam7 is a bijection.** Interlaced PNGs split the image across 7 passes using an 8×8 periodic pattern:

![Adam7 interlacing](https://upload.wikimedia.org/wikipedia/commons/c/c8/Adam7_interlacing_representation.gif)

The PNG spec asserts every pixel lands in exactly one pass and then moves on. We actually proved it:

```lean
theorem adam7_coverage   : ∀ r c, ∃ p, pixel (r,c) lands in pass p
theorem adam7_uniqueness : ∀ r c p q, if (r,c) in p and (r,c) in q then p = q
```

Together: Adam7 is a bijection on `ℕ × ℕ`. A nice little standalone result.

## CVE-class elimination

Two classes of PNG bugs show up over and over in `libpng`'s CVE history. First, integer overflow in dimension arithmetic: a malicious IHDR claims a 65535×65535 RGBA image, `width * height * 4` wraps, a tiny allocation is followed by a huge write. Second, decompression bombs: a 1KB IDAT expands to 4GB of zlib output.

We don't mitigate these. We prove them away.

```lean
def maxImagePixels : Nat := 2 ^ 30  -- 1 billion pixels, a policy choice

theorem expectedIdatSize_fits_nat64 (ihdr : IHDRInfo) :
    ihdr.width.toNat * ihdr.height.toNat ≤ maxImagePixels →
    expectedIdatSize ihdr < 2 ^ 64
```

That's the overflow CVE, gone. The decoder can't be tricked into computing a wrapped size, because the only path that reaches allocation has already passed through a theorem that says the number fits.

For bombs, `extractDecompressValidate` only returns `.ok` when the decompressed size exactly equals `height * (1 + scanlineBytes)`. A bomb-shaped IDAT is rejected before the output buffer is ever touched. The 14 corrupt PngSuite files that try variants of this are all rejected, and we proved they had to be.

Every `]!` (the "trust me, it's in bounds" array access) on the decode path was replaced with a proven-bounds `]`. The decoder does not panic. Not probably. Does not.

## What the PNG spec doesn't say

The most surprising part of writing the proofs was how many invariants the PNG spec leaves implicit. Lean makes you name them:

- IDAT chunks must be *contiguous*. The spec says so, but turning that into a checkable predicate (`idatContiguous`) and threading it through the decoder's completeness proof made it clear that several reference decoders don't actually enforce it.
- Palette indices must be less than `PLTE` size. "Obviously." The spec doesn't state it as a theorem. `libpng` CVE-2015-8126 happened because that bound wasn't checked.
- Adam7's bijectivity. The spec gives you a table. The table happens to be a bijection. Nobody proved that until we had to.

A spec is a contract, and writing one in a proof assistant shows you which clauses were never actually written down.

## Try it

```
git clone https://github.com/fmhall/lean-png
cd lean-png
lake build && lake exe test
```

It builds on top of [lean-zip](https://github.com/kim-em/lean-zip) (verified DEFLATE and CRC32), so the compression layer is proven too, all the way down.

C libpng is 100,000+ lines and still occasionally ships CVEs. Ours is 10,200 lines of Lean and proves it doesn't.
