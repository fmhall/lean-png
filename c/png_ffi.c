/*
 * FFI bindings for libpng.
 *
 * Provides PNG decode/encode via the system libpng library.
 * Used as the reference implementation for conformance testing
 * against the native Lean implementation.
 *
 * All decode functions return RGBA 8-bit pixel data prefixed with
 * a small header: [width:4LE][height:4LE][pixels...].
 * Encode takes raw RGBA pixels and produces PNG-format bytes.
 * IHDR extraction returns a 13-byte packed struct.
 *
 * Error handling: all functions return Except String ByteArray
 * (wrapped in IO), using Lean's C FFI conventions.
 */

#include <lean/lean.h>
#include <png.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>

/* ------------------------------------------------------------------ */
/* Lean FFI helpers                                                    */
/* ------------------------------------------------------------------ */

static lean_obj_res mk_io_ok(lean_obj_arg val) {
    return lean_io_result_mk_ok(val);
}

static lean_obj_res mk_io_err(const char *msg) {
    lean_object *s = lean_mk_string(msg);
    lean_object *err = lean_mk_io_user_error(s);
    return lean_io_result_mk_error(err);
}

/* Except.error (tag 0) */
static lean_obj_res mk_except_error(const char *msg) {
    lean_object *s = lean_mk_string(msg);
    lean_object *e = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(e, 0, s);
    return e;
}

/* Except.ok (tag 1) */
static lean_obj_res mk_except_ok(lean_obj_arg val) {
    lean_object *e = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(e, 0, val);
    return e;
}

/* Create a ByteArray from raw bytes */
static lean_obj_res mk_byte_array(const uint8_t *data, size_t len) {
    lean_object *arr = lean_alloc_sarray(1, len, len);
    if (data && len > 0) {
        memcpy(lean_sarray_cptr(arr), data, len);
    }
    return arr;
}

/* Write a uint32 in little-endian into buf */
static void write_le32(uint8_t *buf, uint32_t val) {
    buf[0] = (uint8_t)(val);
    buf[1] = (uint8_t)(val >> 8);
    buf[2] = (uint8_t)(val >> 16);
    buf[3] = (uint8_t)(val >> 24);
}

/* ------------------------------------------------------------------ */
/* Memory read/write callbacks for libpng                              */
/* ------------------------------------------------------------------ */

typedef struct {
    const uint8_t *data;
    size_t         size;
    size_t         offset;
} mem_read_state;

static void png_read_from_memory(png_structp png, png_bytep out, png_size_t count) {
    mem_read_state *state = (mem_read_state *)png_get_io_ptr(png);
    if (state->offset + count > state->size) {
        png_error(png, "read past end of buffer");
        return;
    }
    memcpy(out, state->data + state->offset, count);
    state->offset += count;
}

typedef struct {
    uint8_t *data;
    size_t   size;
    size_t   capacity;
} mem_write_state;

static void png_write_to_memory(png_structp png, png_bytep in, png_size_t count) {
    mem_write_state *state = (mem_write_state *)png_get_io_ptr(png);
    size_t needed = state->size + count;
    if (needed > state->capacity) {
        size_t new_cap = state->capacity * 2;
        if (new_cap < needed) new_cap = needed;
        uint8_t *new_data = (uint8_t *)realloc(state->data, new_cap);
        if (!new_data) {
            png_error(png, "allocation failure in write callback");
            return;
        }
        state->data = new_data;
        state->capacity = new_cap;
    }
    memcpy(state->data + state->size, in, count);
    state->size += count;
}

static void png_flush_memory(png_structp png) {
    (void)png;
}

/* ------------------------------------------------------------------ */
/* Internal decode: shared between file and memory decode              */
/* ------------------------------------------------------------------ */

/*
 * Decode a PNG image to RGBA 8-bit pixels.
 * Returns a ByteArray: [width:4LE][height:4LE][RGBA pixels...].
 * On error, returns Except.error with a message.
 *
 * The `png` and `info` must already be created. The caller sets up
 * the read source (file or memory) before calling this.
 */
static lean_obj_res decode_png_common(png_structp png, png_infop info) {
    if (setjmp(png_jmpbuf(png))) {
        png_destroy_read_struct(&png, &info, NULL);
        return mk_io_ok(mk_except_error("libpng read error"));
    }

    png_read_info(png, info);

    png_uint_32 width  = png_get_image_width(png, info);
    png_uint_32 height = png_get_image_height(png, info);
    png_byte color_type = png_get_color_type(png, info);
    png_byte bit_depth  = png_get_bit_depth(png, info);

    /* Transform to RGBA 8-bit regardless of source format */
    if (bit_depth == 16)
        png_set_strip_16(png);
    if (color_type == PNG_COLOR_TYPE_PALETTE)
        png_set_palette_to_rgb(png);
    if (color_type == PNG_COLOR_TYPE_GRAY && bit_depth < 8)
        png_set_expand(png);
    if (color_type == PNG_COLOR_TYPE_GRAY ||
        color_type == PNG_COLOR_TYPE_GRAY_ALPHA)
        png_set_gray_to_rgb(png);
    if (png_get_valid(png, info, PNG_INFO_tRNS))
        png_set_tRNS_to_alpha(png);
    /* Add alpha channel if missing */
    if (color_type == PNG_COLOR_TYPE_RGB ||
        color_type == PNG_COLOR_TYPE_GRAY ||
        color_type == PNG_COLOR_TYPE_PALETTE)
        png_set_filler(png, 0xFF, PNG_FILLER_AFTER);

    png_read_update_info(png, info);

    /* Allocate row pointers */
    size_t rowbytes = png_get_rowbytes(png, info);
    /* After transforms, should be width * 4 */
    if (rowbytes < (size_t)width * 4) {
        png_destroy_read_struct(&png, &info, NULL);
        return mk_io_ok(mk_except_error("unexpected row size after transform"));
    }

    /* Check for overflow: height * rowbytes + 8 (header) */
    if (height > 0 && rowbytes > (SIZE_MAX - 8) / height) {
        png_destroy_read_struct(&png, &info, NULL);
        return mk_io_ok(mk_except_error("image too large"));
    }

    size_t pixel_size = (size_t)height * rowbytes;
    size_t total_size = 8 + pixel_size;

    png_bytep *row_ptrs = (png_bytep *)malloc(height * sizeof(png_bytep));
    if (!row_ptrs) {
        png_destroy_read_struct(&png, &info, NULL);
        return mk_io_ok(mk_except_error("allocation failure for row pointers"));
    }

    /* Allocate the Lean ByteArray directly */
    lean_object *result_arr = lean_alloc_sarray(1, total_size, total_size);
    uint8_t *buf = lean_sarray_cptr(result_arr);

    /* Write header */
    write_le32(buf, (uint32_t)width);
    write_le32(buf + 4, (uint32_t)height);

    /* Set row pointers into the ByteArray */
    for (png_uint_32 y = 0; y < height; y++) {
        row_ptrs[y] = buf + 8 + y * rowbytes;
    }

    png_read_image(png, row_ptrs);
    png_read_end(png, NULL);

    free(row_ptrs);
    png_destroy_read_struct(&png, &info, NULL);

    return mk_io_ok(mk_except_ok(result_arr));
}

/* ------------------------------------------------------------------ */
/* Decode from file                                                    */
/* ------------------------------------------------------------------ */

/*
 * @[extern "lean_png_decode_file"]
 * Lean signature: pngDecodeFileFFI (path : @& String) : IO (Except String ByteArray)
 */
LEAN_EXPORT lean_obj_res lean_png_decode_file(b_lean_obj_arg path, lean_obj_arg w) {
    (void)w;
    const char *filepath = lean_string_cstr(path);

    FILE *fp = fopen(filepath, "rb");
    if (!fp) {
        return mk_io_ok(mk_except_error("cannot open file"));
    }

    /* Check PNG signature */
    uint8_t sig[8];
    if (fread(sig, 1, 8, fp) != 8 || png_sig_cmp(sig, 0, 8) != 0) {
        fclose(fp);
        return mk_io_ok(mk_except_error("not a PNG file"));
    }

    png_structp png = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
    if (!png) {
        fclose(fp);
        return mk_io_ok(mk_except_error("png_create_read_struct failed"));
    }

    png_infop info = png_create_info_struct(png);
    if (!info) {
        png_destroy_read_struct(&png, NULL, NULL);
        fclose(fp);
        return mk_io_ok(mk_except_error("png_create_info_struct failed"));
    }

    png_init_io(png, fp);
    png_set_sig_bytes(png, 8);

    lean_obj_res result = decode_png_common(png, info);
    fclose(fp);
    return result;
}

/* ------------------------------------------------------------------ */
/* Decode from memory                                                  */
/* ------------------------------------------------------------------ */

/*
 * @[extern "lean_png_decode_memory"]
 * Lean signature: pngDecodeMemoryFFI (data : @& ByteArray) : IO (Except String ByteArray)
 */
LEAN_EXPORT lean_obj_res lean_png_decode_memory(b_lean_obj_arg data, lean_obj_arg w) {
    (void)w;
    size_t size = lean_sarray_size(data);
    const uint8_t *bytes = lean_sarray_cptr(data);

    if (size < 8 || png_sig_cmp(bytes, 0, 8) != 0) {
        return mk_io_ok(mk_except_error("not a PNG buffer"));
    }

    png_structp png = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
    if (!png) {
        return mk_io_ok(mk_except_error("png_create_read_struct failed"));
    }

    png_infop info = png_create_info_struct(png);
    if (!info) {
        png_destroy_read_struct(&png, NULL, NULL);
        return mk_io_ok(mk_except_error("png_create_info_struct failed"));
    }

    mem_read_state state = { bytes, size, 8 };
    png_set_read_fn(png, &state, png_read_from_memory);
    png_set_sig_bytes(png, 8);

    return decode_png_common(png, info);
}

/* ------------------------------------------------------------------ */
/* Encode RGBA pixels to PNG                                           */
/* ------------------------------------------------------------------ */

/*
 * @[extern "lean_png_encode_rgba"]
 * Lean signature: pngEncodeRGBAFFI (width : UInt32) (height : UInt32)
 *                   (pixels : @& ByteArray) : IO (Except String ByteArray)
 */
LEAN_EXPORT lean_obj_res lean_png_encode_rgba(uint32_t width, uint32_t height,
                                               b_lean_obj_arg pixels, lean_obj_arg w) {
    (void)w;
    size_t expected = (size_t)width * (size_t)height * 4;
    size_t actual = lean_sarray_size(pixels);

    if (actual != expected) {
        return mk_io_ok(mk_except_error("pixel buffer size mismatch"));
    }

    if (width == 0 || height == 0) {
        return mk_io_ok(mk_except_error("zero dimension"));
    }

    png_structp png = png_create_write_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
    if (!png) {
        return mk_io_ok(mk_except_error("png_create_write_struct failed"));
    }

    png_infop info = png_create_info_struct(png);
    if (!info) {
        png_destroy_write_struct(&png, NULL);
        return mk_io_ok(mk_except_error("png_create_info_struct failed"));
    }

    /* Set up memory write */
    mem_write_state wstate = { NULL, 0, 0 };
    wstate.capacity = expected + 1024; /* rough estimate */
    wstate.data = (uint8_t *)malloc(wstate.capacity);
    if (!wstate.data) {
        png_destroy_write_struct(&png, &info);
        return mk_io_ok(mk_except_error("allocation failure"));
    }

    if (setjmp(png_jmpbuf(png))) {
        free(wstate.data);
        png_destroy_write_struct(&png, &info);
        return mk_io_ok(mk_except_error("libpng write error"));
    }

    png_set_write_fn(png, &wstate, png_write_to_memory, png_flush_memory);

    png_set_IHDR(png, info,
                 width, height,
                 8,                         /* bit depth */
                 PNG_COLOR_TYPE_RGBA,
                 PNG_INTERLACE_NONE,
                 PNG_COMPRESSION_TYPE_DEFAULT,
                 PNG_FILTER_TYPE_DEFAULT);

    png_write_info(png, info);

    /* Write rows */
    const uint8_t *px = lean_sarray_cptr(pixels);
    size_t rowbytes = (size_t)width * 4;
    for (uint32_t y = 0; y < height; y++) {
        png_write_row(png, px + y * rowbytes);
    }

    png_write_end(png, NULL);
    png_destroy_write_struct(&png, &info);

    lean_object *result = mk_byte_array(wstate.data, wstate.size);
    free(wstate.data);

    return mk_io_ok(mk_except_ok(result));
}

/* ------------------------------------------------------------------ */
/* IHDR extraction                                                     */
/* ------------------------------------------------------------------ */

/*
 * @[extern "lean_png_read_ihdr_file"]
 * Lean signature: pngReadIHDRFileFFI (path : @& String) : IO (Except String ByteArray)
 *
 * Returns a 13-byte ByteArray:
 *   [width:4LE][height:4LE][bitDepth:1][colorType:1]
 *   [compressionMethod:1][filterMethod:1][interlaceMethod:1]
 */
LEAN_EXPORT lean_obj_res lean_png_read_ihdr_file(b_lean_obj_arg path, lean_obj_arg w) {
    (void)w;
    const char *filepath = lean_string_cstr(path);

    FILE *fp = fopen(filepath, "rb");
    if (!fp) {
        return mk_io_ok(mk_except_error("cannot open file"));
    }

    uint8_t sig[8];
    if (fread(sig, 1, 8, fp) != 8 || png_sig_cmp(sig, 0, 8) != 0) {
        fclose(fp);
        return mk_io_ok(mk_except_error("not a PNG file"));
    }

    png_structp png = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
    if (!png) {
        fclose(fp);
        return mk_io_ok(mk_except_error("png_create_read_struct failed"));
    }

    png_infop info = png_create_info_struct(png);
    if (!info) {
        png_destroy_read_struct(&png, NULL, NULL);
        fclose(fp);
        return mk_io_ok(mk_except_error("png_create_info_struct failed"));
    }

    if (setjmp(png_jmpbuf(png))) {
        png_destroy_read_struct(&png, &info, NULL);
        fclose(fp);
        return mk_io_ok(mk_except_error("libpng read error"));
    }

    png_init_io(png, fp);
    png_set_sig_bytes(png, 8);
    png_read_info(png, info);

    png_uint_32 img_w = png_get_image_width(png, info);
    png_uint_32 img_h = png_get_image_height(png, info);
    png_byte bit_depth = png_get_bit_depth(png, info);
    png_byte color_type = png_get_color_type(png, info);
    png_byte compression = png_get_compression_type(png, info);
    png_byte filter = png_get_filter_type(png, info);
    png_byte interlace = png_get_interlace_type(png, info);

    png_destroy_read_struct(&png, &info, NULL);
    fclose(fp);

    uint8_t buf[13];
    write_le32(buf, (uint32_t)img_w);
    write_le32(buf + 4, (uint32_t)img_h);
    buf[8]  = bit_depth;
    buf[9]  = color_type;
    buf[10] = compression;
    buf[11] = filter;
    buf[12] = interlace;

    return mk_io_ok(mk_except_ok(mk_byte_array(buf, 13)));
}

/* ------------------------------------------------------------------ */
/* IHDR extraction from memory                                         */
/* ------------------------------------------------------------------ */

/*
 * @[extern "lean_png_read_ihdr_memory"]
 * Lean signature: pngReadIHDRMemoryFFI (data : @& ByteArray) : IO (Except String ByteArray)
 *
 * Same 13-byte format as file variant.
 */
LEAN_EXPORT lean_obj_res lean_png_read_ihdr_memory(b_lean_obj_arg data, lean_obj_arg w) {
    (void)w;
    size_t size = lean_sarray_size(data);
    const uint8_t *bytes = lean_sarray_cptr(data);

    if (size < 8 || png_sig_cmp(bytes, 0, 8) != 0) {
        return mk_io_ok(mk_except_error("not a PNG buffer"));
    }

    png_structp png = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
    if (!png) {
        return mk_io_ok(mk_except_error("png_create_read_struct failed"));
    }

    png_infop info = png_create_info_struct(png);
    if (!info) {
        png_destroy_read_struct(&png, NULL, NULL);
        return mk_io_ok(mk_except_error("png_create_info_struct failed"));
    }

    mem_read_state state = { bytes, size, 8 };

    if (setjmp(png_jmpbuf(png))) {
        png_destroy_read_struct(&png, &info, NULL);
        return mk_io_ok(mk_except_error("libpng read error"));
    }

    png_set_read_fn(png, &state, png_read_from_memory);
    png_set_sig_bytes(png, 8);
    png_read_info(png, info);

    png_uint_32 img_w = png_get_image_width(png, info);
    png_uint_32 img_h = png_get_image_height(png, info);
    png_byte bit_depth = png_get_bit_depth(png, info);
    png_byte color_type = png_get_color_type(png, info);
    png_byte compression = png_get_compression_type(png, info);
    png_byte filter = png_get_filter_type(png, info);
    png_byte interlace = png_get_interlace_type(png, info);

    png_destroy_read_struct(&png, &info, NULL);

    uint8_t buf[13];
    write_le32(buf, (uint32_t)img_w);
    write_le32(buf + 4, (uint32_t)img_h);
    buf[8]  = bit_depth;
    buf[9]  = color_type;
    buf[10] = compression;
    buf[11] = filter;
    buf[12] = interlace;

    return mk_io_ok(mk_except_ok(mk_byte_array(buf, 13)));
}
