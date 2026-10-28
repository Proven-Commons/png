# Specification: png

A PNG chunk parser and printer in Lean, with (slice 2) a decoder for the IHDR header. It does not decode pixels, and it does not inflate IDAT data. A reviewer who did not write this specification approves it, together with any statement file a reviewer adds later. No such file exists yet, so nothing here counts toward the verified bar yet.

Bytes are `List UInt8` throughout.

## The signature

Every file starts with the eight bytes 137, 80, 78, 71, 13, 10, 26, 10. A file whose first eight bytes differ, and a file shorter than eight bytes, is rejected.

## Chunks

After the signature come chunks until the input ends. One chunk on the wire is:

- a length: four bytes, big endian, counting the data bytes only. Its value must be below 2^31.
- a type: four bytes, each an ASCII letter, A to Z or a to z.
- the data: that many bytes.
- a CRC: four bytes, big endian, holding the CRC-32 of the type bytes and the data bytes together.

The CRC-32 is the one PNG and ZIP share: the ISO 3309 polynomial, reflected, the register starting at all ones and inverted at the end. The implementation is the one in `Png/Crc32.lean`, shaped like the ZIP reader's in Proven-Commons/zip.

## The checks, in the order the parser makes them

1. The first eight bytes are the signature.
2. For each chunk, from the front: at least four bytes remain for the length; the length is below 2^31; at least four bytes remain for the type; each type byte is an ASCII letter; at least the length plus four bytes remain for the data and the CRC; the stored CRC equals the CRC-32 computed over the type bytes and the data. Any failure rejects the whole file. There is no partial read.
3. Reading stops at a chunk whose type is IEND and whose data is empty. That chunk must be the end of the input: any byte after it rejects the file, and running out of input before such a chunk rejects the file.
4. The first chunk read has type IHDR and a data length of 13.

A chunk of type IEND that carries data is an ordinary chunk at this layer: reading does not stop at it. No other rule about chunk order is checked: which types may appear, how many times, or in what order past the first and last, is outside this slice. At this layer the contents of the IHDR data, past its length, are not checked: width, height, bit depth, and colour type are read as data like any other. The header read of slice 2, below, is a second read on top of this one and does check them.

## The IHDR header (slice 2)

The first chunk's 13 data bytes hold, in order:

- the width: four bytes, big endian.
- the height: four bytes, big endian.
- the bit depth: one byte.
- the colour type: one byte.
- the compression method: one byte.
- the filter method: one byte.
- the interlace method: one byte.

The decoded header value holds the width and the height as numbers, and the bit depth, the colour type, and the interlace method as bytes. The compression and filter bytes are not held: the PNG specification gives them no choice (the only compression method is 0, the only filter method is 0), so reading checks that each is zero and printing writes zero.

A header reads only when all of these hold:

- the width is above zero and below 2^31, and the height is above zero and below 2^31. The PNG specification caps each of them at 2^31 - 1.
- the compression byte is zero, and the filter byte is zero.
- the interlace byte is 0 or 1.
- the bit depth is one the colour type allows, by this table from the PNG specification:

| Colour type | Meaning | Allowed bit depths |
|---|---|---|
| 0 | greyscale | 1, 2, 4, 8, 16 |
| 2 | truecolour | 8, 16 |
| 3 | indexed colour | 1, 2, 4, 8 |
| 4 | greyscale with alpha | 8, 16 |
| 6 | truecolour with alpha | 8, 16 |

A colour type other than 0, 2, 3, 4, or 6 allows no bit depth, and reading anything but exactly 13 bytes is a rejection.

Printing a header writes the 13 bytes back: width and height big endian, then bit depth, colour type, compression zero, filter zero, interlace.

The file level read (`parseFile`) runs the chunk parse of slice 1 and then reads the first chunk's data as a header. A file whose first chunk is not a valid IHDR in this sense is rejected by that read even when the chunk layer accepts it: a file with a width of zero is the plainest case.

## Printing

The printer writes the signature, then each chunk as its length, its type bytes, its data, and the CRC it computes over the type bytes and the data. A file the parser accepts is reprinted byte for byte: the lengths and CRCs it carried were checked against the bytes, so printing writes the same values back.

## The claim

The proved claim of slice 1 is a round trip: for every well formed chunk list, parsing what the printer wrote returns the same list. Well formed means the list is a first chunk, then any middle chunks, then the IEND chunk; the first chunk has type IHDR and 13 data bytes; no chunk before the last is the IEND chunk (type IEND with no data); every chunk type is four ASCII letters; and every data length is below 2^31.

Slice 2 adds three proved claims:

- The header round trip: reading the printed bytes of a well formed header gives the header back. Well formed means the width and height are above zero and below 2^31, the interlace byte is 0 or 1, and the bit depth is one the colour type allows.
- The table is exact: the depth checker agrees with the table above, written out as a list of (colour type, bit depth) pairs, on every colour type byte and every bit depth byte.
- The file level round trip: a document that is well formed at the chunk layer and whose first chunk's data is the printed form of a well formed header prints and reads back whole, header included.

No claim is made that the parser accepts every file the rules above allow, or rejects every file they forbid, beyond what the round trip needs. The test suite checks that behaviour against real PNG files built with Python's zlib and against a strict reading of these rules, and the results record the counts.

The round trip needs no fact about CRC-32 itself: the parser and the printer compute the same function of the same bytes, so a printed file passes its own CRC checks by construction. That the function is the standard CRC-32 rests on the differential tests against Python zlib's `crc32`.

## The command-line tool

`Main.lean` reads one request per line. The operations are `parse` and `header`: the request is the operation word, a space, and the byte codes of a PNG file as comma-separated decimal numbers. The `parse` answer is `ok:` followed by the byte codes of the canonical reprint of the parsed chunk list, or `none` when the file is rejected. The `header` answer is `ok:` followed by the codes of a text line naming the decoded header fields, or `none` when the file is rejected at either layer. The text is the width in decimal, the letter `x`, the height in decimal, a space, the letter `d`, the bit depth in decimal, a space, the letter `t`, the colour type in decimal, a space, the letter `i`, and the interlace method in decimal: for a 1920 by 1080 file at bit depth 8, colour type 6, no interlace, the text is `1920x1080 d8 t6 i0`, and the answer carries the character codes of that text. A malformed request line prints `error`. A code above 255 makes the request malformed, since no byte holds it.
