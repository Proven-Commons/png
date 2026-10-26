/-
  CRC-32, the checksum stored in every PNG chunk, computed a byte
  at a time from a table. The parser checks each chunk against the
  CRC it carries, so a corrupted chunk is rejected instead of being
  handed out with wrong bytes.

  This is the same CRC-32 as the ZIP reader in Proven-Commons/zip:
  the ISO 3309 polynomial, reflected, register starting at all ones
  and inverted at the end. It is covered by the differential tests
  in `tests/`, which run it against Python zlib's crc32, not by a
  proof.
-/

namespace Png.Crc32

/-- One step of the shift register: shift toward the low end, and xor in
    the reflected polynomial 0xEDB88320 when a one bit falls out. -/
def step (c : UInt32) : UInt32 :=
  if c &&& 1 = 1 then (c >>> 1) ^^^ 0xEDB88320 else c >>> 1

/-- Eight steps: one byte's worth. -/
def step8 (c : UInt32) : UInt32 :=
  step (step (step (step (step (step (step (step c)))))))

/-- `table[i]` is eight steps from `i`. -/
def table : Array UInt32 :=
  (Array.range 256).map fun i => step8 i.toUInt32

/-- Feed one byte into the register. -/
def update (c : UInt32) (b : UInt8) : UInt32 :=
  table[((c ^^^ b.toUInt32) &&& 0xFF).toNat]! ^^^ (c >>> 8)

/-- The CRC-32 of a message. -/
def crc32 (bs : List UInt8) : UInt32 :=
  bs.foldl update 0xFFFFFFFF ^^^ 0xFFFFFFFF

end Png.Crc32
