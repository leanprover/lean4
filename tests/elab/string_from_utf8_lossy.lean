/-!
Tests for `String.fromUTF8Lossy`: well-formed input decodes exactly, and every byte that is not part
of a well-formed UTF-8 encoding becomes `U+FFFD`.
-/

#guard String.fromUTF8Lossy ByteArray.empty = ""
#guard String.fromUTF8Lossy "hello".toUTF8 = "hello"
#guard String.fromUTF8Lossy "héllo →".toUTF8 = "héllo →"

-- A lone continuation byte belongs to no encoding.
#guard String.fromUTF8Lossy ⟨#[0x80]⟩ = "�"

-- 0xFF never appears in UTF-8.
#guard String.fromUTF8Lossy ⟨#[0x61, 0xFF, 0x62]⟩ = "a�b"

-- One replacement per bad byte, so a truncated three-byte sequence yields two.
#guard String.fromUTF8Lossy ⟨#[0xE2, 0x86]⟩ = "��"

-- The WTF-8 encoding of the unpaired surrogate U+D800, which Windows can produce but UTF-8 cannot
-- represent.
#guard String.fromUTF8Lossy ⟨#[0xED, 0xA0, 0x80]⟩ = "���"

-- Overlong encoding of '/'.
#guard String.fromUTF8Lossy ⟨#[0xC0, 0xAF]⟩ = "��"

-- Decoding is total but not injective: distinct byte arrays collapse to the same string, which is
-- why paths are kept as bytes.
#guard String.fromUTF8Lossy ⟨#[0xFE]⟩ = String.fromUTF8Lossy ⟨#[0xFF]⟩
