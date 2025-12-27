/-!
  # Parser error messages for unexpected literals

  This test checks that parser errors categorize common literal tokens (numeral, string literal, character literal,
  hexadecimal number) in the `unexpected ...` part of the message and include the literal text.
-/

def 123 := 0
def "hello" := 0
def 'a' := 0
def 0x10 := 0

