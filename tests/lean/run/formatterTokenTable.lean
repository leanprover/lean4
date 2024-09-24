/-!
# Verify that the formatter uses the current token table

Formerly, the formatter was only looking at the builtin token table
when deciding where to insert additional whitespace between tokens.
This lead to `5+' -1` in the following pretty printing as `5+'-1`.
-/

infixl:65 "+'" => Int.add
notation:65 a:65 "+'-" b:66 => Int.add a (id b)

/-- info: 5+' -1 : Int -/
#guard_msgs in #check 5 +' -1

/-- info: 5+'-1 : Int -/
#guard_msgs in #check 5 +'- 1
