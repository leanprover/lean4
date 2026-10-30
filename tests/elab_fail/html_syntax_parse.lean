import Lean.Data.Html

/-! Parse errors in `html%{...}` literals:
`}` cannot appear in text,
end tags cannot be omitted (even for void elements),
attribute values cannot be unquoted or single-quoted,
attribute names can't begin with quotes,
comments must be closed. -/

#eval html%{<p>a } b</p>}
#eval html%{<ul><li>item</ul>}
#eval html%{<br>}
#eval html%{<a href=x/>}
#eval html%{<a href='x'/>}
#eval html%{<a href='xy'/>}
#eval html%{<p 'attr>}
#eval html%{<p a "b/>}
#eval html%{<!-- unterminated}
