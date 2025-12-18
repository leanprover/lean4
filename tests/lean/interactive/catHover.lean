/-- Index syntax category -/
declare_syntax_cat index

                               --v textDocument/hover
syntax "foo " term prio index : term
            --^ textDocument/hover
                       --^ textDocument/hover
namespace Foo

/-- Value syntax category -/
declare_syntax_cat value

syntax "bla " value : term
              --^ textDocument/hover

end Foo

macro "boo " : term => `(0)
             --^ textDocument/hover

syntax term " ++ " value : term
       --^ textDocument/hover
