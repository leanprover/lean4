set_option relaxedAutoBoundImplicitLocal false
inductive Foo
| mk : (a b : Bar) → Foo
            --^ textDocument/hover
