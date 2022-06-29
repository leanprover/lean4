inductive Dyck : Type where
  | round : Dyck → Dyck  -- ( <inner> )
  | curly : Dyck → Dyck  -- { <inner> }
  | leaf : Dyck

-- declare Dyck grammar parse trees
declare_syntax_cat brack
syntax "(" brack ")" : brack
syntax "{" brack "}" : brack
syntax "end" : brack

-- notation for translating `brack` into `term`
syntax "`[Dyck| " brack "]" : term

-- rules to translate Dyck grammar into inductive value of type Dyck
macro_rules
  | `(`[Dyck| end])    => `(Dyck.leaf)
  | `(`[Dyck| ($b)]) => `(Dyck.round `[Dyck| $b])  -- recurse
  | `(`[Dyck| {$b}]) => `(Dyck.curly `[Dyck| $b])  -- recurse

-- tests
#check `[Dyck| end]      -- Dyck.leaf
#check `[Dyck| {(end)}]  -- Dyck.curl (Dyck.round Dyck.leaf)
