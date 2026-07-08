section
section Foo
end   -- `Foo` expected
  --^ completion
end

section
section Foo
end F  -- `Foo` expected
   --^ completion
end

section
section Foo
end B  -- No completions expected
   --^ completion
end

section
section Foo
section Bar
end   -- `Bar` and `Foo.Bar` expected
  --^ completion
end Foo
end

section
section Foo.Bar
end   -- `Bar` and `Foo.Bar` expected
  --^ completion
end Foo
end

section
section Foo
section Bar
end F  -- `Foo.Bar` expected
   --^ completion
end Foo
end

section
section Foo
section Bar
end B  -- `Bar` expected
   --^ completion
end Foo
end

section
section Foo
section Bar
end Foo.  -- `Bar` expected
      --^ completion
end

section
section Foo.Bar
end Foo.Bar
end   -- No completions expected
  --^ completion

section
section Foo.Bar.Geh
end Bar.  -- `Geh` expected
      --^ completion
end

section
section Foo
section
section Bar.Geh
end   -- `Bar.Geh` and `Geh` expected
  --^ completion
end

section
namespace Foo
namespace Bar
end Foo.  -- `Bar` expected
      --^ completion
end
