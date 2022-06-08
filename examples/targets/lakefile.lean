import Lake
open Lake DSL

package targets {
  srcDir := "src"
  libConfigs :=
    Std.RBMap.empty
    |>.insert `foo {
      name := "foo"
    }
    |>.insert `bar {
      name := "bar"
    }
    |>.insert `baz {
      name := "baz"
    }
  exeConfigs :=
    Std.RBMap.empty
    |>.insert `a {
      root := `a
      name := "a"
    }
    |>.insert `b {
      root := `b
      name := "b"
    }
    |>.insert `c {
      root := `c
      name := "c"
    }
}
