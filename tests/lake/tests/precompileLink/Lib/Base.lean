import LibDep

builtin_initialize libGreetingRef : IO.Ref String ← IO.mkRef libGreeting
