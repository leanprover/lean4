function foo()
   print("foo", 1)
   yield()
   print("foo", 2)
end

co = coroutine.create(foo)
print(coroutine.resume(co))
print("--------")
print(coroutine.resume(co))
yield()
