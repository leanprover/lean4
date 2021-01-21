-- Recall that we do not generate code for `sizeOf` instances since they are only used for proving termination
#reduce sizeOf 10
#reduce sizeOf [1, 2]
#reduce sizeOf #[1, 2]
#reduce sizeOf (10 : UInt8)
#reduce sizeOf 'a'
#reduce sizeOf ['h', 'e', 'l', 'l', 'o']
#reduce sizeOf "abc"
#reduce sizeOf `abc
