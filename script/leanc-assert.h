// Minimal `assert.h` for the bundled C toolchain, which ships no libc headers; needed by `mimalloc.h`.
// Mirrors the fallback definition in `lean.h`.
#undef assert
#ifdef NDEBUG
#define assert(expr) ((void)0)
#else
#ifdef __cplusplus
extern "C"
#endif
void lean_notify_assert(const char * fileName, int line, const char * condition);
#define assert(expr) ((expr) ? (void)0 : lean_notify_assert(__FILE__, __LINE__, #expr))
#endif
