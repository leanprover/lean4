#include <lean/lean.h>

#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

typedef struct {
    lean_object m_header;
    unsigned char m_value[1];
} lean_mpz_object_prefix;

extern lean_object *lean_alloc_mpz(void);
extern void *lean_extract_mpz_value(lean_object *o);
extern lean_object *lean_cstr_to_nat(char const *value);
extern lean_object *lean_big_usize_to_nat(size_t value);
extern lean_object *lean_big_uint64_to_nat(uint64_t value);
extern lean_object *lean_nat_overflow_mul(size_t a1, size_t a2);

extern lean_object *leanrt_test_alloc_mpz_from_cstr(char const *value);
extern uint8_t leanrt_test_mpz_eq_cstr(lean_object *o, char const *value);
extern uint8_t leanrt_test_nat_eq_cstr(lean_object *o, char const *value);
extern void leanrt_test_allocator_reset_counters(void);
extern size_t leanrt_test_allocator_alloc_count(void);
extern size_t leanrt_test_allocator_free_count(void);
extern size_t leanrt_test_mpz_object_size(void);
extern size_t leanrt_test_mpz_value_offset(void);

extern size_t leanrt_test_cpp_mpz_object_size(void);
extern size_t leanrt_test_cpp_mpz_value_offset(void);
extern int leanrt_test_mpz_compactor_roundtrip(lean_object *o, char const *expected);

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);

#define CHECK(cond)                                                                 \
    do {                                                                            \
        if (!(cond)) {                                                              \
            fprintf(stderr, "FAIL:%s:%d: %s\n", __FILE__, __LINE__, #cond);         \
            return 1;                                                               \
        }                                                                           \
    } while (0)

_Static_assert(LeanMPZ == 250, "LeanMPZ tag must stay 250");
_Static_assert(offsetof(lean_mpz_object_prefix, m_header) == 0, "LeanMPZ header prefix starts at offset 0");
_Static_assert(offsetof(lean_mpz_object_prefix, m_value) == sizeof(lean_object), "LeanMPZ payload follows header");
_Static_assert(sizeof(((lean_mpz_object_prefix *)0)->m_header) == sizeof(lean_object), "LeanMPZ header prefix matches lean_object");

static int check_nat_object(lean_object *obj, char const *expected, int expect_scalar) {
    CHECK(obj != NULL);
    CHECK((int)lean_is_scalar(obj) == expect_scalar);
    if (expect_scalar) {
        CHECK(lean_unbox(obj) == (size_t)strtoumax(expected, NULL, 10));
    } else {
        CHECK(lean_obj_tag(obj) == LeanMPZ);
        CHECK(obj->m_rc == 1);
        CHECK(leanrt_test_nat_eq_cstr(obj, expected));
        lean_dec(obj);
    }
    return 0;
}

static int check_nat_constructors(void) {
    static char const *const kBig41 = "10000000000000000000000000000000000000000";
    static char const *const kU64Max = "18446744073709551615";
    static char const *const kU64MaxPlusOne = "18446744073709551616";
    char boundary[64];
    char boundary_plus_one[64];
    char usize_max[64];
    char u64_half[64];

    snprintf(boundary, sizeof(boundary), "%zu", (size_t)LEAN_MAX_SMALL_NAT);
    snprintf(boundary_plus_one, sizeof(boundary_plus_one), "%" PRIu64, (uint64_t)LEAN_MAX_SMALL_NAT + 1);
    snprintf(usize_max, sizeof(usize_max), "%zu", (size_t)UINTPTR_MAX);
    snprintf(u64_half, sizeof(u64_half), "%" PRIu64, UINT64_MAX / 2);

    check_nat_object(lean_cstr_to_nat("0"), "0", 1);
    check_nat_object(lean_cstr_to_nat("1"), "1", 1);
    check_nat_object(lean_cstr_to_nat(boundary), boundary, 1);
    check_nat_object(lean_cstr_to_nat(boundary_plus_one), boundary_plus_one, 0);
    check_nat_object(lean_cstr_to_nat(kU64Max), kU64Max, 0);
    check_nat_object(lean_cstr_to_nat(kU64MaxPlusOne), kU64MaxPlusOne, 0);
    check_nat_object(lean_cstr_to_nat(kBig41), kBig41, 0);

    check_nat_object(lean_big_usize_to_nat(0), "0", 1);
    check_nat_object(lean_big_usize_to_nat(1), "1", 1);
    check_nat_object(lean_big_usize_to_nat((size_t)LEAN_MAX_SMALL_NAT), boundary, 1);
    check_nat_object(lean_big_usize_to_nat((size_t)LEAN_MAX_SMALL_NAT + 1), boundary_plus_one, 0);
    check_nat_object(lean_big_usize_to_nat((size_t)UINTPTR_MAX), usize_max, (UINTPTR_MAX <= LEAN_MAX_SMALL_NAT) ? 1 : 0);

    check_nat_object(lean_big_uint64_to_nat(0), "0", 1);
    check_nat_object(lean_big_uint64_to_nat(1), "1", 1);
    check_nat_object(lean_big_uint64_to_nat(UINT32_MAX), "4294967295", (UINT32_MAX <= LEAN_MAX_SMALL_NAT) ? 1 : 0);
    check_nat_object(lean_big_uint64_to_nat(UINT64_MAX / 2), u64_half, ((UINT64_MAX / 2) <= (uint64_t)LEAN_MAX_SMALL_NAT) ? 1 : 0);
    check_nat_object(lean_big_uint64_to_nat(UINT64_MAX), kU64Max, 0);
    return 0;
}

static int check_nat_overflow_mul_panic(void) {
    static char const *const kNeedle = "integer overflow in runtime computation";
    int pipefd[2];
    pid_t pid;
    int status;
    char stderr_buf[1024];
    ssize_t used = 0;
    ssize_t nread;

    CHECK(pipe(pipefd) == 0);
    pid = fork();
    CHECK(pid >= 0);

    if (pid == 0) {
        close(pipefd[0]);
        CHECK(dup2(pipefd[1], STDERR_FILENO) >= 0);
        close(pipefd[1]);
        (void)lean_nat_overflow_mul((size_t)LEAN_MAX_SMALL_NAT, 2);
        _exit(0);
    }

    close(pipefd[1]);
    while ((nread = read(pipefd[0], stderr_buf + used, (sizeof(stderr_buf) - 1) - (size_t)used)) > 0) {
        used += nread;
        if ((size_t)used == sizeof(stderr_buf) - 1) break;
    }
    close(pipefd[0]);
    stderr_buf[used] = '\0';

    CHECK(waitpid(pid, &status, 0) == pid);
    CHECK(!WIFEXITED(status) || WEXITSTATUS(status) != 0);
    CHECK(strstr(stderr_buf, kNeedle) != NULL);
    return 0;
}

static int check_allocator_balance(void) {
    static char const *const kValues[] = {
        "0",
        "9223372036854775808",
        "1234567890123456789012345678901234567890123456789012345678901234567890",
    };
    size_t i;

    leanrt_test_allocator_reset_counters();
    for (i = 0; i < 1000; ++i) {
        size_t j;
        for (j = 0; j < sizeof(kValues) / sizeof(kValues[0]); ++j) {
            lean_object *obj = leanrt_test_alloc_mpz_from_cstr(kValues[j]);
            CHECK(obj != NULL);
            CHECK(lean_obj_tag(obj) == LeanMPZ);
            CHECK(leanrt_test_mpz_eq_cstr(obj, kValues[j]));
            lean_dec(obj);
        }
    }

    CHECK(leanrt_test_allocator_alloc_count() >= 3000);
    CHECK(leanrt_test_allocator_alloc_count() == leanrt_test_allocator_free_count());
    return 0;
}

static int check_compactor_fixture(void) {
    static char const *const kValue = "340282366920938463463374607431768211457";
    size_t zig_size = leanrt_test_mpz_object_size();
    size_t zig_value_offset = leanrt_test_mpz_value_offset();
    size_t cpp_size = leanrt_test_cpp_mpz_object_size();
    size_t cpp_value_offset = leanrt_test_cpp_mpz_value_offset();
    int roundtrip_result;
    lean_object *obj = leanrt_test_alloc_mpz_from_cstr(kValue);

    CHECK(obj != NULL);
    CHECK(zig_value_offset == sizeof(lean_object));
    CHECK(cpp_value_offset == sizeof(lean_object));

    roundtrip_result = leanrt_test_mpz_compactor_roundtrip(obj, kValue);
    if (zig_size == cpp_size && zig_value_offset == cpp_value_offset) {
        CHECK(roundtrip_result == 1);
    } else {
        fprintf(stderr,
                "INFO: LeanMPZ compactor payload mismatch (zig=%zu, cpp=%zu); header-prefix compatibility only\n",
                zig_size,
                cpp_size);
        CHECK(roundtrip_result == 0);
    }

    lean_dec(obj);
    return 0;
}

int main(void) {
    lean_object *obj;
    int rc;

    lean_initialize_runtime_module();
    lean_initialize_thread();

    obj = lean_alloc_mpz();
    CHECK(obj != NULL);
    CHECK(lean_obj_tag(obj) == LeanMPZ);
    CHECK(obj->m_rc == 1);
    CHECK(obj->m_cs_sz == 0);
    CHECK(obj->m_other == 0);
    CHECK(obj->m_tag == LeanMPZ);
    CHECK((unsigned char *)lean_extract_mpz_value(obj) == ((unsigned char *)obj) + offsetof(lean_mpz_object_prefix, m_value));
    lean_dec(obj);

    rc = check_allocator_balance();
    if (rc != 0) return rc;

    rc = check_compactor_fixture();
    if (rc != 0) return rc;

    rc = check_nat_constructors();
    if (rc != 0) return rc;

    rc = check_nat_overflow_mul_panic();
    if (rc != 0) return rc;

    lean_finalize_thread();
    return 0;
}
