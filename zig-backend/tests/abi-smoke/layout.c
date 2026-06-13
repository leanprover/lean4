#include <lean/lean.h>

#include <stddef.h>
#include <stdint.h>

#define ABI_ASSERT_EQ(actual, expected, label) _Static_assert((actual) == (expected), label)
#define CHECK(cond) return (!(cond))

ABI_ASSERT_EQ(LeanMaxCtorTag, 243, "LeanMaxCtorTag matches lean.h");
ABI_ASSERT_EQ(LeanPromise, 244, "LeanPromise matches lean.h");
ABI_ASSERT_EQ(LeanClosure, 245, "LeanClosure matches lean.h");
ABI_ASSERT_EQ(LeanArray, 246, "LeanArray matches lean.h");
ABI_ASSERT_EQ(LeanStructArray, 247, "LeanStructArray matches lean.h");
ABI_ASSERT_EQ(LeanScalarArray, 248, "LeanScalarArray matches lean.h");
ABI_ASSERT_EQ(LeanString, 249, "LeanString matches lean.h");
ABI_ASSERT_EQ(LeanMPZ, 250, "LeanMPZ matches lean.h");
ABI_ASSERT_EQ(LeanThunk, 251, "LeanThunk matches lean.h");
ABI_ASSERT_EQ(LeanTask, 252, "LeanTask matches lean.h");
ABI_ASSERT_EQ(LeanRef, 253, "LeanRef matches lean.h");
ABI_ASSERT_EQ(LeanExternal, 254, "LeanExternal matches lean.h");
ABI_ASSERT_EQ(LeanReserved, 255, "LeanReserved matches lean.h");

ABI_ASSERT_EQ(sizeof(lean_object), 8, "lean_object is 8 bytes");
ABI_ASSERT_EQ(offsetof(lean_object, m_rc), 0, "lean_object.m_rc offset");

ABI_ASSERT_EQ(sizeof(lean_ctor_object), 8, "lean_ctor_object header size");
ABI_ASSERT_EQ(offsetof(lean_ctor_object, m_header), 0, "lean_ctor_object.m_header offset");
ABI_ASSERT_EQ(offsetof(lean_ctor_object, m_objs), 8, "lean_ctor_object.m_objs offset");

ABI_ASSERT_EQ(sizeof(lean_array_object), 24, "lean_array_object size");
ABI_ASSERT_EQ(offsetof(lean_array_object, m_header), 0, "lean_array_object.m_header offset");
ABI_ASSERT_EQ(offsetof(lean_array_object, m_size), 8, "lean_array_object.m_size offset");
ABI_ASSERT_EQ(offsetof(lean_array_object, m_capacity), 16, "lean_array_object.m_capacity offset");
ABI_ASSERT_EQ(offsetof(lean_array_object, m_data), 24, "lean_array_object.m_data offset");

ABI_ASSERT_EQ(sizeof(lean_sarray_object), 24, "lean_sarray_object size");
ABI_ASSERT_EQ(offsetof(lean_sarray_object, m_header), 0, "lean_sarray_object.m_header offset");
ABI_ASSERT_EQ(offsetof(lean_sarray_object, m_size), 8, "lean_sarray_object.m_size offset");
ABI_ASSERT_EQ(offsetof(lean_sarray_object, m_capacity), 16, "lean_sarray_object.m_capacity offset");
ABI_ASSERT_EQ(offsetof(lean_sarray_object, m_data), 24, "lean_sarray_object.m_data offset");

ABI_ASSERT_EQ(sizeof(lean_string_object), 32, "lean_string_object size");
ABI_ASSERT_EQ(offsetof(lean_string_object, m_header), 0, "lean_string_object.m_header offset");
ABI_ASSERT_EQ(offsetof(lean_string_object, m_size), 8, "lean_string_object.m_size offset");
ABI_ASSERT_EQ(offsetof(lean_string_object, m_capacity), 16, "lean_string_object.m_capacity offset");
ABI_ASSERT_EQ(offsetof(lean_string_object, m_length), 24, "lean_string_object.m_length offset");
ABI_ASSERT_EQ(offsetof(lean_string_object, m_data), 32, "lean_string_object.m_data offset");

ABI_ASSERT_EQ(sizeof(lean_closure_object), 24, "lean_closure_object size");
ABI_ASSERT_EQ(offsetof(lean_closure_object, m_header), 0, "lean_closure_object.m_header offset");
ABI_ASSERT_EQ(offsetof(lean_closure_object, m_fun), 8, "lean_closure_object.m_fun offset");
ABI_ASSERT_EQ(offsetof(lean_closure_object, m_arity), 16, "lean_closure_object.m_arity offset");
ABI_ASSERT_EQ(offsetof(lean_closure_object, m_num_fixed), 18, "lean_closure_object.m_num_fixed offset");
ABI_ASSERT_EQ(offsetof(lean_closure_object, m_objs), 24, "lean_closure_object.m_objs offset");

ABI_ASSERT_EQ(sizeof(lean_ref_object), 16, "lean_ref_object size");
ABI_ASSERT_EQ(offsetof(lean_ref_object, m_header), 0, "lean_ref_object.m_header offset");
ABI_ASSERT_EQ(offsetof(lean_ref_object, m_value), 8, "lean_ref_object.m_value offset");

ABI_ASSERT_EQ(sizeof(lean_thunk_object), 24, "lean_thunk_object size");
ABI_ASSERT_EQ(offsetof(lean_thunk_object, m_header), 0, "lean_thunk_object.m_header offset");
ABI_ASSERT_EQ(offsetof(lean_thunk_object, m_value), 8, "lean_thunk_object.m_value offset");
ABI_ASSERT_EQ(offsetof(lean_thunk_object, m_closure), 16, "lean_thunk_object.m_closure offset");

ABI_ASSERT_EQ(sizeof(lean_task_imp), 32, "lean_task_imp size");
ABI_ASSERT_EQ(offsetof(lean_task_imp, m_closure), 0, "lean_task_imp.m_closure offset");
ABI_ASSERT_EQ(offsetof(lean_task_imp, m_head_dep), 8, "lean_task_imp.m_head_dep offset");
ABI_ASSERT_EQ(offsetof(lean_task_imp, m_next_dep), 16, "lean_task_imp.m_next_dep offset");
ABI_ASSERT_EQ(offsetof(lean_task_imp, m_prio), 24, "lean_task_imp.m_prio offset");
ABI_ASSERT_EQ(offsetof(lean_task_imp, m_canceled), 28, "lean_task_imp.m_canceled offset");
ABI_ASSERT_EQ(offsetof(lean_task_imp, m_keep_alive), 29, "lean_task_imp.m_keep_alive offset");
ABI_ASSERT_EQ(offsetof(lean_task_imp, m_deleted), 30, "lean_task_imp.m_deleted offset");

ABI_ASSERT_EQ(sizeof(lean_task_object), 24, "lean_task_object size");
ABI_ASSERT_EQ(offsetof(lean_task_object, m_header), 0, "lean_task_object.m_header offset");
ABI_ASSERT_EQ(offsetof(lean_task_object, m_value), 8, "lean_task_object.m_value offset");
ABI_ASSERT_EQ(offsetof(lean_task_object, m_imp), 16, "lean_task_object.m_imp offset");

ABI_ASSERT_EQ(sizeof(lean_promise_object), 16, "lean_promise_object size");
ABI_ASSERT_EQ(offsetof(lean_promise_object, m_header), 0, "lean_promise_object.m_header offset");
ABI_ASSERT_EQ(offsetof(lean_promise_object, m_result), 8, "lean_promise_object.m_result offset");

ABI_ASSERT_EQ(sizeof(lean_external_class), 16, "lean_external_class size");
ABI_ASSERT_EQ(offsetof(lean_external_class, m_finalize), 0, "lean_external_class.m_finalize offset");
ABI_ASSERT_EQ(offsetof(lean_external_class, m_foreach), 8, "lean_external_class.m_foreach offset");

ABI_ASSERT_EQ(sizeof(lean_external_object), 24, "lean_external_object size");
ABI_ASSERT_EQ(offsetof(lean_external_object, m_header), 0, "lean_external_object.m_header offset");
ABI_ASSERT_EQ(offsetof(lean_external_object, m_class), 8, "lean_external_object.m_class offset");
ABI_ASSERT_EQ(offsetof(lean_external_object, m_data), 16, "lean_external_object.m_data offset");

int main(void) {
    const lean_object probe = {
        .m_rc = 0x01020304,
        .m_cs_sz = 0x0506,
        .m_other = 0x07,
        .m_tag = 0x08,
    };

    CHECK(LEAN_BYTE(probe, 0) == 0x04);
    CHECK(LEAN_BYTE(probe, 1) == 0x03);
    CHECK(LEAN_BYTE(probe, 2) == 0x02);
    CHECK(LEAN_BYTE(probe, 3) == 0x01);
    CHECK(LEAN_BYTE(probe, 4) == 0x06);
    CHECK(LEAN_BYTE(probe, 5) == 0x05);
    CHECK(LEAN_BYTE(probe, 6) == 0x07);
    CHECK(LEAN_BYTE(probe, 7) == 0x08);
    return 0;
}
