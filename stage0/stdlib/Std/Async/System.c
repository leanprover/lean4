// Lean compiler output
// Module: Std.Async.System
// Imports: public import Std.Time public import Std.Internal.UV.System public import Std.Data.HashMap
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_System_instDecidableEqFilePath___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_os_environ();
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_uv_hrtime();
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_uv_os_tmpdir();
lean_object* lean_uv_os_uname();
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Std_Time_Millisecond_instReprOrdinal___lam__0(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_uv_cpu_info();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
lean_object* lean_uv_uptime();
lean_object* lean_uv_os_get_passwd();
lean_object* lean_uv_os_getenv(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_uv_os_get_group(uint64_t);
lean_object* lean_uv_os_homedir();
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_uv_os_unsetenv(lean_object*);
lean_object* lean_uv_os_setenv(lean_object*, lean_object*);
lean_object* lean_uv_os_gethostname();
LEAN_EXPORT lean_object* l_Std_Async_System_instInhabitedGroupId_default;
LEAN_EXPORT lean_object* l_Std_Async_System_instInhabitedGroupId;
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqGroupId_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqGroupId_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqGroupId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqGroupId___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_System_instOrdGroupId_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instOrdGroupId_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_System_instOrdGroupId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_System_instOrdGroupId_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_instOrdGroupId___closed__0 = (const lean_object*)&l_Std_Async_System_instOrdGroupId___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instOrdGroupId = (const lean_object*)&l_Std_Async_System_instOrdGroupId___closed__0_value;
static const lean_string_object l_Std_Async_System_instReprGroupId___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "GroupId.mk "};
static const lean_object* l_Std_Async_System_instReprGroupId___lam__0___closed__0 = (const lean_object*)&l_Std_Async_System_instReprGroupId___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Async_System_instReprGroupId___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprGroupId___lam__0___closed__0_value)}};
static const lean_object* l_Std_Async_System_instReprGroupId___lam__0___closed__1 = (const lean_object*)&l_Std_Async_System_instReprGroupId___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_System_instReprGroupId___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprGroupId___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_System_instReprGroupId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_System_instReprGroupId___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_instReprGroupId___closed__0 = (const lean_object*)&l_Std_Async_System_instReprGroupId___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instReprGroupId = (const lean_object*)&l_Std_Async_System_instReprGroupId___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_System_instInhabitedUserId_default;
LEAN_EXPORT lean_object* l_Std_Async_System_instInhabitedUserId;
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqUserId_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqUserId_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqUserId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqUserId___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_System_instOrdUserId_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instOrdUserId_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_System_instOrdUserId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_System_instOrdUserId_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_instOrdUserId___closed__0 = (const lean_object*)&l_Std_Async_System_instOrdUserId___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instOrdUserId = (const lean_object*)&l_Std_Async_System_instOrdUserId___closed__0_value;
static const lean_string_object l_Std_Async_System_instReprUserId___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UserId.mk "};
static const lean_object* l_Std_Async_System_instReprUserId___lam__0___closed__0 = (const lean_object*)&l_Std_Async_System_instReprUserId___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Async_System_instReprUserId___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprUserId___lam__0___closed__0_value)}};
static const lean_object* l_Std_Async_System_instReprUserId___lam__0___closed__1 = (const lean_object*)&l_Std_Async_System_instReprUserId___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_System_instReprUserId___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprUserId___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_System_instReprUserId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_System_instReprUserId___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_instReprUserId___closed__0 = (const lean_object*)&l_Std_Async_System_instReprUserId___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instReprUserId = (const lean_object*)&l_Std_Async_System_instReprUserId___closed__0_value;
static const lean_string_object l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Async_System_instInhabitedSystemUser_default___closed__0 = (const lean_object*)&l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value;
static const lean_ctor_object l_Std_Async_System_instInhabitedSystemUser_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_System_instInhabitedSystemUser_default___closed__1 = (const lean_object*)&l_Std_Async_System_instInhabitedSystemUser_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instInhabitedSystemUser_default = (const lean_object*)&l_Std_Async_System_instInhabitedSystemUser_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instInhabitedSystemUser = (const lean_object*)&l_Std_Async_System_instInhabitedSystemUser_default___closed__1_value;
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqSystemUser_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqSystemUser_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqSystemUser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqSystemUser___boxed(lean_object*, lean_object*);
static const lean_string_object l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__0 = (const lean_object*)&l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__1 = (const lean_object*)&l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Async_System_instReprSystemUser_repr_spec__4(lean_object*);
static const lean_string_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "username"};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__1 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__2 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__3 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__4 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__3_value),((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__6 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7;
static const lean_string_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__8 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "userId"};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__10 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__11 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__11_value;
static lean_once_cell_t l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12;
static const lean_string_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "groupId"};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__13 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14_value;
static lean_once_cell_t l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15;
static const lean_string_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "shell"};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__16 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__16_value;
static const lean_ctor_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__16_value)}};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__17 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__17_value;
static lean_once_cell_t l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18;
static const lean_string_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "homeDir"};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__19 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__19_value;
static const lean_ctor_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__19_value)}};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__20 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__20_value;
static const lean_string_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__21 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__21_value;
static lean_once_cell_t l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22;
static lean_once_cell_t l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23;
static const lean_ctor_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24_value;
static const lean_ctor_object l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__21_value)}};
static const lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25 = (const lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25_value;
LEAN_EXPORT lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprSystemUser_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprSystemUser_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_System_instReprSystemUser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_System_instReprSystemUser_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_instReprSystemUser___closed__0 = (const lean_object*)&l_Std_Async_System_instReprSystemUser___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instReprSystemUser = (const lean_object*)&l_Std_Async_System_instReprSystemUser___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1_value;
static const lean_string_object l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__2_value;
static lean_once_cell_t l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3;
static lean_once_cell_t l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4;
static const lean_ctor_object l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__5_value;
static const lean_ctor_object l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6_value;
static const lean_string_object l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "groupName"};
static const lean_object* l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__0 = (const lean_object*)&l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__1 = (const lean_object*)&l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__2 = (const lean_object*)&l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__2_value),((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__3 = (const lean_object*)&l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4;
static const lean_string_object l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "members"};
static const lean_object* l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__5 = (const lean_object*)&l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__6 = (const lean_object*)&l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Async_System_instReprGroupInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprGroupInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprGroupInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_System_instReprGroupInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_System_instReprGroupInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_instReprGroupInfo___closed__0 = (const lean_object*)&l_Std_Async_System_instReprGroupInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instReprGroupInfo = (const lean_object*)&l_Std_Async_System_instReprGroupInfo___closed__0_value;
static const lean_array_object l_Std_Async_System_instInhabitedGroupInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Async_System_instInhabitedGroupInfo_default___closed__0 = (const lean_object*)&l_Std_Async_System_instInhabitedGroupInfo_default___closed__0_value;
static const lean_ctor_object l_Std_Async_System_instInhabitedGroupInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_System_instInhabitedGroupInfo_default___closed__0_value)}};
static const lean_object* l_Std_Async_System_instInhabitedGroupInfo_default___closed__1 = (const lean_object*)&l_Std_Async_System_instInhabitedGroupInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instInhabitedGroupInfo_default = (const lean_object*)&l_Std_Async_System_instInhabitedGroupInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instInhabitedGroupInfo = (const lean_object*)&l_Std_Async_System_instInhabitedGroupInfo_default___closed__1_value;
static lean_once_cell_t l_Std_Async_System_instInhabitedCPUTimes_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instInhabitedCPUTimes_default___closed__0;
static lean_once_cell_t l_Std_Async_System_instInhabitedCPUTimes_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instInhabitedCPUTimes_default___closed__1;
LEAN_EXPORT lean_object* l_Std_Async_System_instInhabitedCPUTimes_default;
LEAN_EXPORT lean_object* l_Std_Async_System_instInhabitedCPUTimes;
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqCPUTimes_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqCPUTimes_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqCPUTimes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqCPUTimes___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "userTime"};
static const lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__0 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__1 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__2 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__2_value),((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__3 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "niceTime"};
static const lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__4 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__5 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__5_value;
static const lean_string_object l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "systemTime"};
static const lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__6 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__6_value;
static const lean_ctor_object l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__6_value)}};
static const lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__7 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__7_value;
static lean_once_cell_t l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8;
static const lean_string_object l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "idleTime"};
static const lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__9 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__9_value;
static const lean_ctor_object l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__9_value)}};
static const lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__10 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__10_value;
static const lean_string_object l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "interruptTime"};
static const lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__11 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__11_value;
static const lean_ctor_object l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__11_value)}};
static const lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__12 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__12_value;
static lean_once_cell_t l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13;
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUTimes_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUTimes_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_System_instReprCPUTimes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_System_instReprCPUTimes_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_instReprCPUTimes___closed__0 = (const lean_object*)&l_Std_Async_System_instReprCPUTimes___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instReprCPUTimes = (const lean_object*)&l_Std_Async_System_instReprCPUTimes___closed__0_value;
static lean_once_cell_t l_Std_Async_System_instInhabitedCPUInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instInhabitedCPUInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Async_System_instInhabitedCPUInfo_default;
LEAN_EXPORT lean_object* l_Std_Async_System_instInhabitedCPUInfo;
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqCPUInfo_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqCPUInfo_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqCPUInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqCPUInfo___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "model"};
static const lean_object* l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__0 = (const lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__1 = (const lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__2 = (const lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__2_value),((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__3 = (const lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "speed"};
static const lean_object* l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__4 = (const lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__5 = (const lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__5_value;
static const lean_string_object l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "times"};
static const lean_object* l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__6 = (const lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__6_value;
static const lean_ctor_object l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__6_value)}};
static const lean_object* l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__7 = (const lean_object*)&l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_System_instReprCPUInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_System_instReprCPUInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_instReprCPUInfo___closed__0 = (const lean_object*)&l_Std_Async_System_instReprCPUInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instReprCPUInfo = (const lean_object*)&l_Std_Async_System_instReprCPUInfo___closed__0_value;
static const lean_string_object l_Std_Async_System_instReprOSInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg___closed__0 = (const lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Async_System_instReprOSInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg___closed__1 = (const lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Async_System_instReprOSInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg___closed__2 = (const lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Async_System_instReprOSInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__2_value),((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg___closed__3 = (const lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4;
static const lean_string_object l_Std_Async_System_instReprOSInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "release"};
static const lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg___closed__5 = (const lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Async_System_instReprOSInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg___closed__6 = (const lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__6_value;
static const lean_string_object l_Std_Async_System_instReprOSInfo_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg___closed__7 = (const lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__7_value;
static const lean_ctor_object l_Std_Async_System_instReprOSInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__7_value)}};
static const lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg___closed__8 = (const lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__8_value;
static const lean_string_object l_Std_Async_System_instReprOSInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "machine"};
static const lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg___closed__9 = (const lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__9_value;
static const lean_ctor_object l_Std_Async_System_instReprOSInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__9_value)}};
static const lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg___closed__10 = (const lean_object*)&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprOSInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprOSInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_System_instReprOSInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_System_instReprOSInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_instReprOSInfo___closed__0 = (const lean_object*)&l_Std_Async_System_instReprOSInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instReprOSInfo = (const lean_object*)&l_Std_Async_System_instReprOSInfo___closed__0_value;
static const lean_ctor_object l_Std_Async_System_instInhabitedOSInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value),((lean_object*)&l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value),((lean_object*)&l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value),((lean_object*)&l_Std_Async_System_instInhabitedSystemUser_default___closed__0_value)}};
static const lean_object* l_Std_Async_System_instInhabitedOSInfo_default___closed__0 = (const lean_object*)&l_Std_Async_System_instInhabitedOSInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instInhabitedOSInfo_default = (const lean_object*)&l_Std_Async_System_instInhabitedOSInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instInhabitedOSInfo = (const lean_object*)&l_Std_Async_System_instInhabitedOSInfo_default___closed__0_value;
static lean_once_cell_t l_Std_Async_System_instInhabitedEnvironment_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instInhabitedEnvironment_default___closed__0;
static lean_once_cell_t l_Std_Async_System_instInhabitedEnvironment_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_instInhabitedEnvironment_default___closed__1;
LEAN_EXPORT lean_object* l_Std_Async_System_instInhabitedEnvironment_default;
LEAN_EXPORT lean_object* l_Std_Async_System_instInhabitedEnvironment;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3;
static lean_once_cell_t l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4;
static const lean_ctor_object l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Std_Async_System_instReprEnvironment_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toHashMap"};
static const lean_object* l_Std_Async_System_instReprEnvironment_repr___redArg___closed__0 = (const lean_object*)&l_Std_Async_System_instReprEnvironment_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Async_System_instReprEnvironment_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprEnvironment_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Async_System_instReprEnvironment_repr___redArg___closed__1 = (const lean_object*)&l_Std_Async_System_instReprEnvironment_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Async_System_instReprEnvironment_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_System_instReprEnvironment_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Async_System_instReprEnvironment_repr___redArg___closed__2 = (const lean_object*)&l_Std_Async_System_instReprEnvironment_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Async_System_instReprEnvironment_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprEnvironment_repr___redArg___closed__2_value),((lean_object*)&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Async_System_instReprEnvironment_repr___redArg___closed__3 = (const lean_object*)&l_Std_Async_System_instReprEnvironment_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Async_System_instReprEnvironment_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashMap.ofList "};
static const lean_object* l_Std_Async_System_instReprEnvironment_repr___redArg___closed__4 = (const lean_object*)&l_Std_Async_System_instReprEnvironment_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Async_System_instReprEnvironment_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Async_System_instReprEnvironment_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Async_System_instReprEnvironment_repr___redArg___closed__5 = (const lean_object*)&l_Std_Async_System_instReprEnvironment_repr___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Async_System_instReprEnvironment_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprEnvironment_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_instReprEnvironment_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_System_instReprEnvironment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_System_instReprEnvironment_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_instReprEnvironment___closed__0 = (const lean_object*)&l_Std_Async_System_instReprEnvironment___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Async_System_instReprEnvironment = (const lean_object*)&l_Std_Async_System_instReprEnvironment___closed__0_value;
static const lean_closure_object l_Std_Async_System_Environment_get_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_Environment_get_x3f___closed__0 = (const lean_object*)&l_Std_Async_System_Environment_get_x3f___closed__0_value;
static lean_once_cell_t l_Std_Async_System_Environment_get_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_System_Environment_get_x3f___closed__1;
LEAN_EXPORT lean_object* l_Std_Async_System_Environment_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_Environment_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getSystemInfo();
LEAN_EXPORT lean_object* l_Std_Async_System_getSystemInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getCPUInfo();
LEAN_EXPORT lean_object* l_Std_Async_System_getCPUInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Async_System_getCPUInfo_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getUpTime();
LEAN_EXPORT lean_object* l_Std_Async_System_getUpTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getHighResolutionTime();
LEAN_EXPORT lean_object* l_Std_Async_System_getHighResolutionTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getHostName();
LEAN_EXPORT lean_object* l_Std_Async_System_getHostName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_setEnvVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_setEnvVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getEnvVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getEnvVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_unsetEnvVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_unsetEnvVar___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_System_getEnv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_getEnv___closed__0 = (const lean_object*)&l_Std_Async_System_getEnv___closed__0_value;
static const lean_closure_object l_Std_Async_System_getEnv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_getEnv___closed__1 = (const lean_object*)&l_Std_Async_System_getEnv___closed__1_value;
static const lean_closure_object l_Std_Async_System_getEnv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_getEnv___closed__2 = (const lean_object*)&l_Std_Async_System_getEnv___closed__2_value;
static const lean_closure_object l_Std_Async_System_getEnv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_getEnv___closed__3 = (const lean_object*)&l_Std_Async_System_getEnv___closed__3_value;
static const lean_closure_object l_Std_Async_System_getEnv___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_getEnv___closed__4 = (const lean_object*)&l_Std_Async_System_getEnv___closed__4_value;
static const lean_closure_object l_Std_Async_System_getEnv___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_getEnv___closed__5 = (const lean_object*)&l_Std_Async_System_getEnv___closed__5_value;
static const lean_closure_object l_Std_Async_System_getEnv___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_getEnv___closed__6 = (const lean_object*)&l_Std_Async_System_getEnv___closed__6_value;
static const lean_ctor_object l_Std_Async_System_getEnv___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_System_getEnv___closed__0_value),((lean_object*)&l_Std_Async_System_getEnv___closed__1_value)}};
static const lean_object* l_Std_Async_System_getEnv___closed__7 = (const lean_object*)&l_Std_Async_System_getEnv___closed__7_value;
static const lean_ctor_object l_Std_Async_System_getEnv___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_System_getEnv___closed__7_value),((lean_object*)&l_Std_Async_System_getEnv___closed__2_value),((lean_object*)&l_Std_Async_System_getEnv___closed__3_value),((lean_object*)&l_Std_Async_System_getEnv___closed__4_value),((lean_object*)&l_Std_Async_System_getEnv___closed__5_value)}};
static const lean_object* l_Std_Async_System_getEnv___closed__8 = (const lean_object*)&l_Std_Async_System_getEnv___closed__8_value;
static const lean_ctor_object l_Std_Async_System_getEnv___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_System_getEnv___closed__8_value),((lean_object*)&l_Std_Async_System_getEnv___closed__6_value)}};
static const lean_object* l_Std_Async_System_getEnv___closed__9 = (const lean_object*)&l_Std_Async_System_getEnv___closed__9_value;
static const lean_closure_object l_Std_Async_System_getEnv___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_System_getEnv___closed__9_value)} };
static const lean_object* l_Std_Async_System_getEnv___closed__10 = (const lean_object*)&l_Std_Async_System_getEnv___closed__10_value;
static const lean_closure_object l_Std_Async_System_getEnv___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_System_getEnv___closed__10_value)} };
static const lean_object* l_Std_Async_System_getEnv___closed__11 = (const lean_object*)&l_Std_Async_System_getEnv___closed__11_value;
LEAN_EXPORT lean_object* l_Std_Async_System_getEnv();
LEAN_EXPORT lean_object* l_Std_Async_System_getEnv___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getHomeDir();
LEAN_EXPORT lean_object* l_Std_Async_System_getHomeDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getTmpDir();
LEAN_EXPORT lean_object* l_Std_Async_System_getTmpDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getCurrentUser();
LEAN_EXPORT lean_object* l_Std_Async_System_getCurrentUser___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Std_Async_System_getGroup_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Std_Async_System_getGroup_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getGroup___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getGroup___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Async_System_getGroup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_System_getGroup___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_System_getGroup___closed__0 = (const lean_object*)&l_Std_Async_System_getGroup___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_System_getGroup(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_System_getGroup___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Std_Async_System_instInhabitedGroupId_default(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(0u);
return v___x_1_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedGroupId(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqGroupId_decEq(lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_eq(v_x_3_, v_x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqGroupId_decEq___boxed(lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Std_Async_System_instDecidableEqGroupId_decEq(v_x_6_, v_x_7_);
lean_dec(v_x_7_);
lean_dec(v_x_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqGroupId(lean_object* v_x_10_, lean_object* v_x_11_){
_start:
{
uint8_t v___x_12_; 
v___x_12_ = lean_nat_dec_eq(v_x_10_, v_x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqGroupId___boxed(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Std_Async_System_instDecidableEqGroupId(v_x_13_, v_x_14_);
lean_dec(v_x_14_);
lean_dec(v_x_13_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_System_instOrdGroupId_ord(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = lean_nat_dec_lt(v_x_17_, v_x_18_);
if (v___x_19_ == 0)
{
uint8_t v___x_20_; 
v___x_20_ = lean_nat_dec_eq(v_x_17_, v_x_18_);
if (v___x_20_ == 0)
{
uint8_t v___x_21_; 
v___x_21_ = 2;
return v___x_21_;
}
else
{
uint8_t v___x_22_; 
v___x_22_ = 1;
return v___x_22_;
}
}
else
{
uint8_t v___x_23_; 
v___x_23_ = 0;
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instOrdGroupId_ord___boxed(lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Std_Async_System_instOrdGroupId_ord(v_x_24_, v_x_25_);
lean_dec(v_x_25_);
lean_dec(v_x_24_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprGroupId___lam__0(lean_object* v_g_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_35_ = ((lean_object*)(l_Std_Async_System_instReprGroupId___lam__0___closed__1));
v___x_36_ = l_Nat_reprFast(v_g_33_);
v___x_37_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
v___x_38_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_35_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
v___x_39_ = l_Repr_addAppParen(v___x_38_, v___y_34_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprGroupId___lam__0___boxed(lean_object* v_g_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_Async_System_instReprGroupId___lam__0(v_g_40_, v___y_41_);
lean_dec(v___y_41_);
return v_res_42_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedUserId_default(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_unsigned_to_nat(0u);
return v___x_45_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedUserId(void){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_unsigned_to_nat(0u);
return v___x_46_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqUserId_decEq(lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = lean_nat_dec_eq(v_x_47_, v_x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqUserId_decEq___boxed(lean_object* v_x_50_, lean_object* v_x_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Std_Async_System_instDecidableEqUserId_decEq(v_x_50_, v_x_51_);
lean_dec(v_x_51_);
lean_dec(v_x_50_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqUserId(lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
uint8_t v___x_56_; 
v___x_56_ = lean_nat_dec_eq(v_x_54_, v_x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqUserId___boxed(lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Std_Async_System_instDecidableEqUserId(v_x_57_, v_x_58_);
lean_dec(v_x_58_);
lean_dec(v_x_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_System_instOrdUserId_ord(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = lean_nat_dec_lt(v_x_61_, v_x_62_);
if (v___x_63_ == 0)
{
uint8_t v___x_64_; 
v___x_64_ = lean_nat_dec_eq(v_x_61_, v_x_62_);
if (v___x_64_ == 0)
{
uint8_t v___x_65_; 
v___x_65_ = 2;
return v___x_65_;
}
else
{
uint8_t v___x_66_; 
v___x_66_ = 1;
return v___x_66_;
}
}
else
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instOrdUserId_ord___boxed(lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Std_Async_System_instOrdUserId_ord(v_x_68_, v_x_69_);
lean_dec(v_x_69_);
lean_dec(v_x_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprUserId___lam__0(lean_object* v_u_77_, lean_object* v___y_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = ((lean_object*)(l_Std_Async_System_instReprUserId___lam__0___closed__1));
v___x_80_ = l_Nat_reprFast(v_u_77_);
v___x_81_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_79_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = l_Repr_addAppParen(v___x_82_, v___y_78_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprUserId___lam__0___boxed(lean_object* v_u_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Async_System_instReprUserId___lam__0(v_u_84_, v___y_85_);
lean_dec(v___y_85_);
return v_res_86_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqSystemUser_decEq(lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_username_97_; lean_object* v_userId_98_; lean_object* v_groupId_99_; lean_object* v_shell_100_; lean_object* v_homeDir_101_; lean_object* v_username_102_; lean_object* v_userId_103_; lean_object* v_groupId_104_; lean_object* v_shell_105_; lean_object* v_homeDir_106_; uint8_t v___x_107_; 
v_username_97_ = lean_ctor_get(v_x_95_, 0);
lean_inc_ref(v_username_97_);
v_userId_98_ = lean_ctor_get(v_x_95_, 1);
lean_inc(v_userId_98_);
v_groupId_99_ = lean_ctor_get(v_x_95_, 2);
lean_inc(v_groupId_99_);
v_shell_100_ = lean_ctor_get(v_x_95_, 3);
lean_inc(v_shell_100_);
v_homeDir_101_ = lean_ctor_get(v_x_95_, 4);
lean_inc(v_homeDir_101_);
lean_dec_ref(v_x_95_);
v_username_102_ = lean_ctor_get(v_x_96_, 0);
lean_inc_ref(v_username_102_);
v_userId_103_ = lean_ctor_get(v_x_96_, 1);
lean_inc(v_userId_103_);
v_groupId_104_ = lean_ctor_get(v_x_96_, 2);
lean_inc(v_groupId_104_);
v_shell_105_ = lean_ctor_get(v_x_96_, 3);
lean_inc(v_shell_105_);
v_homeDir_106_ = lean_ctor_get(v_x_96_, 4);
lean_inc(v_homeDir_106_);
lean_dec_ref(v_x_96_);
v___x_107_ = lean_string_dec_eq(v_username_97_, v_username_102_);
lean_dec_ref(v_username_102_);
lean_dec_ref(v_username_97_);
if (v___x_107_ == 0)
{
lean_dec(v_homeDir_106_);
lean_dec(v_shell_105_);
lean_dec(v_groupId_104_);
lean_dec(v_userId_103_);
lean_dec(v_homeDir_101_);
lean_dec(v_shell_100_);
lean_dec(v_groupId_99_);
lean_dec(v_userId_98_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_alloc_closure((void*)(l_Std_Async_System_instDecidableEqUserId___boxed), 2, 0);
v___x_109_ = l_Option_instDecidableEq___redArg(v___x_108_, v_userId_98_, v_userId_103_);
if (v___x_109_ == 0)
{
lean_dec(v_homeDir_106_);
lean_dec(v_shell_105_);
lean_dec(v_groupId_104_);
lean_dec(v_homeDir_101_);
lean_dec(v_shell_100_);
lean_dec(v_groupId_99_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_alloc_closure((void*)(l_Std_Async_System_instDecidableEqGroupId___boxed), 2, 0);
v___x_111_ = l_Option_instDecidableEq___redArg(v___x_110_, v_groupId_99_, v_groupId_104_);
if (v___x_111_ == 0)
{
lean_dec(v_homeDir_106_);
lean_dec(v_shell_105_);
lean_dec(v_homeDir_101_);
lean_dec(v_shell_100_);
return v___x_111_;
}
else
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___x_113_ = l_Option_instDecidableEq___redArg(v___x_112_, v_shell_100_, v_shell_105_);
if (v___x_113_ == 0)
{
lean_dec(v_homeDir_106_);
lean_dec(v_homeDir_101_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = lean_alloc_closure((void*)(l_System_instDecidableEqFilePath___boxed), 2, 0);
v___x_115_ = l_Option_instDecidableEq___redArg(v___x_114_, v_homeDir_101_, v_homeDir_106_);
return v___x_115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqSystemUser_decEq___boxed(lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Std_Async_System_instDecidableEqSystemUser_decEq(v_x_116_, v_x_117_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqSystemUser(lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = l_Std_Async_System_instDecidableEqSystemUser_decEq(v_x_120_, v_x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqSystemUser___boxed(lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_Std_Async_System_instDecidableEqSystemUser(v_x_123_, v_x_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_object* v___x_135_; 
v___x_135_ = ((lean_object*)(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1));
return v___x_135_;
}
else
{
lean_object* v_val_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_151_; 
v_val_136_ = lean_ctor_get(v_x_133_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_151_ == 0)
{
v___x_138_ = v_x_133_;
v_isShared_139_ = v_isSharedCheck_151_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_val_136_);
lean_dec(v_x_133_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_151_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_140_ = ((lean_object*)(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3));
v___x_141_ = lean_unsigned_to_nat(1024u);
v___x_142_ = ((lean_object*)(l_Std_Async_System_instReprUserId___lam__0___closed__1));
v___x_143_ = l_Nat_reprFast(v_val_136_);
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 3);
lean_ctor_set(v___x_138_, 0, v___x_143_);
v___x_145_ = v___x_138_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_150_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_142_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = l_Repr_addAppParen(v___x_146_, v___x_141_);
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_140_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = l_Repr_addAppParen(v___x_148_, v_x_134_);
return v___x_149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___boxed(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0(v_x_152_, v_x_153_);
lean_dec(v_x_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1(lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v___x_157_; 
v___x_157_ = ((lean_object*)(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1));
return v___x_157_;
}
else
{
lean_object* v_val_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_173_; 
v_val_158_ = lean_ctor_get(v_x_155_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_173_ == 0)
{
v___x_160_ = v_x_155_;
v_isShared_161_ = v_isSharedCheck_173_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_val_158_);
lean_dec(v_x_155_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_173_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_162_ = ((lean_object*)(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3));
v___x_163_ = lean_unsigned_to_nat(1024u);
v___x_164_ = ((lean_object*)(l_Std_Async_System_instReprGroupId___lam__0___closed__1));
v___x_165_ = l_Nat_reprFast(v_val_158_);
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 3);
lean_ctor_set(v___x_160_, 0, v___x_165_);
v___x_167_ = v___x_160_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_172_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_164_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = l_Repr_addAppParen(v___x_168_, v___x_163_);
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_162_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = l_Repr_addAppParen(v___x_170_, v_x_156_);
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1___boxed(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1(v_x_174_, v_x_175_);
lean_dec(v_x_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2(lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v___x_179_; 
v___x_179_ = ((lean_object*)(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1));
return v___x_179_;
}
else
{
lean_object* v_val_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_191_; 
v_val_180_ = lean_ctor_get(v_x_177_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_191_ == 0)
{
v___x_182_ = v_x_177_;
v_isShared_183_ = v_isSharedCheck_191_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_val_180_);
lean_dec(v_x_177_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_191_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_184_ = ((lean_object*)(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3));
v___x_185_ = l_String_quote(v_val_180_);
if (v_isShared_183_ == 0)
{
lean_ctor_set_tag(v___x_182_, 3);
lean_ctor_set(v___x_182_, 0, v___x_185_);
v___x_187_ = v___x_182_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_190_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_184_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = l_Repr_addAppParen(v___x_188_, v_x_178_);
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2___boxed(lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2(v_x_192_, v_x_193_);
lean_dec(v_x_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3(lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
lean_object* v___x_200_; 
v___x_200_ = ((lean_object*)(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__1));
return v___x_200_;
}
else
{
lean_object* v_val_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_216_; 
v_val_201_ = lean_ctor_get(v_x_198_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_216_ == 0)
{
v___x_203_ = v_x_198_;
v_isShared_204_ = v_isSharedCheck_216_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_val_201_);
lean_dec(v_x_198_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_216_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_205_ = ((lean_object*)(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0___closed__3));
v___x_206_ = lean_unsigned_to_nat(1024u);
v___x_207_ = ((lean_object*)(l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___closed__1));
v___x_208_ = l_String_quote(v_val_201_);
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 3);
lean_ctor_set(v___x_203_, 0, v___x_208_);
v___x_210_ = v___x_203_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_215_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_207_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = l_Repr_addAppParen(v___x_211_, v___x_206_);
v___x_213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_205_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = l_Repr_addAppParen(v___x_213_, v_x_199_);
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3___boxed(lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3(v_x_217_, v_x_218_);
lean_dec(v_x_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Async_System_instReprSystemUser_repr_spec__4(lean_object* v_a_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_nat_to_int(v_a_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_unsigned_to_nat(12u);
v___x_236_ = lean_nat_to_int(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(10u);
v___x_244_ = lean_nat_to_int(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_unsigned_to_nat(11u);
v___x_249_ = lean_nat_to_int(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(9u);
v___x_254_ = lean_nat_to_int(v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__0));
v___x_260_ = lean_string_length(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__22);
v___x_262_ = lean_nat_to_int(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprSystemUser_repr___redArg(lean_object* v_x_267_){
_start:
{
lean_object* v_username_268_; lean_object* v_userId_269_; lean_object* v_groupId_270_; lean_object* v_shell_271_; lean_object* v_homeDir_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_username_268_ = lean_ctor_get(v_x_267_, 0);
lean_inc_ref(v_username_268_);
v_userId_269_ = lean_ctor_get(v_x_267_, 1);
lean_inc(v_userId_269_);
v_groupId_270_ = lean_ctor_get(v_x_267_, 2);
lean_inc(v_groupId_270_);
v_shell_271_ = lean_ctor_get(v_x_267_, 3);
lean_inc(v_shell_271_);
v_homeDir_272_ = lean_ctor_get(v_x_267_, 4);
lean_inc(v_homeDir_272_);
lean_dec_ref(v_x_267_);
v___x_273_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5));
v___x_274_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__6));
v___x_275_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7);
v___x_276_ = l_String_quote(v_username_268_);
v___x_277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
v___x_278_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_275_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = 0;
v___x_280_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set_uint8(v___x_280_, sizeof(void*)*1, v___x_279_);
v___x_281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_274_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9));
v___x_283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_box(1);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__11));
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_273_);
v___x_289_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__12);
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__0(v_userId_269_, v___x_290_);
v___x_292_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_289_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*1, v___x_279_);
v___x_294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_288_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_282_);
v___x_296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_284_);
v___x_297_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14));
v___x_298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_273_);
v___x_300_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15);
v___x_301_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__1(v_groupId_270_, v___x_290_);
v___x_302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set_uint8(v___x_303_, sizeof(void*)*1, v___x_279_);
v___x_304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_299_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_282_);
v___x_306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_284_);
v___x_307_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__17));
v___x_308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_273_);
v___x_310_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18);
v___x_311_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__2(v_shell_271_, v___x_290_);
v___x_312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*1, v___x_279_);
v___x_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_309_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_282_);
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_284_);
v___x_317_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__20));
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_273_);
v___x_320_ = l_Option_repr___at___00Std_Async_System_instReprSystemUser_repr_spec__3(v_homeDir_272_, v___x_290_);
v___x_321_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_300_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*1, v___x_279_);
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_319_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23);
v___x_325_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24));
v___x_326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_323_);
v___x_327_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25));
v___x_328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_324_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set_uint8(v___x_330_, sizeof(void*)*1, v___x_279_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprSystemUser_repr(lean_object* v_x_331_, lean_object* v_prec_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Std_Async_System_instReprSystemUser_repr___redArg(v_x_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprSystemUser_repr___boxed(lean_object* v_x_334_, lean_object* v_prec_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_Async_System_instReprSystemUser_repr(v_x_334_, v_prec_335_);
lean_dec(v_prec_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(lean_object* v___y_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = l_String_quote(v___y_339_);
v___x_341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_344_) == 0)
{
lean_dec(v_x_342_);
return v_x_343_;
}
else
{
lean_object* v_head_345_; lean_object* v_tail_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_357_; 
v_head_345_ = lean_ctor_get(v_x_344_, 0);
v_tail_346_ = lean_ctor_get(v_x_344_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v_x_344_);
if (v_isSharedCheck_357_ == 0)
{
v___x_348_ = v_x_344_;
v_isShared_349_ = v_isSharedCheck_357_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_tail_346_);
lean_inc(v_head_345_);
lean_dec(v_x_344_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_357_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
lean_inc(v_x_342_);
if (v_isShared_349_ == 0)
{
lean_ctor_set_tag(v___x_348_, 5);
lean_ctor_set(v___x_348_, 1, v_x_342_);
lean_ctor_set(v___x_348_, 0, v_x_343_);
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_x_343_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_x_342_);
v___x_351_ = v_reuseFailAlloc_356_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = l_String_quote(v_head_345_);
v___x_353_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
v___x_354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_351_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v_x_343_ = v___x_354_;
v_x_344_ = v_tail_346_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1(lean_object* v_x_358_, lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
lean_dec(v_x_358_);
return v_x_359_;
}
else
{
lean_object* v_head_361_; lean_object* v_tail_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_373_; 
v_head_361_ = lean_ctor_get(v_x_360_, 0);
v_tail_362_ = lean_ctor_get(v_x_360_, 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_373_ == 0)
{
v___x_364_ = v_x_360_;
v_isShared_365_ = v_isSharedCheck_373_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_tail_362_);
lean_inc(v_head_361_);
lean_dec(v_x_360_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_373_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
lean_inc(v_x_358_);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 5);
lean_ctor_set(v___x_364_, 1, v_x_358_);
lean_ctor_set(v___x_364_, 0, v_x_359_);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_x_359_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_x_358_);
v___x_367_ = v_reuseFailAlloc_372_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_368_ = l_String_quote(v_head_361_);
v___x_369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
v___x_370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_367_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1_spec__2(v_x_358_, v___x_370_, v_tail_362_);
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0(lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
lean_object* v___x_376_; 
lean_dec(v_x_375_);
v___x_376_ = lean_box(0);
return v___x_376_;
}
else
{
lean_object* v_tail_377_; 
v_tail_377_ = lean_ctor_get(v_x_374_, 1);
if (lean_obj_tag(v_tail_377_) == 0)
{
lean_object* v_head_378_; lean_object* v___x_379_; 
lean_dec(v_x_375_);
v_head_378_ = lean_ctor_get(v_x_374_, 0);
lean_inc(v_head_378_);
lean_dec_ref_known(v_x_374_, 2);
v___x_379_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(v_head_378_);
return v___x_379_;
}
else
{
lean_object* v_head_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
lean_inc(v_tail_377_);
v_head_380_ = lean_ctor_get(v_x_374_, 0);
lean_inc(v_head_380_);
lean_dec_ref_known(v_x_374_, 2);
v___x_381_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(v_head_380_);
v___x_382_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1(v_x_375_, v___x_381_, v_tail_377_);
return v___x_382_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__0));
v___x_389_ = lean_string_length(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_obj_once(&l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__3);
v___x_391_ = lean_nat_to_int(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0(lean_object* v_xs_399_){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_400_ = lean_array_get_size(v_xs_399_);
v___x_401_ = lean_unsigned_to_nat(0u);
v___x_402_ = lean_nat_dec_eq(v___x_400_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_403_ = lean_array_to_list(v_xs_399_);
v___x_404_ = ((lean_object*)(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1));
v___x_405_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0_spec__0(v___x_403_, v___x_404_);
v___x_406_ = lean_obj_once(&l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4, &l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__4);
v___x_407_ = ((lean_object*)(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__5));
v___x_408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_405_);
v___x_409_ = ((lean_object*)(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6));
v___x_410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_406_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = l_Std_Format_fill(v___x_411_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; 
lean_dec_ref(v_xs_399_);
v___x_413_ = ((lean_object*)(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__8));
return v___x_413_;
}
}
}
static lean_object* _init_l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_unsigned_to_nat(13u);
v___x_424_ = lean_nat_to_int(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprGroupInfo_repr___redArg(lean_object* v_x_428_){
_start:
{
lean_object* v_groupName_429_; lean_object* v_groupId_430_; lean_object* v_members_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_groupName_429_ = lean_ctor_get(v_x_428_, 0);
lean_inc_ref(v_groupName_429_);
v_groupId_430_ = lean_ctor_get(v_x_428_, 1);
lean_inc(v_groupId_430_);
v_members_431_ = lean_ctor_get(v_x_428_, 2);
lean_inc_ref(v_members_431_);
lean_dec_ref(v_x_428_);
v___x_432_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5));
v___x_433_ = ((lean_object*)(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__3));
v___x_434_ = lean_obj_once(&l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4, &l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4_once, _init_l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4);
v___x_435_ = l_String_quote(v_groupName_429_);
v___x_436_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
v___x_437_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_434_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = 0;
v___x_439_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set_uint8(v___x_439_, sizeof(void*)*1, v___x_438_);
v___x_440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_433_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9));
v___x_442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = lean_box(1);
v___x_444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__14));
v___x_446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_432_);
v___x_448_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = ((lean_object*)(l_Std_Async_System_instReprGroupId___lam__0___closed__1));
v___x_451_ = l_Nat_reprFast(v_groupId_430_);
v___x_452_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_450_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = l_Repr_addAppParen(v___x_453_, v___x_449_);
v___x_455_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_448_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*1, v___x_438_);
v___x_457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_447_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_441_);
v___x_459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_443_);
v___x_460_ = ((lean_object*)(l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__6));
v___x_461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_432_);
v___x_463_ = l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0(v_members_431_);
v___x_464_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_448_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*1, v___x_438_);
v___x_466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_462_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23);
v___x_468_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24));
v___x_469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_466_);
v___x_470_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25));
v___x_471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_467_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*1, v___x_438_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprGroupInfo_repr(lean_object* v_x_474_, lean_object* v_prec_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_Async_System_instReprGroupInfo_repr___redArg(v_x_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprGroupInfo_repr___boxed(lean_object* v_x_477_, lean_object* v_prec_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_Async_System_instReprGroupInfo_repr(v_x_477_, v_prec_478_);
lean_dec(v_prec_478_);
return v_res_479_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedCPUTimes_default___closed__0(void){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
return v___x_490_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedCPUTimes_default___closed__1(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_obj_once(&l_Std_Async_System_instInhabitedCPUTimes_default___closed__0, &l_Std_Async_System_instInhabitedCPUTimes_default___closed__0_once, _init_l_Std_Async_System_instInhabitedCPUTimes_default___closed__0);
v___x_492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
lean_ctor_set(v___x_492_, 2, v___x_491_);
lean_ctor_set(v___x_492_, 3, v___x_491_);
lean_ctor_set(v___x_492_, 4, v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedCPUTimes_default(void){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = lean_obj_once(&l_Std_Async_System_instInhabitedCPUTimes_default___closed__1, &l_Std_Async_System_instInhabitedCPUTimes_default___closed__1_once, _init_l_Std_Async_System_instInhabitedCPUTimes_default___closed__1);
return v___x_493_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedCPUTimes(void){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_Async_System_instInhabitedCPUTimes_default;
return v___x_494_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqCPUTimes_decEq(lean_object* v_x_495_, lean_object* v_x_496_){
_start:
{
lean_object* v_userTime_497_; lean_object* v_niceTime_498_; lean_object* v_systemTime_499_; lean_object* v_idleTime_500_; lean_object* v_interruptTime_501_; lean_object* v_userTime_502_; lean_object* v_niceTime_503_; lean_object* v_systemTime_504_; lean_object* v_idleTime_505_; lean_object* v_interruptTime_506_; uint8_t v___x_507_; 
v_userTime_497_ = lean_ctor_get(v_x_495_, 0);
v_niceTime_498_ = lean_ctor_get(v_x_495_, 1);
v_systemTime_499_ = lean_ctor_get(v_x_495_, 2);
v_idleTime_500_ = lean_ctor_get(v_x_495_, 3);
v_interruptTime_501_ = lean_ctor_get(v_x_495_, 4);
v_userTime_502_ = lean_ctor_get(v_x_496_, 0);
v_niceTime_503_ = lean_ctor_get(v_x_496_, 1);
v_systemTime_504_ = lean_ctor_get(v_x_496_, 2);
v_idleTime_505_ = lean_ctor_get(v_x_496_, 3);
v_interruptTime_506_ = lean_ctor_get(v_x_496_, 4);
v___x_507_ = lean_int_dec_eq(v_userTime_497_, v_userTime_502_);
if (v___x_507_ == 0)
{
return v___x_507_;
}
else
{
uint8_t v___x_508_; 
v___x_508_ = lean_int_dec_eq(v_niceTime_498_, v_niceTime_503_);
if (v___x_508_ == 0)
{
return v___x_508_;
}
else
{
uint8_t v___x_509_; 
v___x_509_ = lean_int_dec_eq(v_systemTime_499_, v_systemTime_504_);
if (v___x_509_ == 0)
{
return v___x_509_;
}
else
{
uint8_t v___x_510_; 
v___x_510_ = lean_int_dec_eq(v_idleTime_500_, v_idleTime_505_);
if (v___x_510_ == 0)
{
return v___x_510_;
}
else
{
uint8_t v___x_511_; 
v___x_511_ = lean_int_dec_eq(v_interruptTime_501_, v_interruptTime_506_);
return v___x_511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqCPUTimes_decEq___boxed(lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
uint8_t v_res_514_; lean_object* v_r_515_; 
v_res_514_ = l_Std_Async_System_instDecidableEqCPUTimes_decEq(v_x_512_, v_x_513_);
lean_dec_ref(v_x_513_);
lean_dec_ref(v_x_512_);
v_r_515_ = lean_box(v_res_514_);
return v_r_515_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqCPUTimes(lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = l_Std_Async_System_instDecidableEqCPUTimes_decEq(v_x_516_, v_x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqCPUTimes___boxed(lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
uint8_t v_res_521_; lean_object* v_r_522_; 
v_res_521_ = l_Std_Async_System_instDecidableEqCPUTimes(v_x_519_, v_x_520_);
lean_dec_ref(v_x_520_);
lean_dec_ref(v_x_519_);
v_r_522_ = lean_box(v_res_521_);
return v_r_522_;
}
}
static lean_object* _init_l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(14u);
v___x_539_ = lean_nat_to_int(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(17u);
v___x_547_ = lean_nat_to_int(v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg(lean_object* v_x_548_){
_start:
{
lean_object* v_userTime_549_; lean_object* v_niceTime_550_; lean_object* v_systemTime_551_; lean_object* v_idleTime_552_; lean_object* v_interruptTime_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_userTime_549_ = lean_ctor_get(v_x_548_, 0);
v_niceTime_550_ = lean_ctor_get(v_x_548_, 1);
v_systemTime_551_ = lean_ctor_get(v_x_548_, 2);
v_idleTime_552_ = lean_ctor_get(v_x_548_, 3);
v_interruptTime_553_ = lean_ctor_get(v_x_548_, 4);
v___x_554_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5));
v___x_555_ = ((lean_object*)(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__3));
v___x_556_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__7);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_userTime_549_, v___x_557_);
v___x_559_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_556_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = 0;
v___x_561_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*1, v___x_560_);
v___x_562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_555_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9));
v___x_564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = lean_box(1);
v___x_566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = ((lean_object*)(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__5));
v___x_568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_566_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_554_);
v___x_570_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_niceTime_550_, v___x_557_);
v___x_571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_556_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*1, v___x_560_);
v___x_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_569_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_563_);
v___x_575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_565_);
v___x_576_ = ((lean_object*)(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__7));
v___x_577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_554_);
v___x_579_ = lean_obj_once(&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8, &l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8_once, _init_l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__8);
v___x_580_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_systemTime_551_, v___x_557_);
v___x_581_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set_uint8(v___x_582_, sizeof(void*)*1, v___x_560_);
v___x_583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_578_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___x_563_);
v___x_585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___x_565_);
v___x_586_ = ((lean_object*)(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__10));
v___x_587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_554_);
v___x_589_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_idleTime_552_, v___x_557_);
v___x_590_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_556_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set_uint8(v___x_591_, sizeof(void*)*1, v___x_560_);
v___x_592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_588_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_563_);
v___x_594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_565_);
v___x_595_ = ((lean_object*)(l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__12));
v___x_596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_554_);
v___x_598_ = lean_obj_once(&l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13, &l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13_once, _init_l_Std_Async_System_instReprCPUTimes_repr___redArg___closed__13);
v___x_599_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v_interruptTime_553_, v___x_557_);
v___x_600_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set_uint8(v___x_601_, sizeof(void*)*1, v___x_560_);
v___x_602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_597_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23);
v___x_604_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24));
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_602_);
v___x_606_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25));
v___x_607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_603_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*1, v___x_560_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUTimes_repr___redArg___boxed(lean_object* v_x_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_Async_System_instReprCPUTimes_repr___redArg(v_x_610_);
lean_dec_ref(v_x_610_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUTimes_repr(lean_object* v_x_612_, lean_object* v_prec_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_Async_System_instReprCPUTimes_repr___redArg(v_x_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUTimes_repr___boxed(lean_object* v_x_615_, lean_object* v_prec_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_Async_System_instReprCPUTimes_repr(v_x_615_, v_prec_616_);
lean_dec(v_prec_616_);
lean_dec_ref(v_x_615_);
return v_res_617_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedCPUInfo_default___closed__0(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_620_ = l_Std_Async_System_instInhabitedCPUTimes_default;
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = ((lean_object*)(l_Std_Async_System_instInhabitedSystemUser_default___closed__0));
v___x_623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
lean_ctor_set(v___x_623_, 2, v___x_620_);
return v___x_623_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedCPUInfo_default(void){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = lean_obj_once(&l_Std_Async_System_instInhabitedCPUInfo_default___closed__0, &l_Std_Async_System_instInhabitedCPUInfo_default___closed__0_once, _init_l_Std_Async_System_instInhabitedCPUInfo_default___closed__0);
return v___x_624_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedCPUInfo(void){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_Async_System_instInhabitedCPUInfo_default;
return v___x_625_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqCPUInfo_decEq(lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
lean_object* v_model_628_; lean_object* v_speed_629_; lean_object* v_times_630_; lean_object* v_model_631_; lean_object* v_speed_632_; lean_object* v_times_633_; uint8_t v___x_634_; 
v_model_628_ = lean_ctor_get(v_x_626_, 0);
v_speed_629_ = lean_ctor_get(v_x_626_, 1);
v_times_630_ = lean_ctor_get(v_x_626_, 2);
v_model_631_ = lean_ctor_get(v_x_627_, 0);
v_speed_632_ = lean_ctor_get(v_x_627_, 1);
v_times_633_ = lean_ctor_get(v_x_627_, 2);
v___x_634_ = lean_string_dec_eq(v_model_628_, v_model_631_);
if (v___x_634_ == 0)
{
return v___x_634_;
}
else
{
uint8_t v___x_635_; 
v___x_635_ = lean_nat_dec_eq(v_speed_629_, v_speed_632_);
if (v___x_635_ == 0)
{
return v___x_635_;
}
else
{
uint8_t v___x_636_; 
v___x_636_ = l_Std_Async_System_instDecidableEqCPUTimes_decEq(v_times_630_, v_times_633_);
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqCPUInfo_decEq___boxed(lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
uint8_t v_res_639_; lean_object* v_r_640_; 
v_res_639_ = l_Std_Async_System_instDecidableEqCPUInfo_decEq(v_x_637_, v_x_638_);
lean_dec_ref(v_x_638_);
lean_dec_ref(v_x_637_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_System_instDecidableEqCPUInfo(lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = l_Std_Async_System_instDecidableEqCPUInfo_decEq(v_x_641_, v_x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instDecidableEqCPUInfo___boxed(lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
uint8_t v_res_646_; lean_object* v_r_647_; 
v_res_646_ = l_Std_Async_System_instDecidableEqCPUInfo(v_x_644_, v_x_645_);
lean_dec_ref(v_x_645_);
lean_dec_ref(v_x_644_);
v_r_647_ = lean_box(v_res_646_);
return v_r_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUInfo_repr___redArg(lean_object* v_x_663_){
_start:
{
lean_object* v_model_664_; lean_object* v_speed_665_; lean_object* v_times_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_model_664_ = lean_ctor_get(v_x_663_, 0);
lean_inc_ref(v_model_664_);
v_speed_665_ = lean_ctor_get(v_x_663_, 1);
lean_inc(v_speed_665_);
v_times_666_ = lean_ctor_get(v_x_663_, 2);
lean_inc_ref(v_times_666_);
lean_dec_ref(v_x_663_);
v___x_667_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5));
v___x_668_ = ((lean_object*)(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__3));
v___x_669_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__18);
v___x_670_ = l_String_quote(v_model_664_);
v___x_671_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
v___x_672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_669_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = 0;
v___x_674_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*1, v___x_673_);
v___x_675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_668_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9));
v___x_677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = lean_box(1);
v___x_679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = ((lean_object*)(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__5));
v___x_681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v___x_667_);
v___x_683_ = l_Nat_reprFast(v_speed_665_);
v___x_684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
v___x_685_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_669_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*1, v___x_673_);
v___x_687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_682_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___x_676_);
v___x_689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___x_678_);
v___x_690_ = ((lean_object*)(l_Std_Async_System_instReprCPUInfo_repr___redArg___closed__7));
v___x_691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_667_);
v___x_693_ = l_Std_Async_System_instReprCPUTimes_repr___redArg(v_times_666_);
lean_dec_ref(v_times_666_);
v___x_694_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_669_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set_uint8(v___x_695_, sizeof(void*)*1, v___x_673_);
v___x_696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_692_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23);
v___x_698_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24));
v___x_699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___x_696_);
v___x_700_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25));
v___x_701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_697_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*1, v___x_673_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUInfo_repr(lean_object* v_x_704_, lean_object* v_prec_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_Async_System_instReprCPUInfo_repr___redArg(v_x_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprCPUInfo_repr___boxed(lean_object* v_x_707_, lean_object* v_prec_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_Async_System_instReprCPUInfo_repr(v_x_707_, v_prec_708_);
lean_dec(v_prec_708_);
return v_res_709_;
}
}
static lean_object* _init_l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_unsigned_to_nat(8u);
v___x_722_ = lean_nat_to_int(v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprOSInfo_repr___redArg(lean_object* v_x_732_){
_start:
{
lean_object* v_name_733_; lean_object* v_release_734_; lean_object* v_version_735_; lean_object* v_machine_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_name_733_ = lean_ctor_get(v_x_732_, 0);
lean_inc_ref(v_name_733_);
v_release_734_ = lean_ctor_get(v_x_732_, 1);
lean_inc_ref(v_release_734_);
v_version_735_ = lean_ctor_get(v_x_732_, 2);
lean_inc_ref(v_version_735_);
v_machine_736_ = lean_ctor_get(v_x_732_, 3);
lean_inc_ref(v_machine_736_);
lean_dec_ref(v_x_732_);
v___x_737_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__5));
v___x_738_ = ((lean_object*)(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__3));
v___x_739_ = lean_obj_once(&l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4, &l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4_once, _init_l_Std_Async_System_instReprOSInfo_repr___redArg___closed__4);
v___x_740_ = l_String_quote(v_name_733_);
v___x_741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
v___x_742_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_739_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = 0;
v___x_744_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*1, v___x_743_);
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_738_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__9));
v___x_747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_box(1);
v___x_749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = ((lean_object*)(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__6));
v___x_751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_737_);
v___x_753_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__15);
v___x_754_ = l_String_quote(v_release_734_);
v___x_755_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
v___x_756_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_753_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*1, v___x_743_);
v___x_758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_752_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v___x_746_);
v___x_760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
lean_ctor_set(v___x_760_, 1, v___x_748_);
v___x_761_ = ((lean_object*)(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__8));
v___x_762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___x_737_);
v___x_764_ = l_String_quote(v_version_735_);
v___x_765_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
v___x_766_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_753_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*1, v___x_743_);
v___x_768_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_763_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v___x_746_);
v___x_770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_748_);
v___x_771_ = ((lean_object*)(l_Std_Async_System_instReprOSInfo_repr___redArg___closed__10));
v___x_772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v___x_737_);
v___x_774_ = l_String_quote(v_machine_736_);
v___x_775_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
v___x_776_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_753_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*1, v___x_743_);
v___x_778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_773_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23);
v___x_780_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24));
v___x_781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_778_);
v___x_782_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25));
v___x_783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_779_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*1, v___x_743_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprOSInfo_repr(lean_object* v_x_786_, lean_object* v_prec_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Std_Async_System_instReprOSInfo_repr___redArg(v_x_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprOSInfo_repr___boxed(lean_object* v_x_789_, lean_object* v_prec_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_Async_System_instReprOSInfo_repr(v_x_789_, v_prec_790_);
lean_dec(v_prec_790_);
return v_res_791_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedEnvironment_default___closed__0(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = lean_box(0);
v___x_799_ = lean_unsigned_to_nat(16u);
v___x_800_ = lean_mk_array(v___x_799_, v___x_798_);
return v___x_800_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedEnvironment_default___closed__1(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_obj_once(&l_Std_Async_System_instInhabitedEnvironment_default___closed__0, &l_Std_Async_System_instInhabitedEnvironment_default___closed__0_once, _init_l_Std_Async_System_instInhabitedEnvironment_default___closed__0);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
return v___x_803_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedEnvironment_default(void){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = lean_obj_once(&l_Std_Async_System_instInhabitedEnvironment_default___closed__1, &l_Std_Async_System_instInhabitedEnvironment_default___closed__1_once, _init_l_Std_Async_System_instInhabitedEnvironment_default___closed__1);
return v___x_804_;
}
}
static lean_object* _init_l_Std_Async_System_instInhabitedEnvironment(void){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Std_Async_System_instInhabitedEnvironment_default;
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1(lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
lean_inc(v_x_806_);
return v_x_806_;
}
else
{
lean_object* v_key_808_; lean_object* v_value_809_; lean_object* v_tail_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_key_808_ = lean_ctor_get(v_x_807_, 0);
v_value_809_ = lean_ctor_get(v_x_807_, 1);
v_tail_810_ = lean_ctor_get(v_x_807_, 2);
v___x_811_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1(v_x_806_, v_tail_810_);
lean_inc(v_value_809_);
lean_inc(v_key_808_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v_key_808_);
lean_ctor_set(v___x_812_, 1, v_value_809_);
v___x_813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___x_811_);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1___boxed(lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1(v_x_814_, v_x_815_);
lean_dec(v_x_815_);
lean_dec(v_x_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2(lean_object* v_as_817_, size_t v_i_818_, size_t v_stop_819_, lean_object* v_b_820_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = lean_usize_dec_eq(v_i_818_, v_stop_819_);
if (v___x_821_ == 0)
{
size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_822_ = ((size_t)1ULL);
v___x_823_ = lean_usize_sub(v_i_818_, v___x_822_);
v___x_824_ = lean_array_uget_borrowed(v_as_817_, v___x_823_);
v___x_825_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Async_System_instReprEnvironment_repr_spec__1(v_b_820_, v___x_824_);
lean_dec(v_b_820_);
v_i_818_ = v___x_823_;
v_b_820_ = v___x_825_;
goto _start;
}
else
{
return v_b_820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2___boxed(lean_object* v_as_827_, lean_object* v_i_828_, lean_object* v_stop_829_, lean_object* v_b_830_){
_start:
{
size_t v_i_boxed_831_; size_t v_stop_boxed_832_; lean_object* v_res_833_; 
v_i_boxed_831_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v_stop_boxed_832_ = lean_unbox_usize(v_stop_829_);
lean_dec(v_stop_829_);
v_res_833_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2(v_as_827_, v_i_boxed_831_, v_stop_boxed_832_, v_b_830_);
lean_dec_ref(v_as_827_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1_spec__4(lean_object* v_x_834_, lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
if (lean_obj_tag(v_x_836_) == 0)
{
lean_dec(v_x_834_);
return v_x_835_;
}
else
{
lean_object* v_head_837_; lean_object* v_tail_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_847_; 
v_head_837_ = lean_ctor_get(v_x_836_, 0);
v_tail_838_ = lean_ctor_get(v_x_836_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v_x_836_);
if (v_isSharedCheck_847_ == 0)
{
v___x_840_ = v_x_836_;
v_isShared_841_ = v_isSharedCheck_847_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_tail_838_);
lean_inc(v_head_837_);
lean_dec(v_x_836_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_847_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
lean_inc(v_x_834_);
if (v_isShared_841_ == 0)
{
lean_ctor_set_tag(v___x_840_, 5);
lean_ctor_set(v___x_840_, 1, v_x_834_);
lean_ctor_set(v___x_840_, 0, v_x_835_);
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_x_835_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_x_834_);
v___x_843_ = v_reuseFailAlloc_846_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; 
v___x_844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v_head_837_);
v_x_835_ = v___x_844_;
v_x_836_ = v_tail_838_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1(lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
if (lean_obj_tag(v_x_848_) == 0)
{
lean_object* v___x_850_; 
lean_dec(v_x_849_);
v___x_850_ = lean_box(0);
return v___x_850_;
}
else
{
lean_object* v_tail_851_; 
v_tail_851_ = lean_ctor_get(v_x_848_, 1);
if (lean_obj_tag(v_tail_851_) == 0)
{
lean_object* v_head_852_; 
lean_dec(v_x_849_);
v_head_852_ = lean_ctor_get(v_x_848_, 0);
lean_inc(v_head_852_);
lean_dec_ref_known(v_x_848_, 2);
return v_head_852_;
}
else
{
lean_object* v_head_853_; lean_object* v___x_854_; 
lean_inc(v_tail_851_);
v_head_853_ = lean_ctor_get(v_x_848_, 0);
lean_inc(v_head_853_);
lean_dec_ref_known(v_x_848_, 2);
v___x_854_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1_spec__4(v_x_849_, v_head_853_, v_tail_851_);
return v___x_854_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__0));
v___x_858_ = lean_string_length(v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__2);
v___x_860_ = lean_nat_to_int(v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(lean_object* v_x_865_){
_start:
{
lean_object* v_fst_866_; lean_object* v_snd_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_891_; 
v_fst_866_ = lean_ctor_get(v_x_865_, 0);
v_snd_867_ = lean_ctor_get(v_x_865_, 1);
v_isSharedCheck_891_ = !lean_is_exclusive(v_x_865_);
if (v_isSharedCheck_891_ == 0)
{
v___x_869_ = v_x_865_;
v_isShared_870_ = v_isSharedCheck_891_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_snd_867_);
lean_inc(v_fst_866_);
lean_dec(v_x_865_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_891_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_871_ = l_String_quote(v_fst_866_);
v___x_872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
v___x_873_ = lean_box(0);
if (v_isShared_870_ == 0)
{
lean_ctor_set_tag(v___x_869_, 1);
lean_ctor_set(v___x_869_, 1, v___x_873_);
lean_ctor_set(v___x_869_, 0, v___x_872_);
v___x_875_ = v___x_869_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_890_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; 
v___x_876_ = l_String_quote(v_snd_867_);
v___x_877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
v___x_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___x_875_);
v___x_879_ = l_List_reverse___redArg(v___x_878_);
v___x_880_ = ((lean_object*)(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1));
v___x_881_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0_spec__1(v___x_879_, v___x_880_);
v___x_882_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__3);
v___x_883_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__4));
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_881_);
v___x_885_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg___closed__5));
v___x_886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_882_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = 0;
v___x_889_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*1, v___x_888_);
return v___x_889_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3_spec__7(lean_object* v_x_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
lean_dec(v_x_892_);
return v_x_893_;
}
else
{
lean_object* v_head_895_; lean_object* v_tail_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_906_; 
v_head_895_ = lean_ctor_get(v_x_894_, 0);
v_tail_896_ = lean_ctor_get(v_x_894_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_x_894_);
if (v_isSharedCheck_906_ == 0)
{
v___x_898_ = v_x_894_;
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_tail_896_);
lean_inc(v_head_895_);
lean_dec(v_x_894_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_906_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
lean_inc(v_x_892_);
if (v_isShared_899_ == 0)
{
lean_ctor_set_tag(v___x_898_, 5);
lean_ctor_set(v___x_898_, 1, v_x_892_);
lean_ctor_set(v___x_898_, 0, v_x_893_);
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_x_893_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_x_892_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_head_895_);
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v_x_893_ = v___x_903_;
v_x_894_ = v_tail_896_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3(lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
if (lean_obj_tag(v_x_909_) == 0)
{
lean_dec(v_x_907_);
return v_x_908_;
}
else
{
lean_object* v_head_910_; lean_object* v_tail_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_921_; 
v_head_910_ = lean_ctor_get(v_x_909_, 0);
v_tail_911_ = lean_ctor_get(v_x_909_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_x_909_);
if (v_isSharedCheck_921_ == 0)
{
v___x_913_ = v_x_909_;
v_isShared_914_ = v_isSharedCheck_921_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_tail_911_);
lean_inc(v_head_910_);
lean_dec(v_x_909_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_921_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
lean_inc(v_x_907_);
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 5);
lean_ctor_set(v___x_913_, 1, v_x_907_);
lean_ctor_set(v___x_913_, 0, v_x_908_);
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_x_908_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_x_907_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_head_910_);
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3_spec__7(v_x_907_, v___x_918_, v_tail_911_);
return v___x_919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1(lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
if (lean_obj_tag(v_x_922_) == 0)
{
lean_object* v___x_924_; 
lean_dec(v_x_923_);
v___x_924_ = lean_box(0);
return v___x_924_;
}
else
{
lean_object* v_tail_925_; 
v_tail_925_ = lean_ctor_get(v_x_922_, 1);
if (lean_obj_tag(v_tail_925_) == 0)
{
lean_object* v_head_926_; lean_object* v___x_927_; 
lean_dec(v_x_923_);
v_head_926_ = lean_ctor_get(v_x_922_, 0);
lean_inc(v_head_926_);
lean_dec_ref_known(v_x_922_, 2);
v___x_927_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_head_926_);
return v___x_927_;
}
else
{
lean_object* v_head_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_inc(v_tail_925_);
v_head_928_ = lean_ctor_get(v_x_922_, 0);
lean_inc(v_head_928_);
lean_dec_ref_known(v_x_922_, 2);
v___x_929_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_head_928_);
v___x_930_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1_spec__3(v_x_923_, v___x_929_, v_tail_925_);
return v___x_930_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__2));
v___x_936_ = lean_string_length(v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = lean_obj_once(&l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3, &l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3_once, _init_l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__3);
v___x_938_ = lean_nat_to_int(v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg(lean_object* v_a_941_){
_start:
{
if (lean_obj_tag(v_a_941_) == 0)
{
lean_object* v___x_942_; 
v___x_942_ = ((lean_object*)(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__1));
return v___x_942_;
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; lean_object* v___x_952_; 
v___x_943_ = ((lean_object*)(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__1));
v___x_944_ = l_Std_Format_joinSep___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__1(v_a_941_, v___x_943_);
v___x_945_ = lean_obj_once(&l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4, &l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4_once, _init_l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__4);
v___x_946_ = ((lean_object*)(l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg___closed__5));
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_944_);
v___x_948_ = ((lean_object*)(l_Array_repr___at___00Std_Async_System_instReprGroupInfo_repr_spec__0___closed__6));
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_945_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = 0;
v___x_952_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*1, v___x_951_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprEnvironment_repr___redArg(lean_object* v_x_965_){
_start:
{
lean_object* v_buckets_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_998_; 
v_buckets_966_ = lean_ctor_get(v_x_965_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v_x_965_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v_x_965_, 0);
lean_dec(v_unused_999_);
v___x_968_ = v_x_965_;
v_isShared_969_ = v_isSharedCheck_998_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_buckets_966_);
lean_dec(v_x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_998_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___y_975_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_970_ = ((lean_object*)(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__3));
v___x_971_ = lean_obj_once(&l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4, &l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4_once, _init_l_Std_Async_System_instReprGroupInfo_repr___redArg___closed__4);
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = ((lean_object*)(l_Std_Async_System_instReprEnvironment_repr___redArg___closed__5));
v___x_992_ = lean_box(0);
v___x_993_ = lean_array_get_size(v_buckets_966_);
v___x_994_ = lean_nat_dec_lt(v___x_972_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec_ref(v_buckets_966_);
v___y_975_ = v___x_992_;
goto v___jp_974_;
}
else
{
size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_usize_of_nat(v___x_993_);
v___x_996_ = ((size_t)0ULL);
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Async_System_instReprEnvironment_repr_spec__2(v_buckets_966_, v___x_995_, v___x_996_, v___x_992_);
lean_dec_ref(v_buckets_966_);
v___y_975_ = v___x_997_;
goto v___jp_974_;
}
v___jp_974_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg(v___y_975_);
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 5);
lean_ctor_set(v___x_968_, 1, v___x_976_);
lean_ctor_set(v___x_968_, 0, v___x_973_);
v___x_978_ = v___x_968_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_976_);
v___x_978_ = v_reuseFailAlloc_991_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_979_ = l_Repr_addAppParen(v___x_978_, v___x_972_);
v___x_980_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_971_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = 0;
v___x_982_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*1, v___x_981_);
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_970_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_obj_once(&l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23, &l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23_once, _init_l_Std_Async_System_instReprSystemUser_repr___redArg___closed__23);
v___x_985_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__24));
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_983_);
v___x_987_ = ((lean_object*)(l_Std_Async_System_instReprSystemUser_repr___redArg___closed__25));
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_984_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*1, v___x_981_);
return v___x_990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprEnvironment_repr(lean_object* v_x_1000_, lean_object* v_prec_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_Async_System_instReprEnvironment_repr___redArg(v_x_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_instReprEnvironment_repr___boxed(lean_object* v_x_1003_, lean_object* v_prec_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Std_Async_System_instReprEnvironment_repr(v_x_1003_, v_prec_1004_);
lean_dec(v_prec_1004_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0(lean_object* v_a_1006_, lean_object* v_n_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___redArg(v_a_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0___boxed(lean_object* v_a_1009_, lean_object* v_n_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0(v_a_1009_, v_n_1010_);
lean_dec(v_n_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0(lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___redArg(v_x_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0___boxed(lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Prod_repr___at___00List_repr___at___00Std_Async_System_instReprEnvironment_repr_spec__0_spec__0(v_x_1015_, v_x_1016_);
lean_dec(v_x_1016_);
return v_res_1017_;
}
}
static lean_object* _init_l_Std_Async_System_Environment_get_x3f___closed__1(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___f_1022_; 
v___x_1021_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_1022_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1022_, 0, v___x_1021_);
return v___f_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_Environment_get_x3f(lean_object* v_env_1023_, lean_object* v_key_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___f_1026_; lean_object* v___x_1027_; 
v___x_1025_ = ((lean_object*)(l_Std_Async_System_Environment_get_x3f___closed__0));
v___f_1026_ = lean_obj_once(&l_Std_Async_System_Environment_get_x3f___closed__1, &l_Std_Async_System_Environment_get_x3f___closed__1_once, _init_l_Std_Async_System_Environment_get_x3f___closed__1);
v___x_1027_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_1026_, v___x_1025_, v_env_1023_, v_key_1024_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_Environment_get_x3f___boxed(lean_object* v_env_1028_, lean_object* v_key_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Std_Async_System_Environment_get_x3f(v_env_1028_, v_key_1029_);
lean_dec_ref(v_env_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getSystemInfo(){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_uv_os_uname();
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1051_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1051_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1051_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_sysname_1037_; lean_object* v_release_1038_; lean_object* v_version_1039_; lean_object* v_machine_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1050_; 
v_sysname_1037_ = lean_ctor_get(v_a_1033_, 0);
v_release_1038_ = lean_ctor_get(v_a_1033_, 1);
v_version_1039_ = lean_ctor_get(v_a_1033_, 2);
v_machine_1040_ = lean_ctor_get(v_a_1033_, 3);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_a_1033_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1042_ = v_a_1033_;
v_isShared_1043_ = v_isSharedCheck_1050_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_machine_1040_);
lean_inc(v_version_1039_);
lean_inc(v_release_1038_);
lean_inc(v_sysname_1037_);
lean_dec(v_a_1033_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1050_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_sysname_1037_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_release_1038_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_version_1039_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_machine_1040_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1045_);
v___x_1047_ = v___x_1035_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1032_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1032_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getSystemInfo___boxed(lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Std_Async_System_getSystemInfo();
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1(size_t v_sz_1062_, size_t v_i_1063_, lean_object* v_bs_1064_){
_start:
{
uint8_t v___x_1065_; 
v___x_1065_ = lean_usize_dec_lt(v_i_1063_, v_sz_1062_);
if (v___x_1065_ == 0)
{
return v_bs_1064_;
}
else
{
lean_object* v_v_1066_; lean_object* v_times_1067_; lean_object* v_model_1068_; uint64_t v_speed_1069_; uint64_t v_user_1070_; uint64_t v_nice_1071_; uint64_t v_sys_1072_; uint64_t v_idle_1073_; uint64_t v_irq_1074_; lean_object* v___x_1075_; lean_object* v_bs_x27_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; size_t v___x_1090_; size_t v___x_1091_; lean_object* v___x_1092_; 
v_v_1066_ = lean_array_uget_borrowed(v_bs_1064_, v_i_1063_);
v_times_1067_ = lean_ctor_get(v_v_1066_, 1);
v_model_1068_ = lean_ctor_get(v_v_1066_, 0);
lean_inc_ref(v_model_1068_);
v_speed_1069_ = lean_ctor_get_uint64(v_v_1066_, sizeof(void*)*2);
v_user_1070_ = lean_ctor_get_uint64(v_times_1067_, 0);
v_nice_1071_ = lean_ctor_get_uint64(v_times_1067_, 8);
v_sys_1072_ = lean_ctor_get_uint64(v_times_1067_, 16);
v_idle_1073_ = lean_ctor_get_uint64(v_times_1067_, 24);
v_irq_1074_ = lean_ctor_get_uint64(v_times_1067_, 32);
v___x_1075_ = lean_unsigned_to_nat(0u);
v_bs_x27_1076_ = lean_array_uset(v_bs_1064_, v_i_1063_, v___x_1075_);
v___x_1077_ = lean_uint64_to_nat(v_speed_1069_);
v___x_1078_ = lean_uint64_to_nat(v_user_1070_);
v___x_1079_ = lean_nat_to_int(v___x_1078_);
v___x_1080_ = lean_uint64_to_nat(v_nice_1071_);
v___x_1081_ = lean_nat_to_int(v___x_1080_);
v___x_1082_ = lean_uint64_to_nat(v_sys_1072_);
v___x_1083_ = lean_nat_to_int(v___x_1082_);
v___x_1084_ = lean_uint64_to_nat(v_idle_1073_);
v___x_1085_ = lean_nat_to_int(v___x_1084_);
v___x_1086_ = lean_uint64_to_nat(v_irq_1074_);
v___x_1087_ = lean_nat_to_int(v___x_1086_);
v___x_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1079_);
lean_ctor_set(v___x_1088_, 1, v___x_1081_);
lean_ctor_set(v___x_1088_, 2, v___x_1083_);
lean_ctor_set(v___x_1088_, 3, v___x_1085_);
lean_ctor_set(v___x_1088_, 4, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1089_, 0, v_model_1068_);
lean_ctor_set(v___x_1089_, 1, v___x_1077_);
lean_ctor_set(v___x_1089_, 2, v___x_1088_);
v___x_1090_ = ((size_t)1ULL);
v___x_1091_ = lean_usize_add(v_i_1063_, v___x_1090_);
v___x_1092_ = lean_array_uset(v_bs_x27_1076_, v_i_1063_, v___x_1089_);
v_i_1063_ = v___x_1091_;
v_bs_1064_ = v___x_1092_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1___boxed(lean_object* v_sz_1094_, lean_object* v_i_1095_, lean_object* v_bs_1096_){
_start:
{
size_t v_sz_boxed_1097_; size_t v_i_boxed_1098_; lean_object* v_res_1099_; 
v_sz_boxed_1097_ = lean_unbox_usize(v_sz_1094_);
lean_dec(v_sz_1094_);
v_i_boxed_1098_ = lean_unbox_usize(v_i_1095_);
lean_dec(v_i_1095_);
v_res_1099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1(v_sz_boxed_1097_, v_i_boxed_1098_, v_bs_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1(size_t v_sz_1100_, size_t v_i_1101_, lean_object* v_bs_1102_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_usize_dec_lt(v_i_1101_, v_sz_1100_);
if (v___x_1103_ == 0)
{
return v_bs_1102_;
}
else
{
lean_object* v_v_1104_; lean_object* v_times_1105_; lean_object* v_model_1106_; uint64_t v_speed_1107_; uint64_t v_user_1108_; uint64_t v_nice_1109_; uint64_t v_sys_1110_; uint64_t v_idle_1111_; uint64_t v_irq_1112_; lean_object* v___x_1113_; lean_object* v_bs_x27_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; size_t v___x_1128_; size_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_v_1104_ = lean_array_uget_borrowed(v_bs_1102_, v_i_1101_);
v_times_1105_ = lean_ctor_get(v_v_1104_, 1);
v_model_1106_ = lean_ctor_get(v_v_1104_, 0);
lean_inc_ref(v_model_1106_);
v_speed_1107_ = lean_ctor_get_uint64(v_v_1104_, sizeof(void*)*2);
v_user_1108_ = lean_ctor_get_uint64(v_times_1105_, 0);
v_nice_1109_ = lean_ctor_get_uint64(v_times_1105_, 8);
v_sys_1110_ = lean_ctor_get_uint64(v_times_1105_, 16);
v_idle_1111_ = lean_ctor_get_uint64(v_times_1105_, 24);
v_irq_1112_ = lean_ctor_get_uint64(v_times_1105_, 32);
v___x_1113_ = lean_unsigned_to_nat(0u);
v_bs_x27_1114_ = lean_array_uset(v_bs_1102_, v_i_1101_, v___x_1113_);
v___x_1115_ = lean_uint64_to_nat(v_speed_1107_);
v___x_1116_ = lean_uint64_to_nat(v_user_1108_);
v___x_1117_ = lean_nat_to_int(v___x_1116_);
v___x_1118_ = lean_uint64_to_nat(v_nice_1109_);
v___x_1119_ = lean_nat_to_int(v___x_1118_);
v___x_1120_ = lean_uint64_to_nat(v_sys_1110_);
v___x_1121_ = lean_nat_to_int(v___x_1120_);
v___x_1122_ = lean_uint64_to_nat(v_idle_1111_);
v___x_1123_ = lean_nat_to_int(v___x_1122_);
v___x_1124_ = lean_uint64_to_nat(v_irq_1112_);
v___x_1125_ = lean_nat_to_int(v___x_1124_);
v___x_1126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1117_);
lean_ctor_set(v___x_1126_, 1, v___x_1119_);
lean_ctor_set(v___x_1126_, 2, v___x_1121_);
lean_ctor_set(v___x_1126_, 3, v___x_1123_);
lean_ctor_set(v___x_1126_, 4, v___x_1125_);
v___x_1127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1127_, 0, v_model_1106_);
lean_ctor_set(v___x_1127_, 1, v___x_1115_);
lean_ctor_set(v___x_1127_, 2, v___x_1126_);
v___x_1128_ = ((size_t)1ULL);
v___x_1129_ = lean_usize_add(v_i_1101_, v___x_1128_);
v___x_1130_ = lean_array_uset(v_bs_x27_1114_, v_i_1101_, v___x_1127_);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1_spec__1(v_sz_1100_, v___x_1129_, v___x_1130_);
return v___x_1131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1___boxed(lean_object* v_sz_1132_, lean_object* v_i_1133_, lean_object* v_bs_1134_){
_start:
{
size_t v_sz_boxed_1135_; size_t v_i_boxed_1136_; lean_object* v_res_1137_; 
v_sz_boxed_1135_ = lean_unbox_usize(v_sz_1132_);
lean_dec(v_sz_1132_);
v_i_boxed_1136_ = lean_unbox_usize(v_i_1133_);
lean_dec(v_i_1133_);
v_res_1137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1(v_sz_boxed_1135_, v_i_boxed_1136_, v_bs_1134_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getCPUInfo(){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_uv_cpu_info();
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1150_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
size_t v_sz_1144_; size_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v_sz_1144_ = lean_array_size(v_a_1140_);
v___x_1145_ = ((size_t)0ULL);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Async_System_getCPUInfo_spec__1(v_sz_1144_, v___x_1145_, v_a_1140_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1146_);
v___x_1148_ = v___x_1142_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
v_a_1151_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1139_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1139_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getCPUInfo___boxed(lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Std_Async_System_getCPUInfo();
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Async_System_getCPUInfo_spec__0(lean_object* v_a_1161_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_nat_to_int(v_a_1161_);
v___x_1163_ = l_Rat_ofInt(v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getUpTime(){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_uv_uptime();
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1176_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1176_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1176_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
uint64_t v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1170_ = lean_unbox_uint64(v_a_1166_);
lean_dec(v_a_1166_);
v___x_1171_ = lean_uint64_to_nat(v___x_1170_);
v___x_1172_ = lean_nat_to_int(v___x_1171_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1172_);
v___x_1174_ = v___x_1168_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
v_a_1177_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1165_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1165_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getUpTime___boxed(lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Std_Async_System_getUpTime();
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getHighResolutionTime(){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_uv_hrtime();
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1199_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1199_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1199_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
uint64_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1193_ = lean_unbox_uint64(v_a_1189_);
lean_dec(v_a_1189_);
v___x_1194_ = lean_uint64_to_nat(v___x_1193_);
v___x_1195_ = lean_nat_to_int(v___x_1194_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1195_);
v___x_1197_ = v___x_1191_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1200_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1188_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1188_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getHighResolutionTime___boxed(lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Std_Async_System_getHighResolutionTime();
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getHostName(){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_uv_os_gethostname();
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getHostName___boxed(lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Std_Async_System_getHostName();
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_setEnvVar(lean_object* v_name_1214_, lean_object* v_value_1215_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_uv_os_setenv(v_name_1214_, v_value_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_setEnvVar___boxed(lean_object* v_name_1218_, lean_object* v_value_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Std_Async_System_setEnvVar(v_name_1218_, v_value_1219_);
lean_dec_ref(v_value_1219_);
lean_dec_ref(v_name_1218_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getEnvVar(lean_object* v_name_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_uv_os_getenv(v_name_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getEnvVar___boxed(lean_object* v_name_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Std_Async_System_getEnvVar(v_name_1225_);
lean_dec_ref(v_name_1225_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_unsetEnvVar(lean_object* v_name_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_uv_os_unsetenv(v_name_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_unsetEnvVar___boxed(lean_object* v_name_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Std_Async_System_unsetEnvVar(v_name_1231_);
lean_dec_ref(v_name_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getEnv(){
_start:
{
lean_object* v___x_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; 
v___x_1258_ = ((lean_object*)(l_Std_Async_System_Environment_get_x3f___closed__0));
v___f_1259_ = ((lean_object*)(l_Std_Async_System_getEnv___closed__11));
v___x_1260_ = lean_uv_os_environ();
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1280_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1280_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1280_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___f_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___f_1265_ = lean_obj_once(&l_Std_Async_System_Environment_get_x3f___closed__1, &l_Std_Async_System_Environment_get_x3f___closed__1_once, _init_l_Std_Async_System_Environment_get_x3f___closed__1);
v___x_1266_ = lean_array_get_size(v_a_1261_);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_unsigned_to_nat(4u);
v___x_1269_ = lean_nat_mul(v___x_1266_, v___x_1268_);
v___x_1270_ = lean_unsigned_to_nat(3u);
v___x_1271_ = lean_nat_div(v___x_1269_, v___x_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = l_Nat_nextPowerOfTwo(v___x_1271_);
lean_dec(v___x_1271_);
v___x_1273_ = lean_box(0);
v___x_1274_ = lean_mk_array(v___x_1272_, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1267_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1259_, v___f_1265_, v___x_1258_, v___x_1275_, v_a_1261_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1276_);
v___x_1278_ = v___x_1263_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
v_a_1281_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1260_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1260_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getEnv___boxed(lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Std_Async_System_getEnv();
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getHomeDir(){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_uv_os_homedir();
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
v_a_1301_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1292_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1292_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getHomeDir___boxed(lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Std_Async_System_getHomeDir();
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getTmpDir(){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_uv_os_tmpdir();
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1321_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1312_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1312_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getTmpDir___boxed(lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Std_Async_System_getTmpDir();
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getCurrentUser(){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_uv_os_get_passwd();
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1392_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1392_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1392_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_username_1337_; lean_object* v_uid_1338_; lean_object* v_gid_1339_; lean_object* v_shell_1340_; lean_object* v_homedir_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1391_; 
v_username_1337_ = lean_ctor_get(v_a_1333_, 0);
v_uid_1338_ = lean_ctor_get(v_a_1333_, 1);
v_gid_1339_ = lean_ctor_get(v_a_1333_, 2);
v_shell_1340_ = lean_ctor_get(v_a_1333_, 3);
v_homedir_1341_ = lean_ctor_get(v_a_1333_, 4);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_a_1333_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1343_ = v_a_1333_;
v_isShared_1344_ = v_isSharedCheck_1391_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_homedir_1341_);
lean_inc(v_shell_1340_);
lean_inc(v_gid_1339_);
lean_inc(v_uid_1338_);
lean_inc(v_username_1337_);
lean_dec(v_a_1333_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1391_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1368_; 
if (lean_obj_tag(v_uid_1338_) == 0)
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_box(0);
v___y_1368_ = v___x_1380_;
goto v___jp_1367_;
}
else
{
lean_object* v_val_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1390_; 
v_val_1381_ = lean_ctor_get(v_uid_1338_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_uid_1338_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1383_ = v_uid_1338_;
v_isShared_1384_ = v_isSharedCheck_1390_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_val_1381_);
lean_dec(v_uid_1338_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1390_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
uint64_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1385_ = lean_unbox_uint64(v_val_1381_);
lean_dec(v_val_1381_);
v___x_1386_ = lean_uint64_to_nat(v___x_1385_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1386_);
v___x_1388_ = v___x_1383_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
v___y_1368_ = v___x_1388_;
goto v___jp_1367_;
}
}
}
v___jp_1345_:
{
lean_object* v___x_1350_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v___y_1348_);
lean_ctor_set(v___x_1343_, 2, v___y_1347_);
lean_ctor_set(v___x_1343_, 1, v___y_1346_);
v___x_1350_ = v___x_1343_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_username_1337_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___y_1346_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v___y_1347_);
lean_ctor_set(v_reuseFailAlloc_1354_, 3, v_shell_1340_);
lean_ctor_set(v_reuseFailAlloc_1354_, 4, v___y_1348_);
v___x_1350_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1350_);
v___x_1352_ = v___x_1335_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
v___jp_1355_:
{
if (lean_obj_tag(v_homedir_1341_) == 0)
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_box(0);
v___y_1346_ = v___y_1356_;
v___y_1347_ = v___y_1357_;
v___y_1348_ = v___x_1358_;
goto v___jp_1345_;
}
else
{
lean_object* v_val_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_val_1359_ = lean_ctor_get(v_homedir_1341_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_homedir_1341_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v_homedir_1341_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_val_1359_);
lean_dec(v_homedir_1341_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_val_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
v___y_1346_ = v___y_1356_;
v___y_1347_ = v___y_1357_;
v___y_1348_ = v___x_1364_;
goto v___jp_1345_;
}
}
}
}
v___jp_1367_:
{
if (lean_obj_tag(v_gid_1339_) == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_box(0);
v___y_1356_ = v___y_1368_;
v___y_1357_ = v___x_1369_;
goto v___jp_1355_;
}
else
{
lean_object* v_val_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1379_; 
v_val_1370_ = lean_ctor_get(v_gid_1339_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_gid_1339_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1372_ = v_gid_1339_;
v_isShared_1373_ = v_isSharedCheck_1379_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_val_1370_);
lean_dec(v_gid_1339_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1379_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
uint64_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1374_ = lean_unbox_uint64(v_val_1370_);
lean_dec(v_val_1370_);
v___x_1375_ = lean_uint64_to_nat(v___x_1374_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1375_);
v___x_1377_ = v___x_1372_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
v___y_1356_ = v___y_1368_;
v___y_1357_ = v___x_1377_;
goto v___jp_1355_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_a_1393_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1332_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1332_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getCurrentUser___boxed(lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Std_Async_System_getCurrentUser();
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Std_Async_System_getGroup_spec__0___redArg(lean_object* v_a_1403_, lean_object* v_f_1404_){
_start:
{
if (lean_obj_tag(v_a_1403_) == 0)
{
lean_object* v___x_1405_; 
lean_dec(v_f_1404_);
v___x_1405_ = lean_box(0);
return v___x_1405_;
}
else
{
lean_object* v_val_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1414_; 
v_val_1406_ = lean_ctor_get(v_a_1403_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_a_1403_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1408_ = v_a_1403_;
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_val_1406_);
lean_dec(v_a_1403_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = lean_apply_1(v_f_1404_, v_val_1406_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1410_);
v___x_1412_ = v___x_1408_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Std_Async_System_getGroup_spec__0(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_a_1417_, lean_object* v_f_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Functor_mapRev___at___00Std_Async_System_getGroup_spec__0___redArg(v_a_1417_, v_f_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getGroup___lam__0(lean_object* v_group_1420_){
_start:
{
lean_object* v_groupname_1421_; uint64_t v_gid_1422_; lean_object* v_members_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_groupname_1421_ = lean_ctor_get(v_group_1420_, 0);
v_gid_1422_ = lean_ctor_get_uint64(v_group_1420_, sizeof(void*)*2);
v_members_1423_ = lean_ctor_get(v_group_1420_, 1);
v___x_1424_ = lean_uint64_to_nat(v_gid_1422_);
lean_inc_ref(v_members_1423_);
lean_inc_ref(v_groupname_1421_);
v___x_1425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1425_, 0, v_groupname_1421_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
lean_ctor_set(v___x_1425_, 2, v_members_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getGroup___lam__0___boxed(lean_object* v_group_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Std_Async_System_getGroup___lam__0(v_group_1426_);
lean_dec_ref(v_group_1426_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getGroup(lean_object* v_groupId_1429_){
_start:
{
lean_object* v___f_1431_; uint64_t v___x_1432_; lean_object* v___x_1433_; 
v___f_1431_ = ((lean_object*)(l_Std_Async_System_getGroup___closed__0));
v___x_1432_ = lean_uint64_of_nat(v_groupId_1429_);
v___x_1433_ = lean_uv_os_get_group(v___x_1432_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1442_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1442_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1442_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = l_Functor_mapRev___at___00Std_Async_System_getGroup_spec__0___redArg(v_a_1434_, v___f_1431_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1438_);
v___x_1440_ = v___x_1436_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
v_a_1443_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1433_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1433_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_System_getGroup___boxed(lean_object* v_groupId_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Std_Async_System_getGroup(v_groupId_1451_);
lean_dec(v_groupId_1451_);
return v_res_1453_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_System(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_System(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_System(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Async_System_instInhabitedGroupId_default = _init_l_Std_Async_System_instInhabitedGroupId_default();
lean_mark_persistent(l_Std_Async_System_instInhabitedGroupId_default);
l_Std_Async_System_instInhabitedGroupId = _init_l_Std_Async_System_instInhabitedGroupId();
lean_mark_persistent(l_Std_Async_System_instInhabitedGroupId);
l_Std_Async_System_instInhabitedUserId_default = _init_l_Std_Async_System_instInhabitedUserId_default();
lean_mark_persistent(l_Std_Async_System_instInhabitedUserId_default);
l_Std_Async_System_instInhabitedUserId = _init_l_Std_Async_System_instInhabitedUserId();
lean_mark_persistent(l_Std_Async_System_instInhabitedUserId);
l_Std_Async_System_instInhabitedCPUTimes_default = _init_l_Std_Async_System_instInhabitedCPUTimes_default();
lean_mark_persistent(l_Std_Async_System_instInhabitedCPUTimes_default);
l_Std_Async_System_instInhabitedCPUTimes = _init_l_Std_Async_System_instInhabitedCPUTimes();
lean_mark_persistent(l_Std_Async_System_instInhabitedCPUTimes);
l_Std_Async_System_instInhabitedCPUInfo_default = _init_l_Std_Async_System_instInhabitedCPUInfo_default();
lean_mark_persistent(l_Std_Async_System_instInhabitedCPUInfo_default);
l_Std_Async_System_instInhabitedCPUInfo = _init_l_Std_Async_System_instInhabitedCPUInfo();
lean_mark_persistent(l_Std_Async_System_instInhabitedCPUInfo);
l_Std_Async_System_instInhabitedEnvironment_default = _init_l_Std_Async_System_instInhabitedEnvironment_default();
lean_mark_persistent(l_Std_Async_System_instInhabitedEnvironment_default);
l_Std_Async_System_instInhabitedEnvironment = _init_l_Std_Async_System_instInhabitedEnvironment();
lean_mark_persistent(l_Std_Async_System_instInhabitedEnvironment);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Async_System(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_System(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Async_System(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_System(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_System(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Async_System(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Async_System(builtin);
}
#ifdef __cplusplus
}
#endif
