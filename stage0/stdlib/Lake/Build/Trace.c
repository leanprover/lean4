// Lean compiler output
// Module: Lake.Build.Trace
// Imports: public import Lean.Data.Json import Init.Data.Nat.Fold import Lake.Util.String public import Init.Data.String.Search public import Init.Data.String.Extra import Init.Data.Option.Coe
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
lean_object* lean_nat_to_int(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint64_t lean_uint8_to_uint64(uint8_t);
uint64_t lean_uint64_add(uint64_t, uint64_t);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_List_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lake_isHex(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
lean_object* l_Lake_lpad(lean_object*, uint32_t, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object*);
lean_object* l_System_FilePath_pathExists___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_FS_instReprSystemTime_repr___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_IO_FS_instOrdSystemTime_ord___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_instBEqSystemTime_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instCheckExistsFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_System_FilePath_pathExists___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCheckExistsFilePath___closed__0 = (const lean_object*)&l_Lake_instCheckExistsFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCheckExistsFilePath = (const lean_object*)&l_Lake_instCheckExistsFilePath___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_computeTrace___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_mixTraceArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_mixTraceArray___redArg___closed__0 = (const lean_object*)&l_Lake_mixTraceArray___redArg___closed__0_value;
static const lean_closure_object l_Lake_mixTraceArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_mixTraceArray___redArg___closed__1 = (const lean_object*)&l_Lake_mixTraceArray___redArg___closed__1_value;
static const lean_closure_object l_Lake_mixTraceArray___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_mixTraceArray___redArg___closed__2 = (const lean_object*)&l_Lake_mixTraceArray___redArg___closed__2_value;
static const lean_closure_object l_Lake_mixTraceArray___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_mixTraceArray___redArg___closed__3 = (const lean_object*)&l_Lake_mixTraceArray___redArg___closed__3_value;
static const lean_closure_object l_Lake_mixTraceArray___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_mixTraceArray___redArg___closed__4 = (const lean_object*)&l_Lake_mixTraceArray___redArg___closed__4_value;
static const lean_closure_object l_Lake_mixTraceArray___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_mixTraceArray___redArg___closed__5 = (const lean_object*)&l_Lake_mixTraceArray___redArg___closed__5_value;
static const lean_closure_object l_Lake_mixTraceArray___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_mixTraceArray___redArg___closed__6 = (const lean_object*)&l_Lake_mixTraceArray___redArg___closed__6_value;
static const lean_ctor_object l_Lake_mixTraceArray___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_mixTraceArray___redArg___closed__0_value),((lean_object*)&l_Lake_mixTraceArray___redArg___closed__1_value)}};
static const lean_object* l_Lake_mixTraceArray___redArg___closed__7 = (const lean_object*)&l_Lake_mixTraceArray___redArg___closed__7_value;
static const lean_ctor_object l_Lake_mixTraceArray___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_mixTraceArray___redArg___closed__7_value),((lean_object*)&l_Lake_mixTraceArray___redArg___closed__2_value),((lean_object*)&l_Lake_mixTraceArray___redArg___closed__3_value),((lean_object*)&l_Lake_mixTraceArray___redArg___closed__4_value),((lean_object*)&l_Lake_mixTraceArray___redArg___closed__5_value)}};
static const lean_object* l_Lake_mixTraceArray___redArg___closed__8 = (const lean_object*)&l_Lake_mixTraceArray___redArg___closed__8_value;
static const lean_ctor_object l_Lake_mixTraceArray___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_mixTraceArray___redArg___closed__8_value),((lean_object*)&l_Lake_mixTraceArray___redArg___closed__6_value)}};
static const lean_object* l_Lake_mixTraceArray___redArg___closed__9 = (const lean_object*)&l_Lake_mixTraceArray___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_mixTraceArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeListTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instComputeTraceListOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instComputeTraceListOfMonad___redArg___closed__0 = (const lean_object*)&l_Lake_instComputeTraceListOfMonad___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprHash_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprHash_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprHash_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprHash_repr___redArg___closed__0_value;
static const lean_string_object l_Lake_instReprHash_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Lake_instReprHash_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprHash_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprHash_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprHash_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprHash_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprHash_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprHash_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprHash_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprHash_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprHash_repr___redArg___closed__3_value;
static const lean_string_object l_Lake_instReprHash_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprHash_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprHash_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprHash_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprHash_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprHash_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprHash_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprHash_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprHash_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprHash_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprHash_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprHash_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprHash_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprHash_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprHash_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprHash_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprHash_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lake_instReprHash_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprHash_repr___redArg___closed__9;
static lean_once_cell_t l_Lake_instReprHash_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprHash_repr___redArg___closed__10;
static const lean_ctor_object l_Lake_instReprHash_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprHash_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprHash_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprHash_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lake_instReprHash_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprHash_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprHash_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprHash_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___redArg(uint64_t);
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprHash___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprHash_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprHash___closed__0 = (const lean_object*)&l_Lake_instReprHash___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprHash = (const lean_object*)&l_Lake_instReprHash___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqHash_decEq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqHash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_instHashable___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lake_Hash_instHashable___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_Hash_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Hash_instHashable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Hash_instHashable___closed__0 = (const lean_object*)&l_Lake_Hash_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Hash_instHashable = (const lean_object*)&l_Lake_Hash_instHashable___closed__0_value;
LEAN_EXPORT uint64_t l_Lake_Hash_nil;
LEAN_EXPORT uint64_t l_Lake_Hash_instNilTrace;
LEAN_EXPORT uint64_t l_Lake_Hash_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofNat___boxed(lean_object*);
static const lean_string_object l_Lake_Hash_ofJsonNumber_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "number is not a natural"};
static const lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__0 = (const lean_object*)&l_Lake_Hash_ofJsonNumber_x3f___closed__0_value;
static const lean_ctor_object l_Lake_Hash_ofJsonNumber_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Hash_ofJsonNumber_x3f___closed__0_value)}};
static const lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__1 = (const lean_object*)&l_Lake_Hash_ofJsonNumber_x3f___closed__1_value;
static lean_once_cell_t l_Lake_Hash_ofJsonNumber_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__2;
static const lean_string_object l_Lake_Hash_ofJsonNumber_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "number too big"};
static const lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__3 = (const lean_object*)&l_Lake_Hash_ofJsonNumber_x3f___closed__3_value;
static const lean_ctor_object l_Lake_Hash_ofJsonNumber_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Hash_ofJsonNumber_x3f___closed__3_value)}};
static const lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__4 = (const lean_object*)&l_Lake_Hash_ofJsonNumber_x3f___closed__4_value;
static lean_once_cell_t l_Lake_Hash_ofJsonNumber_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofHex(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_hex(uint64_t);
LEAN_EXPORT lean_object* l_Lake_Hash_hex___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofDecimal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_mix(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_Hash_mix___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Hash_instMixTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Hash_mix___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Hash_instMixTrace___closed__0 = (const lean_object*)&l_Lake_Hash_instMixTrace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Hash_instMixTrace = (const lean_object*)&l_Lake_Hash_instMixTrace___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Hash_toString(uint64_t);
LEAN_EXPORT lean_object* l_Lake_Hash_toString___boxed(lean_object*);
static const lean_closure_object l_Lake_Hash_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Hash_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Hash_instToString___closed__0 = (const lean_object*)&l_Lake_Hash_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Hash_instToString = (const lean_object*)&l_Lake_Hash_instToString___closed__0_value;
LEAN_EXPORT uint64_t l_Lake_Hash_ofHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofHashable___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofHashable___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofString___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofText(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofText___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofByteArray(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofByteArray___boxed(lean_object*);
static lean_once_cell_t l_Lake_Hash_ofBool___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lake_Hash_ofBool___closed__0;
static lean_once_cell_t l_Lake_Hash_ofBool___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lake_Hash_ofBool___closed__1;
LEAN_EXPORT uint64_t l_Lake_Hash_ofBool(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Hash_ofBool___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_toJson(uint64_t);
LEAN_EXPORT lean_object* l_Lake_Hash_toJson___boxed(lean_object*);
static const lean_closure_object l_Lake_Hash_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Hash_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Hash_instToJson___closed__0 = (const lean_object*)&l_Lake_Hash_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Hash_instToJson = (const lean_object*)&l_Lake_Hash_instToJson___closed__0_value;
static const lean_string_object l_Lake_Hash_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "invalid hash: expected hexadecimal string"};
static const lean_object* l_Lake_Hash_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_Hash_fromJson_x3f___closed__0_value;
static const lean_ctor_object l_Lake_Hash_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Hash_fromJson_x3f___closed__0_value)}};
static const lean_object* l_Lake_Hash_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_Hash_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_Hash_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "invalid hash: expected hexadecimal string of length 16"};
static const lean_object* l_Lake_Hash_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_Hash_fromJson_x3f___closed__2_value;
static const lean_ctor_object l_Lake_Hash_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Hash_fromJson_x3f___closed__2_value)}};
static const lean_object* l_Lake_Hash_fromJson_x3f___closed__3 = (const lean_object*)&l_Lake_Hash_fromJson_x3f___closed__3_value;
static const lean_string_object l_Lake_Hash_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "invalid hash: "};
static const lean_object* l_Lake_Hash_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_Hash_fromJson_x3f___closed__4_value;
static const lean_string_object l_Lake_Hash_fromJson_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "invalid hash: expected string or number"};
static const lean_object* l_Lake_Hash_fromJson_x3f___closed__5 = (const lean_object*)&l_Lake_Hash_fromJson_x3f___closed__5_value;
static const lean_ctor_object l_Lake_Hash_fromJson_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Hash_fromJson_x3f___closed__5_value)}};
static const lean_object* l_Lake_Hash_fromJson_x3f___closed__6 = (const lean_object*)&l_Lake_Hash_fromJson_x3f___closed__6_value;
LEAN_EXPORT lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lake_Hash_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Hash_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Hash_instFromJson___closed__0 = (const lean_object*)&l_Lake_Hash_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Hash_instFromJson = (const lean_object*)&l_Lake_Hash_instFromJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_pureHash___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_pureHash___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_pureHash(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_pureHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeHash___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeHash(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashIdOfHashable___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashIdOfHashable(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instComputeHashFilePathIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_computeBinFileHash___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instComputeHashFilePathIO___closed__0 = (const lean_object*)&l_Lake_instComputeHashFilePathIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instComputeHashFilePathIO = (const lean_object*)&l_Lake_instComputeHashFilePathIO___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instCoeTextFilePathFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeTextFilePathFilePath___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeTextFilePathFilePath___closed__0 = (const lean_object*)&l_Lake_instCoeTextFilePathFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeTextFilePathFilePath = (const lean_object*)&l_Lake_instCoeTextFilePathFilePath___closed__0_value;
static const lean_closure_object l_Lake_instComputeHashTextFilePathIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_computeTextFileHash___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instComputeHashTextFilePathIO___closed__0 = (const lean_object*)&l_Lake_instComputeHashTextFilePathIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instComputeHashTextFilePathIO = (const lean_object*)&l_Lake_instComputeHashTextFilePathIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToStringTextFilePath = (const lean_object*)&l_Lake_instCoeTextFilePathFilePath___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_computeFileHash(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_computeFileHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0(uint64_t, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_computeArrayHash___redArg___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(187, 6, 0, 0, 0, 0, 0, 0)}};
LEAN_EXPORT const lean_object* l_Lake_computeArrayHash___redArg___boxed__const__1 = (const lean_object*)&l_Lake_computeArrayHash___redArg___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_MTime_instOfNat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_MTime_instOfNat___closed__0;
LEAN_EXPORT lean_object* l_Lake_MTime_instOfNat;
static const lean_closure_object l_Lake_MTime_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instBEqSystemTime_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MTime_instBEq___closed__0 = (const lean_object*)&l_Lake_MTime_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MTime_instBEq = (const lean_object*)&l_Lake_MTime_instBEq___closed__0_value;
static const lean_closure_object l_Lake_MTime_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instReprSystemTime_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MTime_instRepr___closed__0 = (const lean_object*)&l_Lake_MTime_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MTime_instRepr = (const lean_object*)&l_Lake_MTime_instRepr___closed__0_value;
static const lean_closure_object l_Lake_MTime_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instOrdSystemTime_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MTime_instOrd___closed__0 = (const lean_object*)&l_Lake_MTime_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MTime_instOrd = (const lean_object*)&l_Lake_MTime_instOrd___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MTime_instLT;
LEAN_EXPORT lean_object* l_Lake_MTime_instLE;
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_MTime_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MTime_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MTime_instMin___closed__0 = (const lean_object*)&l_Lake_MTime_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MTime_instMin = (const lean_object*)&l_Lake_MTime_instMin___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_MTime_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MTime_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MTime_instMax___closed__0 = (const lean_object*)&l_Lake_MTime_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MTime_instMax = (const lean_object*)&l_Lake_MTime_instMax___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MTime_instNilTrace;
LEAN_EXPORT const lean_object* l_Lake_MTime_instMixTrace = (const lean_object*)&l_Lake_MTime_instMax___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getFileMTime(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getFileMTime___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instGetMTimeFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getFileMTime___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instGetMTimeFilePath___closed__0 = (const lean_object*)&l_Lake_instGetMTimeFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instGetMTimeFilePath = (const lean_object*)&l_Lake_instGetMTimeFilePath___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instGetMTimeTextFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instGetMTimeTextFilePath___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instGetMTimeTextFilePath___closed__0 = (const lean_object*)&l_Lake_instGetMTimeTextFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instGetMTimeTextFilePath = (const lean_object*)&l_Lake_instGetMTimeTextFilePath___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprBuildTrace_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caption"};
static const lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprBuildTrace_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprBuildTrace_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprBuildTrace_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__2_value),((lean_object*)&l_Lake_instReprHash_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lake_instReprBuildTrace_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__4;
static const lean_string_object l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2_value;
static const lean_string_object l_Lake_instReprBuildTrace_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inputs"};
static const lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprBuildTrace_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprBuildTrace_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__7;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0_value;
static lean_once_cell_t l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprBuildTrace_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hash"};
static const lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprBuildTrace_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lake_instReprBuildTrace_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__10;
static const lean_string_object l_Lake_instReprBuildTrace_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mtime"};
static const lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lake_instReprBuildTrace_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__11_value)}};
static const lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprBuildTrace_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lake_instReprBuildTrace_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprBuildTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprBuildTrace_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprBuildTrace___closed__0 = (const lean_object*)&l_Lake_instReprBuildTrace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprBuildTrace = (const lean_object*)&l_Lake_instReprBuildTrace___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption(lean_object*, lean_object*);
static const lean_array_object l_Lake_BuildTrace_withoutInputs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildTrace_withoutInputs___closed__0 = (const lean_object*)&l_Lake_BuildTrace_withoutInputs___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_BuildTrace_instCoeHash___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "<hash>"};
static const lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___closed__0 = (const lean_object*)&l_Lake_BuildTrace_instCoeHash___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_BuildTrace_instCoeHash___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildTrace_instCoeHash___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuildTrace_instCoeHash___closed__0 = (const lean_object*)&l_Lake_BuildTrace_instCoeHash___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_BuildTrace_instCoeHash = (const lean_object*)&l_Lake_BuildTrace_instCoeHash___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofMTime(lean_object*, lean_object*);
static const lean_string_object l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<mtime>"};
static const lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0 = (const lean_object*)&l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0(lean_object*);
static const lean_closure_object l_Lake_BuildTrace_instCoeMTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildTrace_instCoeMTime___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuildTrace_instCoeMTime___closed__0 = (const lean_object*)&l_Lake_BuildTrace_instCoeMTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_BuildTrace_instCoeMTime = (const lean_object*)&l_Lake_BuildTrace_instCoeMTime___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_nil(lean_object*);
static const lean_string_object l_Lake_BuildTrace_instNilTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l_Lake_BuildTrace_instNilTrace___closed__0 = (const lean_object*)&l_Lake_BuildTrace_instNilTrace___closed__0_value;
static lean_once_cell_t l_Lake_BuildTrace_instNilTrace___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuildTrace_instNilTrace___closed__1;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instNilTrace;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
static const lean_closure_object l_Lake_BuildTrace_instMixTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildTrace_mix, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuildTrace_instMixTrace___closed__0 = (const lean_object*)&l_Lake_BuildTrace_instMixTrace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_BuildTrace_instMixTrace = (const lean_object*)&l_Lake_BuildTrace_instMixTrace___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash___redArg(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeTrace___redArg(lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_apply_1(v_inst_3_, v_a_5_);
v___x_7_ = lean_apply_2(v_inst_4_, lean_box(0), v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeTrace(lean_object* v_00_u03b1_8_, lean_object* v_m_9_, lean_object* v_00_u03c4_10_, lean_object* v_n_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_apply_1(v_inst_12_, v_a_14_);
v___x_16_ = lean_apply_2(v_inst_13_, lean_box(0), v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___redArg(lean_object* v_inst_17_){
_start:
{
lean_inc(v_inst_17_);
return v_inst_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___redArg___boxed(lean_object* v_inst_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lake_inhabitedOfNilTrace___redArg(v_inst_18_);
lean_dec(v_inst_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace(lean_object* v_00_u03b1_20_, lean_object* v_inst_21_){
_start:
{
lean_inc(v_inst_21_);
return v_inst_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___boxed(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lake_inhabitedOfNilTrace(v_00_u03b1_22_, v_inst_23_);
lean_dec(v_inst_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceList___redArg(lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_traces_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_List_foldl___redArg(v_inst_25_, v_inst_26_, v_traces_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceList(lean_object* v_00_u03c4_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_traces_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_List_foldl___redArg(v_inst_30_, v_inst_31_, v_traces_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceArray___redArg___lam__0(lean_object* v_inst_34_, lean_object* v_x1_35_, lean_object* v_x2_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_apply_2(v_inst_34_, v_x1_35_, v_x2_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceArray___redArg(lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_traces_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = lean_array_get_size(v_traces_59_);
v___x_62_ = ((lean_object*)(l_Lake_mixTraceArray___redArg___closed__9));
v___x_63_ = lean_nat_dec_lt(v___x_60_, v___x_61_);
if (v___x_63_ == 0)
{
lean_dec_ref(v_traces_59_);
lean_dec(v_inst_57_);
return v_inst_58_;
}
else
{
lean_object* v___f_64_; uint8_t v___x_65_; 
v___f_64_ = lean_alloc_closure((void*)(l_Lake_mixTraceArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_64_, 0, v_inst_57_);
v___x_65_ = lean_nat_dec_le(v___x_61_, v___x_61_);
if (v___x_65_ == 0)
{
if (v___x_63_ == 0)
{
lean_dec_ref(v___f_64_);
lean_dec_ref(v_traces_59_);
return v_inst_58_;
}
else
{
size_t v___x_66_; size_t v___x_67_; lean_object* v___x_68_; 
v___x_66_ = ((size_t)0ULL);
v___x_67_ = lean_usize_of_nat(v___x_61_);
v___x_68_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_62_, v___f_64_, v_traces_59_, v___x_66_, v___x_67_, v_inst_58_);
return v___x_68_;
}
}
else
{
size_t v___x_69_; size_t v___x_70_; lean_object* v___x_71_; 
v___x_69_ = ((size_t)0ULL);
v___x_70_ = lean_usize_of_nat(v___x_61_);
v___x_71_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_62_, v___f_64_, v_traces_59_, v___x_69_, v___x_70_, v_inst_58_);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceArray(lean_object* v_00_u03c4_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_traces_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lake_mixTraceArray___redArg(v_inst_73_, v_inst_74_, v_traces_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__0(lean_object* v_inst_77_, lean_object* v_ts_78_, lean_object* v_toPure_79_, lean_object* v_____do__lift_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_apply_2(v_inst_77_, v_ts_78_, v_____do__lift_80_);
v___x_82_ = lean_apply_2(v_toPure_79_, lean_box(0), v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__1(lean_object* v_inst_83_, lean_object* v_toPure_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_toBind_87_, lean_object* v_ts_88_, lean_object* v_t_89_){
_start:
{
lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___f_90_ = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_90_, 0, v_inst_83_);
lean_closure_set(v___f_90_, 1, v_ts_88_);
lean_closure_set(v___f_90_, 2, v_toPure_84_);
v___x_91_ = lean_apply_1(v_inst_85_, v_t_89_);
v___x_92_ = lean_apply_2(v_inst_86_, lean_box(0), v___x_91_);
v___x_93_ = lean_apply_4(v_toBind_87_, lean_box(0), lean_box(0), v___x_92_, v___f_90_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg(lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_as_99_){
_start:
{
lean_object* v_toApplicative_100_; lean_object* v_toBind_101_; lean_object* v_toPure_102_; lean_object* v___f_103_; lean_object* v___x_104_; 
v_toApplicative_100_ = lean_ctor_get(v_inst_98_, 0);
v_toBind_101_ = lean_ctor_get(v_inst_98_, 1);
v_toPure_102_ = lean_ctor_get(v_toApplicative_100_, 1);
lean_inc(v_toBind_101_);
lean_inc(v_toPure_102_);
v___f_103_ = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(v___f_103_, 0, v_inst_94_);
lean_closure_set(v___f_103_, 1, v_toPure_102_);
lean_closure_set(v___f_103_, 2, v_inst_96_);
lean_closure_set(v___f_103_, 3, v_inst_97_);
lean_closure_set(v___f_103_, 4, v_toBind_101_);
v___x_104_ = l_List_foldlM___redArg(v_inst_98_, v___f_103_, v_inst_95_, v_as_99_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace(lean_object* v_00_u03c4_105_, lean_object* v_00_u03b1_106_, lean_object* v_m_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_n_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_as_114_){
_start:
{
lean_object* v_toApplicative_115_; lean_object* v_toBind_116_; lean_object* v_toPure_117_; lean_object* v___f_118_; lean_object* v___x_119_; 
v_toApplicative_115_ = lean_ctor_get(v_inst_113_, 0);
v_toBind_116_ = lean_ctor_get(v_inst_113_, 1);
v_toPure_117_ = lean_ctor_get(v_toApplicative_115_, 1);
lean_inc(v_toBind_116_);
lean_inc(v_toPure_117_);
v___f_118_ = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(v___f_118_, 0, v_inst_108_);
lean_closure_set(v___f_118_, 1, v_toPure_117_);
lean_closure_set(v___f_118_, 2, v_inst_110_);
lean_closure_set(v___f_118_, 3, v_inst_112_);
lean_closure_set(v___f_118_, 4, v_toBind_116_);
v___x_119_ = l_List_foldlM___redArg(v_inst_113_, v___f_118_, v_inst_109_, v_as_114_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad___redArg(lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_){
_start:
{
lean_object* v___f_125_; lean_object* v___x_126_; 
v___f_125_ = ((lean_object*)(l_Lake_instComputeTraceListOfMonad___redArg___closed__0));
v___x_126_ = lean_alloc_closure((void*)(l_Lake_computeListTrace), 10, 9);
lean_closure_set(v___x_126_, 0, lean_box(0));
lean_closure_set(v___x_126_, 1, lean_box(0));
lean_closure_set(v___x_126_, 2, lean_box(0));
lean_closure_set(v___x_126_, 3, v_inst_121_);
lean_closure_set(v___x_126_, 4, v_inst_122_);
lean_closure_set(v___x_126_, 5, v_inst_123_);
lean_closure_set(v___x_126_, 6, lean_box(0));
lean_closure_set(v___x_126_, 7, v___f_125_);
lean_closure_set(v___x_126_, 8, v_inst_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad(lean_object* v_00_u03c4_127_, lean_object* v_00_u03b1_128_, lean_object* v_m_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_inst_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lake_instComputeTraceListOfMonad___redArg(v_inst_130_, v_inst_131_, v_inst_132_, v_inst_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace___redArg(lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_as_140_){
_start:
{
lean_object* v_toApplicative_141_; lean_object* v_toBind_142_; lean_object* v_toPure_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_toApplicative_141_ = lean_ctor_get(v_inst_139_, 0);
v_toBind_142_ = lean_ctor_get(v_inst_139_, 1);
v_toPure_143_ = lean_ctor_get(v_toApplicative_141_, 1);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_array_get_size(v_as_140_);
v___x_146_ = lean_nat_dec_lt(v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; 
lean_inc(v_toPure_143_);
lean_dec_ref(v_as_140_);
lean_dec_ref(v_inst_139_);
lean_dec(v_inst_138_);
lean_dec(v_inst_137_);
lean_dec(v_inst_135_);
v___x_147_ = lean_apply_2(v_toPure_143_, lean_box(0), v_inst_136_);
return v___x_147_;
}
else
{
lean_object* v___f_148_; uint8_t v___x_149_; 
lean_inc(v_toBind_142_);
lean_inc(v_toPure_143_);
v___f_148_ = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(v___f_148_, 0, v_inst_135_);
lean_closure_set(v___f_148_, 1, v_toPure_143_);
lean_closure_set(v___f_148_, 2, v_inst_137_);
lean_closure_set(v___f_148_, 3, v_inst_138_);
lean_closure_set(v___f_148_, 4, v_toBind_142_);
v___x_149_ = lean_nat_dec_le(v___x_145_, v___x_145_);
if (v___x_149_ == 0)
{
if (v___x_146_ == 0)
{
lean_object* v___x_150_; 
lean_inc(v_toPure_143_);
lean_dec_ref(v___f_148_);
lean_dec_ref(v_as_140_);
lean_dec_ref(v_inst_139_);
v___x_150_ = lean_apply_2(v_toPure_143_, lean_box(0), v_inst_136_);
return v___x_150_;
}
else
{
size_t v___x_151_; size_t v___x_152_; lean_object* v___x_153_; 
v___x_151_ = ((size_t)0ULL);
v___x_152_ = lean_usize_of_nat(v___x_145_);
v___x_153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_139_, v___f_148_, v_as_140_, v___x_151_, v___x_152_, v_inst_136_);
return v___x_153_;
}
}
else
{
size_t v___x_154_; size_t v___x_155_; lean_object* v___x_156_; 
v___x_154_ = ((size_t)0ULL);
v___x_155_ = lean_usize_of_nat(v___x_145_);
v___x_156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_139_, v___f_148_, v_as_140_, v___x_154_, v___x_155_, v_inst_136_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace(lean_object* v_00_u03c4_157_, lean_object* v_00_u03b1_158_, lean_object* v_m_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_n_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_as_166_){
_start:
{
lean_object* v_toApplicative_167_; lean_object* v_toBind_168_; lean_object* v_toPure_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v_toApplicative_167_ = lean_ctor_get(v_inst_165_, 0);
v_toBind_168_ = lean_ctor_get(v_inst_165_, 1);
v_toPure_169_ = lean_ctor_get(v_toApplicative_167_, 1);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_array_get_size(v_as_166_);
v___x_172_ = lean_nat_dec_lt(v___x_170_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
lean_inc(v_toPure_169_);
lean_dec_ref(v_as_166_);
lean_dec_ref(v_inst_165_);
lean_dec(v_inst_164_);
lean_dec(v_inst_162_);
lean_dec(v_inst_160_);
v___x_173_ = lean_apply_2(v_toPure_169_, lean_box(0), v_inst_161_);
return v___x_173_;
}
else
{
lean_object* v___f_174_; uint8_t v___x_175_; 
lean_inc(v_toBind_168_);
lean_inc(v_toPure_169_);
v___f_174_ = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(v___f_174_, 0, v_inst_160_);
lean_closure_set(v___f_174_, 1, v_toPure_169_);
lean_closure_set(v___f_174_, 2, v_inst_162_);
lean_closure_set(v___f_174_, 3, v_inst_164_);
lean_closure_set(v___f_174_, 4, v_toBind_168_);
v___x_175_ = lean_nat_dec_le(v___x_171_, v___x_171_);
if (v___x_175_ == 0)
{
if (v___x_172_ == 0)
{
lean_object* v___x_176_; 
lean_inc(v_toPure_169_);
lean_dec_ref(v___f_174_);
lean_dec_ref(v_as_166_);
lean_dec_ref(v_inst_165_);
v___x_176_ = lean_apply_2(v_toPure_169_, lean_box(0), v_inst_161_);
return v___x_176_;
}
else
{
size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((size_t)0ULL);
v___x_178_ = lean_usize_of_nat(v___x_171_);
v___x_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_165_, v___f_174_, v_as_166_, v___x_177_, v___x_178_, v_inst_161_);
return v___x_179_;
}
}
else
{
size_t v___x_180_; size_t v___x_181_; lean_object* v___x_182_; 
v___x_180_ = ((size_t)0ULL);
v___x_181_ = lean_usize_of_nat(v___x_171_);
v___x_182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_165_, v___f_174_, v_as_166_, v___x_180_, v___x_181_, v_inst_161_);
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad___redArg(lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_inst_186_){
_start:
{
lean_object* v___f_187_; lean_object* v___x_188_; 
v___f_187_ = ((lean_object*)(l_Lake_instComputeTraceListOfMonad___redArg___closed__0));
v___x_188_ = lean_alloc_closure((void*)(l_Lake_computeArrayTrace), 10, 9);
lean_closure_set(v___x_188_, 0, lean_box(0));
lean_closure_set(v___x_188_, 1, lean_box(0));
lean_closure_set(v___x_188_, 2, lean_box(0));
lean_closure_set(v___x_188_, 3, v_inst_183_);
lean_closure_set(v___x_188_, 4, v_inst_184_);
lean_closure_set(v___x_188_, 5, v_inst_185_);
lean_closure_set(v___x_188_, 6, lean_box(0));
lean_closure_set(v___x_188_, 7, v___f_187_);
lean_closure_set(v___x_188_, 8, v_inst_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad(lean_object* v_00_u03c4_189_, lean_object* v_00_u03b1_190_, lean_object* v_m_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_inst_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lake_instComputeTraceArrayOfMonad___redArg(v_inst_192_, v_inst_193_, v_inst_194_, v_inst_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprHash_repr_spec__0(lean_object* v_a_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_nat_to_int(v_a_197_);
return v___x_198_;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_unsigned_to_nat(7u);
v___x_213_ = lean_nat_to_int(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__0));
v___x_216_ = lean_string_length(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_obj_once(&l_Lake_instReprHash_repr___redArg___closed__9, &l_Lake_instReprHash_repr___redArg___closed__9_once, _init_l_Lake_instReprHash_repr___redArg___closed__9);
v___x_218_ = lean_nat_to_int(v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___redArg(uint64_t v_x_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_224_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__6));
v___x_225_ = lean_obj_once(&l_Lake_instReprHash_repr___redArg___closed__7, &l_Lake_instReprHash_repr___redArg___closed__7_once, _init_l_Lake_instReprHash_repr___redArg___closed__7);
v___x_226_ = lean_uint64_to_nat(v_x_223_);
v___x_227_ = l_Nat_reprFast(v___x_226_);
v___x_228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
v___x_229_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_225_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = 0;
v___x_231_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*1, v___x_230_);
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_224_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_obj_once(&l_Lake_instReprHash_repr___redArg___closed__10, &l_Lake_instReprHash_repr___redArg___closed__10_once, _init_l_Lake_instReprHash_repr___redArg___closed__10);
v___x_234_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__11));
v___x_235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_232_);
v___x_236_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__12));
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_233_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*1, v___x_230_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___redArg___boxed(lean_object* v_x_240_){
_start:
{
uint64_t v_x_147__boxed_241_; lean_object* v_res_242_; 
v_x_147__boxed_241_ = lean_unbox_uint64(v_x_240_);
lean_dec_ref(v_x_240_);
v_res_242_ = l_Lake_instReprHash_repr___redArg(v_x_147__boxed_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr(uint64_t v_x_243_, lean_object* v_prec_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lake_instReprHash_repr___redArg(v_x_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___boxed(lean_object* v_x_246_, lean_object* v_prec_247_){
_start:
{
uint64_t v_x_206__boxed_248_; lean_object* v_res_249_; 
v_x_206__boxed_248_ = lean_unbox_uint64(v_x_246_);
lean_dec_ref(v_x_246_);
v_res_249_ = l_Lake_instReprHash_repr(v_x_206__boxed_248_, v_prec_247_);
lean_dec(v_prec_247_);
return v_res_249_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqHash_decEq(uint64_t v_x_252_, uint64_t v_x_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = lean_uint64_dec_eq(v_x_252_, v_x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash_decEq___boxed(lean_object* v_x_255_, lean_object* v_x_256_){
_start:
{
uint64_t v_x_25__boxed_257_; uint64_t v_x_26__boxed_258_; uint8_t v_res_259_; lean_object* v_r_260_; 
v_x_25__boxed_257_ = lean_unbox_uint64(v_x_255_);
lean_dec_ref(v_x_255_);
v_x_26__boxed_258_ = lean_unbox_uint64(v_x_256_);
lean_dec_ref(v_x_256_);
v_res_259_ = l_Lake_instDecidableEqHash_decEq(v_x_25__boxed_257_, v_x_26__boxed_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqHash(uint64_t v_x_261_, uint64_t v_x_262_){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = lean_uint64_dec_eq(v_x_261_, v_x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash___boxed(lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
uint64_t v_x_6__boxed_266_; uint64_t v_x_7__boxed_267_; uint8_t v_res_268_; lean_object* v_r_269_; 
v_x_6__boxed_266_ = lean_unbox_uint64(v_x_264_);
lean_dec_ref(v_x_264_);
v_x_7__boxed_267_ = lean_unbox_uint64(v_x_265_);
lean_dec_ref(v_x_265_);
v_res_268_ = l_Lake_instDecidableEqHash(v_x_6__boxed_266_, v_x_7__boxed_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_instHashable___lam__0(uint64_t v_self_270_){
_start:
{
return v_self_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_instHashable___lam__0___boxed(lean_object* v_self_271_){
_start:
{
uint64_t v_self_boxed_272_; uint64_t v_res_273_; lean_object* v_r_274_; 
v_self_boxed_272_ = lean_unbox_uint64(v_self_271_);
lean_dec_ref(v_self_271_);
v_res_273_ = l_Lake_Hash_instHashable___lam__0(v_self_boxed_272_);
v_r_274_ = lean_box_uint64(v_res_273_);
return v_r_274_;
}
}
static uint64_t _init_l_Lake_Hash_nil(void){
_start:
{
uint64_t v___x_277_; 
v___x_277_ = 1723ULL;
return v___x_277_;
}
}
static uint64_t _init_l_Lake_Hash_instNilTrace(void){
_start:
{
uint64_t v___x_278_; 
v___x_278_ = 1723ULL;
return v___x_278_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofNat(lean_object* v_n_279_){
_start:
{
uint64_t v___x_280_; 
v___x_280_ = lean_uint64_of_nat(v_n_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofNat___boxed(lean_object* v_n_281_){
_start:
{
uint64_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l_Lake_Hash_ofNat(v_n_281_);
lean_dec(v_n_281_);
v_r_283_ = lean_box_uint64(v_res_282_);
return v_r_283_;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2(void){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_cstr_to_nat("18446744073709551616");
return v___x_287_;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__5(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_nat_to_int(v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object* v_n_293_){
_start:
{
lean_object* v_mantissa_294_; lean_object* v_exponent_295_; uint8_t v___y_297_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_mantissa_294_ = lean_ctor_get(v_n_293_, 0);
v_exponent_295_ = lean_ctor_get(v_n_293_, 1);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_nat_dec_eq(v_exponent_295_, v___x_306_);
if (v___x_307_ == 0)
{
v___y_297_ = v___x_307_;
goto v___jp_296_;
}
else
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__5, &l_Lake_Hash_ofJsonNumber_x3f___closed__5_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__5);
v___x_309_ = lean_int_dec_le(v___x_308_, v_mantissa_294_);
v___y_297_ = v___x_309_;
goto v___jp_296_;
}
v___jp_296_:
{
if (v___y_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_Lake_Hash_ofJsonNumber_x3f___closed__1));
return v___x_298_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_299_ = l_Int_toNat(v_mantissa_294_);
v___x_300_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__2, &l_Lake_Hash_ofJsonNumber_x3f___closed__2_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2);
v___x_301_ = lean_nat_dec_lt(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
lean_dec(v___x_299_);
v___x_302_ = ((lean_object*)(l_Lake_Hash_ofJsonNumber_x3f___closed__4));
return v___x_302_;
}
else
{
uint64_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_uint64_of_nat(v___x_299_);
lean_dec(v___x_299_);
v___x_304_ = lean_box_uint64(v___x_303_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f___boxed(lean_object* v_n_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_310_);
lean_dec_ref(v_n_310_);
return v_res_311_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(lean_object* v_s_312_, lean_object* v_n_313_, lean_object* v_j_314_, uint64_t v_a_315_){
_start:
{
lean_object* v_zero_316_; uint8_t v_isZero_317_; 
v_zero_316_ = lean_unsigned_to_nat(0u);
v_isZero_317_ = lean_nat_dec_eq(v_j_314_, v_zero_316_);
if (v_isZero_317_ == 1)
{
lean_dec(v_j_314_);
return v_a_315_;
}
else
{
lean_object* v_one_318_; lean_object* v_n_319_; lean_object* v___x_320_; uint8_t v_c_321_; uint8_t v___x_322_; uint8_t v___x_323_; 
v_one_318_ = lean_unsigned_to_nat(1u);
v_n_319_ = lean_nat_sub(v_j_314_, v_one_318_);
v___x_320_ = lean_nat_sub(v_n_313_, v_j_314_);
lean_dec(v_j_314_);
v_c_321_ = lean_string_get_byte_fast(v_s_312_, v___x_320_);
v___x_322_ = 57;
v___x_323_ = lean_uint8_dec_le(v_c_321_, v___x_322_);
if (v___x_323_ == 0)
{
uint8_t v___x_324_; uint8_t v___x_325_; 
v___x_324_ = 97;
v___x_325_ = lean_uint8_dec_le(v___x_324_, v_c_321_);
if (v___x_325_ == 0)
{
uint64_t v___x_326_; uint64_t v___x_327_; uint8_t v___x_328_; uint8_t v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; 
v___x_326_ = 4ULL;
v___x_327_ = lean_uint64_shift_left(v_a_315_, v___x_326_);
v___x_328_ = 55;
v___x_329_ = lean_uint8_sub(v_c_321_, v___x_328_);
v___x_330_ = lean_uint8_to_uint64(v___x_329_);
v___x_331_ = lean_uint64_add(v___x_327_, v___x_330_);
v_j_314_ = v_n_319_;
v_a_315_ = v___x_331_;
goto _start;
}
else
{
uint64_t v___x_333_; uint64_t v___x_334_; uint8_t v___x_335_; uint8_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; 
v___x_333_ = 4ULL;
v___x_334_ = lean_uint64_shift_left(v_a_315_, v___x_333_);
v___x_335_ = 87;
v___x_336_ = lean_uint8_sub(v_c_321_, v___x_335_);
v___x_337_ = lean_uint8_to_uint64(v___x_336_);
v___x_338_ = lean_uint64_add(v___x_334_, v___x_337_);
v_j_314_ = v_n_319_;
v_a_315_ = v___x_338_;
goto _start;
}
}
else
{
uint64_t v___x_340_; uint64_t v___x_341_; uint8_t v___x_342_; uint8_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; 
v___x_340_ = 4ULL;
v___x_341_ = lean_uint64_shift_left(v_a_315_, v___x_340_);
v___x_342_ = 48;
v___x_343_ = lean_uint8_sub(v_c_321_, v___x_342_);
v___x_344_ = lean_uint8_to_uint64(v___x_343_);
v___x_345_ = lean_uint64_add(v___x_341_, v___x_344_);
v_j_314_ = v_n_319_;
v_a_315_ = v___x_345_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg___boxed(lean_object* v_s_347_, lean_object* v_n_348_, lean_object* v_j_349_, lean_object* v_a_350_){
_start:
{
uint64_t v_a_252__boxed_351_; uint64_t v_res_352_; lean_object* v_r_353_; 
v_a_252__boxed_351_ = lean_unbox_uint64(v_a_350_);
lean_dec_ref(v_a_350_);
v_res_352_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_347_, v_n_348_, v_j_349_, v_a_252__boxed_351_);
lean_dec(v_n_348_);
lean_dec_ref(v_s_347_);
v_r_353_ = lean_box_uint64(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofHex(lean_object* v_s_354_){
_start:
{
lean_object* v___x_355_; uint64_t v___x_356_; uint64_t v___x_357_; 
v___x_355_ = lean_string_utf8_byte_size(v_s_354_);
v___x_356_ = 0ULL;
v___x_357_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_354_, v___x_355_, v___x_355_, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex___boxed(lean_object* v_s_358_){
_start:
{
uint64_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Lake_Hash_ofHex(v_s_358_);
lean_dec_ref(v_s_358_);
v_r_360_ = lean_box_uint64(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(lean_object* v_s_361_, lean_object* v_n_362_, lean_object* v_j_363_, lean_object* v_a_364_, uint64_t v_a_365_){
_start:
{
uint64_t v___x_366_; 
v___x_366_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_361_, v_n_362_, v_j_363_, v_a_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___boxed(lean_object* v_s_367_, lean_object* v_n_368_, lean_object* v_j_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
uint64_t v_a_316__boxed_372_; uint64_t v_res_373_; lean_object* v_r_374_; 
v_a_316__boxed_372_ = lean_unbox_uint64(v_a_371_);
lean_dec_ref(v_a_371_);
v_res_373_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(v_s_367_, v_n_368_, v_j_369_, v_a_370_, v_a_316__boxed_372_);
lean_dec(v_n_368_);
lean_dec_ref(v_s_367_);
v_r_374_ = lean_box_uint64(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f(lean_object* v_s_375_){
_start:
{
uint8_t v___y_377_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_382_ = lean_string_utf8_byte_size(v_s_375_);
v___x_383_ = lean_unsigned_to_nat(16u);
v___x_384_ = lean_nat_dec_eq(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
v___y_377_ = v___x_384_;
goto v___jp_376_;
}
else
{
uint8_t v___x_385_; 
v___x_385_ = l_Lake_isHex(v_s_375_);
v___y_377_ = v___x_385_;
goto v___jp_376_;
}
v___jp_376_:
{
if (v___y_377_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_box(0);
return v___x_378_;
}
else
{
uint64_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = l_Lake_Hash_ofHex(v_s_375_);
v___x_380_ = lean_box_uint64(v___x_379_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f___boxed(lean_object* v_s_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lake_Hash_ofHex_x3f(v_s_386_);
lean_dec_ref(v_s_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_hex(uint64_t v_self_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint32_t v___x_393_; lean_object* v___x_394_; 
v___x_389_ = lean_unsigned_to_nat(16u);
v___x_390_ = lean_uint64_to_nat(v_self_388_);
v___x_391_ = l_Nat_toDigits(v___x_389_, v___x_390_);
v___x_392_ = lean_string_mk(v___x_391_);
v___x_393_ = 48;
v___x_394_ = l_Lake_lpad(v___x_392_, v___x_393_, v___x_389_);
lean_dec_ref(v___x_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_hex___boxed(lean_object* v_self_395_){
_start:
{
uint64_t v_self_boxed_396_; lean_object* v_res_397_; 
v_self_boxed_396_ = lean_unbox_uint64(v_self_395_);
lean_dec_ref(v_self_395_);
v_res_397_ = l_Lake_Hash_hex(v_self_boxed_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofDecimal_x3f(lean_object* v_s_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_string_utf8_byte_size(v_s_398_);
v___x_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_401_, 0, v_s_398_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
lean_ctor_set(v___x_401_, 2, v___x_400_);
v___x_402_ = l_String_Slice_toNat_x3f(v___x_401_);
lean_dec_ref(v___x_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; 
v___x_403_ = lean_box(0);
return v___x_403_;
}
else
{
lean_object* v_val_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_413_; 
v_val_404_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_413_ == 0)
{
v___x_406_ = v___x_402_;
v_isShared_407_ = v_isSharedCheck_413_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_val_404_);
lean_dec(v___x_402_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_413_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
uint64_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_408_ = lean_uint64_of_nat(v_val_404_);
lean_dec(v_val_404_);
v___x_409_ = lean_box_uint64(v___x_408_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_409_);
v___x_411_ = v___x_406_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f(lean_object* v_s_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lake_Hash_ofHex_x3f(v_s_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f___boxed(lean_object* v_s_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lake_Hash_ofString_x3f(v_s_416_);
lean_dec_ref(v_s_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f(lean_object* v_hashFile_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_IO_FS_readFile(v_hashFile_418_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_422_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref(v___x_420_);
v___x_422_ = l_Lake_Hash_ofHex_x3f(v_a_421_);
lean_dec(v_a_421_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; 
lean_dec_ref(v___x_420_);
v___x_423_ = lean_box(0);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f___boxed(lean_object* v_hashFile_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lake_Hash_load_x3f(v_hashFile_424_);
lean_dec_ref(v_hashFile_424_);
return v_res_426_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_mix(uint64_t v_h1_427_, uint64_t v_h2_428_){
_start:
{
uint64_t v___x_429_; 
v___x_429_ = lean_uint64_mix_hash(v_h1_427_, v_h2_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_mix___boxed(lean_object* v_h1_430_, lean_object* v_h2_431_){
_start:
{
uint64_t v_h1_boxed_432_; uint64_t v_h2_boxed_433_; uint64_t v_res_434_; lean_object* v_r_435_; 
v_h1_boxed_432_ = lean_unbox_uint64(v_h1_430_);
lean_dec_ref(v_h1_430_);
v_h2_boxed_433_ = lean_unbox_uint64(v_h2_431_);
lean_dec_ref(v_h2_431_);
v_res_434_ = l_Lake_Hash_mix(v_h1_boxed_432_, v_h2_boxed_433_);
v_r_435_ = lean_box_uint64(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toString(uint64_t v_self_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lake_Hash_hex(v_self_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toString___boxed(lean_object* v_self_440_){
_start:
{
uint64_t v_self_boxed_441_; lean_object* v_res_442_; 
v_self_boxed_441_ = lean_unbox_uint64(v_self_440_);
lean_dec_ref(v_self_440_);
v_res_442_ = l_Lake_Hash_toString(v_self_boxed_441_);
return v_res_442_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofHashable___redArg(lean_object* v_inst_445_, lean_object* v_a_446_){
_start:
{
uint64_t v___x_447_; lean_object* v___x_448_; uint64_t v___x_449_; uint64_t v___x_450_; 
v___x_447_ = 1723ULL;
v___x_448_ = lean_apply_1(v_inst_445_, v_a_446_);
v___x_449_ = lean_unbox_uint64(v___x_448_);
lean_dec_ref(v___x_448_);
v___x_450_ = lean_uint64_mix_hash(v___x_447_, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHashable___redArg___boxed(lean_object* v_inst_451_, lean_object* v_a_452_){
_start:
{
uint64_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_Lake_Hash_ofHashable___redArg(v_inst_451_, v_a_452_);
v_r_454_ = lean_box_uint64(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofHashable(lean_object* v_00_u03b1_455_, lean_object* v_inst_456_, lean_object* v_a_457_){
_start:
{
uint64_t v___x_458_; lean_object* v___x_459_; uint64_t v___x_460_; uint64_t v___x_461_; 
v___x_458_ = 1723ULL;
v___x_459_ = lean_apply_1(v_inst_456_, v_a_457_);
v___x_460_ = lean_unbox_uint64(v___x_459_);
lean_dec_ref(v___x_459_);
v___x_461_ = lean_uint64_mix_hash(v___x_458_, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHashable___boxed(lean_object* v_00_u03b1_462_, lean_object* v_inst_463_, lean_object* v_a_464_){
_start:
{
uint64_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Lake_Hash_ofHashable(v_00_u03b1_462_, v_inst_463_, v_a_464_);
v_r_466_ = lean_box_uint64(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofString(lean_object* v_str_467_){
_start:
{
uint64_t v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; 
v___x_468_ = 1723ULL;
v___x_469_ = lean_string_hash(v_str_467_);
v___x_470_ = lean_uint64_mix_hash(v___x_468_, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString___boxed(lean_object* v_str_471_){
_start:
{
uint64_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_Lake_Hash_ofString(v_str_471_);
lean_dec_ref(v_str_471_);
v_r_473_ = lean_box_uint64(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofText(lean_object* v_str_474_){
_start:
{
lean_object* v___x_475_; uint64_t v___x_476_; uint64_t v___x_477_; uint64_t v___x_478_; 
v___x_475_ = l_String_crlfToLf(v_str_474_);
v___x_476_ = 1723ULL;
v___x_477_ = lean_string_hash(v___x_475_);
lean_dec_ref(v___x_475_);
v___x_478_ = lean_uint64_mix_hash(v___x_476_, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofText___boxed(lean_object* v_str_479_){
_start:
{
uint64_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Lake_Hash_ofText(v_str_479_);
lean_dec_ref(v_str_479_);
v_r_481_ = lean_box_uint64(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofByteArray(lean_object* v_bytes_482_){
_start:
{
uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; 
v___x_483_ = 1723ULL;
v___x_484_ = lean_byte_array_hash(v_bytes_482_);
v___x_485_ = lean_uint64_mix_hash(v___x_483_, v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofByteArray___boxed(lean_object* v_bytes_486_){
_start:
{
uint64_t v_res_487_; lean_object* v_r_488_; 
v_res_487_ = l_Lake_Hash_ofByteArray(v_bytes_486_);
lean_dec_ref(v_bytes_486_);
v_r_488_ = lean_box_uint64(v_res_487_);
return v_r_488_;
}
}
static uint64_t _init_l_Lake_Hash_ofBool___closed__0(void){
_start:
{
uint64_t v___x_489_; uint64_t v___x_490_; uint64_t v___x_491_; 
v___x_489_ = 13ULL;
v___x_490_ = 1723ULL;
v___x_491_ = lean_uint64_mix_hash(v___x_490_, v___x_489_);
return v___x_491_;
}
}
static uint64_t _init_l_Lake_Hash_ofBool___closed__1(void){
_start:
{
uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v___x_494_; 
v___x_492_ = 11ULL;
v___x_493_ = 1723ULL;
v___x_494_ = lean_uint64_mix_hash(v___x_493_, v___x_492_);
return v___x_494_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofBool(uint8_t v_b_495_){
_start:
{
if (v_b_495_ == 0)
{
uint64_t v___x_496_; 
v___x_496_ = lean_uint64_once(&l_Lake_Hash_ofBool___closed__0, &l_Lake_Hash_ofBool___closed__0_once, _init_l_Lake_Hash_ofBool___closed__0);
return v___x_496_;
}
else
{
uint64_t v___x_497_; 
v___x_497_ = lean_uint64_once(&l_Lake_Hash_ofBool___closed__1, &l_Lake_Hash_ofBool___closed__1_once, _init_l_Lake_Hash_ofBool___closed__1);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofBool___boxed(lean_object* v_b_498_){
_start:
{
uint8_t v_b_boxed_499_; uint64_t v_res_500_; lean_object* v_r_501_; 
v_b_boxed_499_ = lean_unbox(v_b_498_);
v_res_500_ = l_Lake_Hash_ofBool(v_b_boxed_499_);
v_r_501_ = lean_box_uint64(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson(uint64_t v_self_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = l_Lake_Hash_hex(v_self_502_);
v___x_504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson___boxed(lean_object* v_self_505_){
_start:
{
uint64_t v_self_boxed_506_; lean_object* v_res_507_; 
v_self_boxed_506_ = lean_unbox_uint64(v_self_505_);
lean_dec_ref(v_self_505_);
v_res_507_ = l_Lake_Hash_toJson(v_self_boxed_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_fromJson_x3f(lean_object* v_json_520_){
_start:
{
switch(lean_obj_tag(v_json_520_))
{
case 3:
{
lean_object* v_s_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_536_; 
v_s_521_ = lean_ctor_get(v_json_520_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_json_520_);
if (v_isSharedCheck_536_ == 0)
{
v___x_523_ = v_json_520_;
v_isShared_524_ = v_isSharedCheck_536_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_s_521_);
lean_dec(v_json_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_536_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
uint8_t v___x_525_; 
v___x_525_ = l_Lake_isHex(v_s_521_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
lean_del_object(v___x_523_);
lean_dec_ref(v_s_521_);
v___x_526_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__1));
return v___x_526_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_527_ = lean_string_utf8_byte_size(v_s_521_);
v___x_528_ = lean_unsigned_to_nat(16u);
v___x_529_ = lean_nat_dec_eq(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; 
lean_del_object(v___x_523_);
lean_dec_ref(v_s_521_);
v___x_530_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__3));
return v___x_530_;
}
else
{
uint64_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_531_ = l_Lake_Hash_ofHex(v_s_521_);
lean_dec_ref(v_s_521_);
v___x_532_ = lean_box_uint64(v___x_531_);
if (v_isShared_524_ == 0)
{
lean_ctor_set_tag(v___x_523_, 1);
lean_ctor_set(v___x_523_, 0, v___x_532_);
v___x_534_ = v___x_523_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
case 2:
{
lean_object* v_n_537_; lean_object* v___x_538_; 
v_n_537_ = lean_ctor_get(v_json_520_, 0);
lean_inc_ref(v_n_537_);
lean_dec_ref(v_json_520_);
v___x_538_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_537_);
lean_dec_ref(v_n_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_548_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_548_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_543_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__4));
v___x_544_ = lean_string_append(v___x_543_, v_a_539_);
lean_dec(v_a_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_544_);
v___x_546_ = v___x_541_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
return v___x_538_;
}
}
default: 
{
lean_object* v___x_549_; 
lean_dec(v_json_520_);
v___x_549_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__6));
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg(lean_object* v_inst_552_){
_start:
{
lean_inc(v_inst_552_);
return v_inst_552_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg___boxed(lean_object* v_inst_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lake_instComputeTraceHashOfComputeHash___redArg(v_inst_553_);
lean_dec(v_inst_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash(lean_object* v_00_u03b1_555_, lean_object* v_m_556_, lean_object* v_inst_557_){
_start:
{
lean_inc(v_inst_557_);
return v_inst_557_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___boxed(lean_object* v_00_u03b1_558_, lean_object* v_m_559_, lean_object* v_inst_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lake_instComputeTraceHashOfComputeHash(v_00_u03b1_558_, v_m_559_, v_inst_560_);
lean_dec(v_inst_560_);
return v_res_561_;
}
}
LEAN_EXPORT uint64_t l_Lake_pureHash___redArg(lean_object* v_inst_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_564_; uint64_t v___x_565_; 
v___x_564_ = lean_apply_1(v_inst_562_, v_a_563_);
v___x_565_ = lean_unbox_uint64(v___x_564_);
lean_dec_ref(v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_pureHash___redArg___boxed(lean_object* v_inst_566_, lean_object* v_a_567_){
_start:
{
uint64_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_Lake_pureHash___redArg(v_inst_566_, v_a_567_);
v_r_569_ = lean_box_uint64(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT uint64_t l_Lake_pureHash(lean_object* v_00_u03b1_570_, lean_object* v_inst_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_573_; uint64_t v___x_574_; 
v___x_573_ = lean_apply_1(v_inst_571_, v_a_572_);
v___x_574_ = lean_unbox_uint64(v___x_573_);
lean_dec_ref(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lake_pureHash___boxed(lean_object* v_00_u03b1_575_, lean_object* v_inst_576_, lean_object* v_a_577_){
_start:
{
uint64_t v_res_578_; lean_object* v_r_579_; 
v_res_578_ = l_Lake_pureHash(v_00_u03b1_575_, v_inst_576_, v_a_577_);
v_r_579_ = lean_box_uint64(v_res_578_);
return v_r_579_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash___redArg(lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_apply_1(v_inst_580_, v_a_582_);
v___x_584_ = lean_apply_2(v_inst_581_, lean_box(0), v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash(lean_object* v_00_u03b1_585_, lean_object* v_m_586_, lean_object* v_n_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_apply_1(v_inst_588_, v_a_590_);
v___x_592_ = lean_apply_2(v_inst_589_, lean_box(0), v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashIdOfHashable___redArg(lean_object* v_inst_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_alloc_closure((void*)(l_Lake_Hash_ofHashable___boxed), 3, 2);
lean_closure_set(v___x_594_, 0, lean_box(0));
lean_closure_set(v___x_594_, 1, v_inst_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashIdOfHashable(lean_object* v_00_u03b1_595_, lean_object* v_inst_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_closure((void*)(l_Lake_Hash_ofHashable___boxed), 3, 2);
lean_closure_set(v___x_597_, 0, lean_box(0));
lean_closure_set(v___x_597_, 1, v_inst_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash(lean_object* v_file_598_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_IO_FS_readBinFile(v_file_598_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_612_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_612_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_612_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_612_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_605_ = 1723ULL;
v___x_606_ = lean_byte_array_hash(v_a_601_);
lean_dec(v_a_601_);
v___x_607_ = lean_uint64_mix_hash(v___x_605_, v___x_606_);
v___x_608_ = lean_box_uint64(v___x_607_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_608_);
v___x_610_ = v___x_603_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
v_a_613_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_600_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_600_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash___boxed(lean_object* v_file_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lake_computeBinFileHash(v_file_621_);
lean_dec_ref(v_file_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash(lean_object* v_file_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_IO_FS_readFile(v_file_626_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_641_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_641_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_641_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_641_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; uint64_t v___x_634_; uint64_t v___x_635_; uint64_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_633_ = l_String_crlfToLf(v_a_629_);
lean_dec(v_a_629_);
v___x_634_ = 1723ULL;
v___x_635_ = lean_string_hash(v___x_633_);
lean_dec_ref(v___x_633_);
v___x_636_ = lean_uint64_mix_hash(v___x_634_, v___x_635_);
v___x_637_ = lean_box_uint64(v___x_636_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_637_);
v___x_639_ = v___x_631_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
v_a_642_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_628_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_628_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash___boxed(lean_object* v_file_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lake_computeTextFileHash(v_file_650_);
lean_dec_ref(v_file_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0(lean_object* v_x_653_){
_start:
{
lean_inc_ref(v_x_653_);
return v_x_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0___boxed(lean_object* v_x_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lake_instCoeTextFilePathFilePath___lam__0(v_x_654_);
lean_dec_ref(v_x_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash(lean_object* v_file_661_, uint8_t v_text_662_){
_start:
{
if (v_text_662_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = l_Lake_computeBinFileHash(v_file_661_);
return v___x_664_;
}
else
{
lean_object* v___x_665_; 
v___x_665_ = l_Lake_computeTextFileHash(v_file_661_);
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash___boxed(lean_object* v_file_666_, lean_object* v_text_667_, lean_object* v_a_668_){
_start:
{
uint8_t v_text_boxed_669_; lean_object* v_res_670_; 
v_text_boxed_669_ = lean_unbox(v_text_667_);
v_res_670_ = l_Lake_computeFileHash(v_file_666_, v_text_boxed_669_);
lean_dec_ref(v_file_666_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0(uint64_t v_ts_671_, lean_object* v_toPure_672_, uint64_t v_____do__lift_673_){
_start:
{
uint64_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_uint64_mix_hash(v_ts_671_, v_____do__lift_673_);
v___x_675_ = lean_box_uint64(v___x_674_);
v___x_676_ = lean_apply_2(v_toPure_672_, lean_box(0), v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0___boxed(lean_object* v_ts_677_, lean_object* v_toPure_678_, lean_object* v_____do__lift_679_){
_start:
{
uint64_t v_ts_boxed_680_; uint64_t v_____do__lift_97__boxed_681_; lean_object* v_res_682_; 
v_ts_boxed_680_ = lean_unbox_uint64(v_ts_677_);
lean_dec_ref(v_ts_677_);
v_____do__lift_97__boxed_681_ = lean_unbox_uint64(v_____do__lift_679_);
lean_dec_ref(v_____do__lift_679_);
v_res_682_ = l_Lake_computeArrayHash___redArg___lam__0(v_ts_boxed_680_, v_toPure_678_, v_____do__lift_97__boxed_681_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1(lean_object* v_toPure_683_, lean_object* v_inst_684_, lean_object* v_toBind_685_, uint64_t v_ts_686_, lean_object* v_t_687_){
_start:
{
lean_object* v___x_688_; lean_object* v___f_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_688_ = lean_box_uint64(v_ts_686_);
v___f_689_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_689_, 0, v___x_688_);
lean_closure_set(v___f_689_, 1, v_toPure_683_);
v___x_690_ = lean_apply_1(v_inst_684_, v_t_687_);
v___x_691_ = lean_apply_4(v_toBind_685_, lean_box(0), lean_box(0), v___x_690_, v___f_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1___boxed(lean_object* v_toPure_692_, lean_object* v_inst_693_, lean_object* v_toBind_694_, lean_object* v_ts_695_, lean_object* v_t_696_){
_start:
{
uint64_t v_ts_boxed_697_; lean_object* v_res_698_; 
v_ts_boxed_697_ = lean_unbox_uint64(v_ts_695_);
lean_dec_ref(v_ts_695_);
v_res_698_ = l_Lake_computeArrayHash___redArg___lam__1(v_toPure_692_, v_inst_693_, v_toBind_694_, v_ts_boxed_697_, v_t_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg(lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_as_703_){
_start:
{
lean_object* v_toApplicative_704_; lean_object* v_toBind_705_; lean_object* v_toPure_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_toApplicative_704_ = lean_ctor_get(v_inst_702_, 0);
v_toBind_705_ = lean_ctor_get(v_inst_702_, 1);
v_toPure_706_ = lean_ctor_get(v_toApplicative_704_, 1);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = lean_array_get_size(v_as_703_);
v___x_709_ = lean_nat_dec_lt(v___x_707_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_inc(v_toPure_706_);
lean_dec_ref(v_as_703_);
lean_dec_ref(v_inst_702_);
lean_dec(v_inst_701_);
v___x_710_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_711_ = lean_apply_2(v_toPure_706_, lean_box(0), v___x_710_);
return v___x_711_;
}
else
{
lean_object* v___f_712_; uint8_t v___x_713_; 
lean_inc(v_toBind_705_);
lean_inc(v_toPure_706_);
v___f_712_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_712_, 0, v_toPure_706_);
lean_closure_set(v___f_712_, 1, v_inst_701_);
lean_closure_set(v___f_712_, 2, v_toBind_705_);
v___x_713_ = lean_nat_dec_le(v___x_708_, v___x_708_);
if (v___x_713_ == 0)
{
if (v___x_709_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_inc(v_toPure_706_);
lean_dec_ref(v___f_712_);
lean_dec_ref(v_as_703_);
lean_dec_ref(v_inst_702_);
v___x_714_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_715_ = lean_apply_2(v_toPure_706_, lean_box(0), v___x_714_);
return v___x_715_;
}
else
{
size_t v___x_716_; size_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = ((size_t)0ULL);
v___x_717_ = lean_usize_of_nat(v___x_708_);
v___x_718_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_702_, v___f_712_, v_as_703_, v___x_716_, v___x_717_, v___x_718_);
return v___x_719_;
}
}
else
{
size_t v___x_720_; size_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_720_ = ((size_t)0ULL);
v___x_721_ = lean_usize_of_nat(v___x_708_);
v___x_722_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_702_, v___f_712_, v_as_703_, v___x_720_, v___x_721_, v___x_722_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash(lean_object* v_00_u03b1_724_, lean_object* v_m_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_as_728_){
_start:
{
lean_object* v_toApplicative_729_; lean_object* v_toBind_730_; lean_object* v_toPure_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v_toApplicative_729_ = lean_ctor_get(v_inst_727_, 0);
v_toBind_730_ = lean_ctor_get(v_inst_727_, 1);
v_toPure_731_ = lean_ctor_get(v_toApplicative_729_, 1);
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_array_get_size(v_as_728_);
v___x_734_ = lean_nat_dec_lt(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
lean_inc(v_toPure_731_);
lean_dec_ref(v_as_728_);
lean_dec_ref(v_inst_727_);
lean_dec(v_inst_726_);
v___x_735_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_736_ = lean_apply_2(v_toPure_731_, lean_box(0), v___x_735_);
return v___x_736_;
}
else
{
lean_object* v___f_737_; uint8_t v___x_738_; 
lean_inc(v_toBind_730_);
lean_inc(v_toPure_731_);
v___f_737_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_737_, 0, v_toPure_731_);
lean_closure_set(v___f_737_, 1, v_inst_726_);
lean_closure_set(v___f_737_, 2, v_toBind_730_);
v___x_738_ = lean_nat_dec_le(v___x_733_, v___x_733_);
if (v___x_738_ == 0)
{
if (v___x_734_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_inc(v_toPure_731_);
lean_dec_ref(v___f_737_);
lean_dec_ref(v_as_728_);
lean_dec_ref(v_inst_727_);
v___x_739_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_740_ = lean_apply_2(v_toPure_731_, lean_box(0), v___x_739_);
return v___x_740_;
}
else
{
size_t v___x_741_; size_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_741_ = ((size_t)0ULL);
v___x_742_ = lean_usize_of_nat(v___x_733_);
v___x_743_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_727_, v___f_737_, v_as_728_, v___x_741_, v___x_742_, v___x_743_);
return v___x_744_;
}
}
else
{
size_t v___x_745_; size_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_745_ = ((size_t)0ULL);
v___x_746_ = lean_usize_of_nat(v___x_733_);
v___x_747_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_727_, v___f_737_, v_as_728_, v___x_745_, v___x_746_, v___x_747_);
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad___redArg(lean_object* v_inst_749_, lean_object* v_inst_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash), 5, 4);
lean_closure_set(v___x_751_, 0, lean_box(0));
lean_closure_set(v___x_751_, 1, lean_box(0));
lean_closure_set(v___x_751_, 2, v_inst_749_);
lean_closure_set(v___x_751_, 3, v_inst_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad(lean_object* v_00_u03b1_752_, lean_object* v_m_753_, lean_object* v_inst_754_, lean_object* v_inst_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash), 5, 4);
lean_closure_set(v___x_756_, 0, lean_box(0));
lean_closure_set(v___x_756_, 1, lean_box(0));
lean_closure_set(v___x_756_, 2, v_inst_754_);
lean_closure_set(v___x_756_, 3, v_inst_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Lake_MTime_instOfNat___closed__0(void){
_start:
{
uint32_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = 0;
v___x_758_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__5, &l_Lake_Hash_ofJsonNumber_x3f___closed__5_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__5);
v___x_759_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set_uint32(v___x_759_, sizeof(void*)*1, v___x_757_);
return v___x_759_;
}
}
static lean_object* _init_l_Lake_MTime_instOfNat(void){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
return v___x_760_;
}
}
static lean_object* _init_l_Lake_MTime_instLT(void){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = lean_box(0);
return v___x_767_;
}
}
static lean_object* _init_l_Lake_MTime_instLE(void){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = lean_box(0);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0(lean_object* v_x_769_, lean_object* v_y_770_){
_start:
{
uint8_t v___x_771_; 
v___x_771_ = l_IO_FS_instOrdSystemTime_ord(v_x_769_, v_y_770_);
if (v___x_771_ == 2)
{
lean_inc_ref(v_y_770_);
return v_y_770_;
}
else
{
lean_inc_ref(v_x_769_);
return v_x_769_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0___boxed(lean_object* v_x_772_, lean_object* v_y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lake_MTime_instMin___lam__0(v_x_772_, v_y_773_);
lean_dec_ref(v_y_773_);
lean_dec_ref(v_x_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0(lean_object* v_x_777_, lean_object* v_y_778_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = l_IO_FS_instOrdSystemTime_ord(v_x_777_, v_y_778_);
if (v___x_779_ == 2)
{
lean_inc_ref(v_x_777_);
return v_x_777_;
}
else
{
lean_inc_ref(v_y_778_);
return v_y_778_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0___boxed(lean_object* v_x_780_, lean_object* v_y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lake_MTime_instMax___lam__0(v_x_780_, v_y_781_);
lean_dec_ref(v_y_781_);
lean_dec_ref(v_x_780_);
return v_res_782_;
}
}
static lean_object* _init_l_Lake_MTime_instNilTrace(void){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(lean_object* v_inst_787_){
_start:
{
lean_inc_ref(v_inst_787_);
return v_inst_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(lean_object* v_inst_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(v_inst_788_);
lean_dec_ref(v_inst_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(lean_object* v_00_u03b1_790_, lean_object* v_inst_791_){
_start:
{
lean_inc_ref(v_inst_791_);
return v_inst_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___boxed(lean_object* v_00_u03b1_792_, lean_object* v_inst_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(v_00_u03b1_792_, v_inst_793_);
lean_dec_ref(v_inst_793_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime(lean_object* v_file_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = lean_io_metadata(v_file_795_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_modified_802_; lean_object* v___x_804_; 
v_modified_802_ = lean_ctor_get(v_a_798_, 1);
lean_inc_ref(v_modified_802_);
lean_dec(v_a_798_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v_modified_802_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_modified_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
v_a_807_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_797_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_797_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime___boxed(lean_object* v_file_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lake_getFileMTime(v_file_815_);
lean_dec_ref(v_file_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0(lean_object* v_x_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = lean_io_metadata(v_x_820_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_831_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_831_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_modified_827_; lean_object* v___x_829_; 
v_modified_827_ = lean_ctor_get(v_a_823_, 1);
lean_inc_ref(v_modified_827_);
lean_dec(v_a_823_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v_modified_827_);
v___x_829_ = v___x_825_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_modified_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_a_832_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_822_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_822_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0___boxed(lean_object* v_x_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lake_instGetMTimeTextFilePath___lam__0(v_x_840_);
lean_dec_ref(v_x_840_);
return v_res_842_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object* v_inst_845_, lean_object* v_info_846_, lean_object* v_self_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_apply_2(v_inst_845_, v_info_846_, lean_box(0));
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; uint8_t v___x_851_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref(v___x_849_);
v___x_851_ = l_IO_FS_instOrdSystemTime_ord(v_self_847_, v_a_850_);
lean_dec(v_a_850_);
if (v___x_851_ == 0)
{
uint8_t v___x_852_; 
v___x_852_ = 1;
return v___x_852_;
}
else
{
uint8_t v___x_853_; 
v___x_853_ = 0;
return v___x_853_;
}
}
else
{
uint8_t v___x_854_; 
lean_dec_ref(v___x_849_);
v___x_854_ = 0;
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___redArg___boxed(lean_object* v_inst_855_, lean_object* v_info_856_, lean_object* v_self_857_, lean_object* v_a_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_855_, v_info_856_, v_self_857_);
lean_dec_ref(v_self_857_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate(lean_object* v_i_861_, lean_object* v_inst_862_, lean_object* v_info_863_, lean_object* v_self_864_){
_start:
{
uint8_t v___x_866_; 
v___x_866_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_862_, v_info_863_, v_self_864_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___boxed(lean_object* v_i_867_, lean_object* v_inst_868_, lean_object* v_info_869_, lean_object* v_self_870_, lean_object* v_a_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l_Lake_MTime_checkUpToDate(v_i_867_, v_inst_868_, v_info_869_, v_self_870_);
lean_dec_ref(v_self_870_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_unsigned_to_nat(11u);
v___x_884_ = lean_nat_to_int(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_unsigned_to_nat(10u);
v___x_892_ = lean_nat_to_int(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
if (lean_obj_tag(v_x_898_) == 0)
{
lean_dec(v_x_896_);
return v_x_897_;
}
else
{
lean_object* v_head_899_; lean_object* v_tail_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_910_; 
v_head_899_ = lean_ctor_get(v_x_898_, 0);
v_tail_900_ = lean_ctor_get(v_x_898_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_x_898_);
if (v_isSharedCheck_910_ == 0)
{
v___x_902_ = v_x_898_;
v_isShared_903_ = v_isSharedCheck_910_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_tail_900_);
lean_inc(v_head_899_);
lean_dec(v_x_898_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_910_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
lean_inc(v_x_896_);
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 5);
lean_ctor_set(v___x_902_, 1, v_x_896_);
lean_ctor_set(v___x_902_, 0, v_x_897_);
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_x_897_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_x_896_);
v___x_905_ = v_reuseFailAlloc_909_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_899_);
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(v_x_896_, v___x_907_, v_tail_900_);
return v___x_908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
if (lean_obj_tag(v_x_911_) == 0)
{
lean_object* v___x_913_; 
lean_dec(v_x_912_);
v___x_913_ = lean_box(0);
return v___x_913_;
}
else
{
lean_object* v_tail_914_; 
v_tail_914_ = lean_ctor_get(v_x_911_, 1);
if (lean_obj_tag(v_tail_914_) == 0)
{
lean_object* v_head_915_; lean_object* v___x_916_; 
lean_dec(v_x_912_);
v_head_915_ = lean_ctor_get(v_x_911_, 0);
lean_inc(v_head_915_);
lean_dec_ref(v_x_911_);
v___x_916_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_915_);
return v___x_916_;
}
else
{
lean_object* v_head_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_inc(v_tail_914_);
v_head_917_ = lean_ctor_get(v_x_911_, 0);
lean_inc(v_head_917_);
lean_dec_ref(v_x_911_);
v___x_918_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_917_);
v___x_919_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(v_x_912_, v___x_918_, v_tail_914_);
return v___x_919_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0));
v___x_922_ = lean_string_length(v___x_921_);
return v___x_922_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5);
v___x_924_ = lean_nat_to_int(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(lean_object* v_xs_933_){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_934_ = lean_array_get_size(v_xs_933_);
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = lean_nat_dec_eq(v___x_934_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_937_ = lean_array_to_list(v_xs_933_);
v___x_938_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3));
v___x_939_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(v___x_937_, v___x_938_);
v___x_940_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6, &l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6);
v___x_941_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7));
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___x_939_);
v___x_943_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8));
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_940_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = l_Std_Format_fill(v___x_945_);
return v___x_946_;
}
else
{
lean_object* v___x_947_; 
lean_dec_ref(v_xs_933_);
v___x_947_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10));
return v___x_947_;
}
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_unsigned_to_nat(8u);
v___x_952_ = lean_nat_to_int(v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_unsigned_to_nat(9u);
v___x_957_ = lean_nat_to_int(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___redArg(lean_object* v_x_958_){
_start:
{
lean_object* v_caption_959_; lean_object* v_inputs_960_; uint64_t v_hash_961_; lean_object* v_mtime_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_caption_959_ = lean_ctor_get(v_x_958_, 0);
lean_inc_ref(v_caption_959_);
v_inputs_960_ = lean_ctor_get(v_x_958_, 1);
lean_inc_ref(v_inputs_960_);
v_hash_961_ = lean_ctor_get_uint64(v_x_958_, sizeof(void*)*3);
v_mtime_962_ = lean_ctor_get(v_x_958_, 2);
lean_inc_ref(v_mtime_962_);
lean_dec_ref(v_x_958_);
v___x_963_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__5));
v___x_964_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__3));
v___x_965_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__4, &l_Lake_instReprBuildTrace_repr___redArg___closed__4_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4);
v___x_966_ = l_String_quote(v_caption_959_);
v___x_967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
v___x_968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_965_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = 0;
v___x_970_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*1, v___x_969_);
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_964_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2));
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_box(1);
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__6));
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_963_);
v___x_979_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__7, &l_Lake_instReprBuildTrace_repr___redArg___closed__7_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7);
v___x_980_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(v_inputs_960_);
v___x_981_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*1, v___x_969_);
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_978_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_972_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v___x_974_);
v___x_986_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__9));
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_963_);
v___x_989_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__10, &l_Lake_instReprBuildTrace_repr___redArg___closed__10_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10);
v___x_990_ = l_Lake_instReprHash_repr___redArg(v_hash_961_);
v___x_991_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*1, v___x_969_);
v___x_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_988_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___x_972_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_974_);
v___x_996_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__12));
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_963_);
v___x_999_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__13, &l_Lake_instReprBuildTrace_repr___redArg___closed__13_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13);
v___x_1000_ = l_IO_FS_instReprSystemTime_repr___redArg(v_mtime_962_);
lean_dec_ref(v_mtime_962_);
v___x_1001_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*1, v___x_969_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_998_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_obj_once(&l_Lake_instReprHash_repr___redArg___closed__10, &l_Lake_instReprHash_repr___redArg___closed__10_once, _init_l_Lake_instReprHash_repr___redArg___closed__10);
v___x_1005_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__11));
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_1003_);
v___x_1007_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__12));
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1004_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set_uint8(v___x_1010_, sizeof(void*)*1, v___x_969_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
if (lean_obj_tag(v_x_1013_) == 0)
{
lean_dec(v_x_1011_);
return v_x_1012_;
}
else
{
lean_object* v_head_1014_; lean_object* v_tail_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1025_; 
v_head_1014_ = lean_ctor_get(v_x_1013_, 0);
v_tail_1015_ = lean_ctor_get(v_x_1013_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_x_1013_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1017_ = v_x_1013_;
v_isShared_1018_ = v_isSharedCheck_1025_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_tail_1015_);
lean_inc(v_head_1014_);
lean_dec(v_x_1013_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1025_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
lean_inc(v_x_1011_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 5);
lean_ctor_set(v___x_1017_, 1, v_x_1011_);
lean_ctor_set(v___x_1017_, 0, v_x_1012_);
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_x_1012_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_x_1011_);
v___x_1020_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_1014_);
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v_x_1012_ = v___x_1022_;
v_x_1013_ = v_tail_1015_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr(lean_object* v_x_1026_, lean_object* v_prec_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lake_instReprBuildTrace_repr___redArg(v_x_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___boxed(lean_object* v_x_1029_, lean_object* v_prec_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lake_instReprBuildTrace_repr(v_x_1029_, v_prec_1030_);
lean_dec(v_prec_1030_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption(lean_object* v_caption_1034_, lean_object* v_self_1035_){
_start:
{
lean_object* v_inputs_1036_; uint64_t v_hash_1037_; lean_object* v_mtime_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
v_inputs_1036_ = lean_ctor_get(v_self_1035_, 1);
v_hash_1037_ = lean_ctor_get_uint64(v_self_1035_, sizeof(void*)*3);
v_mtime_1038_ = lean_ctor_get(v_self_1035_, 2);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_self_1035_);
if (v_isSharedCheck_1045_ == 0)
{
lean_object* v_unused_1046_; 
v_unused_1046_ = lean_ctor_get(v_self_1035_, 0);
lean_dec(v_unused_1046_);
v___x_1040_ = v_self_1035_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_mtime_1038_);
lean_inc(v_inputs_1036_);
lean_dec(v_self_1035_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v_caption_1034_);
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_caption_1034_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_inputs_1036_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v_mtime_1038_);
lean_ctor_set_uint64(v_reuseFailAlloc_1044_, sizeof(void*)*3, v_hash_1037_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs(lean_object* v_self_1049_){
_start:
{
lean_object* v_caption_1050_; uint64_t v_hash_1051_; lean_object* v_mtime_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1060_; 
v_caption_1050_ = lean_ctor_get(v_self_1049_, 0);
v_hash_1051_ = lean_ctor_get_uint64(v_self_1049_, sizeof(void*)*3);
v_mtime_1052_ = lean_ctor_get(v_self_1049_, 2);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_self_1049_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v_self_1049_, 1);
lean_dec(v_unused_1061_);
v___x_1054_ = v_self_1049_;
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_mtime_1052_);
lean_inc(v_caption_1050_);
lean_dec(v_self_1049_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1056_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v___x_1056_);
v___x_1058_ = v___x_1054_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_caption_1050_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v_mtime_1052_);
lean_ctor_set_uint64(v_reuseFailAlloc_1059_, sizeof(void*)*3, v_hash_1051_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash(uint64_t v_hash_1062_, lean_object* v_caption_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1065_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1066_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1066_, 0, v_caption_1063_);
lean_ctor_set(v___x_1066_, 1, v___x_1064_);
lean_ctor_set(v___x_1066_, 2, v___x_1065_);
lean_ctor_set_uint64(v___x_1066_, sizeof(void*)*3, v_hash_1062_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash___boxed(lean_object* v_hash_1067_, lean_object* v_caption_1068_){
_start:
{
uint64_t v_hash_boxed_1069_; lean_object* v_res_1070_; 
v_hash_boxed_1069_ = lean_unbox_uint64(v_hash_1067_);
lean_dec_ref(v_hash_1067_);
v_res_1070_ = l_Lake_BuildTrace_ofHash(v_hash_boxed_1069_, v_caption_1068_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0(uint64_t v_hash_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1073_ = ((lean_object*)(l_Lake_BuildTrace_instCoeHash___lam__0___closed__0));
v___x_1074_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1075_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1076_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1076_, 0, v___x_1073_);
lean_ctor_set(v___x_1076_, 1, v___x_1074_);
lean_ctor_set(v___x_1076_, 2, v___x_1075_);
lean_ctor_set_uint64(v___x_1076_, sizeof(void*)*3, v_hash_1072_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___boxed(lean_object* v_hash_1077_){
_start:
{
uint64_t v_hash_boxed_1078_; lean_object* v_res_1079_; 
v_hash_boxed_1078_ = lean_unbox_uint64(v_hash_1077_);
lean_dec_ref(v_hash_1077_);
v_res_1079_ = l_Lake_BuildTrace_instCoeHash___lam__0(v_hash_boxed_1078_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofMTime(lean_object* v_mtime_1082_, lean_object* v_caption_1083_){
_start:
{
lean_object* v___x_1084_; uint64_t v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1085_ = 1723ULL;
v___x_1086_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1086_, 0, v_caption_1083_);
lean_ctor_set(v___x_1086_, 1, v___x_1084_);
lean_ctor_set(v___x_1086_, 2, v_mtime_1082_);
lean_ctor_set_uint64(v___x_1086_, sizeof(void*)*3, v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0(lean_object* v_mtime_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; uint64_t v___x_1091_; lean_object* v___x_1092_; 
v___x_1089_ = ((lean_object*)(l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0));
v___x_1090_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1091_ = 1723ULL;
v___x_1092_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1092_, 0, v___x_1089_);
lean_ctor_set(v___x_1092_, 1, v___x_1090_);
lean_ctor_set(v___x_1092_, 2, v_mtime_1088_);
lean_ctor_set_uint64(v___x_1092_, sizeof(void*)*3, v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_nil(lean_object* v_caption_1095_){
_start:
{
lean_object* v___x_1096_; uint64_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1096_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1097_ = 1723ULL;
v___x_1098_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1099_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1099_, 0, v_caption_1095_);
lean_ctor_set(v___x_1099_, 1, v___x_1096_);
lean_ctor_set(v___x_1099_, 2, v___x_1098_);
lean_ctor_set_uint64(v___x_1099_, sizeof(void*)*3, v___x_1097_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace___closed__1(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lake_BuildTrace_instNilTrace___closed__0));
v___x_1102_ = l_Lake_BuildTrace_nil(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace(void){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_obj_once(&l_Lake_BuildTrace_instNilTrace___closed__1, &l_Lake_BuildTrace_instNilTrace___closed__1_once, _init_l_Lake_BuildTrace_instNilTrace___closed__1);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg(lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_info_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_inc(v_info_1108_);
v___x_1110_ = lean_apply_1(v_inst_1105_, v_info_1108_);
v___x_1111_ = lean_apply_3(v_inst_1106_, lean_box(0), v___x_1110_, lean_box(0));
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1113_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref(v___x_1111_);
lean_inc(v_info_1108_);
v___x_1113_ = lean_apply_2(v_inst_1107_, v_info_1108_, lean_box(0));
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1125_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1125_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1125_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint64_t v___x_1121_; lean_object* v___x_1123_; 
v___x_1118_ = lean_apply_1(v_inst_1104_, v_info_1108_);
v___x_1119_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1120_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
lean_ctor_set(v___x_1120_, 2, v_a_1114_);
v___x_1121_ = lean_unbox_uint64(v_a_1112_);
lean_dec(v_a_1112_);
lean_ctor_set_uint64(v___x_1120_, sizeof(void*)*3, v___x_1121_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1120_);
v___x_1123_ = v___x_1116_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1120_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_a_1112_);
lean_dec(v_info_1108_);
lean_dec_ref(v_inst_1104_);
v_a_1126_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1113_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1113_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_info_1108_);
lean_dec_ref(v_inst_1107_);
lean_dec_ref(v_inst_1104_);
v_a_1134_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1111_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1111_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg___boxed(lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_info_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lake_BuildTrace_compute___redArg(v_inst_1142_, v_inst_1143_, v_inst_1144_, v_inst_1145_, v_info_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute(lean_object* v_00_u03b1_1149_, lean_object* v_m_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_info_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lake_BuildTrace_compute___redArg(v_inst_1151_, v_inst_1152_, v_inst_1153_, v_inst_1154_, v_info_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___boxed(lean_object* v_00_u03b1_1158_, lean_object* v_m_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_inst_1163_, lean_object* v_info_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lake_BuildTrace_compute(v_00_u03b1_1158_, v_m_1159_, v_inst_1160_, v_inst_1161_, v_inst_1162_, v_inst_1163_, v_info_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime___redArg(lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(v___x_1171_, 0, lean_box(0));
lean_closure_set(v___x_1171_, 1, lean_box(0));
lean_closure_set(v___x_1171_, 2, v_inst_1167_);
lean_closure_set(v___x_1171_, 3, v_inst_1168_);
lean_closure_set(v___x_1171_, 4, v_inst_1169_);
lean_closure_set(v___x_1171_, 5, v_inst_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(lean_object* v_00_u03b1_1172_, lean_object* v_m_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(v___x_1178_, 0, lean_box(0));
lean_closure_set(v___x_1178_, 1, lean_box(0));
lean_closure_set(v___x_1178_, 2, v_inst_1174_);
lean_closure_set(v___x_1178_, 3, v_inst_1175_);
lean_closure_set(v___x_1178_, 4, v_inst_1176_);
lean_closure_set(v___x_1178_, 5, v_inst_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_mix(lean_object* v_t1_1179_, lean_object* v_t2_1180_){
_start:
{
lean_object* v_caption_1181_; lean_object* v_inputs_1182_; uint64_t v_hash_1183_; lean_object* v_mtime_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1199_; 
v_caption_1181_ = lean_ctor_get(v_t1_1179_, 0);
v_inputs_1182_ = lean_ctor_get(v_t1_1179_, 1);
v_hash_1183_ = lean_ctor_get_uint64(v_t1_1179_, sizeof(void*)*3);
v_mtime_1184_ = lean_ctor_get(v_t1_1179_, 2);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_t1_1179_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1186_ = v_t1_1179_;
v_isShared_1187_ = v_isSharedCheck_1199_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_mtime_1184_);
lean_inc(v_inputs_1182_);
lean_inc(v_caption_1181_);
lean_dec(v_t1_1179_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1199_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
uint64_t v_hash_1188_; lean_object* v_mtime_1189_; lean_object* v___x_1190_; uint64_t v___x_1191_; uint8_t v___x_1192_; 
v_hash_1188_ = lean_ctor_get_uint64(v_t2_1180_, sizeof(void*)*3);
v_mtime_1189_ = lean_ctor_get(v_t2_1180_, 2);
lean_inc_ref(v_mtime_1189_);
v___x_1190_ = lean_array_push(v_inputs_1182_, v_t2_1180_);
v___x_1191_ = lean_uint64_mix_hash(v_hash_1183_, v_hash_1188_);
v___x_1192_ = l_IO_FS_instOrdSystemTime_ord(v_mtime_1184_, v_mtime_1189_);
if (v___x_1192_ == 2)
{
lean_object* v___x_1194_; 
lean_dec_ref(v_mtime_1189_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v___x_1190_);
v___x_1194_ = v___x_1186_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_caption_1181_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_mtime_1184_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_ctor_set_uint64(v___x_1194_, sizeof(void*)*3, v___x_1191_);
return v___x_1194_;
}
}
else
{
lean_object* v___x_1197_; 
lean_dec_ref(v_mtime_1184_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 2, v_mtime_1189_);
lean_ctor_set(v___x_1186_, 1, v___x_1190_);
v___x_1197_ = v___x_1186_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_caption_1181_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_mtime_1189_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_ctor_set_uint64(v___x_1197_, sizeof(void*)*3, v___x_1191_);
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash___redArg(lean_object* v_inst_1202_, lean_object* v_info_1203_, uint64_t v_hash_1204_, lean_object* v_self_1205_){
_start:
{
uint64_t v_hash_1207_; uint8_t v___x_1208_; 
v_hash_1207_ = lean_ctor_get_uint64(v_self_1205_, sizeof(void*)*3);
v___x_1208_ = lean_uint64_dec_eq(v_hash_1204_, v_hash_1207_);
if (v___x_1208_ == 0)
{
lean_dec(v_info_1203_);
lean_dec_ref(v_inst_1202_);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_apply_2(v_inst_1202_, v_info_1203_, lean_box(0));
v___x_1210_ = lean_unbox(v___x_1209_);
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(lean_object* v_inst_1211_, lean_object* v_info_1212_, lean_object* v_hash_1213_, lean_object* v_self_1214_, lean_object* v_a_1215_){
_start:
{
uint64_t v_hash_boxed_1216_; uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_hash_boxed_1216_ = lean_unbox_uint64(v_hash_1213_);
lean_dec_ref(v_hash_1213_);
v_res_1217_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1211_, v_info_1212_, v_hash_boxed_1216_, v_self_1214_);
lean_dec_ref(v_self_1214_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash(lean_object* v_i_1219_, lean_object* v_inst_1220_, lean_object* v_info_1221_, uint64_t v_hash_1222_, lean_object* v_self_1223_){
_start:
{
uint8_t v___x_1225_; 
v___x_1225_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1220_, v_info_1221_, v_hash_1222_, v_self_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___boxed(lean_object* v_i_1226_, lean_object* v_inst_1227_, lean_object* v_info_1228_, lean_object* v_hash_1229_, lean_object* v_self_1230_, lean_object* v_a_1231_){
_start:
{
uint64_t v_hash_boxed_1232_; uint8_t v_res_1233_; lean_object* v_r_1234_; 
v_hash_boxed_1232_ = lean_unbox_uint64(v_hash_1229_);
lean_dec_ref(v_hash_1229_);
v_res_1233_ = l_Lake_BuildTrace_checkAgainstHash(v_i_1226_, v_inst_1227_, v_info_1228_, v_hash_boxed_1232_, v_self_1230_);
lean_dec_ref(v_self_1230_);
v_r_1234_ = lean_box(v_res_1233_);
return v_r_1234_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime___redArg(lean_object* v_inst_1235_, lean_object* v_info_1236_, lean_object* v_self_1237_){
_start:
{
lean_object* v_mtime_1239_; uint8_t v___x_1240_; 
v_mtime_1239_ = lean_ctor_get(v_self_1237_, 2);
v___x_1240_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1235_, v_info_1236_, v_mtime_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___redArg___boxed(lean_object* v_inst_1241_, lean_object* v_info_1242_, lean_object* v_self_1243_, lean_object* v_a_1244_){
_start:
{
uint8_t v_res_1245_; lean_object* v_r_1246_; 
v_res_1245_ = l_Lake_BuildTrace_checkAgainstTime___redArg(v_inst_1241_, v_info_1242_, v_self_1243_);
lean_dec_ref(v_self_1243_);
v_r_1246_ = lean_box(v_res_1245_);
return v_r_1246_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime(lean_object* v_i_1247_, lean_object* v_inst_1248_, lean_object* v_info_1249_, lean_object* v_self_1250_){
_start:
{
lean_object* v_mtime_1252_; uint8_t v___x_1253_; 
v_mtime_1252_ = lean_ctor_get(v_self_1250_, 2);
v___x_1253_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1248_, v_info_1249_, v_mtime_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___boxed(lean_object* v_i_1254_, lean_object* v_inst_1255_, lean_object* v_info_1256_, lean_object* v_self_1257_, lean_object* v_a_1258_){
_start:
{
uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_Lake_BuildTrace_checkAgainstTime(v_i_1254_, v_inst_1255_, v_info_1256_, v_self_1257_);
lean_dec_ref(v_self_1257_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
}
}
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Fold(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Trace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Hash_nil = _init_l_Lake_Hash_nil();
l_Lake_Hash_instNilTrace = _init_l_Lake_Hash_instNilTrace();
l_Lake_MTime_instOfNat = _init_l_Lake_MTime_instOfNat();
lean_mark_persistent(l_Lake_MTime_instOfNat);
l_Lake_MTime_instLT = _init_l_Lake_MTime_instLT();
lean_mark_persistent(l_Lake_MTime_instLT);
l_Lake_MTime_instLE = _init_l_Lake_MTime_instLE();
lean_mark_persistent(l_Lake_MTime_instLE);
l_Lake_MTime_instNilTrace = _init_l_Lake_MTime_instNilTrace();
lean_mark_persistent(l_Lake_MTime_instNilTrace);
l_Lake_BuildTrace_instNilTrace = _init_l_Lake_BuildTrace_instNilTrace();
lean_mark_persistent(l_Lake_BuildTrace_instNilTrace);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Trace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Fold(uint8_t builtin);
lean_object* initialize_Lake_Util_String(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Trace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Trace(builtin);
}
#ifdef __cplusplus
}
#endif
