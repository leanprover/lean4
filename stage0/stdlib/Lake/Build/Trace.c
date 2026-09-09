// Lean compiler output
// Module: Lake.Build.Trace
// Imports: public import Lean.Data.Json import Init.Data.Nat.Fold meta import Init.Data.Nat.Fold public import Lake.Util.String public import Init.Data.String.Search public import Init.Data.String.Extra import Init.Data.Option.Coe
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
lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object*);
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
uint8_t l_IO_FS_instBEqSystemTime_beq(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lake_lowerHexUInt64(uint64_t);
lean_object* l_String_quote(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lake_Hash_ofJsonNumber_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__3;
static const lean_string_object l_Lake_Hash_ofJsonNumber_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "number too big"};
static const lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__4 = (const lean_object*)&l_Lake_Hash_ofJsonNumber_x3f___closed__4_value;
static const lean_ctor_object l_Lake_Hash_ofJsonNumber_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Hash_ofJsonNumber_x3f___closed__4_value)}};
static const lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__5 = (const lean_object*)&l_Lake_Hash_ofJsonNumber_x3f___closed__5_value;
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
LEAN_EXPORT uint8_t l_Lake_MTime_instBEq___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instBEq___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_MTime_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MTime_instBEq___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MTime_instBEq___closed__0 = (const lean_object*)&l_Lake_MTime_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MTime_instBEq = (const lean_object*)&l_Lake_MTime_instBEq___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_MTime_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MTime_instRepr___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MTime_instRepr___closed__0 = (const lean_object*)&l_Lake_MTime_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MTime_instRepr = (const lean_object*)&l_Lake_MTime_instRepr___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_MTime_instOrd___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instOrd___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_MTime_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MTime_instOrd___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
uint64_t v_x_31__boxed_257_; uint64_t v_x_32__boxed_258_; uint8_t v_res_259_; lean_object* v_r_260_; 
v_x_31__boxed_257_ = lean_unbox_uint64(v_x_255_);
lean_dec_ref(v_x_255_);
v_x_32__boxed_258_ = lean_unbox_uint64(v_x_256_);
lean_dec_ref(v_x_256_);
v_res_259_ = l_Lake_instDecidableEqHash_decEq(v_x_31__boxed_257_, v_x_32__boxed_258_);
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
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_nat_to_int(v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__3(void){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_cstr_to_nat("18446744073709551616");
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object* v_n_293_){
_start:
{
lean_object* v_mantissa_296_; lean_object* v_exponent_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_mantissa_296_ = lean_ctor_get(v_n_293_, 0);
v_exponent_297_ = lean_ctor_get(v_n_293_, 1);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_nat_dec_eq(v_exponent_297_, v___x_298_);
if (v___x_299_ == 0)
{
goto v___jp_294_;
}
else
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__2, &l_Lake_Hash_ofJsonNumber_x3f___closed__2_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2);
v___x_301_ = lean_int_dec_le(v___x_300_, v_mantissa_296_);
if (v___x_301_ == 0)
{
goto v___jp_294_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_302_ = l_Int_toNat(v_mantissa_296_);
v___x_303_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__3, &l_Lake_Hash_ofJsonNumber_x3f___closed__3_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__3);
v___x_304_ = lean_nat_dec_lt(v___x_302_, v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
lean_dec(v___x_302_);
v___x_305_ = ((lean_object*)(l_Lake_Hash_ofJsonNumber_x3f___closed__5));
return v___x_305_;
}
else
{
uint64_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_uint64_of_nat(v___x_302_);
lean_dec(v___x_302_);
v___x_307_ = lean_box_uint64(v___x_306_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
}
v___jp_294_:
{
lean_object* v___x_295_; 
v___x_295_ = ((lean_object*)(l_Lake_Hash_ofJsonNumber_x3f___closed__1));
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f___boxed(lean_object* v_n_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_309_);
lean_dec_ref(v_n_309_);
return v_res_310_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(lean_object* v_s_311_, lean_object* v_n_312_, lean_object* v_j_313_, uint64_t v_a_314_){
_start:
{
lean_object* v_zero_315_; uint8_t v_isZero_316_; 
v_zero_315_ = lean_unsigned_to_nat(0u);
v_isZero_316_ = lean_nat_dec_eq(v_j_313_, v_zero_315_);
if (v_isZero_316_ == 1)
{
lean_dec(v_j_313_);
return v_a_314_;
}
else
{
lean_object* v_one_317_; lean_object* v_n_318_; lean_object* v___x_319_; uint8_t v_c_320_; uint8_t v___x_321_; uint8_t v___x_322_; 
v_one_317_ = lean_unsigned_to_nat(1u);
v_n_318_ = lean_nat_sub(v_j_313_, v_one_317_);
v___x_319_ = lean_nat_sub(v_n_312_, v_j_313_);
lean_dec(v_j_313_);
v_c_320_ = lean_string_get_byte_fast(v_s_311_, v___x_319_);
v___x_321_ = 57;
v___x_322_ = lean_uint8_dec_le(v_c_320_, v___x_321_);
if (v___x_322_ == 0)
{
uint8_t v___x_323_; uint8_t v___x_324_; 
v___x_323_ = 97;
v___x_324_ = lean_uint8_dec_le(v___x_323_, v_c_320_);
if (v___x_324_ == 0)
{
uint64_t v___x_325_; uint64_t v___x_326_; uint8_t v___x_327_; uint8_t v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; 
v___x_325_ = 4ULL;
v___x_326_ = lean_uint64_shift_left(v_a_314_, v___x_325_);
v___x_327_ = 55;
v___x_328_ = lean_uint8_sub(v_c_320_, v___x_327_);
v___x_329_ = lean_uint8_to_uint64(v___x_328_);
v___x_330_ = lean_uint64_add(v___x_326_, v___x_329_);
v_j_313_ = v_n_318_;
v_a_314_ = v___x_330_;
goto _start;
}
else
{
uint64_t v___x_332_; uint64_t v___x_333_; uint8_t v___x_334_; uint8_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; 
v___x_332_ = 4ULL;
v___x_333_ = lean_uint64_shift_left(v_a_314_, v___x_332_);
v___x_334_ = 87;
v___x_335_ = lean_uint8_sub(v_c_320_, v___x_334_);
v___x_336_ = lean_uint8_to_uint64(v___x_335_);
v___x_337_ = lean_uint64_add(v___x_333_, v___x_336_);
v_j_313_ = v_n_318_;
v_a_314_ = v___x_337_;
goto _start;
}
}
else
{
uint64_t v___x_339_; uint64_t v___x_340_; uint8_t v___x_341_; uint8_t v___x_342_; uint64_t v___x_343_; uint64_t v___x_344_; 
v___x_339_ = 4ULL;
v___x_340_ = lean_uint64_shift_left(v_a_314_, v___x_339_);
v___x_341_ = 48;
v___x_342_ = lean_uint8_sub(v_c_320_, v___x_341_);
v___x_343_ = lean_uint8_to_uint64(v___x_342_);
v___x_344_ = lean_uint64_add(v___x_340_, v___x_343_);
v_j_313_ = v_n_318_;
v_a_314_ = v___x_344_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg___boxed(lean_object* v_s_346_, lean_object* v_n_347_, lean_object* v_j_348_, lean_object* v_a_349_){
_start:
{
uint64_t v_a_246__boxed_350_; uint64_t v_res_351_; lean_object* v_r_352_; 
v_a_246__boxed_350_ = lean_unbox_uint64(v_a_349_);
lean_dec_ref(v_a_349_);
v_res_351_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_346_, v_n_347_, v_j_348_, v_a_246__boxed_350_);
lean_dec(v_n_347_);
lean_dec_ref(v_s_346_);
v_r_352_ = lean_box_uint64(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofHex(lean_object* v_s_353_){
_start:
{
lean_object* v___x_354_; uint64_t v___x_355_; uint64_t v___x_356_; 
v___x_354_ = lean_string_utf8_byte_size(v_s_353_);
v___x_355_ = 0ULL;
v___x_356_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_353_, v___x_354_, v___x_354_, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex___boxed(lean_object* v_s_357_){
_start:
{
uint64_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_Lake_Hash_ofHex(v_s_357_);
lean_dec_ref(v_s_357_);
v_r_359_ = lean_box_uint64(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(lean_object* v_s_360_, lean_object* v_n_361_, lean_object* v_j_362_, lean_object* v_a_363_, uint64_t v_a_364_){
_start:
{
uint64_t v___x_365_; 
v___x_365_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_360_, v_n_361_, v_j_362_, v_a_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___boxed(lean_object* v_s_366_, lean_object* v_n_367_, lean_object* v_j_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
uint64_t v_a_310__boxed_371_; uint64_t v_res_372_; lean_object* v_r_373_; 
v_a_310__boxed_371_ = lean_unbox_uint64(v_a_370_);
lean_dec_ref(v_a_370_);
v_res_372_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(v_s_366_, v_n_367_, v_j_368_, v_a_369_, v_a_310__boxed_371_);
lean_dec(v_n_367_);
lean_dec_ref(v_s_366_);
v_r_373_ = lean_box_uint64(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f(lean_object* v_s_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = lean_string_utf8_byte_size(v_s_374_);
v___x_376_ = lean_unsigned_to_nat(16u);
v___x_377_ = lean_nat_dec_eq(v___x_375_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_box(0);
return v___x_378_;
}
else
{
uint8_t v___x_379_; 
v___x_379_ = l_Lake_isHex(v_s_374_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
v___x_380_ = lean_box(0);
return v___x_380_;
}
else
{
uint64_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = l_Lake_Hash_ofHex(v_s_374_);
v___x_382_ = lean_box_uint64(v___x_381_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f___boxed(lean_object* v_s_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lake_Hash_ofHex_x3f(v_s_384_);
lean_dec_ref(v_s_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_hex(uint64_t v_self_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lake_lowerHexUInt64(v_self_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_hex___boxed(lean_object* v_self_388_){
_start:
{
uint64_t v_self_boxed_389_; lean_object* v_res_390_; 
v_self_boxed_389_ = lean_unbox_uint64(v_self_388_);
lean_dec_ref(v_self_388_);
v_res_390_ = l_Lake_Hash_hex(v_self_boxed_389_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofDecimal_x3f(lean_object* v_s_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_string_utf8_byte_size(v_s_391_);
v___x_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_394_, 0, v_s_391_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_393_);
v___x_395_ = l_String_Slice_toNat_x3f(v___x_394_);
lean_dec_ref_known(v___x_394_, 3);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v___x_396_; 
v___x_396_ = lean_box(0);
return v___x_396_;
}
else
{
lean_object* v_val_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_406_; 
v_val_397_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_406_ == 0)
{
v___x_399_ = v___x_395_;
v_isShared_400_ = v_isSharedCheck_406_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_val_397_);
lean_dec(v___x_395_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_406_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
uint64_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_401_ = lean_uint64_of_nat(v_val_397_);
lean_dec(v_val_397_);
v___x_402_ = lean_box_uint64(v___x_401_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_402_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f(lean_object* v_s_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lake_Hash_ofHex_x3f(v_s_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f___boxed(lean_object* v_s_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lake_Hash_ofString_x3f(v_s_409_);
lean_dec_ref(v_s_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f(lean_object* v_hashFile_411_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_IO_FS_readFile(v_hashFile_411_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_415_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v___x_415_ = l_Lake_Hash_ofHex_x3f(v_a_414_);
lean_dec(v_a_414_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; 
lean_dec_ref_known(v___x_413_, 1);
v___x_416_ = lean_box(0);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f___boxed(lean_object* v_hashFile_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lake_Hash_load_x3f(v_hashFile_417_);
lean_dec_ref(v_hashFile_417_);
return v_res_419_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_mix(uint64_t v_h1_420_, uint64_t v_h2_421_){
_start:
{
uint64_t v___x_422_; 
v___x_422_ = lean_uint64_mix_hash(v_h1_420_, v_h2_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_mix___boxed(lean_object* v_h1_423_, lean_object* v_h2_424_){
_start:
{
uint64_t v_h1_boxed_425_; uint64_t v_h2_boxed_426_; uint64_t v_res_427_; lean_object* v_r_428_; 
v_h1_boxed_425_ = lean_unbox_uint64(v_h1_423_);
lean_dec_ref(v_h1_423_);
v_h2_boxed_426_ = lean_unbox_uint64(v_h2_424_);
lean_dec_ref(v_h2_424_);
v_res_427_ = l_Lake_Hash_mix(v_h1_boxed_425_, v_h2_boxed_426_);
v_r_428_ = lean_box_uint64(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toString(uint64_t v_self_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lake_lowerHexUInt64(v_self_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toString___boxed(lean_object* v_self_433_){
_start:
{
uint64_t v_self_boxed_434_; lean_object* v_res_435_; 
v_self_boxed_434_ = lean_unbox_uint64(v_self_433_);
lean_dec_ref(v_self_433_);
v_res_435_ = l_Lake_Hash_toString(v_self_boxed_434_);
return v_res_435_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofHashable___redArg(lean_object* v_inst_438_, lean_object* v_a_439_){
_start:
{
uint64_t v___x_440_; lean_object* v___x_441_; uint64_t v___x_442_; uint64_t v___x_443_; 
v___x_440_ = 1723ULL;
v___x_441_ = lean_apply_1(v_inst_438_, v_a_439_);
v___x_442_ = lean_unbox_uint64(v___x_441_);
lean_dec_ref(v___x_441_);
v___x_443_ = lean_uint64_mix_hash(v___x_440_, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHashable___redArg___boxed(lean_object* v_inst_444_, lean_object* v_a_445_){
_start:
{
uint64_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Lake_Hash_ofHashable___redArg(v_inst_444_, v_a_445_);
v_r_447_ = lean_box_uint64(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofHashable(lean_object* v_00_u03b1_448_, lean_object* v_inst_449_, lean_object* v_a_450_){
_start:
{
uint64_t v___x_451_; lean_object* v___x_452_; uint64_t v___x_453_; uint64_t v___x_454_; 
v___x_451_ = 1723ULL;
v___x_452_ = lean_apply_1(v_inst_449_, v_a_450_);
v___x_453_ = lean_unbox_uint64(v___x_452_);
lean_dec_ref(v___x_452_);
v___x_454_ = lean_uint64_mix_hash(v___x_451_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHashable___boxed(lean_object* v_00_u03b1_455_, lean_object* v_inst_456_, lean_object* v_a_457_){
_start:
{
uint64_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Lake_Hash_ofHashable(v_00_u03b1_455_, v_inst_456_, v_a_457_);
v_r_459_ = lean_box_uint64(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofString(lean_object* v_str_460_){
_start:
{
uint64_t v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; 
v___x_461_ = 1723ULL;
v___x_462_ = lean_string_hash(v_str_460_);
v___x_463_ = lean_uint64_mix_hash(v___x_461_, v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString___boxed(lean_object* v_str_464_){
_start:
{
uint64_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Lake_Hash_ofString(v_str_464_);
lean_dec_ref(v_str_464_);
v_r_466_ = lean_box_uint64(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofText(lean_object* v_str_467_){
_start:
{
lean_object* v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; 
v___x_468_ = l_String_crlfToLf(v_str_467_);
v___x_469_ = 1723ULL;
v___x_470_ = lean_string_hash(v___x_468_);
lean_dec_ref(v___x_468_);
v___x_471_ = lean_uint64_mix_hash(v___x_469_, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofText___boxed(lean_object* v_str_472_){
_start:
{
uint64_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l_Lake_Hash_ofText(v_str_472_);
lean_dec_ref(v_str_472_);
v_r_474_ = lean_box_uint64(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofByteArray(lean_object* v_bytes_475_){
_start:
{
uint64_t v___x_476_; uint64_t v___x_477_; uint64_t v___x_478_; 
v___x_476_ = 1723ULL;
v___x_477_ = lean_byte_array_hash(v_bytes_475_);
v___x_478_ = lean_uint64_mix_hash(v___x_476_, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofByteArray___boxed(lean_object* v_bytes_479_){
_start:
{
uint64_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Lake_Hash_ofByteArray(v_bytes_479_);
lean_dec_ref(v_bytes_479_);
v_r_481_ = lean_box_uint64(v_res_480_);
return v_r_481_;
}
}
static uint64_t _init_l_Lake_Hash_ofBool___closed__0(void){
_start:
{
uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v___x_484_; 
v___x_482_ = 13ULL;
v___x_483_ = 1723ULL;
v___x_484_ = lean_uint64_mix_hash(v___x_483_, v___x_482_);
return v___x_484_;
}
}
static uint64_t _init_l_Lake_Hash_ofBool___closed__1(void){
_start:
{
uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v___x_487_; 
v___x_485_ = 11ULL;
v___x_486_ = 1723ULL;
v___x_487_ = lean_uint64_mix_hash(v___x_486_, v___x_485_);
return v___x_487_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofBool(uint8_t v_b_488_){
_start:
{
if (v_b_488_ == 0)
{
uint64_t v___x_489_; 
v___x_489_ = lean_uint64_once(&l_Lake_Hash_ofBool___closed__0, &l_Lake_Hash_ofBool___closed__0_once, _init_l_Lake_Hash_ofBool___closed__0);
return v___x_489_;
}
else
{
uint64_t v___x_490_; 
v___x_490_ = lean_uint64_once(&l_Lake_Hash_ofBool___closed__1, &l_Lake_Hash_ofBool___closed__1_once, _init_l_Lake_Hash_ofBool___closed__1);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofBool___boxed(lean_object* v_b_491_){
_start:
{
uint8_t v_b_boxed_492_; uint64_t v_res_493_; lean_object* v_r_494_; 
v_b_boxed_492_ = lean_unbox(v_b_491_);
v_res_493_ = l_Lake_Hash_ofBool(v_b_boxed_492_);
v_r_494_ = lean_box_uint64(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson(uint64_t v_self_495_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = l_Lake_lowerHexUInt64(v_self_495_);
v___x_497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson___boxed(lean_object* v_self_498_){
_start:
{
uint64_t v_self_boxed_499_; lean_object* v_res_500_; 
v_self_boxed_499_ = lean_unbox_uint64(v_self_498_);
lean_dec_ref(v_self_498_);
v_res_500_ = l_Lake_Hash_toJson(v_self_boxed_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_fromJson_x3f(lean_object* v_json_513_){
_start:
{
switch(lean_obj_tag(v_json_513_))
{
case 3:
{
lean_object* v_s_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_529_; 
v_s_514_ = lean_ctor_get(v_json_513_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_json_513_);
if (v_isSharedCheck_529_ == 0)
{
v___x_516_ = v_json_513_;
v_isShared_517_ = v_isSharedCheck_529_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_s_514_);
lean_dec(v_json_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_529_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
uint8_t v___x_518_; 
v___x_518_ = l_Lake_isHex(v_s_514_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
lean_del_object(v___x_516_);
lean_dec_ref(v_s_514_);
v___x_519_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__1));
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_520_ = lean_string_utf8_byte_size(v_s_514_);
v___x_521_ = lean_unsigned_to_nat(16u);
v___x_522_ = lean_nat_dec_eq(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_del_object(v___x_516_);
lean_dec_ref(v_s_514_);
v___x_523_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__3));
return v___x_523_;
}
else
{
uint64_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_524_ = l_Lake_Hash_ofHex(v_s_514_);
lean_dec_ref(v_s_514_);
v___x_525_ = lean_box_uint64(v___x_524_);
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 1);
lean_ctor_set(v___x_516_, 0, v___x_525_);
v___x_527_ = v___x_516_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
case 2:
{
lean_object* v_n_530_; lean_object* v___x_531_; 
v_n_530_ = lean_ctor_get(v_json_513_, 0);
lean_inc_ref(v_n_530_);
lean_dec_ref_known(v_json_513_, 1);
v___x_531_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_530_);
lean_dec_ref(v_n_530_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_541_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_541_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_536_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__4));
v___x_537_ = lean_string_append(v___x_536_, v_a_532_);
lean_dec(v_a_532_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_537_);
v___x_539_ = v___x_534_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
else
{
return v___x_531_;
}
}
default: 
{
lean_object* v___x_542_; 
lean_dec(v_json_513_);
v___x_542_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__6));
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg(lean_object* v_inst_545_){
_start:
{
lean_inc(v_inst_545_);
return v_inst_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg___boxed(lean_object* v_inst_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lake_instComputeTraceHashOfComputeHash___redArg(v_inst_546_);
lean_dec(v_inst_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash(lean_object* v_00_u03b1_548_, lean_object* v_m_549_, lean_object* v_inst_550_){
_start:
{
lean_inc(v_inst_550_);
return v_inst_550_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___boxed(lean_object* v_00_u03b1_551_, lean_object* v_m_552_, lean_object* v_inst_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lake_instComputeTraceHashOfComputeHash(v_00_u03b1_551_, v_m_552_, v_inst_553_);
lean_dec(v_inst_553_);
return v_res_554_;
}
}
LEAN_EXPORT uint64_t l_Lake_pureHash___redArg(lean_object* v_inst_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_557_; uint64_t v___x_558_; 
v___x_557_ = lean_apply_1(v_inst_555_, v_a_556_);
v___x_558_ = lean_unbox_uint64(v___x_557_);
lean_dec_ref(v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lake_pureHash___redArg___boxed(lean_object* v_inst_559_, lean_object* v_a_560_){
_start:
{
uint64_t v_res_561_; lean_object* v_r_562_; 
v_res_561_ = l_Lake_pureHash___redArg(v_inst_559_, v_a_560_);
v_r_562_ = lean_box_uint64(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT uint64_t l_Lake_pureHash(lean_object* v_00_u03b1_563_, lean_object* v_inst_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_566_; uint64_t v___x_567_; 
v___x_566_ = lean_apply_1(v_inst_564_, v_a_565_);
v___x_567_ = lean_unbox_uint64(v___x_566_);
lean_dec_ref(v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_pureHash___boxed(lean_object* v_00_u03b1_568_, lean_object* v_inst_569_, lean_object* v_a_570_){
_start:
{
uint64_t v_res_571_; lean_object* v_r_572_; 
v_res_571_ = l_Lake_pureHash(v_00_u03b1_568_, v_inst_569_, v_a_570_);
v_r_572_ = lean_box_uint64(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash___redArg(lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_apply_1(v_inst_573_, v_a_575_);
v___x_577_ = lean_apply_2(v_inst_574_, lean_box(0), v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash(lean_object* v_00_u03b1_578_, lean_object* v_m_579_, lean_object* v_n_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_apply_1(v_inst_581_, v_a_583_);
v___x_585_ = lean_apply_2(v_inst_582_, lean_box(0), v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashIdOfHashable___redArg(lean_object* v_inst_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_closure((void*)(l_Lake_Hash_ofHashable___boxed), 3, 2);
lean_closure_set(v___x_587_, 0, lean_box(0));
lean_closure_set(v___x_587_, 1, v_inst_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashIdOfHashable(lean_object* v_00_u03b1_588_, lean_object* v_inst_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_closure((void*)(l_Lake_Hash_ofHashable___boxed), 3, 2);
lean_closure_set(v___x_590_, 0, lean_box(0));
lean_closure_set(v___x_590_, 1, v_inst_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash(lean_object* v_file_591_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_IO_FS_readBinFile(v_file_591_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_605_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_605_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_605_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_605_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
uint64_t v___x_598_; uint64_t v___x_599_; uint64_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_598_ = 1723ULL;
v___x_599_ = lean_byte_array_hash(v_a_594_);
lean_dec(v_a_594_);
v___x_600_ = lean_uint64_mix_hash(v___x_598_, v___x_599_);
v___x_601_ = lean_box_uint64(v___x_600_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_601_);
v___x_603_ = v___x_596_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
v_a_606_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_593_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_593_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash___boxed(lean_object* v_file_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lake_computeBinFileHash(v_file_614_);
lean_dec_ref(v_file_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash(lean_object* v_file_619_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_IO_FS_readFile(v_file_619_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_634_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_634_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_634_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_634_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; uint64_t v___x_627_; uint64_t v___x_628_; uint64_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_626_ = l_String_crlfToLf(v_a_622_);
lean_dec(v_a_622_);
v___x_627_ = 1723ULL;
v___x_628_ = lean_string_hash(v___x_626_);
lean_dec_ref(v___x_626_);
v___x_629_ = lean_uint64_mix_hash(v___x_627_, v___x_628_);
v___x_630_ = lean_box_uint64(v___x_629_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_630_);
v___x_632_ = v___x_624_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
v_a_635_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_621_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_621_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash___boxed(lean_object* v_file_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lake_computeTextFileHash(v_file_643_);
lean_dec_ref(v_file_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0(lean_object* v_x_646_){
_start:
{
lean_inc_ref(v_x_646_);
return v_x_646_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0___boxed(lean_object* v_x_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lake_instCoeTextFilePathFilePath___lam__0(v_x_647_);
lean_dec_ref(v_x_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash(lean_object* v_file_654_, uint8_t v_text_655_){
_start:
{
if (v_text_655_ == 0)
{
lean_object* v___x_657_; 
v___x_657_ = l_Lake_computeBinFileHash(v_file_654_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; 
v___x_658_ = l_Lake_computeTextFileHash(v_file_654_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash___boxed(lean_object* v_file_659_, lean_object* v_text_660_, lean_object* v_a_661_){
_start:
{
uint8_t v_text_boxed_662_; lean_object* v_res_663_; 
v_text_boxed_662_ = lean_unbox(v_text_660_);
v_res_663_ = l_Lake_computeFileHash(v_file_659_, v_text_boxed_662_);
lean_dec_ref(v_file_659_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0(uint64_t v_ts_664_, lean_object* v_toPure_665_, uint64_t v_____do__lift_666_){
_start:
{
uint64_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_uint64_mix_hash(v_ts_664_, v_____do__lift_666_);
v___x_668_ = lean_box_uint64(v___x_667_);
v___x_669_ = lean_apply_2(v_toPure_665_, lean_box(0), v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0___boxed(lean_object* v_ts_670_, lean_object* v_toPure_671_, lean_object* v_____do__lift_672_){
_start:
{
uint64_t v_ts_boxed_673_; uint64_t v_____do__lift_88__boxed_674_; lean_object* v_res_675_; 
v_ts_boxed_673_ = lean_unbox_uint64(v_ts_670_);
lean_dec_ref(v_ts_670_);
v_____do__lift_88__boxed_674_ = lean_unbox_uint64(v_____do__lift_672_);
lean_dec_ref(v_____do__lift_672_);
v_res_675_ = l_Lake_computeArrayHash___redArg___lam__0(v_ts_boxed_673_, v_toPure_671_, v_____do__lift_88__boxed_674_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1(lean_object* v_toPure_676_, lean_object* v_inst_677_, lean_object* v_toBind_678_, uint64_t v_ts_679_, lean_object* v_t_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_681_ = lean_box_uint64(v_ts_679_);
v___f_682_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_682_, 0, v___x_681_);
lean_closure_set(v___f_682_, 1, v_toPure_676_);
v___x_683_ = lean_apply_1(v_inst_677_, v_t_680_);
v___x_684_ = lean_apply_4(v_toBind_678_, lean_box(0), lean_box(0), v___x_683_, v___f_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1___boxed(lean_object* v_toPure_685_, lean_object* v_inst_686_, lean_object* v_toBind_687_, lean_object* v_ts_688_, lean_object* v_t_689_){
_start:
{
uint64_t v_ts_boxed_690_; lean_object* v_res_691_; 
v_ts_boxed_690_ = lean_unbox_uint64(v_ts_688_);
lean_dec_ref(v_ts_688_);
v_res_691_ = l_Lake_computeArrayHash___redArg___lam__1(v_toPure_685_, v_inst_686_, v_toBind_687_, v_ts_boxed_690_, v_t_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg(lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_as_696_){
_start:
{
lean_object* v_toApplicative_697_; lean_object* v_toBind_698_; lean_object* v_toPure_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_toApplicative_697_ = lean_ctor_get(v_inst_695_, 0);
v_toBind_698_ = lean_ctor_get(v_inst_695_, 1);
v_toPure_699_ = lean_ctor_get(v_toApplicative_697_, 1);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_array_get_size(v_as_696_);
v___x_702_ = lean_nat_dec_lt(v___x_700_, v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_inc(v_toPure_699_);
lean_dec_ref(v_as_696_);
lean_dec_ref(v_inst_695_);
lean_dec(v_inst_694_);
v___x_703_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_704_ = lean_apply_2(v_toPure_699_, lean_box(0), v___x_703_);
return v___x_704_;
}
else
{
lean_object* v___f_705_; size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_inc(v_toBind_698_);
lean_inc(v_toPure_699_);
v___f_705_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_705_, 0, v_toPure_699_);
lean_closure_set(v___f_705_, 1, v_inst_694_);
lean_closure_set(v___f_705_, 2, v_toBind_698_);
v___x_706_ = ((size_t)0ULL);
v___x_707_ = lean_usize_of_nat(v___x_701_);
v___x_708_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_695_, v___f_705_, v_as_696_, v___x_706_, v___x_707_, v___x_708_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash(lean_object* v_00_u03b1_710_, lean_object* v_m_711_, lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_as_714_){
_start:
{
lean_object* v_toApplicative_715_; lean_object* v_toBind_716_; lean_object* v_toPure_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_toApplicative_715_ = lean_ctor_get(v_inst_713_, 0);
v_toBind_716_ = lean_ctor_get(v_inst_713_, 1);
v_toPure_717_ = lean_ctor_get(v_toApplicative_715_, 1);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = lean_array_get_size(v_as_714_);
v___x_720_ = lean_nat_dec_lt(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_inc(v_toPure_717_);
lean_dec_ref(v_as_714_);
lean_dec_ref(v_inst_713_);
lean_dec(v_inst_712_);
v___x_721_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_722_ = lean_apply_2(v_toPure_717_, lean_box(0), v___x_721_);
return v___x_722_;
}
else
{
lean_object* v___f_723_; size_t v___x_724_; size_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
lean_inc(v_toBind_716_);
lean_inc(v_toPure_717_);
v___f_723_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_723_, 0, v_toPure_717_);
lean_closure_set(v___f_723_, 1, v_inst_712_);
lean_closure_set(v___f_723_, 2, v_toBind_716_);
v___x_724_ = ((size_t)0ULL);
v___x_725_ = lean_usize_of_nat(v___x_719_);
v___x_726_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_713_, v___f_723_, v_as_714_, v___x_724_, v___x_725_, v___x_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad___redArg(lean_object* v_inst_728_, lean_object* v_inst_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash), 5, 4);
lean_closure_set(v___x_730_, 0, lean_box(0));
lean_closure_set(v___x_730_, 1, lean_box(0));
lean_closure_set(v___x_730_, 2, v_inst_728_);
lean_closure_set(v___x_730_, 3, v_inst_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad(lean_object* v_00_u03b1_731_, lean_object* v_m_732_, lean_object* v_inst_733_, lean_object* v_inst_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash), 5, 4);
lean_closure_set(v___x_735_, 0, lean_box(0));
lean_closure_set(v___x_735_, 1, lean_box(0));
lean_closure_set(v___x_735_, 2, v_inst_733_);
lean_closure_set(v___x_735_, 3, v_inst_734_);
return v___x_735_;
}
}
static lean_object* _init_l_Lake_MTime_instOfNat___closed__0(void){
_start:
{
uint32_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_736_ = 0;
v___x_737_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__2, &l_Lake_Hash_ofJsonNumber_x3f___closed__2_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2);
v___x_738_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set_uint32(v___x_738_, sizeof(void*)*1, v___x_736_);
return v___x_738_;
}
}
static lean_object* _init_l_Lake_MTime_instOfNat(void){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
return v___x_739_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_instBEq___aux__1(lean_object* v_x_740_, lean_object* v_x_741_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = l_IO_FS_instBEqSystemTime_beq(v_x_740_, v_x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instBEq___aux__1___boxed(lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_Lake_MTime_instBEq___aux__1(v_x_743_, v_x_744_);
lean_dec_ref(v_x_744_);
lean_dec_ref(v_x_743_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___redArg(lean_object* v_x_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___redArg___boxed(lean_object* v_x_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lake_MTime_instRepr___aux__1___redArg(v_x_751_);
lean_dec_ref(v_x_751_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1(lean_object* v_x_753_, lean_object* v_prec_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___boxed(lean_object* v_x_756_, lean_object* v_prec_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lake_MTime_instRepr___aux__1(v_x_756_, v_prec_757_);
lean_dec(v_prec_757_);
lean_dec_ref(v_x_756_);
return v_res_758_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_instOrd___aux__1(lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = l_IO_FS_instOrdSystemTime_ord(v_x_761_, v_x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instOrd___aux__1___boxed(lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_Lake_MTime_instOrd___aux__1(v_x_764_, v_x_765_);
lean_dec_ref(v_x_765_);
lean_dec_ref(v_x_764_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
static lean_object* _init_l_Lake_MTime_instLT(void){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = lean_box(0);
return v___x_770_;
}
}
static lean_object* _init_l_Lake_MTime_instLE(void){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = lean_box(0);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0(lean_object* v_x_772_, lean_object* v_y_773_){
_start:
{
uint8_t v___x_774_; 
v___x_774_ = l_IO_FS_instOrdSystemTime_ord(v_x_772_, v_y_773_);
if (v___x_774_ == 2)
{
lean_inc_ref(v_y_773_);
return v_y_773_;
}
else
{
lean_inc_ref(v_x_772_);
return v_x_772_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0___boxed(lean_object* v_x_775_, lean_object* v_y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lake_MTime_instMin___lam__0(v_x_775_, v_y_776_);
lean_dec_ref(v_y_776_);
lean_dec_ref(v_x_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0(lean_object* v_x_780_, lean_object* v_y_781_){
_start:
{
uint8_t v___x_782_; 
v___x_782_ = l_IO_FS_instOrdSystemTime_ord(v_x_780_, v_y_781_);
if (v___x_782_ == 2)
{
lean_inc_ref(v_x_780_);
return v_x_780_;
}
else
{
lean_inc_ref(v_y_781_);
return v_y_781_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0___boxed(lean_object* v_x_783_, lean_object* v_y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lake_MTime_instMax___lam__0(v_x_783_, v_y_784_);
lean_dec_ref(v_y_784_);
lean_dec_ref(v_x_783_);
return v_res_785_;
}
}
static lean_object* _init_l_Lake_MTime_instNilTrace(void){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(lean_object* v_inst_790_){
_start:
{
lean_inc_ref(v_inst_790_);
return v_inst_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(lean_object* v_inst_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(v_inst_791_);
lean_dec_ref(v_inst_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(lean_object* v_00_u03b1_793_, lean_object* v_inst_794_){
_start:
{
lean_inc_ref(v_inst_794_);
return v_inst_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___boxed(lean_object* v_00_u03b1_795_, lean_object* v_inst_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(v_00_u03b1_795_, v_inst_796_);
lean_dec_ref(v_inst_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime(lean_object* v_file_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = lean_io_metadata(v_file_798_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_809_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_809_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_modified_805_; lean_object* v___x_807_; 
v_modified_805_ = lean_ctor_get(v_a_801_, 1);
lean_inc_ref(v_modified_805_);
lean_dec(v_a_801_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v_modified_805_);
v___x_807_ = v___x_803_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_modified_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v_a_810_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_800_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_800_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime___boxed(lean_object* v_file_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lake_getFileMTime(v_file_818_);
lean_dec_ref(v_file_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0(lean_object* v_x_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = lean_io_metadata(v_x_823_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_834_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_834_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_modified_830_; lean_object* v___x_832_; 
v_modified_830_ = lean_ctor_get(v_a_826_, 1);
lean_inc_ref(v_modified_830_);
lean_dec(v_a_826_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_modified_830_);
v___x_832_ = v___x_828_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_modified_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_835_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_825_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_825_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0___boxed(lean_object* v_x_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lake_instGetMTimeTextFilePath___lam__0(v_x_843_);
lean_dec_ref(v_x_843_);
return v_res_845_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object* v_inst_848_, lean_object* v_info_849_, lean_object* v_self_850_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = lean_apply_2(v_inst_848_, v_info_849_, lean_box(0));
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; uint8_t v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = l_IO_FS_instOrdSystemTime_ord(v_self_850_, v_a_853_);
lean_dec(v_a_853_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; 
v___x_855_ = 1;
return v___x_855_;
}
else
{
uint8_t v___x_856_; 
v___x_856_ = 0;
return v___x_856_;
}
}
else
{
uint8_t v___x_857_; 
lean_dec_ref_known(v___x_852_, 1);
v___x_857_ = 0;
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___redArg___boxed(lean_object* v_inst_858_, lean_object* v_info_859_, lean_object* v_self_860_, lean_object* v_a_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_858_, v_info_859_, v_self_860_);
lean_dec_ref(v_self_860_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate(lean_object* v_i_864_, lean_object* v_inst_865_, lean_object* v_info_866_, lean_object* v_self_867_){
_start:
{
uint8_t v___x_869_; 
v___x_869_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_865_, v_info_866_, v_self_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___boxed(lean_object* v_i_870_, lean_object* v_inst_871_, lean_object* v_info_872_, lean_object* v_self_873_, lean_object* v_a_874_){
_start:
{
uint8_t v_res_875_; lean_object* v_r_876_; 
v_res_875_ = l_Lake_MTime_checkUpToDate(v_i_870_, v_inst_871_, v_info_872_, v_self_873_);
lean_dec_ref(v_self_873_);
v_r_876_ = lean_box(v_res_875_);
return v_r_876_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_unsigned_to_nat(11u);
v___x_887_ = lean_nat_to_int(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_unsigned_to_nat(10u);
v___x_895_ = lean_nat_to_int(v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
lean_dec(v_x_899_);
return v_x_900_;
}
else
{
lean_object* v_head_902_; lean_object* v_tail_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_913_; 
v_head_902_ = lean_ctor_get(v_x_901_, 0);
v_tail_903_ = lean_ctor_get(v_x_901_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v_x_901_);
if (v_isSharedCheck_913_ == 0)
{
v___x_905_ = v_x_901_;
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_tail_903_);
lean_inc(v_head_902_);
lean_dec(v_x_901_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
lean_inc(v_x_899_);
if (v_isShared_906_ == 0)
{
lean_ctor_set_tag(v___x_905_, 5);
lean_ctor_set(v___x_905_, 1, v_x_899_);
lean_ctor_set(v___x_905_, 0, v_x_900_);
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_x_900_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_x_899_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_902_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(v_x_899_, v___x_910_, v_tail_903_);
return v___x_911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
if (lean_obj_tag(v_x_914_) == 0)
{
lean_object* v___x_916_; 
lean_dec(v_x_915_);
v___x_916_ = lean_box(0);
return v___x_916_;
}
else
{
lean_object* v_tail_917_; 
v_tail_917_ = lean_ctor_get(v_x_914_, 1);
if (lean_obj_tag(v_tail_917_) == 0)
{
lean_object* v_head_918_; lean_object* v___x_919_; 
lean_dec(v_x_915_);
v_head_918_ = lean_ctor_get(v_x_914_, 0);
lean_inc(v_head_918_);
lean_dec_ref_known(v_x_914_, 2);
v___x_919_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_918_);
return v___x_919_;
}
else
{
lean_object* v_head_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
lean_inc(v_tail_917_);
v_head_920_ = lean_ctor_get(v_x_914_, 0);
lean_inc(v_head_920_);
lean_dec_ref_known(v_x_914_, 2);
v___x_921_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_920_);
v___x_922_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(v_x_915_, v___x_921_, v_tail_917_);
return v___x_922_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0));
v___x_925_ = lean_string_length(v___x_924_);
return v___x_925_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5);
v___x_927_ = lean_nat_to_int(v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(lean_object* v_xs_936_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_937_ = lean_array_get_size(v_xs_936_);
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = lean_nat_dec_eq(v___x_937_, v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_940_ = lean_array_to_list(v_xs_936_);
v___x_941_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3));
v___x_942_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(v___x_940_, v___x_941_);
v___x_943_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6, &l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6);
v___x_944_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7));
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_942_);
v___x_946_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8));
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_943_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = l_Std_Format_fill(v___x_948_);
return v___x_949_;
}
else
{
lean_object* v___x_950_; 
lean_dec_ref(v_xs_936_);
v___x_950_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10));
return v___x_950_;
}
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_unsigned_to_nat(8u);
v___x_955_ = lean_nat_to_int(v___x_954_);
return v___x_955_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_unsigned_to_nat(9u);
v___x_960_ = lean_nat_to_int(v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___redArg(lean_object* v_x_961_){
_start:
{
lean_object* v_caption_962_; lean_object* v_inputs_963_; uint64_t v_hash_964_; lean_object* v_mtime_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_caption_962_ = lean_ctor_get(v_x_961_, 0);
lean_inc_ref(v_caption_962_);
v_inputs_963_ = lean_ctor_get(v_x_961_, 1);
lean_inc_ref(v_inputs_963_);
v_hash_964_ = lean_ctor_get_uint64(v_x_961_, sizeof(void*)*3);
v_mtime_965_ = lean_ctor_get(v_x_961_, 2);
lean_inc_ref(v_mtime_965_);
lean_dec_ref(v_x_961_);
v___x_966_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__5));
v___x_967_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__3));
v___x_968_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__4, &l_Lake_instReprBuildTrace_repr___redArg___closed__4_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4);
v___x_969_ = l_String_quote(v_caption_962_);
v___x_970_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
v___x_971_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_968_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = 0;
v___x_973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*1, v___x_972_);
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_967_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2));
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_box(1);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__6));
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_966_);
v___x_982_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__7, &l_Lake_instReprBuildTrace_repr___redArg___closed__7_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7);
v___x_983_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(v_inputs_963_);
v___x_984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*1, v___x_972_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_981_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_975_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_977_);
v___x_989_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__9));
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_966_);
v___x_992_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__10, &l_Lake_instReprBuildTrace_repr___redArg___closed__10_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10);
v___x_993_ = l_Lake_instReprHash_repr___redArg(v_hash_964_);
v___x_994_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*1, v___x_972_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_991_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_975_);
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_977_);
v___x_999_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__12));
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_966_);
v___x_1002_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__13, &l_Lake_instReprBuildTrace_repr___redArg___closed__13_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13);
v___x_1003_ = l_IO_FS_instReprSystemTime_repr___redArg(v_mtime_965_);
lean_dec_ref(v_mtime_965_);
v___x_1004_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*1, v___x_972_);
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1001_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = lean_obj_once(&l_Lake_instReprHash_repr___redArg___closed__10, &l_Lake_instReprHash_repr___redArg___closed__10_once, _init_l_Lake_instReprHash_repr___redArg___closed__10);
v___x_1008_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__11));
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_1006_);
v___x_1010_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__12));
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1007_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*1, v___x_972_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
if (lean_obj_tag(v_x_1016_) == 0)
{
lean_dec(v_x_1014_);
return v_x_1015_;
}
else
{
lean_object* v_head_1017_; lean_object* v_tail_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1028_; 
v_head_1017_ = lean_ctor_get(v_x_1016_, 0);
v_tail_1018_ = lean_ctor_get(v_x_1016_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_x_1016_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1020_ = v_x_1016_;
v_isShared_1021_ = v_isSharedCheck_1028_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_tail_1018_);
lean_inc(v_head_1017_);
lean_dec(v_x_1016_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1028_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
lean_inc(v_x_1014_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 5);
lean_ctor_set(v___x_1020_, 1, v_x_1014_);
lean_ctor_set(v___x_1020_, 0, v_x_1015_);
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_x_1015_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_x_1014_);
v___x_1023_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_1017_);
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v_x_1015_ = v___x_1025_;
v_x_1016_ = v_tail_1018_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr(lean_object* v_x_1029_, lean_object* v_prec_1030_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lake_instReprBuildTrace_repr___redArg(v_x_1029_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___boxed(lean_object* v_x_1032_, lean_object* v_prec_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lake_instReprBuildTrace_repr(v_x_1032_, v_prec_1033_);
lean_dec(v_prec_1033_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption(lean_object* v_caption_1037_, lean_object* v_self_1038_){
_start:
{
lean_object* v_inputs_1039_; uint64_t v_hash_1040_; lean_object* v_mtime_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
v_inputs_1039_ = lean_ctor_get(v_self_1038_, 1);
v_hash_1040_ = lean_ctor_get_uint64(v_self_1038_, sizeof(void*)*3);
v_mtime_1041_ = lean_ctor_get(v_self_1038_, 2);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_self_1038_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v_self_1038_, 0);
lean_dec(v_unused_1049_);
v___x_1043_ = v_self_1038_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_mtime_1041_);
lean_inc(v_inputs_1039_);
lean_dec(v_self_1038_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v_caption_1037_);
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_caption_1037_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_inputs_1039_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_mtime_1041_);
lean_ctor_set_uint64(v_reuseFailAlloc_1047_, sizeof(void*)*3, v_hash_1040_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs(lean_object* v_self_1052_){
_start:
{
lean_object* v_caption_1053_; uint64_t v_hash_1054_; lean_object* v_mtime_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1063_; 
v_caption_1053_ = lean_ctor_get(v_self_1052_, 0);
v_hash_1054_ = lean_ctor_get_uint64(v_self_1052_, sizeof(void*)*3);
v_mtime_1055_ = lean_ctor_get(v_self_1052_, 2);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_self_1052_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v_self_1052_, 1);
lean_dec(v_unused_1064_);
v___x_1057_ = v_self_1052_;
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_mtime_1055_);
lean_inc(v_caption_1053_);
lean_dec(v_self_1052_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v___x_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_caption_1053_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v_mtime_1055_);
lean_ctor_set_uint64(v_reuseFailAlloc_1062_, sizeof(void*)*3, v_hash_1054_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash(uint64_t v_hash_1065_, lean_object* v_caption_1066_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1068_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1069_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1069_, 0, v_caption_1066_);
lean_ctor_set(v___x_1069_, 1, v___x_1067_);
lean_ctor_set(v___x_1069_, 2, v___x_1068_);
lean_ctor_set_uint64(v___x_1069_, sizeof(void*)*3, v_hash_1065_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash___boxed(lean_object* v_hash_1070_, lean_object* v_caption_1071_){
_start:
{
uint64_t v_hash_boxed_1072_; lean_object* v_res_1073_; 
v_hash_boxed_1072_ = lean_unbox_uint64(v_hash_1070_);
lean_dec_ref(v_hash_1070_);
v_res_1073_ = l_Lake_BuildTrace_ofHash(v_hash_boxed_1072_, v_caption_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0(uint64_t v_hash_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1076_ = ((lean_object*)(l_Lake_BuildTrace_instCoeHash___lam__0___closed__0));
v___x_1077_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1078_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1079_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1079_, 0, v___x_1076_);
lean_ctor_set(v___x_1079_, 1, v___x_1077_);
lean_ctor_set(v___x_1079_, 2, v___x_1078_);
lean_ctor_set_uint64(v___x_1079_, sizeof(void*)*3, v_hash_1075_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___boxed(lean_object* v_hash_1080_){
_start:
{
uint64_t v_hash_boxed_1081_; lean_object* v_res_1082_; 
v_hash_boxed_1081_ = lean_unbox_uint64(v_hash_1080_);
lean_dec_ref(v_hash_1080_);
v_res_1082_ = l_Lake_BuildTrace_instCoeHash___lam__0(v_hash_boxed_1081_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofMTime(lean_object* v_mtime_1085_, lean_object* v_caption_1086_){
_start:
{
lean_object* v___x_1087_; uint64_t v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1088_ = 1723ULL;
v___x_1089_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1089_, 0, v_caption_1086_);
lean_ctor_set(v___x_1089_, 1, v___x_1087_);
lean_ctor_set(v___x_1089_, 2, v_mtime_1085_);
lean_ctor_set_uint64(v___x_1089_, sizeof(void*)*3, v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0(lean_object* v_mtime_1091_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; uint64_t v___x_1094_; lean_object* v___x_1095_; 
v___x_1092_ = ((lean_object*)(l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0));
v___x_1093_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1094_ = 1723ULL;
v___x_1095_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1095_, 0, v___x_1092_);
lean_ctor_set(v___x_1095_, 1, v___x_1093_);
lean_ctor_set(v___x_1095_, 2, v_mtime_1091_);
lean_ctor_set_uint64(v___x_1095_, sizeof(void*)*3, v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_nil(lean_object* v_caption_1098_){
_start:
{
lean_object* v___x_1099_; uint64_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1099_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1100_ = 1723ULL;
v___x_1101_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1102_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1102_, 0, v_caption_1098_);
lean_ctor_set(v___x_1102_, 1, v___x_1099_);
lean_ctor_set(v___x_1102_, 2, v___x_1101_);
lean_ctor_set_uint64(v___x_1102_, sizeof(void*)*3, v___x_1100_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace___closed__1(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lake_BuildTrace_instNilTrace___closed__0));
v___x_1105_ = l_Lake_BuildTrace_nil(v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace(void){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_obj_once(&l_Lake_BuildTrace_instNilTrace___closed__1, &l_Lake_BuildTrace_instNilTrace___closed__1_once, _init_l_Lake_BuildTrace_instNilTrace___closed__1);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg(lean_object* v_inst_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_info_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_inc(v_info_1111_);
v___x_1113_ = lean_apply_1(v_inst_1108_, v_info_1111_);
v___x_1114_ = lean_apply_3(v_inst_1109_, lean_box(0), v___x_1113_, lean_box(0));
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
lean_inc(v_info_1111_);
v___x_1116_ = lean_apply_2(v_inst_1110_, v_info_1111_, lean_box(0));
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1128_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1128_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1128_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint64_t v___x_1124_; lean_object* v___x_1126_; 
v___x_1121_ = lean_apply_1(v_inst_1107_, v_info_1111_);
v___x_1122_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1123_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
lean_ctor_set(v___x_1123_, 2, v_a_1117_);
v___x_1124_ = lean_unbox_uint64(v_a_1115_);
lean_dec(v_a_1115_);
lean_ctor_set_uint64(v___x_1123_, sizeof(void*)*3, v___x_1124_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1123_);
v___x_1126_ = v___x_1119_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1123_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v_a_1115_);
lean_dec(v_info_1111_);
lean_dec_ref(v_inst_1107_);
v_a_1129_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1116_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1116_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_info_1111_);
lean_dec_ref(v_inst_1110_);
lean_dec_ref(v_inst_1107_);
v_a_1137_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1114_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1114_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg___boxed(lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_info_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lake_BuildTrace_compute___redArg(v_inst_1145_, v_inst_1146_, v_inst_1147_, v_inst_1148_, v_info_1149_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute(lean_object* v_00_u03b1_1152_, lean_object* v_m_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_info_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lake_BuildTrace_compute___redArg(v_inst_1154_, v_inst_1155_, v_inst_1156_, v_inst_1157_, v_info_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___boxed(lean_object* v_00_u03b1_1161_, lean_object* v_m_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_info_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lake_BuildTrace_compute(v_00_u03b1_1161_, v_m_1162_, v_inst_1163_, v_inst_1164_, v_inst_1165_, v_inst_1166_, v_info_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime___redArg(lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(v___x_1174_, 0, lean_box(0));
lean_closure_set(v___x_1174_, 1, lean_box(0));
lean_closure_set(v___x_1174_, 2, v_inst_1170_);
lean_closure_set(v___x_1174_, 3, v_inst_1171_);
lean_closure_set(v___x_1174_, 4, v_inst_1172_);
lean_closure_set(v___x_1174_, 5, v_inst_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(lean_object* v_00_u03b1_1175_, lean_object* v_m_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(v___x_1181_, 0, lean_box(0));
lean_closure_set(v___x_1181_, 1, lean_box(0));
lean_closure_set(v___x_1181_, 2, v_inst_1177_);
lean_closure_set(v___x_1181_, 3, v_inst_1178_);
lean_closure_set(v___x_1181_, 4, v_inst_1179_);
lean_closure_set(v___x_1181_, 5, v_inst_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_mix(lean_object* v_t1_1182_, lean_object* v_t2_1183_){
_start:
{
lean_object* v_caption_1184_; lean_object* v_inputs_1185_; uint64_t v_hash_1186_; lean_object* v_mtime_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1202_; 
v_caption_1184_ = lean_ctor_get(v_t1_1182_, 0);
v_inputs_1185_ = lean_ctor_get(v_t1_1182_, 1);
v_hash_1186_ = lean_ctor_get_uint64(v_t1_1182_, sizeof(void*)*3);
v_mtime_1187_ = lean_ctor_get(v_t1_1182_, 2);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_t1_1182_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1189_ = v_t1_1182_;
v_isShared_1190_ = v_isSharedCheck_1202_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_mtime_1187_);
lean_inc(v_inputs_1185_);
lean_inc(v_caption_1184_);
lean_dec(v_t1_1182_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1202_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
uint64_t v_hash_1191_; lean_object* v_mtime_1192_; lean_object* v___x_1193_; uint64_t v___x_1194_; uint8_t v___x_1195_; 
v_hash_1191_ = lean_ctor_get_uint64(v_t2_1183_, sizeof(void*)*3);
v_mtime_1192_ = lean_ctor_get(v_t2_1183_, 2);
lean_inc_ref(v_mtime_1192_);
v___x_1193_ = lean_array_push(v_inputs_1185_, v_t2_1183_);
v___x_1194_ = lean_uint64_mix_hash(v_hash_1186_, v_hash_1191_);
v___x_1195_ = l_IO_FS_instOrdSystemTime_ord(v_mtime_1187_, v_mtime_1192_);
if (v___x_1195_ == 2)
{
lean_object* v___x_1197_; 
lean_dec_ref(v_mtime_1192_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1193_);
v___x_1197_ = v___x_1189_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_caption_1184_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_mtime_1187_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_ctor_set_uint64(v___x_1197_, sizeof(void*)*3, v___x_1194_);
return v___x_1197_;
}
}
else
{
lean_object* v___x_1200_; 
lean_dec_ref(v_mtime_1187_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 2, v_mtime_1192_);
lean_ctor_set(v___x_1189_, 1, v___x_1193_);
v___x_1200_ = v___x_1189_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_caption_1184_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_mtime_1192_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_ctor_set_uint64(v___x_1200_, sizeof(void*)*3, v___x_1194_);
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash___redArg(lean_object* v_inst_1205_, lean_object* v_info_1206_, uint64_t v_hash_1207_, lean_object* v_self_1208_){
_start:
{
uint64_t v_hash_1210_; uint8_t v___x_1211_; 
v_hash_1210_ = lean_ctor_get_uint64(v_self_1208_, sizeof(void*)*3);
v___x_1211_ = lean_uint64_dec_eq(v_hash_1207_, v_hash_1210_);
if (v___x_1211_ == 0)
{
lean_dec(v_info_1206_);
lean_dec_ref(v_inst_1205_);
return v___x_1211_;
}
else
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_apply_2(v_inst_1205_, v_info_1206_, lean_box(0));
v___x_1213_ = lean_unbox(v___x_1212_);
return v___x_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(lean_object* v_inst_1214_, lean_object* v_info_1215_, lean_object* v_hash_1216_, lean_object* v_self_1217_, lean_object* v_a_1218_){
_start:
{
uint64_t v_hash_boxed_1219_; uint8_t v_res_1220_; lean_object* v_r_1221_; 
v_hash_boxed_1219_ = lean_unbox_uint64(v_hash_1216_);
lean_dec_ref(v_hash_1216_);
v_res_1220_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1214_, v_info_1215_, v_hash_boxed_1219_, v_self_1217_);
lean_dec_ref(v_self_1217_);
v_r_1221_ = lean_box(v_res_1220_);
return v_r_1221_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash(lean_object* v_i_1222_, lean_object* v_inst_1223_, lean_object* v_info_1224_, uint64_t v_hash_1225_, lean_object* v_self_1226_){
_start:
{
uint8_t v___x_1228_; 
v___x_1228_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1223_, v_info_1224_, v_hash_1225_, v_self_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___boxed(lean_object* v_i_1229_, lean_object* v_inst_1230_, lean_object* v_info_1231_, lean_object* v_hash_1232_, lean_object* v_self_1233_, lean_object* v_a_1234_){
_start:
{
uint64_t v_hash_boxed_1235_; uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_hash_boxed_1235_ = lean_unbox_uint64(v_hash_1232_);
lean_dec_ref(v_hash_1232_);
v_res_1236_ = l_Lake_BuildTrace_checkAgainstHash(v_i_1229_, v_inst_1230_, v_info_1231_, v_hash_boxed_1235_, v_self_1233_);
lean_dec_ref(v_self_1233_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime___redArg(lean_object* v_inst_1238_, lean_object* v_info_1239_, lean_object* v_self_1240_){
_start:
{
lean_object* v_mtime_1242_; uint8_t v___x_1243_; 
v_mtime_1242_ = lean_ctor_get(v_self_1240_, 2);
v___x_1243_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1238_, v_info_1239_, v_mtime_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___redArg___boxed(lean_object* v_inst_1244_, lean_object* v_info_1245_, lean_object* v_self_1246_, lean_object* v_a_1247_){
_start:
{
uint8_t v_res_1248_; lean_object* v_r_1249_; 
v_res_1248_ = l_Lake_BuildTrace_checkAgainstTime___redArg(v_inst_1244_, v_info_1245_, v_self_1246_);
lean_dec_ref(v_self_1246_);
v_r_1249_ = lean_box(v_res_1248_);
return v_r_1249_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime(lean_object* v_i_1250_, lean_object* v_inst_1251_, lean_object* v_info_1252_, lean_object* v_self_1253_){
_start:
{
lean_object* v_mtime_1255_; uint8_t v___x_1256_; 
v_mtime_1255_ = lean_ctor_get(v_self_1253_, 2);
v___x_1256_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1251_, v_info_1252_, v_mtime_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___boxed(lean_object* v_i_1257_, lean_object* v_inst_1258_, lean_object* v_info_1259_, lean_object* v_self_1260_, lean_object* v_a_1261_){
_start:
{
uint8_t v_res_1262_; lean_object* v_r_1263_; 
v_res_1262_ = l_Lake_BuildTrace_checkAgainstTime(v_i_1257_, v_inst_1258_, v_info_1259_, v_self_1260_);
lean_dec_ref(v_self_1260_);
v_r_1263_ = lean_box(v_res_1262_);
return v_r_1263_;
}
}
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Fold(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Trace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
lean_object* runtime_initialize_Init_Data_Nat_Fold(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Trace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Fold(uint8_t builtin);
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
