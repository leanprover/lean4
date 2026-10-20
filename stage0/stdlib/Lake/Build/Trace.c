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
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Lake_instComputeTraceListOfMonad___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___f_64_; size_t v___x_65_; size_t v___x_66_; lean_object* v___x_67_; 
v___f_64_ = lean_alloc_closure((void*)(l_Lake_mixTraceArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_64_, 0, v_inst_57_);
v___x_65_ = ((size_t)0ULL);
v___x_66_ = lean_usize_of_nat(v___x_61_);
v___x_67_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_62_, v___f_64_, v_traces_59_, v___x_65_, v___x_66_, v_inst_58_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceArray(lean_object* v_00_u03c4_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_traces_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lake_mixTraceArray___redArg(v_inst_69_, v_inst_70_, v_traces_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__0(lean_object* v_inst_73_, lean_object* v_ts_74_, lean_object* v_toPure_75_, lean_object* v_____do__lift_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_apply_2(v_inst_73_, v_ts_74_, v_____do__lift_76_);
v___x_78_ = lean_apply_2(v_toPure_75_, lean_box(0), v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__1(lean_object* v_inst_79_, lean_object* v_toPure_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_toBind_83_, lean_object* v_ts_84_, lean_object* v_t_85_){
_start:
{
lean_object* v___f_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___f_86_ = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_86_, 0, v_inst_79_);
lean_closure_set(v___f_86_, 1, v_ts_84_);
lean_closure_set(v___f_86_, 2, v_toPure_80_);
v___x_87_ = lean_apply_1(v_inst_81_, v_t_85_);
v___x_88_ = lean_apply_2(v_inst_82_, lean_box(0), v___x_87_);
v___x_89_ = lean_apply_4(v_toBind_83_, lean_box(0), lean_box(0), v___x_88_, v___f_86_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg(lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_as_95_){
_start:
{
lean_object* v_toApplicative_96_; lean_object* v_toBind_97_; lean_object* v_toPure_98_; lean_object* v___f_99_; lean_object* v___x_100_; 
v_toApplicative_96_ = lean_ctor_get(v_inst_94_, 0);
v_toBind_97_ = lean_ctor_get(v_inst_94_, 1);
v_toPure_98_ = lean_ctor_get(v_toApplicative_96_, 1);
lean_inc(v_toBind_97_);
lean_inc(v_toPure_98_);
v___f_99_ = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(v___f_99_, 0, v_inst_90_);
lean_closure_set(v___f_99_, 1, v_toPure_98_);
lean_closure_set(v___f_99_, 2, v_inst_92_);
lean_closure_set(v___f_99_, 3, v_inst_93_);
lean_closure_set(v___f_99_, 4, v_toBind_97_);
v___x_100_ = l_List_foldlM___redArg(v_inst_94_, v___f_99_, v_inst_91_, v_as_95_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace(lean_object* v_00_u03c4_101_, lean_object* v_00_u03b1_102_, lean_object* v_m_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_n_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_as_110_){
_start:
{
lean_object* v_toApplicative_111_; lean_object* v_toBind_112_; lean_object* v_toPure_113_; lean_object* v___f_114_; lean_object* v___x_115_; 
v_toApplicative_111_ = lean_ctor_get(v_inst_109_, 0);
v_toBind_112_ = lean_ctor_get(v_inst_109_, 1);
v_toPure_113_ = lean_ctor_get(v_toApplicative_111_, 1);
lean_inc(v_toBind_112_);
lean_inc(v_toPure_113_);
v___f_114_ = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(v___f_114_, 0, v_inst_104_);
lean_closure_set(v___f_114_, 1, v_toPure_113_);
lean_closure_set(v___f_114_, 2, v_inst_106_);
lean_closure_set(v___f_114_, 3, v_inst_108_);
lean_closure_set(v___f_114_, 4, v_toBind_112_);
v___x_115_ = l_List_foldlM___redArg(v_inst_109_, v___f_114_, v_inst_105_, v_as_110_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad___redArg(lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_){
_start:
{
lean_object* v___f_121_; lean_object* v___x_122_; 
v___f_121_ = ((lean_object*)(l_Lake_instComputeTraceListOfMonad___redArg___closed__0));
v___x_122_ = lean_alloc_closure((void*)(l_Lake_computeListTrace), 10, 9);
lean_closure_set(v___x_122_, 0, lean_box(0));
lean_closure_set(v___x_122_, 1, lean_box(0));
lean_closure_set(v___x_122_, 2, lean_box(0));
lean_closure_set(v___x_122_, 3, v_inst_117_);
lean_closure_set(v___x_122_, 4, v_inst_118_);
lean_closure_set(v___x_122_, 5, v_inst_119_);
lean_closure_set(v___x_122_, 6, lean_box(0));
lean_closure_set(v___x_122_, 7, v___f_121_);
lean_closure_set(v___x_122_, 8, v_inst_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad(lean_object* v_00_u03c4_123_, lean_object* v_00_u03b1_124_, lean_object* v_m_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lake_instComputeTraceListOfMonad___redArg(v_inst_126_, v_inst_127_, v_inst_128_, v_inst_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace___redArg(lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_as_136_){
_start:
{
lean_object* v_toApplicative_137_; lean_object* v_toBind_138_; lean_object* v_toPure_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_toApplicative_137_ = lean_ctor_get(v_inst_135_, 0);
v_toBind_138_ = lean_ctor_get(v_inst_135_, 1);
v_toPure_139_ = lean_ctor_get(v_toApplicative_137_, 1);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_array_get_size(v_as_136_);
v___x_142_ = lean_nat_dec_lt(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
lean_inc(v_toPure_139_);
lean_dec_ref(v_as_136_);
lean_dec_ref(v_inst_135_);
lean_dec(v_inst_134_);
lean_dec(v_inst_133_);
lean_dec(v_inst_131_);
v___x_143_ = lean_apply_2(v_toPure_139_, lean_box(0), v_inst_132_);
return v___x_143_;
}
else
{
lean_object* v___f_144_; size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; 
lean_inc(v_toBind_138_);
lean_inc(v_toPure_139_);
v___f_144_ = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(v___f_144_, 0, v_inst_131_);
lean_closure_set(v___f_144_, 1, v_toPure_139_);
lean_closure_set(v___f_144_, 2, v_inst_133_);
lean_closure_set(v___f_144_, 3, v_inst_134_);
lean_closure_set(v___f_144_, 4, v_toBind_138_);
v___x_145_ = ((size_t)0ULL);
v___x_146_ = lean_usize_of_nat(v___x_141_);
v___x_147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_135_, v___f_144_, v_as_136_, v___x_145_, v___x_146_, v_inst_132_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace(lean_object* v_00_u03c4_148_, lean_object* v_00_u03b1_149_, lean_object* v_m_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_n_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_as_157_){
_start:
{
lean_object* v_toApplicative_158_; lean_object* v_toBind_159_; lean_object* v_toPure_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_toApplicative_158_ = lean_ctor_get(v_inst_156_, 0);
v_toBind_159_ = lean_ctor_get(v_inst_156_, 1);
v_toPure_160_ = lean_ctor_get(v_toApplicative_158_, 1);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_array_get_size(v_as_157_);
v___x_163_ = lean_nat_dec_lt(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
lean_inc(v_toPure_160_);
lean_dec_ref(v_as_157_);
lean_dec_ref(v_inst_156_);
lean_dec(v_inst_155_);
lean_dec(v_inst_153_);
lean_dec(v_inst_151_);
v___x_164_ = lean_apply_2(v_toPure_160_, lean_box(0), v_inst_152_);
return v___x_164_;
}
else
{
lean_object* v___f_165_; size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; 
lean_inc(v_toBind_159_);
lean_inc(v_toPure_160_);
v___f_165_ = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(v___f_165_, 0, v_inst_151_);
lean_closure_set(v___f_165_, 1, v_toPure_160_);
lean_closure_set(v___f_165_, 2, v_inst_153_);
lean_closure_set(v___f_165_, 3, v_inst_155_);
lean_closure_set(v___f_165_, 4, v_toBind_159_);
v___x_166_ = ((size_t)0ULL);
v___x_167_ = lean_usize_of_nat(v___x_162_);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_156_, v___f_165_, v_as_157_, v___x_166_, v___x_167_, v_inst_152_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad___redArg(lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_inst_172_){
_start:
{
lean_object* v___f_173_; lean_object* v___x_174_; 
v___f_173_ = ((lean_object*)(l_Lake_instComputeTraceListOfMonad___redArg___closed__0));
v___x_174_ = lean_alloc_closure((void*)(l_Lake_computeArrayTrace), 10, 9);
lean_closure_set(v___x_174_, 0, lean_box(0));
lean_closure_set(v___x_174_, 1, lean_box(0));
lean_closure_set(v___x_174_, 2, lean_box(0));
lean_closure_set(v___x_174_, 3, v_inst_169_);
lean_closure_set(v___x_174_, 4, v_inst_170_);
lean_closure_set(v___x_174_, 5, v_inst_171_);
lean_closure_set(v___x_174_, 6, lean_box(0));
lean_closure_set(v___x_174_, 7, v___f_173_);
lean_closure_set(v___x_174_, 8, v_inst_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad(lean_object* v_00_u03c4_175_, lean_object* v_00_u03b1_176_, lean_object* v_m_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lake_instComputeTraceArrayOfMonad___redArg(v_inst_178_, v_inst_179_, v_inst_180_, v_inst_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprHash_repr_spec__0(lean_object* v_a_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_nat_to_int(v_a_183_);
return v___x_184_;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(7u);
v___x_199_ = lean_nat_to_int(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__0));
v___x_202_ = lean_string_length(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_obj_once(&l_Lake_instReprHash_repr___redArg___closed__9, &l_Lake_instReprHash_repr___redArg___closed__9_once, _init_l_Lake_instReprHash_repr___redArg___closed__9);
v___x_204_ = lean_nat_to_int(v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___redArg(uint64_t v_x_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_210_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__6));
v___x_211_ = lean_obj_once(&l_Lake_instReprHash_repr___redArg___closed__7, &l_Lake_instReprHash_repr___redArg___closed__7_once, _init_l_Lake_instReprHash_repr___redArg___closed__7);
v___x_212_ = lean_uint64_to_nat(v_x_209_);
v___x_213_ = l_Nat_reprFast(v___x_212_);
v___x_214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
v___x_215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_211_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = 0;
v___x_217_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*1, v___x_216_);
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_210_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = lean_obj_once(&l_Lake_instReprHash_repr___redArg___closed__10, &l_Lake_instReprHash_repr___redArg___closed__10_once, _init_l_Lake_instReprHash_repr___redArg___closed__10);
v___x_220_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__11));
v___x_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_218_);
v___x_222_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__12));
v___x_223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_219_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_216_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___redArg___boxed(lean_object* v_x_226_){
_start:
{
uint64_t v_x_147__boxed_227_; lean_object* v_res_228_; 
v_x_147__boxed_227_ = lean_unbox_uint64(v_x_226_);
lean_dec_ref(v_x_226_);
v_res_228_ = l_Lake_instReprHash_repr___redArg(v_x_147__boxed_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr(uint64_t v_x_229_, lean_object* v_prec_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lake_instReprHash_repr___redArg(v_x_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___boxed(lean_object* v_x_232_, lean_object* v_prec_233_){
_start:
{
uint64_t v_x_206__boxed_234_; lean_object* v_res_235_; 
v_x_206__boxed_234_ = lean_unbox_uint64(v_x_232_);
lean_dec_ref(v_x_232_);
v_res_235_ = l_Lake_instReprHash_repr(v_x_206__boxed_234_, v_prec_233_);
lean_dec(v_prec_233_);
return v_res_235_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqHash_decEq(uint64_t v_x_238_, uint64_t v_x_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = lean_uint64_dec_eq(v_x_238_, v_x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash_decEq___boxed(lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
uint64_t v_x_31__boxed_243_; uint64_t v_x_32__boxed_244_; uint8_t v_res_245_; lean_object* v_r_246_; 
v_x_31__boxed_243_ = lean_unbox_uint64(v_x_241_);
lean_dec_ref(v_x_241_);
v_x_32__boxed_244_ = lean_unbox_uint64(v_x_242_);
lean_dec_ref(v_x_242_);
v_res_245_ = l_Lake_instDecidableEqHash_decEq(v_x_31__boxed_243_, v_x_32__boxed_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqHash(uint64_t v_x_247_, uint64_t v_x_248_){
_start:
{
uint8_t v___x_249_; 
v___x_249_ = lean_uint64_dec_eq(v_x_247_, v_x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash___boxed(lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
uint64_t v_x_6__boxed_252_; uint64_t v_x_7__boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v_x_6__boxed_252_ = lean_unbox_uint64(v_x_250_);
lean_dec_ref(v_x_250_);
v_x_7__boxed_253_ = lean_unbox_uint64(v_x_251_);
lean_dec_ref(v_x_251_);
v_res_254_ = l_Lake_instDecidableEqHash(v_x_6__boxed_252_, v_x_7__boxed_253_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_instHashable___lam__0(uint64_t v_self_256_){
_start:
{
return v_self_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_instHashable___lam__0___boxed(lean_object* v_self_257_){
_start:
{
uint64_t v_self_boxed_258_; uint64_t v_res_259_; lean_object* v_r_260_; 
v_self_boxed_258_ = lean_unbox_uint64(v_self_257_);
lean_dec_ref(v_self_257_);
v_res_259_ = l_Lake_Hash_instHashable___lam__0(v_self_boxed_258_);
v_r_260_ = lean_box_uint64(v_res_259_);
return v_r_260_;
}
}
static uint64_t _init_l_Lake_Hash_nil(void){
_start:
{
uint64_t v___x_263_; 
v___x_263_ = 1723ULL;
return v___x_263_;
}
}
static uint64_t _init_l_Lake_Hash_instNilTrace(void){
_start:
{
uint64_t v___x_264_; 
v___x_264_ = 1723ULL;
return v___x_264_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofNat(lean_object* v_n_265_){
_start:
{
uint64_t v___x_266_; 
v___x_266_ = lean_uint64_of_nat(v_n_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofNat___boxed(lean_object* v_n_267_){
_start:
{
uint64_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Lake_Hash_ofNat(v_n_267_);
lean_dec(v_n_267_);
v_r_269_ = lean_box_uint64(v_res_268_);
return v_r_269_;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_nat_to_int(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__3(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_cstr_to_nat("18446744073709551616");
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object* v_n_279_){
_start:
{
lean_object* v_mantissa_282_; lean_object* v_exponent_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_mantissa_282_ = lean_ctor_get(v_n_279_, 0);
v_exponent_283_ = lean_ctor_get(v_n_279_, 1);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_nat_dec_eq(v_exponent_283_, v___x_284_);
if (v___x_285_ == 0)
{
goto v___jp_280_;
}
else
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__2, &l_Lake_Hash_ofJsonNumber_x3f___closed__2_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2);
v___x_287_ = lean_int_dec_le(v___x_286_, v_mantissa_282_);
if (v___x_287_ == 0)
{
goto v___jp_280_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = l_Int_toNat(v_mantissa_282_);
v___x_289_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__3, &l_Lake_Hash_ofJsonNumber_x3f___closed__3_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__3);
v___x_290_ = lean_nat_dec_lt(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
lean_dec(v___x_288_);
v___x_291_ = ((lean_object*)(l_Lake_Hash_ofJsonNumber_x3f___closed__5));
return v___x_291_;
}
else
{
uint64_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_uint64_of_nat(v___x_288_);
lean_dec(v___x_288_);
v___x_293_ = lean_box_uint64(v___x_292_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
v___jp_280_:
{
lean_object* v___x_281_; 
v___x_281_ = ((lean_object*)(l_Lake_Hash_ofJsonNumber_x3f___closed__1));
return v___x_281_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f___boxed(lean_object* v_n_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_295_);
lean_dec_ref(v_n_295_);
return v_res_296_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(lean_object* v_s_297_, lean_object* v_n_298_, lean_object* v_j_299_, uint64_t v_a_300_){
_start:
{
lean_object* v_zero_301_; uint8_t v_isZero_302_; 
v_zero_301_ = lean_unsigned_to_nat(0u);
v_isZero_302_ = lean_nat_dec_eq(v_j_299_, v_zero_301_);
if (v_isZero_302_ == 1)
{
lean_dec(v_j_299_);
return v_a_300_;
}
else
{
lean_object* v_one_303_; lean_object* v_n_304_; lean_object* v___x_305_; uint8_t v_c_306_; uint8_t v___x_307_; uint8_t v___x_308_; 
v_one_303_ = lean_unsigned_to_nat(1u);
v_n_304_ = lean_nat_sub(v_j_299_, v_one_303_);
v___x_305_ = lean_nat_sub(v_n_298_, v_j_299_);
lean_dec(v_j_299_);
v_c_306_ = lean_string_get_byte_fast(v_s_297_, v___x_305_);
v___x_307_ = 57;
v___x_308_ = lean_uint8_dec_le(v_c_306_, v___x_307_);
if (v___x_308_ == 0)
{
uint8_t v___x_309_; uint8_t v___x_310_; 
v___x_309_ = 97;
v___x_310_ = lean_uint8_dec_le(v___x_309_, v_c_306_);
if (v___x_310_ == 0)
{
uint64_t v___x_311_; uint64_t v___x_312_; uint8_t v___x_313_; uint8_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; 
v___x_311_ = 4ULL;
v___x_312_ = lean_uint64_shift_left(v_a_300_, v___x_311_);
v___x_313_ = 55;
v___x_314_ = lean_uint8_sub(v_c_306_, v___x_313_);
v___x_315_ = lean_uint8_to_uint64(v___x_314_);
v___x_316_ = lean_uint64_add(v___x_312_, v___x_315_);
v_j_299_ = v_n_304_;
v_a_300_ = v___x_316_;
goto _start;
}
else
{
uint64_t v___x_318_; uint64_t v___x_319_; uint8_t v___x_320_; uint8_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; 
v___x_318_ = 4ULL;
v___x_319_ = lean_uint64_shift_left(v_a_300_, v___x_318_);
v___x_320_ = 87;
v___x_321_ = lean_uint8_sub(v_c_306_, v___x_320_);
v___x_322_ = lean_uint8_to_uint64(v___x_321_);
v___x_323_ = lean_uint64_add(v___x_319_, v___x_322_);
v_j_299_ = v_n_304_;
v_a_300_ = v___x_323_;
goto _start;
}
}
else
{
uint64_t v___x_325_; uint64_t v___x_326_; uint8_t v___x_327_; uint8_t v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; 
v___x_325_ = 4ULL;
v___x_326_ = lean_uint64_shift_left(v_a_300_, v___x_325_);
v___x_327_ = 48;
v___x_328_ = lean_uint8_sub(v_c_306_, v___x_327_);
v___x_329_ = lean_uint8_to_uint64(v___x_328_);
v___x_330_ = lean_uint64_add(v___x_326_, v___x_329_);
v_j_299_ = v_n_304_;
v_a_300_ = v___x_330_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg___boxed(lean_object* v_s_332_, lean_object* v_n_333_, lean_object* v_j_334_, lean_object* v_a_335_){
_start:
{
uint64_t v_a_246__boxed_336_; uint64_t v_res_337_; lean_object* v_r_338_; 
v_a_246__boxed_336_ = lean_unbox_uint64(v_a_335_);
lean_dec_ref(v_a_335_);
v_res_337_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_332_, v_n_333_, v_j_334_, v_a_246__boxed_336_);
lean_dec(v_n_333_);
lean_dec_ref(v_s_332_);
v_r_338_ = lean_box_uint64(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofHex(lean_object* v_s_339_){
_start:
{
lean_object* v___x_340_; uint64_t v___x_341_; uint64_t v___x_342_; 
v___x_340_ = lean_string_utf8_byte_size(v_s_339_);
v___x_341_ = 0ULL;
v___x_342_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_339_, v___x_340_, v___x_340_, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex___boxed(lean_object* v_s_343_){
_start:
{
uint64_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Lake_Hash_ofHex(v_s_343_);
lean_dec_ref(v_s_343_);
v_r_345_ = lean_box_uint64(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(lean_object* v_s_346_, lean_object* v_n_347_, lean_object* v_j_348_, lean_object* v_a_349_, uint64_t v_a_350_){
_start:
{
uint64_t v___x_351_; 
v___x_351_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_346_, v_n_347_, v_j_348_, v_a_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___boxed(lean_object* v_s_352_, lean_object* v_n_353_, lean_object* v_j_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
uint64_t v_a_310__boxed_357_; uint64_t v_res_358_; lean_object* v_r_359_; 
v_a_310__boxed_357_ = lean_unbox_uint64(v_a_356_);
lean_dec_ref(v_a_356_);
v_res_358_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(v_s_352_, v_n_353_, v_j_354_, v_a_355_, v_a_310__boxed_357_);
lean_dec(v_n_353_);
lean_dec_ref(v_s_352_);
v_r_359_ = lean_box_uint64(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f(lean_object* v_s_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_361_ = lean_string_utf8_byte_size(v_s_360_);
v___x_362_ = lean_unsigned_to_nat(16u);
v___x_363_ = lean_nat_dec_eq(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_box(0);
return v___x_364_;
}
else
{
uint8_t v___x_365_; 
v___x_365_ = l_Lake_isHex(v_s_360_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
v___x_366_ = lean_box(0);
return v___x_366_;
}
else
{
uint64_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = l_Lake_Hash_ofHex(v_s_360_);
v___x_368_ = lean_box_uint64(v___x_367_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f___boxed(lean_object* v_s_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lake_Hash_ofHex_x3f(v_s_370_);
lean_dec_ref(v_s_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_hex(uint64_t v_self_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lake_lowerHexUInt64(v_self_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_hex___boxed(lean_object* v_self_374_){
_start:
{
uint64_t v_self_boxed_375_; lean_object* v_res_376_; 
v_self_boxed_375_ = lean_unbox_uint64(v_self_374_);
lean_dec_ref(v_self_374_);
v_res_376_ = l_Lake_Hash_hex(v_self_boxed_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofDecimal_x3f(lean_object* v_s_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_string_utf8_byte_size(v_s_377_);
v___x_380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_380_, 0, v_s_377_);
lean_ctor_set(v___x_380_, 1, v___x_378_);
lean_ctor_set(v___x_380_, 2, v___x_379_);
v___x_381_ = l_String_Slice_toNat_x3f(v___x_380_);
lean_dec_ref_known(v___x_380_, 3);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v___x_382_; 
v___x_382_ = lean_box(0);
return v___x_382_;
}
else
{
lean_object* v_val_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_392_; 
v_val_383_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_392_ == 0)
{
v___x_385_ = v___x_381_;
v_isShared_386_ = v_isSharedCheck_392_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_val_383_);
lean_dec(v___x_381_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_392_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
uint64_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_387_ = lean_uint64_of_nat(v_val_383_);
lean_dec(v_val_383_);
v___x_388_ = lean_box_uint64(v___x_387_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_388_);
v___x_390_ = v___x_385_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f(lean_object* v_s_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lake_Hash_ofHex_x3f(v_s_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f___boxed(lean_object* v_s_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lake_Hash_ofString_x3f(v_s_395_);
lean_dec_ref(v_s_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f(lean_object* v_hashFile_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_IO_FS_readFile(v_hashFile_397_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_401_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 1);
v___x_401_ = l_Lake_Hash_ofHex_x3f(v_a_400_);
lean_dec(v_a_400_);
return v___x_401_;
}
else
{
lean_object* v___x_402_; 
lean_dec_ref_known(v___x_399_, 1);
v___x_402_ = lean_box(0);
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f___boxed(lean_object* v_hashFile_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lake_Hash_load_x3f(v_hashFile_403_);
lean_dec_ref(v_hashFile_403_);
return v_res_405_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_mix(uint64_t v_h1_406_, uint64_t v_h2_407_){
_start:
{
uint64_t v___x_408_; 
v___x_408_ = lean_uint64_mix_hash(v_h1_406_, v_h2_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_mix___boxed(lean_object* v_h1_409_, lean_object* v_h2_410_){
_start:
{
uint64_t v_h1_boxed_411_; uint64_t v_h2_boxed_412_; uint64_t v_res_413_; lean_object* v_r_414_; 
v_h1_boxed_411_ = lean_unbox_uint64(v_h1_409_);
lean_dec_ref(v_h1_409_);
v_h2_boxed_412_ = lean_unbox_uint64(v_h2_410_);
lean_dec_ref(v_h2_410_);
v_res_413_ = l_Lake_Hash_mix(v_h1_boxed_411_, v_h2_boxed_412_);
v_r_414_ = lean_box_uint64(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toString(uint64_t v_self_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lake_lowerHexUInt64(v_self_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toString___boxed(lean_object* v_self_419_){
_start:
{
uint64_t v_self_boxed_420_; lean_object* v_res_421_; 
v_self_boxed_420_ = lean_unbox_uint64(v_self_419_);
lean_dec_ref(v_self_419_);
v_res_421_ = l_Lake_Hash_toString(v_self_boxed_420_);
return v_res_421_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofHashable___redArg(lean_object* v_inst_424_, lean_object* v_a_425_){
_start:
{
uint64_t v___x_426_; lean_object* v___x_427_; uint64_t v___x_428_; uint64_t v___x_429_; 
v___x_426_ = 1723ULL;
v___x_427_ = lean_apply_1(v_inst_424_, v_a_425_);
v___x_428_ = lean_unbox_uint64(v___x_427_);
lean_dec_ref(v___x_427_);
v___x_429_ = lean_uint64_mix_hash(v___x_426_, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHashable___redArg___boxed(lean_object* v_inst_430_, lean_object* v_a_431_){
_start:
{
uint64_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Lake_Hash_ofHashable___redArg(v_inst_430_, v_a_431_);
v_r_433_ = lean_box_uint64(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofHashable(lean_object* v_00_u03b1_434_, lean_object* v_inst_435_, lean_object* v_a_436_){
_start:
{
uint64_t v___x_437_; lean_object* v___x_438_; uint64_t v___x_439_; uint64_t v___x_440_; 
v___x_437_ = 1723ULL;
v___x_438_ = lean_apply_1(v_inst_435_, v_a_436_);
v___x_439_ = lean_unbox_uint64(v___x_438_);
lean_dec_ref(v___x_438_);
v___x_440_ = lean_uint64_mix_hash(v___x_437_, v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHashable___boxed(lean_object* v_00_u03b1_441_, lean_object* v_inst_442_, lean_object* v_a_443_){
_start:
{
uint64_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Lake_Hash_ofHashable(v_00_u03b1_441_, v_inst_442_, v_a_443_);
v_r_445_ = lean_box_uint64(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofString(lean_object* v_str_446_){
_start:
{
uint64_t v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; 
v___x_447_ = 1723ULL;
v___x_448_ = lean_string_hash(v_str_446_);
v___x_449_ = lean_uint64_mix_hash(v___x_447_, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString___boxed(lean_object* v_str_450_){
_start:
{
uint64_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l_Lake_Hash_ofString(v_str_450_);
lean_dec_ref(v_str_450_);
v_r_452_ = lean_box_uint64(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofText(lean_object* v_str_453_){
_start:
{
lean_object* v___x_454_; uint64_t v___x_455_; uint64_t v___x_456_; uint64_t v___x_457_; 
v___x_454_ = l_String_crlfToLf(v_str_453_);
v___x_455_ = 1723ULL;
v___x_456_ = lean_string_hash(v___x_454_);
lean_dec_ref(v___x_454_);
v___x_457_ = lean_uint64_mix_hash(v___x_455_, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofText___boxed(lean_object* v_str_458_){
_start:
{
uint64_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_Lake_Hash_ofText(v_str_458_);
lean_dec_ref(v_str_458_);
v_r_460_ = lean_box_uint64(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofByteArray(lean_object* v_bytes_461_){
_start:
{
uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v___x_464_; 
v___x_462_ = 1723ULL;
v___x_463_ = lean_byte_array_hash(v_bytes_461_);
v___x_464_ = lean_uint64_mix_hash(v___x_462_, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofByteArray___boxed(lean_object* v_bytes_465_){
_start:
{
uint64_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Lake_Hash_ofByteArray(v_bytes_465_);
lean_dec_ref(v_bytes_465_);
v_r_467_ = lean_box_uint64(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofBool(uint8_t v_b_468_){
_start:
{
if (v_b_468_ == 0)
{
uint64_t v___x_469_; 
v___x_469_ = 18370132993254720638ULL;
return v___x_469_;
}
else
{
uint64_t v___x_470_; 
v___x_470_ = 8507242618548079515ULL;
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofBool___boxed(lean_object* v_b_471_){
_start:
{
uint8_t v_b_boxed_472_; uint64_t v_res_473_; lean_object* v_r_474_; 
v_b_boxed_472_ = lean_unbox(v_b_471_);
v_res_473_ = l_Lake_Hash_ofBool(v_b_boxed_472_);
v_r_474_ = lean_box_uint64(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson(uint64_t v_self_475_){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = l_Lake_lowerHexUInt64(v_self_475_);
v___x_477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson___boxed(lean_object* v_self_478_){
_start:
{
uint64_t v_self_boxed_479_; lean_object* v_res_480_; 
v_self_boxed_479_ = lean_unbox_uint64(v_self_478_);
lean_dec_ref(v_self_478_);
v_res_480_ = l_Lake_Hash_toJson(v_self_boxed_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_fromJson_x3f(lean_object* v_json_493_){
_start:
{
switch(lean_obj_tag(v_json_493_))
{
case 3:
{
lean_object* v_s_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_509_; 
v_s_494_ = lean_ctor_get(v_json_493_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_json_493_);
if (v_isSharedCheck_509_ == 0)
{
v___x_496_ = v_json_493_;
v_isShared_497_ = v_isSharedCheck_509_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_s_494_);
lean_dec(v_json_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_509_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
uint8_t v___x_498_; 
v___x_498_ = l_Lake_isHex(v_s_494_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_del_object(v___x_496_);
lean_dec_ref(v_s_494_);
v___x_499_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__1));
return v___x_499_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_500_ = lean_string_utf8_byte_size(v_s_494_);
v___x_501_ = lean_unsigned_to_nat(16u);
v___x_502_ = lean_nat_dec_eq(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_del_object(v___x_496_);
lean_dec_ref(v_s_494_);
v___x_503_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__3));
return v___x_503_;
}
else
{
uint64_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_504_ = l_Lake_Hash_ofHex(v_s_494_);
lean_dec_ref(v_s_494_);
v___x_505_ = lean_box_uint64(v___x_504_);
if (v_isShared_497_ == 0)
{
lean_ctor_set_tag(v___x_496_, 1);
lean_ctor_set(v___x_496_, 0, v___x_505_);
v___x_507_ = v___x_496_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
case 2:
{
lean_object* v_n_510_; lean_object* v___x_511_; 
v_n_510_ = lean_ctor_get(v_json_493_, 0);
lean_inc_ref(v_n_510_);
lean_dec_ref_known(v_json_493_, 1);
v___x_511_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_510_);
lean_dec_ref(v_n_510_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_521_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_521_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_516_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__4));
v___x_517_ = lean_string_append(v___x_516_, v_a_512_);
lean_dec(v_a_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_517_);
v___x_519_ = v___x_514_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
return v___x_511_;
}
}
default: 
{
lean_object* v___x_522_; 
lean_dec(v_json_493_);
v___x_522_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__6));
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg(lean_object* v_inst_525_){
_start:
{
lean_inc(v_inst_525_);
return v_inst_525_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg___boxed(lean_object* v_inst_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lake_instComputeTraceHashOfComputeHash___redArg(v_inst_526_);
lean_dec(v_inst_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash(lean_object* v_00_u03b1_528_, lean_object* v_m_529_, lean_object* v_inst_530_){
_start:
{
lean_inc(v_inst_530_);
return v_inst_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___boxed(lean_object* v_00_u03b1_531_, lean_object* v_m_532_, lean_object* v_inst_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lake_instComputeTraceHashOfComputeHash(v_00_u03b1_531_, v_m_532_, v_inst_533_);
lean_dec(v_inst_533_);
return v_res_534_;
}
}
LEAN_EXPORT uint64_t l_Lake_pureHash___redArg(lean_object* v_inst_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_537_; uint64_t v___x_538_; 
v___x_537_ = lean_apply_1(v_inst_535_, v_a_536_);
v___x_538_ = lean_unbox_uint64(v___x_537_);
lean_dec_ref(v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_pureHash___redArg___boxed(lean_object* v_inst_539_, lean_object* v_a_540_){
_start:
{
uint64_t v_res_541_; lean_object* v_r_542_; 
v_res_541_ = l_Lake_pureHash___redArg(v_inst_539_, v_a_540_);
v_r_542_ = lean_box_uint64(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT uint64_t l_Lake_pureHash(lean_object* v_00_u03b1_543_, lean_object* v_inst_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_546_; uint64_t v___x_547_; 
v___x_546_ = lean_apply_1(v_inst_544_, v_a_545_);
v___x_547_ = lean_unbox_uint64(v___x_546_);
lean_dec_ref(v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_pureHash___boxed(lean_object* v_00_u03b1_548_, lean_object* v_inst_549_, lean_object* v_a_550_){
_start:
{
uint64_t v_res_551_; lean_object* v_r_552_; 
v_res_551_ = l_Lake_pureHash(v_00_u03b1_548_, v_inst_549_, v_a_550_);
v_r_552_ = lean_box_uint64(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash___redArg(lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_apply_1(v_inst_553_, v_a_555_);
v___x_557_ = lean_apply_2(v_inst_554_, lean_box(0), v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash(lean_object* v_00_u03b1_558_, lean_object* v_m_559_, lean_object* v_n_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_apply_1(v_inst_561_, v_a_563_);
v___x_565_ = lean_apply_2(v_inst_562_, lean_box(0), v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashIdOfHashable___redArg(lean_object* v_inst_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_alloc_closure((void*)(l_Lake_Hash_ofHashable___boxed), 3, 2);
lean_closure_set(v___x_567_, 0, lean_box(0));
lean_closure_set(v___x_567_, 1, v_inst_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashIdOfHashable(lean_object* v_00_u03b1_568_, lean_object* v_inst_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = lean_alloc_closure((void*)(l_Lake_Hash_ofHashable___boxed), 3, 2);
lean_closure_set(v___x_570_, 0, lean_box(0));
lean_closure_set(v___x_570_, 1, v_inst_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash(lean_object* v_file_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_IO_FS_readBinFile(v_file_571_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_585_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_585_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
uint64_t v___x_578_; uint64_t v___x_579_; uint64_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_578_ = 1723ULL;
v___x_579_ = lean_byte_array_hash(v_a_574_);
lean_dec(v_a_574_);
v___x_580_ = lean_uint64_mix_hash(v___x_578_, v___x_579_);
v___x_581_ = lean_box_uint64(v___x_580_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_581_);
v___x_583_ = v___x_576_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_a_586_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_573_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_573_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash___boxed(lean_object* v_file_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lake_computeBinFileHash(v_file_594_);
lean_dec_ref(v_file_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash(lean_object* v_file_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_IO_FS_readFile(v_file_599_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_614_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_614_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_614_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_614_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; uint64_t v___x_607_; uint64_t v___x_608_; uint64_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_606_ = l_String_crlfToLf(v_a_602_);
lean_dec(v_a_602_);
v___x_607_ = 1723ULL;
v___x_608_ = lean_string_hash(v___x_606_);
lean_dec_ref(v___x_606_);
v___x_609_ = lean_uint64_mix_hash(v___x_607_, v___x_608_);
v___x_610_ = lean_box_uint64(v___x_609_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_610_);
v___x_612_ = v___x_604_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_a_615_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_601_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_601_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash___boxed(lean_object* v_file_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lake_computeTextFileHash(v_file_623_);
lean_dec_ref(v_file_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0(lean_object* v_x_626_){
_start:
{
lean_inc_ref(v_x_626_);
return v_x_626_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0___boxed(lean_object* v_x_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lake_instCoeTextFilePathFilePath___lam__0(v_x_627_);
lean_dec_ref(v_x_627_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash(lean_object* v_file_634_, uint8_t v_text_635_){
_start:
{
if (v_text_635_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = l_Lake_computeBinFileHash(v_file_634_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = l_Lake_computeTextFileHash(v_file_634_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash___boxed(lean_object* v_file_639_, lean_object* v_text_640_, lean_object* v_a_641_){
_start:
{
uint8_t v_text_boxed_642_; lean_object* v_res_643_; 
v_text_boxed_642_ = lean_unbox(v_text_640_);
v_res_643_ = l_Lake_computeFileHash(v_file_639_, v_text_boxed_642_);
lean_dec_ref(v_file_639_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0(uint64_t v_ts_644_, lean_object* v_toPure_645_, uint64_t v_____do__lift_646_){
_start:
{
uint64_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_uint64_mix_hash(v_ts_644_, v_____do__lift_646_);
v___x_648_ = lean_box_uint64(v___x_647_);
v___x_649_ = lean_apply_2(v_toPure_645_, lean_box(0), v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0___boxed(lean_object* v_ts_650_, lean_object* v_toPure_651_, lean_object* v_____do__lift_652_){
_start:
{
uint64_t v_ts_boxed_653_; uint64_t v_____do__lift_88__boxed_654_; lean_object* v_res_655_; 
v_ts_boxed_653_ = lean_unbox_uint64(v_ts_650_);
lean_dec_ref(v_ts_650_);
v_____do__lift_88__boxed_654_ = lean_unbox_uint64(v_____do__lift_652_);
lean_dec_ref(v_____do__lift_652_);
v_res_655_ = l_Lake_computeArrayHash___redArg___lam__0(v_ts_boxed_653_, v_toPure_651_, v_____do__lift_88__boxed_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1(lean_object* v_toPure_656_, lean_object* v_inst_657_, lean_object* v_toBind_658_, uint64_t v_ts_659_, lean_object* v_t_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___f_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_661_ = lean_box_uint64(v_ts_659_);
v___f_662_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_662_, 0, v___x_661_);
lean_closure_set(v___f_662_, 1, v_toPure_656_);
v___x_663_ = lean_apply_1(v_inst_657_, v_t_660_);
v___x_664_ = lean_apply_4(v_toBind_658_, lean_box(0), lean_box(0), v___x_663_, v___f_662_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1___boxed(lean_object* v_toPure_665_, lean_object* v_inst_666_, lean_object* v_toBind_667_, lean_object* v_ts_668_, lean_object* v_t_669_){
_start:
{
uint64_t v_ts_boxed_670_; lean_object* v_res_671_; 
v_ts_boxed_670_ = lean_unbox_uint64(v_ts_668_);
lean_dec_ref(v_ts_668_);
v_res_671_ = l_Lake_computeArrayHash___redArg___lam__1(v_toPure_665_, v_inst_666_, v_toBind_667_, v_ts_boxed_670_, v_t_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg(lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_as_676_){
_start:
{
lean_object* v_toApplicative_677_; lean_object* v_toBind_678_; lean_object* v_toPure_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_toApplicative_677_ = lean_ctor_get(v_inst_675_, 0);
v_toBind_678_ = lean_ctor_get(v_inst_675_, 1);
v_toPure_679_ = lean_ctor_get(v_toApplicative_677_, 1);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_array_get_size(v_as_676_);
v___x_682_ = lean_nat_dec_lt(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_inc(v_toPure_679_);
lean_dec_ref(v_as_676_);
lean_dec_ref(v_inst_675_);
lean_dec(v_inst_674_);
v___x_683_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_684_ = lean_apply_2(v_toPure_679_, lean_box(0), v___x_683_);
return v___x_684_;
}
else
{
lean_object* v___f_685_; size_t v___x_686_; size_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
lean_inc(v_toBind_678_);
lean_inc(v_toPure_679_);
v___f_685_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_685_, 0, v_toPure_679_);
lean_closure_set(v___f_685_, 1, v_inst_674_);
lean_closure_set(v___f_685_, 2, v_toBind_678_);
v___x_686_ = ((size_t)0ULL);
v___x_687_ = lean_usize_of_nat(v___x_681_);
v___x_688_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_675_, v___f_685_, v_as_676_, v___x_686_, v___x_687_, v___x_688_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash(lean_object* v_00_u03b1_690_, lean_object* v_m_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_as_694_){
_start:
{
lean_object* v_toApplicative_695_; lean_object* v_toBind_696_; lean_object* v_toPure_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_toApplicative_695_ = lean_ctor_get(v_inst_693_, 0);
v_toBind_696_ = lean_ctor_get(v_inst_693_, 1);
v_toPure_697_ = lean_ctor_get(v_toApplicative_695_, 1);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_array_get_size(v_as_694_);
v___x_700_ = lean_nat_dec_lt(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; 
lean_inc(v_toPure_697_);
lean_dec_ref(v_as_694_);
lean_dec_ref(v_inst_693_);
lean_dec(v_inst_692_);
v___x_701_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_702_ = lean_apply_2(v_toPure_697_, lean_box(0), v___x_701_);
return v___x_702_;
}
else
{
lean_object* v___f_703_; size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_inc(v_toBind_696_);
lean_inc(v_toPure_697_);
v___f_703_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_703_, 0, v_toPure_697_);
lean_closure_set(v___f_703_, 1, v_inst_692_);
lean_closure_set(v___f_703_, 2, v_toBind_696_);
v___x_704_ = ((size_t)0ULL);
v___x_705_ = lean_usize_of_nat(v___x_699_);
v___x_706_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_693_, v___f_703_, v_as_694_, v___x_704_, v___x_705_, v___x_706_);
return v___x_707_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad___redArg(lean_object* v_inst_708_, lean_object* v_inst_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash), 5, 4);
lean_closure_set(v___x_710_, 0, lean_box(0));
lean_closure_set(v___x_710_, 1, lean_box(0));
lean_closure_set(v___x_710_, 2, v_inst_708_);
lean_closure_set(v___x_710_, 3, v_inst_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad(lean_object* v_00_u03b1_711_, lean_object* v_m_712_, lean_object* v_inst_713_, lean_object* v_inst_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash), 5, 4);
lean_closure_set(v___x_715_, 0, lean_box(0));
lean_closure_set(v___x_715_, 1, lean_box(0));
lean_closure_set(v___x_715_, 2, v_inst_713_);
lean_closure_set(v___x_715_, 3, v_inst_714_);
return v___x_715_;
}
}
static lean_object* _init_l_Lake_MTime_instOfNat___closed__0(void){
_start:
{
uint32_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = 0;
v___x_717_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__2, &l_Lake_Hash_ofJsonNumber_x3f___closed__2_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2);
v___x_718_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set_uint32(v___x_718_, sizeof(void*)*1, v___x_716_);
return v___x_718_;
}
}
static lean_object* _init_l_Lake_MTime_instOfNat(void){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
return v___x_719_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_instBEq___aux__1(lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = l_IO_FS_instBEqSystemTime_beq(v_x_720_, v_x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instBEq___aux__1___boxed(lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l_Lake_MTime_instBEq___aux__1(v_x_723_, v_x_724_);
lean_dec_ref(v_x_724_);
lean_dec_ref(v_x_723_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___redArg(lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___redArg___boxed(lean_object* v_x_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lake_MTime_instRepr___aux__1___redArg(v_x_731_);
lean_dec_ref(v_x_731_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1(lean_object* v_x_733_, lean_object* v_prec_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___boxed(lean_object* v_x_736_, lean_object* v_prec_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lake_MTime_instRepr___aux__1(v_x_736_, v_prec_737_);
lean_dec(v_prec_737_);
lean_dec_ref(v_x_736_);
return v_res_738_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_instOrd___aux__1(lean_object* v_x_741_, lean_object* v_x_742_){
_start:
{
uint8_t v___x_743_; 
v___x_743_ = l_IO_FS_instOrdSystemTime_ord(v_x_741_, v_x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instOrd___aux__1___boxed(lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
uint8_t v_res_746_; lean_object* v_r_747_; 
v_res_746_ = l_Lake_MTime_instOrd___aux__1(v_x_744_, v_x_745_);
lean_dec_ref(v_x_745_);
lean_dec_ref(v_x_744_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
static lean_object* _init_l_Lake_MTime_instLT(void){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_box(0);
return v___x_750_;
}
}
static lean_object* _init_l_Lake_MTime_instLE(void){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lean_box(0);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0(lean_object* v_x_752_, lean_object* v_y_753_){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = l_IO_FS_instOrdSystemTime_ord(v_x_752_, v_y_753_);
if (v___x_754_ == 2)
{
lean_inc_ref(v_y_753_);
return v_y_753_;
}
else
{
lean_inc_ref(v_x_752_);
return v_x_752_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0___boxed(lean_object* v_x_755_, lean_object* v_y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lake_MTime_instMin___lam__0(v_x_755_, v_y_756_);
lean_dec_ref(v_y_756_);
lean_dec_ref(v_x_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0(lean_object* v_x_760_, lean_object* v_y_761_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = l_IO_FS_instOrdSystemTime_ord(v_x_760_, v_y_761_);
if (v___x_762_ == 2)
{
lean_inc_ref(v_x_760_);
return v_x_760_;
}
else
{
lean_inc_ref(v_y_761_);
return v_y_761_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0___boxed(lean_object* v_x_763_, lean_object* v_y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lake_MTime_instMax___lam__0(v_x_763_, v_y_764_);
lean_dec_ref(v_y_764_);
lean_dec_ref(v_x_763_);
return v_res_765_;
}
}
static lean_object* _init_l_Lake_MTime_instNilTrace(void){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(lean_object* v_inst_770_){
_start:
{
lean_inc_ref(v_inst_770_);
return v_inst_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(lean_object* v_inst_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(v_inst_771_);
lean_dec_ref(v_inst_771_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(lean_object* v_00_u03b1_773_, lean_object* v_inst_774_){
_start:
{
lean_inc_ref(v_inst_774_);
return v_inst_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___boxed(lean_object* v_00_u03b1_775_, lean_object* v_inst_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(v_00_u03b1_775_, v_inst_776_);
lean_dec_ref(v_inst_776_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime(lean_object* v_file_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = lean_io_metadata(v_file_778_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_789_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_789_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_modified_785_; lean_object* v___x_787_; 
v_modified_785_ = lean_ctor_get(v_a_781_, 1);
lean_inc_ref(v_modified_785_);
lean_dec(v_a_781_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v_modified_785_);
v___x_787_ = v___x_783_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_modified_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_a_790_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_780_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_780_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime___boxed(lean_object* v_file_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lake_getFileMTime(v_file_798_);
lean_dec_ref(v_file_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0(lean_object* v_x_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = lean_io_metadata(v_x_803_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_814_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_modified_810_; lean_object* v___x_812_; 
v_modified_810_ = lean_ctor_get(v_a_806_, 1);
lean_inc_ref(v_modified_810_);
lean_dec(v_a_806_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v_modified_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_modified_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
v_a_815_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_805_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_805_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0___boxed(lean_object* v_x_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lake_instGetMTimeTextFilePath___lam__0(v_x_823_);
lean_dec_ref(v_x_823_);
return v_res_825_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object* v_inst_828_, lean_object* v_info_829_, lean_object* v_self_830_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = lean_apply_2(v_inst_828_, v_info_829_, lean_box(0));
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; uint8_t v___x_834_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = l_IO_FS_instOrdSystemTime_ord(v_self_830_, v_a_833_);
lean_dec(v_a_833_);
if (v___x_834_ == 0)
{
uint8_t v___x_835_; 
v___x_835_ = 1;
return v___x_835_;
}
else
{
uint8_t v___x_836_; 
v___x_836_ = 0;
return v___x_836_;
}
}
else
{
uint8_t v___x_837_; 
lean_dec_ref_known(v___x_832_, 1);
v___x_837_ = 0;
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___redArg___boxed(lean_object* v_inst_838_, lean_object* v_info_839_, lean_object* v_self_840_, lean_object* v_a_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_838_, v_info_839_, v_self_840_);
lean_dec_ref(v_self_840_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate(lean_object* v_i_844_, lean_object* v_inst_845_, lean_object* v_info_846_, lean_object* v_self_847_){
_start:
{
uint8_t v___x_849_; 
v___x_849_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_845_, v_info_846_, v_self_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___boxed(lean_object* v_i_850_, lean_object* v_inst_851_, lean_object* v_info_852_, lean_object* v_self_853_, lean_object* v_a_854_){
_start:
{
uint8_t v_res_855_; lean_object* v_r_856_; 
v_res_855_ = l_Lake_MTime_checkUpToDate(v_i_850_, v_inst_851_, v_info_852_, v_self_853_);
lean_dec_ref(v_self_853_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_unsigned_to_nat(11u);
v___x_867_ = lean_nat_to_int(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_unsigned_to_nat(10u);
v___x_875_ = lean_nat_to_int(v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
lean_dec(v_x_879_);
return v_x_880_;
}
else
{
lean_object* v_head_882_; lean_object* v_tail_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_893_; 
v_head_882_ = lean_ctor_get(v_x_881_, 0);
v_tail_883_ = lean_ctor_get(v_x_881_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v_x_881_);
if (v_isSharedCheck_893_ == 0)
{
v___x_885_ = v_x_881_;
v_isShared_886_ = v_isSharedCheck_893_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_tail_883_);
lean_inc(v_head_882_);
lean_dec(v_x_881_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_893_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
lean_inc(v_x_879_);
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 5);
lean_ctor_set(v___x_885_, 1, v_x_879_);
lean_ctor_set(v___x_885_, 0, v_x_880_);
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_x_880_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_x_879_);
v___x_888_ = v_reuseFailAlloc_892_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_882_);
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(v_x_879_, v___x_890_, v_tail_883_);
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
lean_object* v___x_896_; 
lean_dec(v_x_895_);
v___x_896_ = lean_box(0);
return v___x_896_;
}
else
{
lean_object* v_tail_897_; 
v_tail_897_ = lean_ctor_get(v_x_894_, 1);
if (lean_obj_tag(v_tail_897_) == 0)
{
lean_object* v_head_898_; lean_object* v___x_899_; 
lean_dec(v_x_895_);
v_head_898_ = lean_ctor_get(v_x_894_, 0);
lean_inc(v_head_898_);
lean_dec_ref_known(v_x_894_, 2);
v___x_899_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_898_);
return v___x_899_;
}
else
{
lean_object* v_head_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
lean_inc(v_tail_897_);
v_head_900_ = lean_ctor_get(v_x_894_, 0);
lean_inc(v_head_900_);
lean_dec_ref_known(v_x_894_, 2);
v___x_901_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_900_);
v___x_902_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(v_x_895_, v___x_901_, v_tail_897_);
return v___x_902_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0));
v___x_905_ = lean_string_length(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5);
v___x_907_ = lean_nat_to_int(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(lean_object* v_xs_916_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_917_ = lean_array_get_size(v_xs_916_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_nat_dec_eq(v___x_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_920_ = lean_array_to_list(v_xs_916_);
v___x_921_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3));
v___x_922_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(v___x_920_, v___x_921_);
v___x_923_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6, &l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6);
v___x_924_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7));
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_922_);
v___x_926_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8));
v___x_927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_923_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Std_Format_fill(v___x_928_);
return v___x_929_;
}
else
{
lean_object* v___x_930_; 
lean_dec_ref(v_xs_916_);
v___x_930_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10));
return v___x_930_;
}
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_unsigned_to_nat(8u);
v___x_935_ = lean_nat_to_int(v___x_934_);
return v___x_935_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_unsigned_to_nat(9u);
v___x_940_ = lean_nat_to_int(v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___redArg(lean_object* v_x_941_){
_start:
{
lean_object* v_caption_942_; lean_object* v_inputs_943_; uint64_t v_hash_944_; lean_object* v_mtime_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_caption_942_ = lean_ctor_get(v_x_941_, 0);
lean_inc_ref(v_caption_942_);
v_inputs_943_ = lean_ctor_get(v_x_941_, 1);
lean_inc_ref(v_inputs_943_);
v_hash_944_ = lean_ctor_get_uint64(v_x_941_, sizeof(void*)*3);
v_mtime_945_ = lean_ctor_get(v_x_941_, 2);
lean_inc_ref(v_mtime_945_);
lean_dec_ref(v_x_941_);
v___x_946_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__5));
v___x_947_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__3));
v___x_948_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__4, &l_Lake_instReprBuildTrace_repr___redArg___closed__4_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4);
v___x_949_ = l_String_quote(v_caption_942_);
v___x_950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
v___x_951_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_948_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = 0;
v___x_953_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*1, v___x_952_);
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_947_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2));
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = lean_box(1);
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__6));
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_946_);
v___x_962_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__7, &l_Lake_instReprBuildTrace_repr___redArg___closed__7_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7);
v___x_963_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(v_inputs_943_);
v___x_964_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*1, v___x_952_);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_961_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_955_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_957_);
v___x_969_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__9));
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v___x_946_);
v___x_972_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__10, &l_Lake_instReprBuildTrace_repr___redArg___closed__10_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10);
v___x_973_ = l_Lake_instReprHash_repr___redArg(v_hash_944_);
v___x_974_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*1, v___x_952_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_971_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_955_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_957_);
v___x_979_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__12));
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_946_);
v___x_982_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__13, &l_Lake_instReprBuildTrace_repr___redArg___closed__13_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13);
v___x_983_ = l_IO_FS_instReprSystemTime_repr___redArg(v_mtime_945_);
lean_dec_ref(v_mtime_945_);
v___x_984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*1, v___x_952_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_981_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_obj_once(&l_Lake_instReprHash_repr___redArg___closed__10, &l_Lake_instReprHash_repr___redArg___closed__10_once, _init_l_Lake_instReprHash_repr___redArg___closed__10);
v___x_988_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__11));
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v___x_986_);
v___x_990_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__12));
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_987_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*1, v___x_952_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_x_996_){
_start:
{
if (lean_obj_tag(v_x_996_) == 0)
{
lean_dec(v_x_994_);
return v_x_995_;
}
else
{
lean_object* v_head_997_; lean_object* v_tail_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1008_; 
v_head_997_ = lean_ctor_get(v_x_996_, 0);
v_tail_998_ = lean_ctor_get(v_x_996_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1000_ = v_x_996_;
v_isShared_1001_ = v_isSharedCheck_1008_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_tail_998_);
lean_inc(v_head_997_);
lean_dec(v_x_996_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1008_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
lean_inc(v_x_994_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set_tag(v___x_1000_, 5);
lean_ctor_set(v___x_1000_, 1, v_x_994_);
lean_ctor_set(v___x_1000_, 0, v_x_995_);
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_x_995_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_x_994_);
v___x_1003_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_997_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v_x_995_ = v___x_1005_;
v_x_996_ = v_tail_998_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr(lean_object* v_x_1009_, lean_object* v_prec_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lake_instReprBuildTrace_repr___redArg(v_x_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___boxed(lean_object* v_x_1012_, lean_object* v_prec_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lake_instReprBuildTrace_repr(v_x_1012_, v_prec_1013_);
lean_dec(v_prec_1013_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption(lean_object* v_caption_1017_, lean_object* v_self_1018_){
_start:
{
lean_object* v_inputs_1019_; uint64_t v_hash_1020_; lean_object* v_mtime_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v_inputs_1019_ = lean_ctor_get(v_self_1018_, 1);
v_hash_1020_ = lean_ctor_get_uint64(v_self_1018_, sizeof(void*)*3);
v_mtime_1021_ = lean_ctor_get(v_self_1018_, 2);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_self_1018_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v_self_1018_, 0);
lean_dec(v_unused_1029_);
v___x_1023_ = v_self_1018_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_mtime_1021_);
lean_inc(v_inputs_1019_);
lean_dec(v_self_1018_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v_caption_1017_);
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_caption_1017_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_inputs_1019_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v_mtime_1021_);
lean_ctor_set_uint64(v_reuseFailAlloc_1027_, sizeof(void*)*3, v_hash_1020_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs(lean_object* v_self_1032_){
_start:
{
lean_object* v_caption_1033_; uint64_t v_hash_1034_; lean_object* v_mtime_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1043_; 
v_caption_1033_ = lean_ctor_get(v_self_1032_, 0);
v_hash_1034_ = lean_ctor_get_uint64(v_self_1032_, sizeof(void*)*3);
v_mtime_1035_ = lean_ctor_get(v_self_1032_, 2);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_self_1032_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v_self_1032_, 1);
lean_dec(v_unused_1044_);
v___x_1037_ = v_self_1032_;
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_mtime_1035_);
lean_inc(v_caption_1033_);
lean_dec(v_self_1032_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___x_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_caption_1033_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_mtime_1035_);
lean_ctor_set_uint64(v_reuseFailAlloc_1042_, sizeof(void*)*3, v_hash_1034_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash(uint64_t v_hash_1045_, lean_object* v_caption_1046_){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1048_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1049_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1049_, 0, v_caption_1046_);
lean_ctor_set(v___x_1049_, 1, v___x_1047_);
lean_ctor_set(v___x_1049_, 2, v___x_1048_);
lean_ctor_set_uint64(v___x_1049_, sizeof(void*)*3, v_hash_1045_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash___boxed(lean_object* v_hash_1050_, lean_object* v_caption_1051_){
_start:
{
uint64_t v_hash_boxed_1052_; lean_object* v_res_1053_; 
v_hash_boxed_1052_ = lean_unbox_uint64(v_hash_1050_);
lean_dec_ref(v_hash_1050_);
v_res_1053_ = l_Lake_BuildTrace_ofHash(v_hash_boxed_1052_, v_caption_1051_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0(uint64_t v_hash_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1056_ = ((lean_object*)(l_Lake_BuildTrace_instCoeHash___lam__0___closed__0));
v___x_1057_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1058_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1059_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1059_, 0, v___x_1056_);
lean_ctor_set(v___x_1059_, 1, v___x_1057_);
lean_ctor_set(v___x_1059_, 2, v___x_1058_);
lean_ctor_set_uint64(v___x_1059_, sizeof(void*)*3, v_hash_1055_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___boxed(lean_object* v_hash_1060_){
_start:
{
uint64_t v_hash_boxed_1061_; lean_object* v_res_1062_; 
v_hash_boxed_1061_ = lean_unbox_uint64(v_hash_1060_);
lean_dec_ref(v_hash_1060_);
v_res_1062_ = l_Lake_BuildTrace_instCoeHash___lam__0(v_hash_boxed_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofMTime(lean_object* v_mtime_1065_, lean_object* v_caption_1066_){
_start:
{
lean_object* v___x_1067_; uint64_t v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1068_ = 1723ULL;
v___x_1069_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1069_, 0, v_caption_1066_);
lean_ctor_set(v___x_1069_, 1, v___x_1067_);
lean_ctor_set(v___x_1069_, 2, v_mtime_1065_);
lean_ctor_set_uint64(v___x_1069_, sizeof(void*)*3, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0(lean_object* v_mtime_1071_){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint64_t v___x_1074_; lean_object* v___x_1075_; 
v___x_1072_ = ((lean_object*)(l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0));
v___x_1073_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1074_ = 1723ULL;
v___x_1075_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1075_, 0, v___x_1072_);
lean_ctor_set(v___x_1075_, 1, v___x_1073_);
lean_ctor_set(v___x_1075_, 2, v_mtime_1071_);
lean_ctor_set_uint64(v___x_1075_, sizeof(void*)*3, v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_nil(lean_object* v_caption_1078_){
_start:
{
lean_object* v___x_1079_; uint64_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1079_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1080_ = 1723ULL;
v___x_1081_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1082_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1082_, 0, v_caption_1078_);
lean_ctor_set(v___x_1082_, 1, v___x_1079_);
lean_ctor_set(v___x_1082_, 2, v___x_1081_);
lean_ctor_set_uint64(v___x_1082_, sizeof(void*)*3, v___x_1080_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace___closed__1(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lake_BuildTrace_instNilTrace___closed__0));
v___x_1085_ = l_Lake_BuildTrace_nil(v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace(void){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_obj_once(&l_Lake_BuildTrace_instNilTrace___closed__1, &l_Lake_BuildTrace_instNilTrace___closed__1_once, _init_l_Lake_BuildTrace_instNilTrace___closed__1);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg(lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_info_1091_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_inc(v_info_1091_);
v___x_1093_ = lean_apply_1(v_inst_1088_, v_info_1091_);
v___x_1094_ = lean_apply_3(v_inst_1089_, lean_box(0), v___x_1093_, lean_box(0));
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
lean_inc(v_info_1091_);
v___x_1096_ = lean_apply_2(v_inst_1090_, v_info_1091_, lean_box(0));
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1108_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1099_ = v___x_1096_;
v_isShared_1100_ = v_isSharedCheck_1108_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1108_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint64_t v___x_1104_; lean_object* v___x_1106_; 
v___x_1101_ = lean_apply_1(v_inst_1087_, v_info_1091_);
v___x_1102_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1103_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
lean_ctor_set(v___x_1103_, 2, v_a_1097_);
v___x_1104_ = lean_unbox_uint64(v_a_1095_);
lean_dec(v_a_1095_);
lean_ctor_set_uint64(v___x_1103_, sizeof(void*)*3, v___x_1104_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1103_);
v___x_1106_ = v___x_1099_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1103_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v_a_1095_);
lean_dec(v_info_1091_);
lean_dec_ref(v_inst_1087_);
v_a_1109_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1096_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1096_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec(v_info_1091_);
lean_dec_ref(v_inst_1090_);
lean_dec_ref(v_inst_1087_);
v_a_1117_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1094_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1094_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg___boxed(lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_info_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lake_BuildTrace_compute___redArg(v_inst_1125_, v_inst_1126_, v_inst_1127_, v_inst_1128_, v_info_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute(lean_object* v_00_u03b1_1132_, lean_object* v_m_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_info_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lake_BuildTrace_compute___redArg(v_inst_1134_, v_inst_1135_, v_inst_1136_, v_inst_1137_, v_info_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_m_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_info_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lake_BuildTrace_compute(v_00_u03b1_1141_, v_m_1142_, v_inst_1143_, v_inst_1144_, v_inst_1145_, v_inst_1146_, v_info_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime___redArg(lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(v___x_1154_, 0, lean_box(0));
lean_closure_set(v___x_1154_, 1, lean_box(0));
lean_closure_set(v___x_1154_, 2, v_inst_1150_);
lean_closure_set(v___x_1154_, 3, v_inst_1151_);
lean_closure_set(v___x_1154_, 4, v_inst_1152_);
lean_closure_set(v___x_1154_, 5, v_inst_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(lean_object* v_00_u03b1_1155_, lean_object* v_m_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(v___x_1161_, 0, lean_box(0));
lean_closure_set(v___x_1161_, 1, lean_box(0));
lean_closure_set(v___x_1161_, 2, v_inst_1157_);
lean_closure_set(v___x_1161_, 3, v_inst_1158_);
lean_closure_set(v___x_1161_, 4, v_inst_1159_);
lean_closure_set(v___x_1161_, 5, v_inst_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_mix(lean_object* v_t1_1162_, lean_object* v_t2_1163_){
_start:
{
lean_object* v_caption_1164_; lean_object* v_inputs_1165_; uint64_t v_hash_1166_; lean_object* v_mtime_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1182_; 
v_caption_1164_ = lean_ctor_get(v_t1_1162_, 0);
v_inputs_1165_ = lean_ctor_get(v_t1_1162_, 1);
v_hash_1166_ = lean_ctor_get_uint64(v_t1_1162_, sizeof(void*)*3);
v_mtime_1167_ = lean_ctor_get(v_t1_1162_, 2);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_t1_1162_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1169_ = v_t1_1162_;
v_isShared_1170_ = v_isSharedCheck_1182_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_mtime_1167_);
lean_inc(v_inputs_1165_);
lean_inc(v_caption_1164_);
lean_dec(v_t1_1162_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1182_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
uint64_t v_hash_1171_; lean_object* v_mtime_1172_; lean_object* v___x_1173_; uint64_t v___x_1174_; uint8_t v___x_1175_; 
v_hash_1171_ = lean_ctor_get_uint64(v_t2_1163_, sizeof(void*)*3);
v_mtime_1172_ = lean_ctor_get(v_t2_1163_, 2);
lean_inc_ref(v_mtime_1172_);
v___x_1173_ = lean_array_push(v_inputs_1165_, v_t2_1163_);
v___x_1174_ = lean_uint64_mix_hash(v_hash_1166_, v_hash_1171_);
v___x_1175_ = l_IO_FS_instOrdSystemTime_ord(v_mtime_1167_, v_mtime_1172_);
if (v___x_1175_ == 2)
{
lean_object* v___x_1177_; 
lean_dec_ref(v_mtime_1172_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1173_);
v___x_1177_ = v___x_1169_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_caption_1164_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1178_, 2, v_mtime_1167_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_ctor_set_uint64(v___x_1177_, sizeof(void*)*3, v___x_1174_);
return v___x_1177_;
}
}
else
{
lean_object* v___x_1180_; 
lean_dec_ref(v_mtime_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 2, v_mtime_1172_);
lean_ctor_set(v___x_1169_, 1, v___x_1173_);
v___x_1180_ = v___x_1169_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_caption_1164_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_mtime_1172_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_ctor_set_uint64(v___x_1180_, sizeof(void*)*3, v___x_1174_);
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash___redArg(lean_object* v_inst_1185_, lean_object* v_info_1186_, uint64_t v_hash_1187_, lean_object* v_self_1188_){
_start:
{
uint64_t v_hash_1190_; uint8_t v___x_1191_; 
v_hash_1190_ = lean_ctor_get_uint64(v_self_1188_, sizeof(void*)*3);
v___x_1191_ = lean_uint64_dec_eq(v_hash_1187_, v_hash_1190_);
if (v___x_1191_ == 0)
{
lean_dec(v_info_1186_);
lean_dec_ref(v_inst_1185_);
return v___x_1191_;
}
else
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = lean_apply_2(v_inst_1185_, v_info_1186_, lean_box(0));
v___x_1193_ = lean_unbox(v___x_1192_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(lean_object* v_inst_1194_, lean_object* v_info_1195_, lean_object* v_hash_1196_, lean_object* v_self_1197_, lean_object* v_a_1198_){
_start:
{
uint64_t v_hash_boxed_1199_; uint8_t v_res_1200_; lean_object* v_r_1201_; 
v_hash_boxed_1199_ = lean_unbox_uint64(v_hash_1196_);
lean_dec_ref(v_hash_1196_);
v_res_1200_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1194_, v_info_1195_, v_hash_boxed_1199_, v_self_1197_);
lean_dec_ref(v_self_1197_);
v_r_1201_ = lean_box(v_res_1200_);
return v_r_1201_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash(lean_object* v_i_1202_, lean_object* v_inst_1203_, lean_object* v_info_1204_, uint64_t v_hash_1205_, lean_object* v_self_1206_){
_start:
{
uint8_t v___x_1208_; 
v___x_1208_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1203_, v_info_1204_, v_hash_1205_, v_self_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___boxed(lean_object* v_i_1209_, lean_object* v_inst_1210_, lean_object* v_info_1211_, lean_object* v_hash_1212_, lean_object* v_self_1213_, lean_object* v_a_1214_){
_start:
{
uint64_t v_hash_boxed_1215_; uint8_t v_res_1216_; lean_object* v_r_1217_; 
v_hash_boxed_1215_ = lean_unbox_uint64(v_hash_1212_);
lean_dec_ref(v_hash_1212_);
v_res_1216_ = l_Lake_BuildTrace_checkAgainstHash(v_i_1209_, v_inst_1210_, v_info_1211_, v_hash_boxed_1215_, v_self_1213_);
lean_dec_ref(v_self_1213_);
v_r_1217_ = lean_box(v_res_1216_);
return v_r_1217_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime___redArg(lean_object* v_inst_1218_, lean_object* v_info_1219_, lean_object* v_self_1220_){
_start:
{
lean_object* v_mtime_1222_; uint8_t v___x_1223_; 
v_mtime_1222_ = lean_ctor_get(v_self_1220_, 2);
v___x_1223_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1218_, v_info_1219_, v_mtime_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___redArg___boxed(lean_object* v_inst_1224_, lean_object* v_info_1225_, lean_object* v_self_1226_, lean_object* v_a_1227_){
_start:
{
uint8_t v_res_1228_; lean_object* v_r_1229_; 
v_res_1228_ = l_Lake_BuildTrace_checkAgainstTime___redArg(v_inst_1224_, v_info_1225_, v_self_1226_);
lean_dec_ref(v_self_1226_);
v_r_1229_ = lean_box(v_res_1228_);
return v_r_1229_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime(lean_object* v_i_1230_, lean_object* v_inst_1231_, lean_object* v_info_1232_, lean_object* v_self_1233_){
_start:
{
lean_object* v_mtime_1235_; uint8_t v___x_1236_; 
v_mtime_1235_ = lean_ctor_get(v_self_1233_, 2);
v___x_1236_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1231_, v_info_1232_, v_mtime_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___boxed(lean_object* v_i_1237_, lean_object* v_inst_1238_, lean_object* v_info_1239_, lean_object* v_self_1240_, lean_object* v_a_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Lake_BuildTrace_checkAgainstTime(v_i_1237_, v_inst_1238_, v_info_1239_, v_self_1240_);
lean_dec_ref(v_self_1240_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
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
