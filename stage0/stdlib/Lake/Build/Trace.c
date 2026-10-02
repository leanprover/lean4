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
LEAN_EXPORT uint64_t l_Lake_Hash_ofBool(uint8_t v_b_482_){
_start:
{
if (v_b_482_ == 0)
{
uint64_t v___x_483_; 
v___x_483_ = 18370132993254720638ULL;
return v___x_483_;
}
else
{
uint64_t v___x_484_; 
v___x_484_ = 8507242618548079515ULL;
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofBool___boxed(lean_object* v_b_485_){
_start:
{
uint8_t v_b_boxed_486_; uint64_t v_res_487_; lean_object* v_r_488_; 
v_b_boxed_486_ = lean_unbox(v_b_485_);
v_res_487_ = l_Lake_Hash_ofBool(v_b_boxed_486_);
v_r_488_ = lean_box_uint64(v_res_487_);
return v_r_488_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson(uint64_t v_self_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = l_Lake_lowerHexUInt64(v_self_489_);
v___x_491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson___boxed(lean_object* v_self_492_){
_start:
{
uint64_t v_self_boxed_493_; lean_object* v_res_494_; 
v_self_boxed_493_ = lean_unbox_uint64(v_self_492_);
lean_dec_ref(v_self_492_);
v_res_494_ = l_Lake_Hash_toJson(v_self_boxed_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_fromJson_x3f(lean_object* v_json_507_){
_start:
{
switch(lean_obj_tag(v_json_507_))
{
case 3:
{
lean_object* v_s_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_523_; 
v_s_508_ = lean_ctor_get(v_json_507_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_json_507_);
if (v_isSharedCheck_523_ == 0)
{
v___x_510_ = v_json_507_;
v_isShared_511_ = v_isSharedCheck_523_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_s_508_);
lean_dec(v_json_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_523_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
uint8_t v___x_512_; 
v___x_512_ = l_Lake_isHex(v_s_508_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_del_object(v___x_510_);
lean_dec_ref(v_s_508_);
v___x_513_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__1));
return v___x_513_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_514_ = lean_string_utf8_byte_size(v_s_508_);
v___x_515_ = lean_unsigned_to_nat(16u);
v___x_516_ = lean_nat_dec_eq(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
lean_del_object(v___x_510_);
lean_dec_ref(v_s_508_);
v___x_517_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__3));
return v___x_517_;
}
else
{
uint64_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_518_ = l_Lake_Hash_ofHex(v_s_508_);
lean_dec_ref(v_s_508_);
v___x_519_ = lean_box_uint64(v___x_518_);
if (v_isShared_511_ == 0)
{
lean_ctor_set_tag(v___x_510_, 1);
lean_ctor_set(v___x_510_, 0, v___x_519_);
v___x_521_ = v___x_510_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
case 2:
{
lean_object* v_n_524_; lean_object* v___x_525_; 
v_n_524_ = lean_ctor_get(v_json_507_, 0);
lean_inc_ref(v_n_524_);
lean_dec_ref_known(v_json_507_, 1);
v___x_525_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_524_);
lean_dec_ref(v_n_524_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_535_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_535_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_535_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_535_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_530_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__4));
v___x_531_ = lean_string_append(v___x_530_, v_a_526_);
lean_dec(v_a_526_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_531_);
v___x_533_ = v___x_528_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
else
{
return v___x_525_;
}
}
default: 
{
lean_object* v___x_536_; 
lean_dec(v_json_507_);
v___x_536_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__6));
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg(lean_object* v_inst_539_){
_start:
{
lean_inc(v_inst_539_);
return v_inst_539_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg___boxed(lean_object* v_inst_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lake_instComputeTraceHashOfComputeHash___redArg(v_inst_540_);
lean_dec(v_inst_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash(lean_object* v_00_u03b1_542_, lean_object* v_m_543_, lean_object* v_inst_544_){
_start:
{
lean_inc(v_inst_544_);
return v_inst_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___boxed(lean_object* v_00_u03b1_545_, lean_object* v_m_546_, lean_object* v_inst_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lake_instComputeTraceHashOfComputeHash(v_00_u03b1_545_, v_m_546_, v_inst_547_);
lean_dec(v_inst_547_);
return v_res_548_;
}
}
LEAN_EXPORT uint64_t l_Lake_pureHash___redArg(lean_object* v_inst_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_551_; uint64_t v___x_552_; 
v___x_551_ = lean_apply_1(v_inst_549_, v_a_550_);
v___x_552_ = lean_unbox_uint64(v___x_551_);
lean_dec_ref(v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lake_pureHash___redArg___boxed(lean_object* v_inst_553_, lean_object* v_a_554_){
_start:
{
uint64_t v_res_555_; lean_object* v_r_556_; 
v_res_555_ = l_Lake_pureHash___redArg(v_inst_553_, v_a_554_);
v_r_556_ = lean_box_uint64(v_res_555_);
return v_r_556_;
}
}
LEAN_EXPORT uint64_t l_Lake_pureHash(lean_object* v_00_u03b1_557_, lean_object* v_inst_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_560_; uint64_t v___x_561_; 
v___x_560_ = lean_apply_1(v_inst_558_, v_a_559_);
v___x_561_ = lean_unbox_uint64(v___x_560_);
lean_dec_ref(v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lake_pureHash___boxed(lean_object* v_00_u03b1_562_, lean_object* v_inst_563_, lean_object* v_a_564_){
_start:
{
uint64_t v_res_565_; lean_object* v_r_566_; 
v_res_565_ = l_Lake_pureHash(v_00_u03b1_562_, v_inst_563_, v_a_564_);
v_r_566_ = lean_box_uint64(v_res_565_);
return v_r_566_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash___redArg(lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_apply_1(v_inst_567_, v_a_569_);
v___x_571_ = lean_apply_2(v_inst_568_, lean_box(0), v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash(lean_object* v_00_u03b1_572_, lean_object* v_m_573_, lean_object* v_n_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_apply_1(v_inst_575_, v_a_577_);
v___x_579_ = lean_apply_2(v_inst_576_, lean_box(0), v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashIdOfHashable___redArg(lean_object* v_inst_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = lean_alloc_closure((void*)(l_Lake_Hash_ofHashable___boxed), 3, 2);
lean_closure_set(v___x_581_, 0, lean_box(0));
lean_closure_set(v___x_581_, 1, v_inst_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashIdOfHashable(lean_object* v_00_u03b1_582_, lean_object* v_inst_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_alloc_closure((void*)(l_Lake_Hash_ofHashable___boxed), 3, 2);
lean_closure_set(v___x_584_, 0, lean_box(0));
lean_closure_set(v___x_584_, 1, v_inst_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash(lean_object* v_file_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_IO_FS_readBinFile(v_file_585_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_599_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_599_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_599_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_599_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
uint64_t v___x_592_; uint64_t v___x_593_; uint64_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_592_ = 1723ULL;
v___x_593_ = lean_byte_array_hash(v_a_588_);
lean_dec(v_a_588_);
v___x_594_ = lean_uint64_mix_hash(v___x_592_, v___x_593_);
v___x_595_ = lean_box_uint64(v___x_594_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_595_);
v___x_597_ = v___x_590_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_a_600_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_587_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_587_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash___boxed(lean_object* v_file_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lake_computeBinFileHash(v_file_608_);
lean_dec_ref(v_file_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash(lean_object* v_file_613_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_IO_FS_readFile(v_file_613_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_628_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_628_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; uint64_t v___x_621_; uint64_t v___x_622_; uint64_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_620_ = l_String_crlfToLf(v_a_616_);
lean_dec(v_a_616_);
v___x_621_ = 1723ULL;
v___x_622_ = lean_string_hash(v___x_620_);
lean_dec_ref(v___x_620_);
v___x_623_ = lean_uint64_mix_hash(v___x_621_, v___x_622_);
v___x_624_ = lean_box_uint64(v___x_623_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_624_);
v___x_626_ = v___x_618_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
v_a_629_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_615_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_615_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash___boxed(lean_object* v_file_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lake_computeTextFileHash(v_file_637_);
lean_dec_ref(v_file_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0(lean_object* v_x_640_){
_start:
{
lean_inc_ref(v_x_640_);
return v_x_640_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0___boxed(lean_object* v_x_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lake_instCoeTextFilePathFilePath___lam__0(v_x_641_);
lean_dec_ref(v_x_641_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash(lean_object* v_file_648_, uint8_t v_text_649_){
_start:
{
if (v_text_649_ == 0)
{
lean_object* v___x_651_; 
v___x_651_ = l_Lake_computeBinFileHash(v_file_648_);
return v___x_651_;
}
else
{
lean_object* v___x_652_; 
v___x_652_ = l_Lake_computeTextFileHash(v_file_648_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash___boxed(lean_object* v_file_653_, lean_object* v_text_654_, lean_object* v_a_655_){
_start:
{
uint8_t v_text_boxed_656_; lean_object* v_res_657_; 
v_text_boxed_656_ = lean_unbox(v_text_654_);
v_res_657_ = l_Lake_computeFileHash(v_file_653_, v_text_boxed_656_);
lean_dec_ref(v_file_653_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0(uint64_t v_ts_658_, lean_object* v_toPure_659_, uint64_t v_____do__lift_660_){
_start:
{
uint64_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = lean_uint64_mix_hash(v_ts_658_, v_____do__lift_660_);
v___x_662_ = lean_box_uint64(v___x_661_);
v___x_663_ = lean_apply_2(v_toPure_659_, lean_box(0), v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0___boxed(lean_object* v_ts_664_, lean_object* v_toPure_665_, lean_object* v_____do__lift_666_){
_start:
{
uint64_t v_ts_boxed_667_; uint64_t v_____do__lift_88__boxed_668_; lean_object* v_res_669_; 
v_ts_boxed_667_ = lean_unbox_uint64(v_ts_664_);
lean_dec_ref(v_ts_664_);
v_____do__lift_88__boxed_668_ = lean_unbox_uint64(v_____do__lift_666_);
lean_dec_ref(v_____do__lift_666_);
v_res_669_ = l_Lake_computeArrayHash___redArg___lam__0(v_ts_boxed_667_, v_toPure_665_, v_____do__lift_88__boxed_668_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1(lean_object* v_toPure_670_, lean_object* v_inst_671_, lean_object* v_toBind_672_, uint64_t v_ts_673_, lean_object* v_t_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___f_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = lean_box_uint64(v_ts_673_);
v___f_676_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_676_, 0, v___x_675_);
lean_closure_set(v___f_676_, 1, v_toPure_670_);
v___x_677_ = lean_apply_1(v_inst_671_, v_t_674_);
v___x_678_ = lean_apply_4(v_toBind_672_, lean_box(0), lean_box(0), v___x_677_, v___f_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1___boxed(lean_object* v_toPure_679_, lean_object* v_inst_680_, lean_object* v_toBind_681_, lean_object* v_ts_682_, lean_object* v_t_683_){
_start:
{
uint64_t v_ts_boxed_684_; lean_object* v_res_685_; 
v_ts_boxed_684_ = lean_unbox_uint64(v_ts_682_);
lean_dec_ref(v_ts_682_);
v_res_685_ = l_Lake_computeArrayHash___redArg___lam__1(v_toPure_679_, v_inst_680_, v_toBind_681_, v_ts_boxed_684_, v_t_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg(lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_as_690_){
_start:
{
lean_object* v_toApplicative_691_; lean_object* v_toBind_692_; lean_object* v_toPure_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v_toApplicative_691_ = lean_ctor_get(v_inst_689_, 0);
v_toBind_692_ = lean_ctor_get(v_inst_689_, 1);
v_toPure_693_ = lean_ctor_get(v_toApplicative_691_, 1);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_array_get_size(v_as_690_);
v___x_696_ = lean_nat_dec_lt(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
lean_inc(v_toPure_693_);
lean_dec_ref(v_as_690_);
lean_dec_ref(v_inst_689_);
lean_dec(v_inst_688_);
v___x_697_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_698_ = lean_apply_2(v_toPure_693_, lean_box(0), v___x_697_);
return v___x_698_;
}
else
{
lean_object* v___f_699_; size_t v___x_700_; size_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_inc(v_toBind_692_);
lean_inc(v_toPure_693_);
v___f_699_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_699_, 0, v_toPure_693_);
lean_closure_set(v___f_699_, 1, v_inst_688_);
lean_closure_set(v___f_699_, 2, v_toBind_692_);
v___x_700_ = ((size_t)0ULL);
v___x_701_ = lean_usize_of_nat(v___x_695_);
v___x_702_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_689_, v___f_699_, v_as_690_, v___x_700_, v___x_701_, v___x_702_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash(lean_object* v_00_u03b1_704_, lean_object* v_m_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_as_708_){
_start:
{
lean_object* v_toApplicative_709_; lean_object* v_toBind_710_; lean_object* v_toPure_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_toApplicative_709_ = lean_ctor_get(v_inst_707_, 0);
v_toBind_710_ = lean_ctor_get(v_inst_707_, 1);
v_toPure_711_ = lean_ctor_get(v_toApplicative_709_, 1);
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = lean_array_get_size(v_as_708_);
v___x_714_ = lean_nat_dec_lt(v___x_712_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; 
lean_inc(v_toPure_711_);
lean_dec_ref(v_as_708_);
lean_dec_ref(v_inst_707_);
lean_dec(v_inst_706_);
v___x_715_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_716_ = lean_apply_2(v_toPure_711_, lean_box(0), v___x_715_);
return v___x_716_;
}
else
{
lean_object* v___f_717_; size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
lean_inc(v_toBind_710_);
lean_inc(v_toPure_711_);
v___f_717_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_717_, 0, v_toPure_711_);
lean_closure_set(v___f_717_, 1, v_inst_706_);
lean_closure_set(v___f_717_, 2, v_toBind_710_);
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_713_);
v___x_720_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_707_, v___f_717_, v_as_708_, v___x_718_, v___x_719_, v___x_720_);
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad___redArg(lean_object* v_inst_722_, lean_object* v_inst_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash), 5, 4);
lean_closure_set(v___x_724_, 0, lean_box(0));
lean_closure_set(v___x_724_, 1, lean_box(0));
lean_closure_set(v___x_724_, 2, v_inst_722_);
lean_closure_set(v___x_724_, 3, v_inst_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad(lean_object* v_00_u03b1_725_, lean_object* v_m_726_, lean_object* v_inst_727_, lean_object* v_inst_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash), 5, 4);
lean_closure_set(v___x_729_, 0, lean_box(0));
lean_closure_set(v___x_729_, 1, lean_box(0));
lean_closure_set(v___x_729_, 2, v_inst_727_);
lean_closure_set(v___x_729_, 3, v_inst_728_);
return v___x_729_;
}
}
static lean_object* _init_l_Lake_MTime_instOfNat___closed__0(void){
_start:
{
uint32_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = 0;
v___x_731_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__2, &l_Lake_Hash_ofJsonNumber_x3f___closed__2_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2);
v___x_732_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set_uint32(v___x_732_, sizeof(void*)*1, v___x_730_);
return v___x_732_;
}
}
static lean_object* _init_l_Lake_MTime_instOfNat(void){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
return v___x_733_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_instBEq___aux__1(lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
uint8_t v___x_736_; 
v___x_736_ = l_IO_FS_instBEqSystemTime_beq(v_x_734_, v_x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instBEq___aux__1___boxed(lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_Lake_MTime_instBEq___aux__1(v_x_737_, v_x_738_);
lean_dec_ref(v_x_738_);
lean_dec_ref(v_x_737_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___redArg(lean_object* v_x_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___redArg___boxed(lean_object* v_x_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lake_MTime_instRepr___aux__1___redArg(v_x_745_);
lean_dec_ref(v_x_745_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1(lean_object* v_x_747_, lean_object* v_prec_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___boxed(lean_object* v_x_750_, lean_object* v_prec_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lake_MTime_instRepr___aux__1(v_x_750_, v_prec_751_);
lean_dec(v_prec_751_);
lean_dec_ref(v_x_750_);
return v_res_752_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_instOrd___aux__1(lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = l_IO_FS_instOrdSystemTime_ord(v_x_755_, v_x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instOrd___aux__1___boxed(lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_Lake_MTime_instOrd___aux__1(v_x_758_, v_x_759_);
lean_dec_ref(v_x_759_);
lean_dec_ref(v_x_758_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
static lean_object* _init_l_Lake_MTime_instLT(void){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = lean_box(0);
return v___x_764_;
}
}
static lean_object* _init_l_Lake_MTime_instLE(void){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = lean_box(0);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0(lean_object* v_x_766_, lean_object* v_y_767_){
_start:
{
uint8_t v___x_768_; 
v___x_768_ = l_IO_FS_instOrdSystemTime_ord(v_x_766_, v_y_767_);
if (v___x_768_ == 2)
{
lean_inc_ref(v_y_767_);
return v_y_767_;
}
else
{
lean_inc_ref(v_x_766_);
return v_x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0___boxed(lean_object* v_x_769_, lean_object* v_y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lake_MTime_instMin___lam__0(v_x_769_, v_y_770_);
lean_dec_ref(v_y_770_);
lean_dec_ref(v_x_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0(lean_object* v_x_774_, lean_object* v_y_775_){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = l_IO_FS_instOrdSystemTime_ord(v_x_774_, v_y_775_);
if (v___x_776_ == 2)
{
lean_inc_ref(v_x_774_);
return v_x_774_;
}
else
{
lean_inc_ref(v_y_775_);
return v_y_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0___boxed(lean_object* v_x_777_, lean_object* v_y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lake_MTime_instMax___lam__0(v_x_777_, v_y_778_);
lean_dec_ref(v_y_778_);
lean_dec_ref(v_x_777_);
return v_res_779_;
}
}
static lean_object* _init_l_Lake_MTime_instNilTrace(void){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(lean_object* v_inst_784_){
_start:
{
lean_inc_ref(v_inst_784_);
return v_inst_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(lean_object* v_inst_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(v_inst_785_);
lean_dec_ref(v_inst_785_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(lean_object* v_00_u03b1_787_, lean_object* v_inst_788_){
_start:
{
lean_inc_ref(v_inst_788_);
return v_inst_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___boxed(lean_object* v_00_u03b1_789_, lean_object* v_inst_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(v_00_u03b1_789_, v_inst_790_);
lean_dec_ref(v_inst_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime(lean_object* v_file_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = lean_io_metadata(v_file_792_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_803_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_803_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_modified_799_; lean_object* v___x_801_; 
v_modified_799_ = lean_ctor_get(v_a_795_, 1);
lean_inc_ref(v_modified_799_);
lean_dec(v_a_795_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v_modified_799_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_modified_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
v_a_804_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_794_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_794_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime___boxed(lean_object* v_file_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lake_getFileMTime(v_file_812_);
lean_dec_ref(v_file_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0(lean_object* v_x_817_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = lean_io_metadata(v_x_817_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_828_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_828_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_828_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_828_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_modified_824_; lean_object* v___x_826_; 
v_modified_824_ = lean_ctor_get(v_a_820_, 1);
lean_inc_ref(v_modified_824_);
lean_dec(v_a_820_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v_modified_824_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_modified_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_819_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_819_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0___boxed(lean_object* v_x_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lake_instGetMTimeTextFilePath___lam__0(v_x_837_);
lean_dec_ref(v_x_837_);
return v_res_839_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object* v_inst_842_, lean_object* v_info_843_, lean_object* v_self_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_apply_2(v_inst_842_, v_info_843_, lean_box(0));
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; uint8_t v___x_848_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = l_IO_FS_instOrdSystemTime_ord(v_self_844_, v_a_847_);
lean_dec(v_a_847_);
if (v___x_848_ == 0)
{
uint8_t v___x_849_; 
v___x_849_ = 1;
return v___x_849_;
}
else
{
uint8_t v___x_850_; 
v___x_850_ = 0;
return v___x_850_;
}
}
else
{
uint8_t v___x_851_; 
lean_dec_ref_known(v___x_846_, 1);
v___x_851_ = 0;
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___redArg___boxed(lean_object* v_inst_852_, lean_object* v_info_853_, lean_object* v_self_854_, lean_object* v_a_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_852_, v_info_853_, v_self_854_);
lean_dec_ref(v_self_854_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate(lean_object* v_i_858_, lean_object* v_inst_859_, lean_object* v_info_860_, lean_object* v_self_861_){
_start:
{
uint8_t v___x_863_; 
v___x_863_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_859_, v_info_860_, v_self_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___boxed(lean_object* v_i_864_, lean_object* v_inst_865_, lean_object* v_info_866_, lean_object* v_self_867_, lean_object* v_a_868_){
_start:
{
uint8_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l_Lake_MTime_checkUpToDate(v_i_864_, v_inst_865_, v_info_866_, v_self_867_);
lean_dec_ref(v_self_867_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_unsigned_to_nat(11u);
v___x_881_ = lean_nat_to_int(v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_unsigned_to_nat(10u);
v___x_889_ = lean_nat_to_int(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_x_895_) == 0)
{
lean_dec(v_x_893_);
return v_x_894_;
}
else
{
lean_object* v_head_896_; lean_object* v_tail_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_907_; 
v_head_896_ = lean_ctor_get(v_x_895_, 0);
v_tail_897_ = lean_ctor_get(v_x_895_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_x_895_);
if (v_isSharedCheck_907_ == 0)
{
v___x_899_ = v_x_895_;
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_tail_897_);
lean_inc(v_head_896_);
lean_dec(v_x_895_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_907_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
lean_inc(v_x_893_);
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 5);
lean_ctor_set(v___x_899_, 1, v_x_893_);
lean_ctor_set(v___x_899_, 0, v_x_894_);
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_x_894_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_x_893_);
v___x_902_ = v_reuseFailAlloc_906_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_896_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(v_x_893_, v___x_904_, v_tail_897_);
return v___x_905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
if (lean_obj_tag(v_x_908_) == 0)
{
lean_object* v___x_910_; 
lean_dec(v_x_909_);
v___x_910_ = lean_box(0);
return v___x_910_;
}
else
{
lean_object* v_tail_911_; 
v_tail_911_ = lean_ctor_get(v_x_908_, 1);
if (lean_obj_tag(v_tail_911_) == 0)
{
lean_object* v_head_912_; lean_object* v___x_913_; 
lean_dec(v_x_909_);
v_head_912_ = lean_ctor_get(v_x_908_, 0);
lean_inc(v_head_912_);
lean_dec_ref_known(v_x_908_, 2);
v___x_913_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_912_);
return v___x_913_;
}
else
{
lean_object* v_head_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_inc(v_tail_911_);
v_head_914_ = lean_ctor_get(v_x_908_, 0);
lean_inc(v_head_914_);
lean_dec_ref_known(v_x_908_, 2);
v___x_915_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_914_);
v___x_916_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(v_x_909_, v___x_915_, v_tail_911_);
return v___x_916_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0));
v___x_919_ = lean_string_length(v___x_918_);
return v___x_919_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5);
v___x_921_ = lean_nat_to_int(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(lean_object* v_xs_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_931_ = lean_array_get_size(v_xs_930_);
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = lean_nat_dec_eq(v___x_931_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_934_ = lean_array_to_list(v_xs_930_);
v___x_935_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3));
v___x_936_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(v___x_934_, v___x_935_);
v___x_937_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6, &l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6);
v___x_938_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7));
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_936_);
v___x_940_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8));
v___x_941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_937_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l_Std_Format_fill(v___x_942_);
return v___x_943_;
}
else
{
lean_object* v___x_944_; 
lean_dec_ref(v_xs_930_);
v___x_944_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10));
return v___x_944_;
}
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_unsigned_to_nat(8u);
v___x_949_ = lean_nat_to_int(v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_unsigned_to_nat(9u);
v___x_954_ = lean_nat_to_int(v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___redArg(lean_object* v_x_955_){
_start:
{
lean_object* v_caption_956_; lean_object* v_inputs_957_; uint64_t v_hash_958_; lean_object* v_mtime_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_caption_956_ = lean_ctor_get(v_x_955_, 0);
lean_inc_ref(v_caption_956_);
v_inputs_957_ = lean_ctor_get(v_x_955_, 1);
lean_inc_ref(v_inputs_957_);
v_hash_958_ = lean_ctor_get_uint64(v_x_955_, sizeof(void*)*3);
v_mtime_959_ = lean_ctor_get(v_x_955_, 2);
lean_inc_ref(v_mtime_959_);
lean_dec_ref(v_x_955_);
v___x_960_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__5));
v___x_961_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__3));
v___x_962_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__4, &l_Lake_instReprBuildTrace_repr___redArg___closed__4_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4);
v___x_963_ = l_String_quote(v_caption_956_);
v___x_964_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
v___x_965_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_962_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = 0;
v___x_967_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*1, v___x_966_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_961_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2));
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_box(1);
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__6));
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_960_);
v___x_976_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__7, &l_Lake_instReprBuildTrace_repr___redArg___closed__7_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7);
v___x_977_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(v_inputs_957_);
v___x_978_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*1, v___x_966_);
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_975_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_969_);
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_971_);
v___x_983_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__9));
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v___x_960_);
v___x_986_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__10, &l_Lake_instReprBuildTrace_repr___redArg___closed__10_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10);
v___x_987_ = l_Lake_instReprHash_repr___redArg(v_hash_958_);
v___x_988_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*1, v___x_966_);
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_985_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_969_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_971_);
v___x_993_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__12));
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_960_);
v___x_996_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__13, &l_Lake_instReprBuildTrace_repr___redArg___closed__13_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13);
v___x_997_ = l_IO_FS_instReprSystemTime_repr___redArg(v_mtime_959_);
lean_dec_ref(v_mtime_959_);
v___x_998_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*1, v___x_966_);
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_995_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_obj_once(&l_Lake_instReprHash_repr___redArg___closed__10, &l_Lake_instReprHash_repr___redArg___closed__10_once, _init_l_Lake_instReprHash_repr___redArg___closed__10);
v___x_1002_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__11));
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_1000_);
v___x_1004_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__12));
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1001_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set_uint8(v___x_1007_, sizeof(void*)*1, v___x_966_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
if (lean_obj_tag(v_x_1010_) == 0)
{
lean_dec(v_x_1008_);
return v_x_1009_;
}
else
{
lean_object* v_head_1011_; lean_object* v_tail_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1022_; 
v_head_1011_ = lean_ctor_get(v_x_1010_, 0);
v_tail_1012_ = lean_ctor_get(v_x_1010_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_x_1010_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1014_ = v_x_1010_;
v_isShared_1015_ = v_isSharedCheck_1022_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_tail_1012_);
lean_inc(v_head_1011_);
lean_dec(v_x_1010_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1022_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
lean_inc(v_x_1008_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set_tag(v___x_1014_, 5);
lean_ctor_set(v___x_1014_, 1, v_x_1008_);
lean_ctor_set(v___x_1014_, 0, v_x_1009_);
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_x_1009_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_x_1008_);
v___x_1017_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_1011_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v_x_1009_ = v___x_1019_;
v_x_1010_ = v_tail_1012_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr(lean_object* v_x_1023_, lean_object* v_prec_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lake_instReprBuildTrace_repr___redArg(v_x_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___boxed(lean_object* v_x_1026_, lean_object* v_prec_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lake_instReprBuildTrace_repr(v_x_1026_, v_prec_1027_);
lean_dec(v_prec_1027_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption(lean_object* v_caption_1031_, lean_object* v_self_1032_){
_start:
{
lean_object* v_inputs_1033_; uint64_t v_hash_1034_; lean_object* v_mtime_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
v_inputs_1033_ = lean_ctor_get(v_self_1032_, 1);
v_hash_1034_ = lean_ctor_get_uint64(v_self_1032_, sizeof(void*)*3);
v_mtime_1035_ = lean_ctor_get(v_self_1032_, 2);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_self_1032_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v_self_1032_, 0);
lean_dec(v_unused_1043_);
v___x_1037_ = v_self_1032_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_mtime_1035_);
lean_inc(v_inputs_1033_);
lean_dec(v_self_1032_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v_caption_1031_);
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_caption_1031_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_inputs_1033_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_mtime_1035_);
lean_ctor_set_uint64(v_reuseFailAlloc_1041_, sizeof(void*)*3, v_hash_1034_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs(lean_object* v_self_1046_){
_start:
{
lean_object* v_caption_1047_; uint64_t v_hash_1048_; lean_object* v_mtime_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1057_; 
v_caption_1047_ = lean_ctor_get(v_self_1046_, 0);
v_hash_1048_ = lean_ctor_get_uint64(v_self_1046_, sizeof(void*)*3);
v_mtime_1049_ = lean_ctor_get(v_self_1046_, 2);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_self_1046_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v_self_1046_, 1);
lean_dec(v_unused_1058_);
v___x_1051_ = v_self_1046_;
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_mtime_1049_);
lean_inc(v_caption_1047_);
lean_dec(v_self_1046_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___x_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_caption_1047_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_mtime_1049_);
lean_ctor_set_uint64(v_reuseFailAlloc_1056_, sizeof(void*)*3, v_hash_1048_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash(uint64_t v_hash_1059_, lean_object* v_caption_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1062_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1063_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1063_, 0, v_caption_1060_);
lean_ctor_set(v___x_1063_, 1, v___x_1061_);
lean_ctor_set(v___x_1063_, 2, v___x_1062_);
lean_ctor_set_uint64(v___x_1063_, sizeof(void*)*3, v_hash_1059_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash___boxed(lean_object* v_hash_1064_, lean_object* v_caption_1065_){
_start:
{
uint64_t v_hash_boxed_1066_; lean_object* v_res_1067_; 
v_hash_boxed_1066_ = lean_unbox_uint64(v_hash_1064_);
lean_dec_ref(v_hash_1064_);
v_res_1067_ = l_Lake_BuildTrace_ofHash(v_hash_boxed_1066_, v_caption_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0(uint64_t v_hash_1069_){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1070_ = ((lean_object*)(l_Lake_BuildTrace_instCoeHash___lam__0___closed__0));
v___x_1071_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1072_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1073_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1073_, 0, v___x_1070_);
lean_ctor_set(v___x_1073_, 1, v___x_1071_);
lean_ctor_set(v___x_1073_, 2, v___x_1072_);
lean_ctor_set_uint64(v___x_1073_, sizeof(void*)*3, v_hash_1069_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___boxed(lean_object* v_hash_1074_){
_start:
{
uint64_t v_hash_boxed_1075_; lean_object* v_res_1076_; 
v_hash_boxed_1075_ = lean_unbox_uint64(v_hash_1074_);
lean_dec_ref(v_hash_1074_);
v_res_1076_ = l_Lake_BuildTrace_instCoeHash___lam__0(v_hash_boxed_1075_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofMTime(lean_object* v_mtime_1079_, lean_object* v_caption_1080_){
_start:
{
lean_object* v___x_1081_; uint64_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1082_ = 1723ULL;
v___x_1083_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1083_, 0, v_caption_1080_);
lean_ctor_set(v___x_1083_, 1, v___x_1081_);
lean_ctor_set(v___x_1083_, 2, v_mtime_1079_);
lean_ctor_set_uint64(v___x_1083_, sizeof(void*)*3, v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0(lean_object* v_mtime_1085_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; uint64_t v___x_1088_; lean_object* v___x_1089_; 
v___x_1086_ = ((lean_object*)(l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0));
v___x_1087_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1088_ = 1723ULL;
v___x_1089_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1089_, 0, v___x_1086_);
lean_ctor_set(v___x_1089_, 1, v___x_1087_);
lean_ctor_set(v___x_1089_, 2, v_mtime_1085_);
lean_ctor_set_uint64(v___x_1089_, sizeof(void*)*3, v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_nil(lean_object* v_caption_1092_){
_start:
{
lean_object* v___x_1093_; uint64_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1093_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1094_ = 1723ULL;
v___x_1095_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1096_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1096_, 0, v_caption_1092_);
lean_ctor_set(v___x_1096_, 1, v___x_1093_);
lean_ctor_set(v___x_1096_, 2, v___x_1095_);
lean_ctor_set_uint64(v___x_1096_, sizeof(void*)*3, v___x_1094_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace___closed__1(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lake_BuildTrace_instNilTrace___closed__0));
v___x_1099_ = l_Lake_BuildTrace_nil(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace(void){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_obj_once(&l_Lake_BuildTrace_instNilTrace___closed__1, &l_Lake_BuildTrace_instNilTrace___closed__1_once, _init_l_Lake_BuildTrace_instNilTrace___closed__1);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg(lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_info_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_inc(v_info_1105_);
v___x_1107_ = lean_apply_1(v_inst_1102_, v_info_1105_);
v___x_1108_ = lean_apply_3(v_inst_1103_, lean_box(0), v___x_1107_, lean_box(0));
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1110_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1108_, 1);
lean_inc(v_info_1105_);
v___x_1110_ = lean_apply_2(v_inst_1104_, v_info_1105_, lean_box(0));
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1122_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1122_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1122_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; uint64_t v___x_1118_; lean_object* v___x_1120_; 
v___x_1115_ = lean_apply_1(v_inst_1101_, v_info_1105_);
v___x_1116_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1117_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
lean_ctor_set(v___x_1117_, 2, v_a_1111_);
v___x_1118_ = lean_unbox_uint64(v_a_1109_);
lean_dec(v_a_1109_);
lean_ctor_set_uint64(v___x_1117_, sizeof(void*)*3, v___x_1118_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1117_);
v___x_1120_ = v___x_1113_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1117_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec(v_a_1109_);
lean_dec(v_info_1105_);
lean_dec_ref(v_inst_1101_);
v_a_1123_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1110_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1110_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_info_1105_);
lean_dec_ref(v_inst_1104_);
lean_dec_ref(v_inst_1101_);
v_a_1131_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1108_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1108_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg___boxed(lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_info_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lake_BuildTrace_compute___redArg(v_inst_1139_, v_inst_1140_, v_inst_1141_, v_inst_1142_, v_info_1143_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute(lean_object* v_00_u03b1_1146_, lean_object* v_m_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_info_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lake_BuildTrace_compute___redArg(v_inst_1148_, v_inst_1149_, v_inst_1150_, v_inst_1151_, v_info_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_m_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_info_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lake_BuildTrace_compute(v_00_u03b1_1155_, v_m_1156_, v_inst_1157_, v_inst_1158_, v_inst_1159_, v_inst_1160_, v_info_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime___redArg(lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(v___x_1168_, 0, lean_box(0));
lean_closure_set(v___x_1168_, 1, lean_box(0));
lean_closure_set(v___x_1168_, 2, v_inst_1164_);
lean_closure_set(v___x_1168_, 3, v_inst_1165_);
lean_closure_set(v___x_1168_, 4, v_inst_1166_);
lean_closure_set(v___x_1168_, 5, v_inst_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(lean_object* v_00_u03b1_1169_, lean_object* v_m_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_inst_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(v___x_1175_, 0, lean_box(0));
lean_closure_set(v___x_1175_, 1, lean_box(0));
lean_closure_set(v___x_1175_, 2, v_inst_1171_);
lean_closure_set(v___x_1175_, 3, v_inst_1172_);
lean_closure_set(v___x_1175_, 4, v_inst_1173_);
lean_closure_set(v___x_1175_, 5, v_inst_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_mix(lean_object* v_t1_1176_, lean_object* v_t2_1177_){
_start:
{
lean_object* v_caption_1178_; lean_object* v_inputs_1179_; uint64_t v_hash_1180_; lean_object* v_mtime_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1196_; 
v_caption_1178_ = lean_ctor_get(v_t1_1176_, 0);
v_inputs_1179_ = lean_ctor_get(v_t1_1176_, 1);
v_hash_1180_ = lean_ctor_get_uint64(v_t1_1176_, sizeof(void*)*3);
v_mtime_1181_ = lean_ctor_get(v_t1_1176_, 2);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_t1_1176_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1183_ = v_t1_1176_;
v_isShared_1184_ = v_isSharedCheck_1196_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_mtime_1181_);
lean_inc(v_inputs_1179_);
lean_inc(v_caption_1178_);
lean_dec(v_t1_1176_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1196_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
uint64_t v_hash_1185_; lean_object* v_mtime_1186_; lean_object* v___x_1187_; uint64_t v___x_1188_; uint8_t v___x_1189_; 
v_hash_1185_ = lean_ctor_get_uint64(v_t2_1177_, sizeof(void*)*3);
v_mtime_1186_ = lean_ctor_get(v_t2_1177_, 2);
lean_inc_ref(v_mtime_1186_);
v___x_1187_ = lean_array_push(v_inputs_1179_, v_t2_1177_);
v___x_1188_ = lean_uint64_mix_hash(v_hash_1180_, v_hash_1185_);
v___x_1189_ = l_IO_FS_instOrdSystemTime_ord(v_mtime_1181_, v_mtime_1186_);
if (v___x_1189_ == 2)
{
lean_object* v___x_1191_; 
lean_dec_ref(v_mtime_1186_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v___x_1187_);
v___x_1191_ = v___x_1183_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_caption_1178_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_mtime_1181_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_ctor_set_uint64(v___x_1191_, sizeof(void*)*3, v___x_1188_);
return v___x_1191_;
}
}
else
{
lean_object* v___x_1194_; 
lean_dec_ref(v_mtime_1181_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 2, v_mtime_1186_);
lean_ctor_set(v___x_1183_, 1, v___x_1187_);
v___x_1194_ = v___x_1183_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_caption_1178_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_mtime_1186_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_ctor_set_uint64(v___x_1194_, sizeof(void*)*3, v___x_1188_);
return v___x_1194_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash___redArg(lean_object* v_inst_1199_, lean_object* v_info_1200_, uint64_t v_hash_1201_, lean_object* v_self_1202_){
_start:
{
uint64_t v_hash_1204_; uint8_t v___x_1205_; 
v_hash_1204_ = lean_ctor_get_uint64(v_self_1202_, sizeof(void*)*3);
v___x_1205_ = lean_uint64_dec_eq(v_hash_1201_, v_hash_1204_);
if (v___x_1205_ == 0)
{
lean_dec(v_info_1200_);
lean_dec_ref(v_inst_1199_);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = lean_apply_2(v_inst_1199_, v_info_1200_, lean_box(0));
v___x_1207_ = lean_unbox(v___x_1206_);
return v___x_1207_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(lean_object* v_inst_1208_, lean_object* v_info_1209_, lean_object* v_hash_1210_, lean_object* v_self_1211_, lean_object* v_a_1212_){
_start:
{
uint64_t v_hash_boxed_1213_; uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_hash_boxed_1213_ = lean_unbox_uint64(v_hash_1210_);
lean_dec_ref(v_hash_1210_);
v_res_1214_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1208_, v_info_1209_, v_hash_boxed_1213_, v_self_1211_);
lean_dec_ref(v_self_1211_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash(lean_object* v_i_1216_, lean_object* v_inst_1217_, lean_object* v_info_1218_, uint64_t v_hash_1219_, lean_object* v_self_1220_){
_start:
{
uint8_t v___x_1222_; 
v___x_1222_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1217_, v_info_1218_, v_hash_1219_, v_self_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___boxed(lean_object* v_i_1223_, lean_object* v_inst_1224_, lean_object* v_info_1225_, lean_object* v_hash_1226_, lean_object* v_self_1227_, lean_object* v_a_1228_){
_start:
{
uint64_t v_hash_boxed_1229_; uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_hash_boxed_1229_ = lean_unbox_uint64(v_hash_1226_);
lean_dec_ref(v_hash_1226_);
v_res_1230_ = l_Lake_BuildTrace_checkAgainstHash(v_i_1223_, v_inst_1224_, v_info_1225_, v_hash_boxed_1229_, v_self_1227_);
lean_dec_ref(v_self_1227_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime___redArg(lean_object* v_inst_1232_, lean_object* v_info_1233_, lean_object* v_self_1234_){
_start:
{
lean_object* v_mtime_1236_; uint8_t v___x_1237_; 
v_mtime_1236_ = lean_ctor_get(v_self_1234_, 2);
v___x_1237_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1232_, v_info_1233_, v_mtime_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___redArg___boxed(lean_object* v_inst_1238_, lean_object* v_info_1239_, lean_object* v_self_1240_, lean_object* v_a_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Lake_BuildTrace_checkAgainstTime___redArg(v_inst_1238_, v_info_1239_, v_self_1240_);
lean_dec_ref(v_self_1240_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime(lean_object* v_i_1244_, lean_object* v_inst_1245_, lean_object* v_info_1246_, lean_object* v_self_1247_){
_start:
{
lean_object* v_mtime_1249_; uint8_t v___x_1250_; 
v_mtime_1249_ = lean_ctor_get(v_self_1247_, 2);
v___x_1250_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1245_, v_info_1246_, v_mtime_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___boxed(lean_object* v_i_1251_, lean_object* v_inst_1252_, lean_object* v_info_1253_, lean_object* v_self_1254_, lean_object* v_a_1255_){
_start:
{
uint8_t v_res_1256_; lean_object* v_r_1257_; 
v_res_1256_ = l_Lake_BuildTrace_checkAgainstTime(v_i_1251_, v_inst_1252_, v_info_1253_, v_self_1254_);
lean_dec_ref(v_self_1254_);
v_r_1257_ = lean_box(v_res_1256_);
return v_r_1257_;
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
