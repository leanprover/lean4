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
lean_object* l_Lake_instReprHash_repr___redArg(uint64_t v_x_223_){
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
LEAN_EXPORT void l_Lake_instReprHash_repr___redArg_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_223_ = stack[0].m_num;
lean_object* v_res_240_;
v_res_240_ = l_Lake_instReprHash_repr___redArg(v_x_223_);
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___redArg___boxed(lean_object* v_x_241_){
_start:
{
uint64_t v_x_149__boxed_242_; lean_object* v_res_243_; 
v_x_149__boxed_242_ = lean_unbox_uint64(v_x_241_);
lean_dec_ref(v_x_241_);
v_res_243_ = l_Lake_instReprHash_repr___redArg(v_x_149__boxed_242_);
return v_res_243_;
}
}
lean_object* l_Lake_instReprHash_repr(uint64_t v_x_244_, lean_object* v_prec_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lake_instReprHash_repr___redArg(v_x_244_);
return v___x_246_;
}
}
LEAN_EXPORT void l_Lake_instReprHash_repr_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_244_ = stack[0].m_num;
lean_object* v_prec_245_ = stack[1].m_obj;
lean_object* v_res_247_;
v_res_247_ = l_Lake_instReprHash_repr(v_x_244_, v_prec_245_);
stack->m_obj
 = v_res_247_;
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___boxed(lean_object* v_x_248_, lean_object* v_prec_249_){
_start:
{
uint64_t v_x_250__boxed_250_; lean_object* v_res_251_; 
v_x_250__boxed_250_ = lean_unbox_uint64(v_x_248_);
lean_dec_ref(v_x_248_);
v_res_251_ = l_Lake_instReprHash_repr(v_x_250__boxed_250_, v_prec_249_);
lean_dec(v_prec_249_);
return v_res_251_;
}
}
uint8_t l_Lake_instDecidableEqHash_decEq(uint64_t v_x_254_, uint64_t v_x_255_){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = lean_uint64_dec_eq(v_x_254_, v_x_255_);
return v___x_256_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqHash_decEq_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_254_ = stack[0].m_num;
uint64_t v_x_255_ = stack[1].m_num;
uint8_t v_res_257_;
v_res_257_ = l_Lake_instDecidableEqHash_decEq(v_x_254_, v_x_255_);
stack->m_num = v_res_257_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash_decEq___boxed(lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
uint64_t v_x_31__boxed_260_; uint64_t v_x_32__boxed_261_; uint8_t v_res_262_; lean_object* v_r_263_; 
v_x_31__boxed_260_ = lean_unbox_uint64(v_x_258_);
lean_dec_ref(v_x_258_);
v_x_32__boxed_261_ = lean_unbox_uint64(v_x_259_);
lean_dec_ref(v_x_259_);
v_res_262_ = l_Lake_instDecidableEqHash_decEq(v_x_31__boxed_260_, v_x_32__boxed_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
uint8_t l_Lake_instDecidableEqHash(uint64_t v_x_264_, uint64_t v_x_265_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = lean_uint64_dec_eq(v_x_264_, v_x_265_);
return v___x_266_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqHash_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_264_ = stack[0].m_num;
uint64_t v_x_265_ = stack[1].m_num;
uint8_t v_res_267_;
v_res_267_ = l_Lake_instDecidableEqHash(v_x_264_, v_x_265_);
stack->m_num = v_res_267_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash___boxed(lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
uint64_t v_x_6__boxed_270_; uint64_t v_x_7__boxed_271_; uint8_t v_res_272_; lean_object* v_r_273_; 
v_x_6__boxed_270_ = lean_unbox_uint64(v_x_268_);
lean_dec_ref(v_x_268_);
v_x_7__boxed_271_ = lean_unbox_uint64(v_x_269_);
lean_dec_ref(v_x_269_);
v_res_272_ = l_Lake_instDecidableEqHash(v_x_6__boxed_270_, v_x_7__boxed_271_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
uint64_t l_Lake_Hash_instHashable___lam__0(uint64_t v_self_274_){
_start:
{
return v_self_274_;
}
}
LEAN_EXPORT void l_Lake_Hash_instHashable___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_self_274_ = stack[0].m_num;
uint64_t v_res_275_;
v_res_275_ = l_Lake_Hash_instHashable___lam__0(v_self_274_);
stack->m_num = v_res_275_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_instHashable___lam__0___boxed(lean_object* v_self_276_){
_start:
{
uint64_t v_self_boxed_277_; uint64_t v_res_278_; lean_object* v_r_279_; 
v_self_boxed_277_ = lean_unbox_uint64(v_self_276_);
lean_dec_ref(v_self_276_);
v_res_278_ = l_Lake_Hash_instHashable___lam__0(v_self_boxed_277_);
v_r_279_ = lean_box_uint64(v_res_278_);
return v_r_279_;
}
}
static uint64_t _init_l_Lake_Hash_nil(void){
_start:
{
uint64_t v___x_282_; 
v___x_282_ = 1723ULL;
return v___x_282_;
}
}
static uint64_t _init_l_Lake_Hash_instNilTrace(void){
_start:
{
uint64_t v___x_283_; 
v___x_283_ = 1723ULL;
return v___x_283_;
}
}
uint64_t l_Lake_Hash_ofNat(lean_object* v_n_284_){
_start:
{
uint64_t v___x_285_; 
v___x_285_ = lean_uint64_of_nat(v_n_284_);
return v___x_285_;
}
}
LEAN_EXPORT void l_Lake_Hash_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_284_ = stack[0].m_obj;
uint64_t v_res_286_;
v_res_286_ = l_Lake_Hash_ofNat(v_n_284_);
stack->m_num = v_res_286_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofNat___boxed(lean_object* v_n_287_){
_start:
{
uint64_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Lake_Hash_ofNat(v_n_287_);
lean_dec(v_n_287_);
v_r_289_ = lean_box_uint64(v_res_288_);
return v_r_289_;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_nat_to_int(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__3(void){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lean_cstr_to_nat("18446744073709551616");
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object* v_n_299_){
_start:
{
lean_object* v_mantissa_302_; lean_object* v_exponent_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_mantissa_302_ = lean_ctor_get(v_n_299_, 0);
v_exponent_303_ = lean_ctor_get(v_n_299_, 1);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_nat_dec_eq(v_exponent_303_, v___x_304_);
if (v___x_305_ == 0)
{
goto v___jp_300_;
}
else
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__2, &l_Lake_Hash_ofJsonNumber_x3f___closed__2_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2);
v___x_307_ = lean_int_dec_le(v___x_306_, v_mantissa_302_);
if (v___x_307_ == 0)
{
goto v___jp_300_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_308_ = l_Int_toNat(v_mantissa_302_);
v___x_309_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__3, &l_Lake_Hash_ofJsonNumber_x3f___closed__3_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__3);
v___x_310_ = lean_nat_dec_lt(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_dec(v___x_308_);
v___x_311_ = ((lean_object*)(l_Lake_Hash_ofJsonNumber_x3f___closed__5));
return v___x_311_;
}
else
{
uint64_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_uint64_of_nat(v___x_308_);
lean_dec(v___x_308_);
v___x_313_ = lean_box_uint64(v___x_312_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
}
v___jp_300_:
{
lean_object* v___x_301_; 
v___x_301_ = ((lean_object*)(l_Lake_Hash_ofJsonNumber_x3f___closed__1));
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f___boxed(lean_object* v_n_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_315_);
lean_dec_ref(v_n_315_);
return v_res_316_;
}
}
uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(lean_object* v_s_317_, lean_object* v_n_318_, lean_object* v_j_319_, uint64_t v_a_320_){
_start:
{
lean_object* v_zero_321_; uint8_t v_isZero_322_; 
v_zero_321_ = lean_unsigned_to_nat(0u);
v_isZero_322_ = lean_nat_dec_eq(v_j_319_, v_zero_321_);
if (v_isZero_322_ == 1)
{
lean_dec(v_j_319_);
return v_a_320_;
}
else
{
lean_object* v_one_323_; lean_object* v_n_324_; lean_object* v___x_325_; uint8_t v_c_326_; uint8_t v___x_327_; uint8_t v___x_328_; 
v_one_323_ = lean_unsigned_to_nat(1u);
v_n_324_ = lean_nat_sub(v_j_319_, v_one_323_);
v___x_325_ = lean_nat_sub(v_n_318_, v_j_319_);
lean_dec(v_j_319_);
v_c_326_ = lean_string_get_byte_fast(v_s_317_, v___x_325_);
v___x_327_ = 57;
v___x_328_ = lean_uint8_dec_le(v_c_326_, v___x_327_);
if (v___x_328_ == 0)
{
uint8_t v___x_329_; uint8_t v___x_330_; 
v___x_329_ = 97;
v___x_330_ = lean_uint8_dec_le(v___x_329_, v_c_326_);
if (v___x_330_ == 0)
{
uint64_t v___x_331_; uint64_t v___x_332_; uint8_t v___x_333_; uint8_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; 
v___x_331_ = 4ULL;
v___x_332_ = lean_uint64_shift_left(v_a_320_, v___x_331_);
v___x_333_ = 55;
v___x_334_ = lean_uint8_sub(v_c_326_, v___x_333_);
v___x_335_ = lean_uint8_to_uint64(v___x_334_);
v___x_336_ = lean_uint64_add(v___x_332_, v___x_335_);
v_j_319_ = v_n_324_;
v_a_320_ = v___x_336_;
goto _start;
}
else
{
uint64_t v___x_338_; uint64_t v___x_339_; uint8_t v___x_340_; uint8_t v___x_341_; uint64_t v___x_342_; uint64_t v___x_343_; 
v___x_338_ = 4ULL;
v___x_339_ = lean_uint64_shift_left(v_a_320_, v___x_338_);
v___x_340_ = 87;
v___x_341_ = lean_uint8_sub(v_c_326_, v___x_340_);
v___x_342_ = lean_uint8_to_uint64(v___x_341_);
v___x_343_ = lean_uint64_add(v___x_339_, v___x_342_);
v_j_319_ = v_n_324_;
v_a_320_ = v___x_343_;
goto _start;
}
}
else
{
uint64_t v___x_345_; uint64_t v___x_346_; uint8_t v___x_347_; uint8_t v___x_348_; uint64_t v___x_349_; uint64_t v___x_350_; 
v___x_345_ = 4ULL;
v___x_346_ = lean_uint64_shift_left(v_a_320_, v___x_345_);
v___x_347_ = 48;
v___x_348_ = lean_uint8_sub(v_c_326_, v___x_347_);
v___x_349_ = lean_uint8_to_uint64(v___x_348_);
v___x_350_ = lean_uint64_add(v___x_346_, v___x_349_);
v_j_319_ = v_n_324_;
v_a_320_ = v___x_350_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_317_ = stack[0].m_obj;
lean_object* v_n_318_ = stack[1].m_obj;
lean_object* v_j_319_ = stack[2].m_obj;
uint64_t v_a_320_ = stack[3].m_num;
uint64_t v_res_352_;
v_res_352_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_317_, v_n_318_, v_j_319_, v_a_320_);
stack->m_num = v_res_352_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg___boxed(lean_object* v_s_353_, lean_object* v_n_354_, lean_object* v_j_355_, lean_object* v_a_356_){
_start:
{
uint64_t v_a_246__boxed_357_; uint64_t v_res_358_; lean_object* v_r_359_; 
v_a_246__boxed_357_ = lean_unbox_uint64(v_a_356_);
lean_dec_ref(v_a_356_);
v_res_358_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_353_, v_n_354_, v_j_355_, v_a_246__boxed_357_);
lean_dec(v_n_354_);
lean_dec_ref(v_s_353_);
v_r_359_ = lean_box_uint64(v_res_358_);
return v_r_359_;
}
}
uint64_t l_Lake_Hash_ofHex(lean_object* v_s_360_){
_start:
{
lean_object* v___x_361_; uint64_t v___x_362_; uint64_t v___x_363_; 
v___x_361_ = lean_string_utf8_byte_size(v_s_360_);
v___x_362_ = 0ULL;
v___x_363_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_360_, v___x_361_, v___x_361_, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT void l_Lake_Hash_ofHex_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_360_ = stack[0].m_obj;
uint64_t v_res_364_;
v_res_364_ = l_Lake_Hash_ofHex(v_s_360_);
stack->m_num = v_res_364_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex___boxed(lean_object* v_s_365_){
_start:
{
uint64_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Lake_Hash_ofHex(v_s_365_);
lean_dec_ref(v_s_365_);
v_r_367_ = lean_box_uint64(v_res_366_);
return v_r_367_;
}
}
uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(lean_object* v_s_368_, lean_object* v_n_369_, lean_object* v_j_370_, lean_object* v_a_371_, uint64_t v_a_372_){
_start:
{
uint64_t v___x_373_; 
v___x_373_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(v_s_368_, v_n_369_, v_j_370_, v_a_372_);
return v___x_373_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_368_ = stack[0].m_obj;
lean_object* v_n_369_ = stack[1].m_obj;
lean_object* v_j_370_ = stack[2].m_obj;
uint64_t v_a_372_ = stack[4].m_num;
uint64_t v_res_374_;
v_res_374_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(v_s_368_, v_n_369_, v_j_370_, lean_box(0), v_a_372_);
stack->m_num = v_res_374_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___boxed(lean_object* v_s_375_, lean_object* v_n_376_, lean_object* v_j_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
uint64_t v_a_342__boxed_380_; uint64_t v_res_381_; lean_object* v_r_382_; 
v_a_342__boxed_380_ = lean_unbox_uint64(v_a_379_);
lean_dec_ref(v_a_379_);
v_res_381_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(v_s_375_, v_n_376_, v_j_377_, v_a_378_, v_a_342__boxed_380_);
lean_dec(v_n_376_);
lean_dec_ref(v_s_375_);
v_r_382_ = lean_box_uint64(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f(lean_object* v_s_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_384_ = lean_string_utf8_byte_size(v_s_383_);
v___x_385_ = lean_unsigned_to_nat(16u);
v___x_386_ = lean_nat_dec_eq(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
v___x_387_ = lean_box(0);
return v___x_387_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = l_Lake_isHex(v_s_383_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = lean_box(0);
return v___x_389_;
}
else
{
uint64_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = l_Lake_Hash_ofHex(v_s_383_);
v___x_391_ = lean_box_uint64(v___x_390_);
v___x_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f___boxed(lean_object* v_s_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lake_Hash_ofHex_x3f(v_s_393_);
lean_dec_ref(v_s_393_);
return v_res_394_;
}
}
lean_object* l_Lake_Hash_hex(uint64_t v_self_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lake_lowerHexUInt64(v_self_395_);
return v___x_396_;
}
}
LEAN_EXPORT void l_Lake_Hash_hex_0interp(lean_interpreter_value* stack)
{
uint64_t v_self_395_ = stack[0].m_num;
lean_object* v_res_397_;
v_res_397_ = l_Lake_Hash_hex(v_self_395_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_hex___boxed(lean_object* v_self_398_){
_start:
{
uint64_t v_self_boxed_399_; lean_object* v_res_400_; 
v_self_boxed_399_ = lean_unbox_uint64(v_self_398_);
lean_dec_ref(v_self_398_);
v_res_400_ = l_Lake_Hash_hex(v_self_boxed_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofDecimal_x3f(lean_object* v_s_401_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = lean_string_utf8_byte_size(v_s_401_);
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v_s_401_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
lean_ctor_set(v___x_404_, 2, v___x_403_);
v___x_405_ = l_String_Slice_toNat_x3f(v___x_404_);
lean_dec_ref_known(v___x_404_, 3);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_406_; 
v___x_406_ = lean_box(0);
return v___x_406_;
}
else
{
lean_object* v_val_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_416_; 
v_val_407_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_416_ == 0)
{
v___x_409_ = v___x_405_;
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_val_407_);
lean_dec(v___x_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
uint64_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_411_ = lean_uint64_of_nat(v_val_407_);
lean_dec(v_val_407_);
v___x_412_ = lean_box_uint64(v___x_411_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_412_);
v___x_414_ = v___x_409_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f(lean_object* v_s_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lake_Hash_ofHex_x3f(v_s_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f___boxed(lean_object* v_s_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lake_Hash_ofString_x3f(v_s_419_);
lean_dec_ref(v_s_419_);
return v_res_420_;
}
}
lean_object* l_Lake_Hash_load_x3f(lean_object* v_hashFile_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_IO_FS_readFile(v_hashFile_421_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
v___x_425_ = l_Lake_Hash_ofHex_x3f(v_a_424_);
lean_dec(v_a_424_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; 
lean_dec_ref_known(v___x_423_, 1);
v___x_426_ = lean_box(0);
return v___x_426_;
}
}
}
LEAN_EXPORT void l_Lake_Hash_load_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_hashFile_421_ = stack[0].m_obj;
lean_object* v_res_427_;
v_res_427_ = l_Lake_Hash_load_x3f(v_hashFile_421_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f___boxed(lean_object* v_hashFile_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lake_Hash_load_x3f(v_hashFile_428_);
lean_dec_ref(v_hashFile_428_);
return v_res_430_;
}
}
uint64_t l_Lake_Hash_mix(uint64_t v_h1_431_, uint64_t v_h2_432_){
_start:
{
uint64_t v___x_433_; 
v___x_433_ = lean_uint64_mix_hash(v_h1_431_, v_h2_432_);
return v___x_433_;
}
}
LEAN_EXPORT void l_Lake_Hash_mix_0interp(lean_interpreter_value* stack)
{
uint64_t v_h1_431_ = stack[0].m_num;
uint64_t v_h2_432_ = stack[1].m_num;
uint64_t v_res_434_;
v_res_434_ = l_Lake_Hash_mix(v_h1_431_, v_h2_432_);
stack->m_num = v_res_434_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_mix___boxed(lean_object* v_h1_435_, lean_object* v_h2_436_){
_start:
{
uint64_t v_h1_boxed_437_; uint64_t v_h2_boxed_438_; uint64_t v_res_439_; lean_object* v_r_440_; 
v_h1_boxed_437_ = lean_unbox_uint64(v_h1_435_);
lean_dec_ref(v_h1_435_);
v_h2_boxed_438_ = lean_unbox_uint64(v_h2_436_);
lean_dec_ref(v_h2_436_);
v_res_439_ = l_Lake_Hash_mix(v_h1_boxed_437_, v_h2_boxed_438_);
v_r_440_ = lean_box_uint64(v_res_439_);
return v_r_440_;
}
}
lean_object* l_Lake_Hash_toString(uint64_t v_self_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lake_lowerHexUInt64(v_self_443_);
return v___x_444_;
}
}
LEAN_EXPORT void l_Lake_Hash_toString_0interp(lean_interpreter_value* stack)
{
uint64_t v_self_443_ = stack[0].m_num;
lean_object* v_res_445_;
v_res_445_ = l_Lake_Hash_toString(v_self_443_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_toString___boxed(lean_object* v_self_446_){
_start:
{
uint64_t v_self_boxed_447_; lean_object* v_res_448_; 
v_self_boxed_447_ = lean_unbox_uint64(v_self_446_);
lean_dec_ref(v_self_446_);
v_res_448_ = l_Lake_Hash_toString(v_self_boxed_447_);
return v_res_448_;
}
}
uint64_t l_Lake_Hash_ofHashable___redArg(lean_object* v_inst_451_, lean_object* v_a_452_){
_start:
{
uint64_t v___x_453_; lean_object* v___x_454_; uint64_t v___x_455_; uint64_t v___x_456_; 
v___x_453_ = 1723ULL;
v___x_454_ = lean_apply_1(v_inst_451_, v_a_452_);
v___x_455_ = lean_unbox_uint64(v___x_454_);
lean_dec_ref(v___x_454_);
v___x_456_ = lean_uint64_mix_hash(v___x_453_, v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT void l_Lake_Hash_ofHashable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_451_ = stack[0].m_obj;
lean_object* v_a_452_ = stack[1].m_obj;
uint64_t v_res_457_;
v_res_457_ = l_Lake_Hash_ofHashable___redArg(v_inst_451_, v_a_452_);
stack->m_num = v_res_457_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHashable___redArg___boxed(lean_object* v_inst_458_, lean_object* v_a_459_){
_start:
{
uint64_t v_res_460_; lean_object* v_r_461_; 
v_res_460_ = l_Lake_Hash_ofHashable___redArg(v_inst_458_, v_a_459_);
v_r_461_ = lean_box_uint64(v_res_460_);
return v_r_461_;
}
}
uint64_t l_Lake_Hash_ofHashable(lean_object* v_00_u03b1_462_, lean_object* v_inst_463_, lean_object* v_a_464_){
_start:
{
uint64_t v___x_465_; lean_object* v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; 
v___x_465_ = 1723ULL;
v___x_466_ = lean_apply_1(v_inst_463_, v_a_464_);
v___x_467_ = lean_unbox_uint64(v___x_466_);
lean_dec_ref(v___x_466_);
v___x_468_ = lean_uint64_mix_hash(v___x_465_, v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT void l_Lake_Hash_ofHashable_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_463_ = stack[1].m_obj;
lean_object* v_a_464_ = stack[2].m_obj;
uint64_t v_res_469_;
v_res_469_ = l_Lake_Hash_ofHashable(lean_box(0), v_inst_463_, v_a_464_);
stack->m_num = v_res_469_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHashable___boxed(lean_object* v_00_u03b1_470_, lean_object* v_inst_471_, lean_object* v_a_472_){
_start:
{
uint64_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l_Lake_Hash_ofHashable(v_00_u03b1_470_, v_inst_471_, v_a_472_);
v_r_474_ = lean_box_uint64(v_res_473_);
return v_r_474_;
}
}
uint64_t l_Lake_Hash_ofString(lean_object* v_str_475_){
_start:
{
uint64_t v___x_476_; uint64_t v___x_477_; uint64_t v___x_478_; 
v___x_476_ = 1723ULL;
v___x_477_ = lean_string_hash(v_str_475_);
v___x_478_ = lean_uint64_mix_hash(v___x_476_, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT void l_Lake_Hash_ofString_0interp(lean_interpreter_value* stack)
{
lean_object* v_str_475_ = stack[0].m_obj;
uint64_t v_res_479_;
v_res_479_ = l_Lake_Hash_ofString(v_str_475_);
stack->m_num = v_res_479_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString___boxed(lean_object* v_str_480_){
_start:
{
uint64_t v_res_481_; lean_object* v_r_482_; 
v_res_481_ = l_Lake_Hash_ofString(v_str_480_);
lean_dec_ref(v_str_480_);
v_r_482_ = lean_box_uint64(v_res_481_);
return v_r_482_;
}
}
uint64_t l_Lake_Hash_ofText(lean_object* v_str_483_){
_start:
{
lean_object* v___x_484_; uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v___x_487_; 
v___x_484_ = l_String_crlfToLf(v_str_483_);
v___x_485_ = 1723ULL;
v___x_486_ = lean_string_hash(v___x_484_);
lean_dec_ref(v___x_484_);
v___x_487_ = lean_uint64_mix_hash(v___x_485_, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT void l_Lake_Hash_ofText_0interp(lean_interpreter_value* stack)
{
lean_object* v_str_483_ = stack[0].m_obj;
uint64_t v_res_488_;
v_res_488_ = l_Lake_Hash_ofText(v_str_483_);
stack->m_num = v_res_488_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofText___boxed(lean_object* v_str_489_){
_start:
{
uint64_t v_res_490_; lean_object* v_r_491_; 
v_res_490_ = l_Lake_Hash_ofText(v_str_489_);
lean_dec_ref(v_str_489_);
v_r_491_ = lean_box_uint64(v_res_490_);
return v_r_491_;
}
}
uint64_t l_Lake_Hash_ofByteArray(lean_object* v_bytes_492_){
_start:
{
uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v___x_495_; 
v___x_493_ = 1723ULL;
v___x_494_ = lean_byte_array_hash(v_bytes_492_);
v___x_495_ = lean_uint64_mix_hash(v___x_493_, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT void l_Lake_Hash_ofByteArray_0interp(lean_interpreter_value* stack)
{
lean_object* v_bytes_492_ = stack[0].m_obj;
uint64_t v_res_496_;
v_res_496_ = l_Lake_Hash_ofByteArray(v_bytes_492_);
stack->m_num = v_res_496_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofByteArray___boxed(lean_object* v_bytes_497_){
_start:
{
uint64_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_Lake_Hash_ofByteArray(v_bytes_497_);
lean_dec_ref(v_bytes_497_);
v_r_499_ = lean_box_uint64(v_res_498_);
return v_r_499_;
}
}
uint64_t l_Lake_Hash_ofBool(uint8_t v_b_500_){
_start:
{
if (v_b_500_ == 0)
{
uint64_t v___x_501_; 
v___x_501_ = 18370132993254720638ULL;
return v___x_501_;
}
else
{
uint64_t v___x_502_; 
v___x_502_ = 8507242618548079515ULL;
return v___x_502_;
}
}
}
LEAN_EXPORT void l_Lake_Hash_ofBool_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_500_ = stack[0].m_num;
uint64_t v_res_503_;
v_res_503_ = l_Lake_Hash_ofBool(v_b_500_);
stack->m_num = v_res_503_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofBool___boxed(lean_object* v_b_504_){
_start:
{
uint8_t v_b_boxed_505_; uint64_t v_res_506_; lean_object* v_r_507_; 
v_b_boxed_505_ = lean_unbox(v_b_504_);
v_res_506_ = l_Lake_Hash_ofBool(v_b_boxed_505_);
v_r_507_ = lean_box_uint64(v_res_506_);
return v_r_507_;
}
}
lean_object* l_Lake_Hash_toJson(uint64_t v_self_508_){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = l_Lake_lowerHexUInt64(v_self_508_);
v___x_510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT void l_Lake_Hash_toJson_0interp(lean_interpreter_value* stack)
{
uint64_t v_self_508_ = stack[0].m_num;
lean_object* v_res_511_;
v_res_511_ = l_Lake_Hash_toJson(v_self_508_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson___boxed(lean_object* v_self_512_){
_start:
{
uint64_t v_self_boxed_513_; lean_object* v_res_514_; 
v_self_boxed_513_ = lean_unbox_uint64(v_self_512_);
lean_dec_ref(v_self_512_);
v_res_514_ = l_Lake_Hash_toJson(v_self_boxed_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_fromJson_x3f(lean_object* v_json_527_){
_start:
{
switch(lean_obj_tag(v_json_527_))
{
case 3:
{
lean_object* v_s_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_543_; 
v_s_528_ = lean_ctor_get(v_json_527_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v_json_527_);
if (v_isSharedCheck_543_ == 0)
{
v___x_530_ = v_json_527_;
v_isShared_531_ = v_isSharedCheck_543_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_s_528_);
lean_dec(v_json_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_543_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
uint8_t v___x_532_; 
v___x_532_ = l_Lake_isHex(v_s_528_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; 
lean_del_object(v___x_530_);
lean_dec_ref(v_s_528_);
v___x_533_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__1));
return v___x_533_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_534_ = lean_string_utf8_byte_size(v_s_528_);
v___x_535_ = lean_unsigned_to_nat(16u);
v___x_536_ = lean_nat_dec_eq(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_del_object(v___x_530_);
lean_dec_ref(v_s_528_);
v___x_537_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__3));
return v___x_537_;
}
else
{
uint64_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_538_ = l_Lake_Hash_ofHex(v_s_528_);
lean_dec_ref(v_s_528_);
v___x_539_ = lean_box_uint64(v___x_538_);
if (v_isShared_531_ == 0)
{
lean_ctor_set_tag(v___x_530_, 1);
lean_ctor_set(v___x_530_, 0, v___x_539_);
v___x_541_ = v___x_530_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
case 2:
{
lean_object* v_n_544_; lean_object* v___x_545_; 
v_n_544_ = lean_ctor_get(v_json_527_, 0);
lean_inc_ref(v_n_544_);
lean_dec_ref_known(v_json_527_, 1);
v___x_545_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_544_);
lean_dec_ref(v_n_544_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_555_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_555_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_555_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_555_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_550_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__4));
v___x_551_ = lean_string_append(v___x_550_, v_a_546_);
lean_dec(v_a_546_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_551_);
v___x_553_ = v___x_548_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
return v___x_545_;
}
}
default: 
{
lean_object* v___x_556_; 
lean_dec(v_json_527_);
v___x_556_ = ((lean_object*)(l_Lake_Hash_fromJson_x3f___closed__6));
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg(lean_object* v_inst_559_){
_start:
{
lean_inc(v_inst_559_);
return v_inst_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg___boxed(lean_object* v_inst_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lake_instComputeTraceHashOfComputeHash___redArg(v_inst_560_);
lean_dec(v_inst_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash(lean_object* v_00_u03b1_562_, lean_object* v_m_563_, lean_object* v_inst_564_){
_start:
{
lean_inc(v_inst_564_);
return v_inst_564_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___boxed(lean_object* v_00_u03b1_565_, lean_object* v_m_566_, lean_object* v_inst_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lake_instComputeTraceHashOfComputeHash(v_00_u03b1_565_, v_m_566_, v_inst_567_);
lean_dec(v_inst_567_);
return v_res_568_;
}
}
uint64_t l_Lake_pureHash___redArg(lean_object* v_inst_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_571_; uint64_t v___x_572_; 
v___x_571_ = lean_apply_1(v_inst_569_, v_a_570_);
v___x_572_ = lean_unbox_uint64(v___x_571_);
lean_dec_ref(v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT void l_Lake_pureHash___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_569_ = stack[0].m_obj;
lean_object* v_a_570_ = stack[1].m_obj;
uint64_t v_res_573_;
v_res_573_ = l_Lake_pureHash___redArg(v_inst_569_, v_a_570_);
stack->m_num = v_res_573_;
}
LEAN_EXPORT lean_object* l_Lake_pureHash___redArg___boxed(lean_object* v_inst_574_, lean_object* v_a_575_){
_start:
{
uint64_t v_res_576_; lean_object* v_r_577_; 
v_res_576_ = l_Lake_pureHash___redArg(v_inst_574_, v_a_575_);
v_r_577_ = lean_box_uint64(v_res_576_);
return v_r_577_;
}
}
uint64_t l_Lake_pureHash(lean_object* v_00_u03b1_578_, lean_object* v_inst_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_581_; uint64_t v___x_582_; 
v___x_581_ = lean_apply_1(v_inst_579_, v_a_580_);
v___x_582_ = lean_unbox_uint64(v___x_581_);
lean_dec_ref(v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT void l_Lake_pureHash_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_579_ = stack[1].m_obj;
lean_object* v_a_580_ = stack[2].m_obj;
uint64_t v_res_583_;
v_res_583_ = l_Lake_pureHash(lean_box(0), v_inst_579_, v_a_580_);
stack->m_num = v_res_583_;
}
LEAN_EXPORT lean_object* l_Lake_pureHash___boxed(lean_object* v_00_u03b1_584_, lean_object* v_inst_585_, lean_object* v_a_586_){
_start:
{
uint64_t v_res_587_; lean_object* v_r_588_; 
v_res_587_ = l_Lake_pureHash(v_00_u03b1_584_, v_inst_585_, v_a_586_);
v_r_588_ = lean_box_uint64(v_res_587_);
return v_r_588_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash___redArg(lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_apply_1(v_inst_589_, v_a_591_);
v___x_593_ = lean_apply_2(v_inst_590_, lean_box(0), v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash(lean_object* v_00_u03b1_594_, lean_object* v_m_595_, lean_object* v_n_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_a_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_apply_1(v_inst_597_, v_a_599_);
v___x_601_ = lean_apply_2(v_inst_598_, lean_box(0), v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashIdOfHashable___redArg(lean_object* v_inst_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_alloc_closure((void*)(l_Lake_Hash_ofHashable___boxed), 3, 2);
lean_closure_set(v___x_603_, 0, lean_box(0));
lean_closure_set(v___x_603_, 1, v_inst_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashIdOfHashable(lean_object* v_00_u03b1_604_, lean_object* v_inst_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = lean_alloc_closure((void*)(l_Lake_Hash_ofHashable___boxed), 3, 2);
lean_closure_set(v___x_606_, 0, lean_box(0));
lean_closure_set(v___x_606_, 1, v_inst_605_);
return v___x_606_;
}
}
lean_object* l_Lake_computeBinFileHash(lean_object* v_file_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_IO_FS_readBinFile(v_file_607_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_621_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_621_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_621_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_621_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
uint64_t v___x_614_; uint64_t v___x_615_; uint64_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_614_ = 1723ULL;
v___x_615_ = lean_byte_array_hash(v_a_610_);
lean_dec(v_a_610_);
v___x_616_ = lean_uint64_mix_hash(v___x_614_, v___x_615_);
v___x_617_ = lean_box_uint64(v___x_616_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_617_);
v___x_619_ = v___x_612_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
v_a_622_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_609_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_609_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_computeBinFileHash_0interp(lean_interpreter_value* stack)
{
lean_object* v_file_607_ = stack[0].m_obj;
lean_object* v_res_630_;
v_res_630_ = l_Lake_computeBinFileHash(v_file_607_);
stack->m_obj
 = v_res_630_;
}
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash___boxed(lean_object* v_file_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lake_computeBinFileHash(v_file_631_);
lean_dec_ref(v_file_631_);
return v_res_633_;
}
}
lean_object* l_Lake_computeTextFileHash(lean_object* v_file_636_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_IO_FS_readFile(v_file_636_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_651_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_651_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_651_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_651_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; uint64_t v___x_644_; uint64_t v___x_645_; uint64_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_643_ = l_String_crlfToLf(v_a_639_);
lean_dec(v_a_639_);
v___x_644_ = 1723ULL;
v___x_645_ = lean_string_hash(v___x_643_);
lean_dec_ref(v___x_643_);
v___x_646_ = lean_uint64_mix_hash(v___x_644_, v___x_645_);
v___x_647_ = lean_box_uint64(v___x_646_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_647_);
v___x_649_ = v___x_641_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
v_a_652_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_638_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_638_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_computeTextFileHash_0interp(lean_interpreter_value* stack)
{
lean_object* v_file_636_ = stack[0].m_obj;
lean_object* v_res_660_;
v_res_660_ = l_Lake_computeTextFileHash(v_file_636_);
stack->m_obj
 = v_res_660_;
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash___boxed(lean_object* v_file_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lake_computeTextFileHash(v_file_661_);
lean_dec_ref(v_file_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0(lean_object* v_x_664_){
_start:
{
lean_inc_ref(v_x_664_);
return v_x_664_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0___boxed(lean_object* v_x_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lake_instCoeTextFilePathFilePath___lam__0(v_x_665_);
lean_dec_ref(v_x_665_);
return v_res_666_;
}
}
lean_object* l_Lake_computeFileHash(lean_object* v_file_672_, uint8_t v_text_673_){
_start:
{
if (v_text_673_ == 0)
{
lean_object* v___x_675_; 
v___x_675_ = l_Lake_computeBinFileHash(v_file_672_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = l_Lake_computeTextFileHash(v_file_672_);
return v___x_676_;
}
}
}
LEAN_EXPORT void l_Lake_computeFileHash_0interp(lean_interpreter_value* stack)
{
lean_object* v_file_672_ = stack[0].m_obj;
uint8_t v_text_673_ = stack[1].m_num;
lean_object* v_res_677_;
v_res_677_ = l_Lake_computeFileHash(v_file_672_, v_text_673_);
stack->m_obj
 = v_res_677_;
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash___boxed(lean_object* v_file_678_, lean_object* v_text_679_, lean_object* v_a_680_){
_start:
{
uint8_t v_text_boxed_681_; lean_object* v_res_682_; 
v_text_boxed_681_ = lean_unbox(v_text_679_);
v_res_682_ = l_Lake_computeFileHash(v_file_678_, v_text_boxed_681_);
lean_dec_ref(v_file_678_);
return v_res_682_;
}
}
lean_object* l_Lake_computeArrayHash___redArg___lam__0(uint64_t v_ts_683_, lean_object* v_toPure_684_, uint64_t v_____do__lift_685_){
_start:
{
uint64_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_uint64_mix_hash(v_ts_683_, v_____do__lift_685_);
v___x_687_ = lean_box_uint64(v___x_686_);
v___x_688_ = lean_apply_2(v_toPure_684_, lean_box(0), v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT void l_Lake_computeArrayHash___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_ts_683_ = stack[0].m_num;
lean_object* v_toPure_684_ = stack[1].m_obj;
uint64_t v_____do__lift_685_ = stack[2].m_num;
lean_object* v_res_689_;
v_res_689_ = l_Lake_computeArrayHash___redArg___lam__0(v_ts_683_, v_toPure_684_, v_____do__lift_685_);
stack->m_obj
 = v_res_689_;
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0___boxed(lean_object* v_ts_690_, lean_object* v_toPure_691_, lean_object* v_____do__lift_692_){
_start:
{
uint64_t v_ts_boxed_693_; uint64_t v_____do__lift_88__boxed_694_; lean_object* v_res_695_; 
v_ts_boxed_693_ = lean_unbox_uint64(v_ts_690_);
lean_dec_ref(v_ts_690_);
v_____do__lift_88__boxed_694_ = lean_unbox_uint64(v_____do__lift_692_);
lean_dec_ref(v_____do__lift_692_);
v_res_695_ = l_Lake_computeArrayHash___redArg___lam__0(v_ts_boxed_693_, v_toPure_691_, v_____do__lift_88__boxed_694_);
return v_res_695_;
}
}
lean_object* l_Lake_computeArrayHash___redArg___lam__1(lean_object* v_toPure_696_, lean_object* v_inst_697_, lean_object* v_toBind_698_, uint64_t v_ts_699_, lean_object* v_t_700_){
_start:
{
lean_object* v___x_701_; lean_object* v___f_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_701_ = lean_box_uint64(v_ts_699_);
v___f_702_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_702_, 0, v___x_701_);
lean_closure_set(v___f_702_, 1, v_toPure_696_);
v___x_703_ = lean_apply_1(v_inst_697_, v_t_700_);
v___x_704_ = lean_apply_4(v_toBind_698_, lean_box(0), lean_box(0), v___x_703_, v___f_702_);
return v___x_704_;
}
}
LEAN_EXPORT void l_Lake_computeArrayHash___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_696_ = stack[0].m_obj;
lean_object* v_inst_697_ = stack[1].m_obj;
lean_object* v_toBind_698_ = stack[2].m_obj;
uint64_t v_ts_699_ = stack[3].m_num;
lean_object* v_t_700_ = stack[4].m_obj;
lean_object* v_res_705_;
v_res_705_ = l_Lake_computeArrayHash___redArg___lam__1(v_toPure_696_, v_inst_697_, v_toBind_698_, v_ts_699_, v_t_700_);
stack->m_obj
 = v_res_705_;
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1___boxed(lean_object* v_toPure_706_, lean_object* v_inst_707_, lean_object* v_toBind_708_, lean_object* v_ts_709_, lean_object* v_t_710_){
_start:
{
uint64_t v_ts_boxed_711_; lean_object* v_res_712_; 
v_ts_boxed_711_ = lean_unbox_uint64(v_ts_709_);
lean_dec_ref(v_ts_709_);
v_res_712_ = l_Lake_computeArrayHash___redArg___lam__1(v_toPure_706_, v_inst_707_, v_toBind_708_, v_ts_boxed_711_, v_t_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg(lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_as_717_){
_start:
{
lean_object* v_toApplicative_718_; lean_object* v_toBind_719_; lean_object* v_toPure_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_toApplicative_718_ = lean_ctor_get(v_inst_716_, 0);
v_toBind_719_ = lean_ctor_get(v_inst_716_, 1);
v_toPure_720_ = lean_ctor_get(v_toApplicative_718_, 1);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = lean_array_get_size(v_as_717_);
v___x_723_ = lean_nat_dec_lt(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_inc(v_toPure_720_);
lean_dec_ref(v_as_717_);
lean_dec_ref(v_inst_716_);
lean_dec(v_inst_715_);
v___x_724_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_725_ = lean_apply_2(v_toPure_720_, lean_box(0), v___x_724_);
return v___x_725_;
}
else
{
lean_object* v___f_726_; size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_inc(v_toBind_719_);
lean_inc(v_toPure_720_);
v___f_726_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_726_, 0, v_toPure_720_);
lean_closure_set(v___f_726_, 1, v_inst_715_);
lean_closure_set(v___f_726_, 2, v_toBind_719_);
v___x_727_ = ((size_t)0ULL);
v___x_728_ = lean_usize_of_nat(v___x_722_);
v___x_729_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_716_, v___f_726_, v_as_717_, v___x_727_, v___x_728_, v___x_729_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash(lean_object* v_00_u03b1_731_, lean_object* v_m_732_, lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_as_735_){
_start:
{
lean_object* v_toApplicative_736_; lean_object* v_toBind_737_; lean_object* v_toPure_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_toApplicative_736_ = lean_ctor_get(v_inst_734_, 0);
v_toBind_737_ = lean_ctor_get(v_inst_734_, 1);
v_toPure_738_ = lean_ctor_get(v_toApplicative_736_, 1);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_array_get_size(v_as_735_);
v___x_741_ = lean_nat_dec_lt(v___x_739_, v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
lean_inc(v_toPure_738_);
lean_dec_ref(v_as_735_);
lean_dec_ref(v_inst_734_);
lean_dec(v_inst_733_);
v___x_742_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_743_ = lean_apply_2(v_toPure_738_, lean_box(0), v___x_742_);
return v___x_743_;
}
else
{
lean_object* v___f_744_; size_t v___x_745_; size_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
lean_inc(v_toBind_737_);
lean_inc(v_toPure_738_);
v___f_744_ = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_744_, 0, v_toPure_738_);
lean_closure_set(v___f_744_, 1, v_inst_733_);
lean_closure_set(v___f_744_, 2, v_toBind_737_);
v___x_745_ = ((size_t)0ULL);
v___x_746_ = lean_usize_of_nat(v___x_740_);
v___x_747_ = ((lean_object*)(l_Lake_computeArrayHash___redArg___boxed__const__1));
v___x_748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_734_, v___f_744_, v_as_735_, v___x_745_, v___x_746_, v___x_747_);
return v___x_748_;
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
v___x_758_ = lean_obj_once(&l_Lake_Hash_ofJsonNumber_x3f___closed__2, &l_Lake_Hash_ofJsonNumber_x3f___closed__2_once, _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2);
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
uint8_t l_Lake_MTime_instBEq___aux__1(lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = l_IO_FS_instBEqSystemTime_beq(v_x_761_, v_x_762_);
return v___x_763_;
}
}
LEAN_EXPORT void l_Lake_MTime_instBEq___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_761_ = stack[0].m_obj;
lean_object* v_x_762_ = stack[1].m_obj;
uint8_t v_res_764_;
v_res_764_ = l_Lake_MTime_instBEq___aux__1(v_x_761_, v_x_762_);
stack->m_num = v_res_764_;
}
LEAN_EXPORT lean_object* l_Lake_MTime_instBEq___aux__1___boxed(lean_object* v_x_765_, lean_object* v_x_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l_Lake_MTime_instBEq___aux__1(v_x_765_, v_x_766_);
lean_dec_ref(v_x_766_);
lean_dec_ref(v_x_765_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___redArg(lean_object* v_x_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___redArg___boxed(lean_object* v_x_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lake_MTime_instRepr___aux__1___redArg(v_x_773_);
lean_dec_ref(v_x_773_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1(lean_object* v_x_775_, lean_object* v_prec_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___boxed(lean_object* v_x_778_, lean_object* v_prec_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lake_MTime_instRepr___aux__1(v_x_778_, v_prec_779_);
lean_dec(v_prec_779_);
lean_dec_ref(v_x_778_);
return v_res_780_;
}
}
uint8_t l_Lake_MTime_instOrd___aux__1(lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = l_IO_FS_instOrdSystemTime_ord(v_x_783_, v_x_784_);
return v___x_785_;
}
}
LEAN_EXPORT void l_Lake_MTime_instOrd___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_783_ = stack[0].m_obj;
lean_object* v_x_784_ = stack[1].m_obj;
uint8_t v_res_786_;
v_res_786_ = l_Lake_MTime_instOrd___aux__1(v_x_783_, v_x_784_);
stack->m_num = v_res_786_;
}
LEAN_EXPORT lean_object* l_Lake_MTime_instOrd___aux__1___boxed(lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_Lake_MTime_instOrd___aux__1(v_x_787_, v_x_788_);
lean_dec_ref(v_x_788_);
lean_dec_ref(v_x_787_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
static lean_object* _init_l_Lake_MTime_instLT(void){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = lean_box(0);
return v___x_793_;
}
}
static lean_object* _init_l_Lake_MTime_instLE(void){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = lean_box(0);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0(lean_object* v_x_795_, lean_object* v_y_796_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = l_IO_FS_instOrdSystemTime_ord(v_x_795_, v_y_796_);
if (v___x_797_ == 2)
{
lean_inc_ref(v_y_796_);
return v_y_796_;
}
else
{
lean_inc_ref(v_x_795_);
return v_x_795_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0___boxed(lean_object* v_x_798_, lean_object* v_y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lake_MTime_instMin___lam__0(v_x_798_, v_y_799_);
lean_dec_ref(v_y_799_);
lean_dec_ref(v_x_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0(lean_object* v_x_803_, lean_object* v_y_804_){
_start:
{
uint8_t v___x_805_; 
v___x_805_ = l_IO_FS_instOrdSystemTime_ord(v_x_803_, v_y_804_);
if (v___x_805_ == 2)
{
lean_inc_ref(v_x_803_);
return v_x_803_;
}
else
{
lean_inc_ref(v_y_804_);
return v_y_804_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0___boxed(lean_object* v_x_806_, lean_object* v_y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lake_MTime_instMax___lam__0(v_x_806_, v_y_807_);
lean_dec_ref(v_y_807_);
lean_dec_ref(v_x_806_);
return v_res_808_;
}
}
static lean_object* _init_l_Lake_MTime_instNilTrace(void){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(lean_object* v_inst_813_){
_start:
{
lean_inc_ref(v_inst_813_);
return v_inst_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(lean_object* v_inst_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(v_inst_814_);
lean_dec_ref(v_inst_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(lean_object* v_00_u03b1_816_, lean_object* v_inst_817_){
_start:
{
lean_inc_ref(v_inst_817_);
return v_inst_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___boxed(lean_object* v_00_u03b1_818_, lean_object* v_inst_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(v_00_u03b1_818_, v_inst_819_);
lean_dec_ref(v_inst_819_);
return v_res_820_;
}
}
lean_object* l_Lake_getFileMTime(lean_object* v_file_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = lean_io_metadata(v_file_821_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_832_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_832_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_832_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_832_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_modified_828_; lean_object* v___x_830_; 
v_modified_828_ = lean_ctor_get(v_a_824_, 1);
lean_inc_ref(v_modified_828_);
lean_dec(v_a_824_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v_modified_828_);
v___x_830_ = v___x_826_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_modified_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v_a_833_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_823_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_823_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_getFileMTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_file_821_ = stack[0].m_obj;
lean_object* v_res_841_;
v_res_841_ = l_Lake_getFileMTime(v_file_821_);
stack->m_obj
 = v_res_841_;
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime___boxed(lean_object* v_file_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lake_getFileMTime(v_file_842_);
lean_dec_ref(v_file_842_);
return v_res_844_;
}
}
lean_object* l_Lake_instGetMTimeTextFilePath___lam__0(lean_object* v_x_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_io_metadata(v_x_847_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_858_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_858_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_858_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_858_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_modified_854_; lean_object* v___x_856_; 
v_modified_854_ = lean_ctor_get(v_a_850_, 1);
lean_inc_ref(v_modified_854_);
lean_dec(v_a_850_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v_modified_854_);
v___x_856_ = v___x_852_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_modified_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
v_a_859_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_849_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_849_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instGetMTimeTextFilePath___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_847_ = stack[0].m_obj;
lean_object* v_res_867_;
v_res_867_ = l_Lake_instGetMTimeTextFilePath___lam__0(v_x_847_);
stack->m_obj
 = v_res_867_;
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0___boxed(lean_object* v_x_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lake_instGetMTimeTextFilePath___lam__0(v_x_868_);
lean_dec_ref(v_x_868_);
return v_res_870_;
}
}
uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object* v_inst_873_, lean_object* v_info_874_, lean_object* v_self_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = lean_apply_2(v_inst_873_, v_info_874_, lean_box(0));
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; uint8_t v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
v___x_879_ = l_IO_FS_instOrdSystemTime_ord(v_self_875_, v_a_878_);
lean_dec(v_a_878_);
if (v___x_879_ == 0)
{
uint8_t v___x_880_; 
v___x_880_ = 1;
return v___x_880_;
}
else
{
uint8_t v___x_881_; 
v___x_881_ = 0;
return v___x_881_;
}
}
else
{
uint8_t v___x_882_; 
lean_dec_ref_known(v___x_877_, 1);
v___x_882_ = 0;
return v___x_882_;
}
}
}
LEAN_EXPORT void l_Lake_MTime_checkUpToDate___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_873_ = stack[0].m_obj;
lean_object* v_info_874_ = stack[1].m_obj;
lean_object* v_self_875_ = stack[2].m_obj;
uint8_t v_res_883_;
v_res_883_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_873_, v_info_874_, v_self_875_);
stack->m_num = v_res_883_;
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___redArg___boxed(lean_object* v_inst_884_, lean_object* v_info_885_, lean_object* v_self_886_, lean_object* v_a_887_){
_start:
{
uint8_t v_res_888_; lean_object* v_r_889_; 
v_res_888_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_884_, v_info_885_, v_self_886_);
lean_dec_ref(v_self_886_);
v_r_889_ = lean_box(v_res_888_);
return v_r_889_;
}
}
uint8_t l_Lake_MTime_checkUpToDate(lean_object* v_i_890_, lean_object* v_inst_891_, lean_object* v_info_892_, lean_object* v_self_893_){
_start:
{
uint8_t v___x_895_; 
v___x_895_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_891_, v_info_892_, v_self_893_);
return v___x_895_;
}
}
LEAN_EXPORT void l_Lake_MTime_checkUpToDate_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_891_ = stack[1].m_obj;
lean_object* v_info_892_ = stack[2].m_obj;
lean_object* v_self_893_ = stack[3].m_obj;
uint8_t v_res_896_;
v_res_896_ = l_Lake_MTime_checkUpToDate(lean_box(0), v_inst_891_, v_info_892_, v_self_893_);
stack->m_num = v_res_896_;
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___boxed(lean_object* v_i_897_, lean_object* v_inst_898_, lean_object* v_info_899_, lean_object* v_self_900_, lean_object* v_a_901_){
_start:
{
uint8_t v_res_902_; lean_object* v_r_903_; 
v_res_902_ = l_Lake_MTime_checkUpToDate(v_i_897_, v_inst_898_, v_info_899_, v_self_900_);
lean_dec_ref(v_self_900_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_unsigned_to_nat(11u);
v___x_914_ = lean_nat_to_int(v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_unsigned_to_nat(10u);
v___x_922_ = lean_nat_to_int(v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(lean_object* v_x_926_, lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
if (lean_obj_tag(v_x_928_) == 0)
{
lean_dec(v_x_926_);
return v_x_927_;
}
else
{
lean_object* v_head_929_; lean_object* v_tail_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_940_; 
v_head_929_ = lean_ctor_get(v_x_928_, 0);
v_tail_930_ = lean_ctor_get(v_x_928_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v_x_928_);
if (v_isSharedCheck_940_ == 0)
{
v___x_932_ = v_x_928_;
v_isShared_933_ = v_isSharedCheck_940_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_tail_930_);
lean_inc(v_head_929_);
lean_dec(v_x_928_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_940_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
lean_inc(v_x_926_);
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 5);
lean_ctor_set(v___x_932_, 1, v_x_926_);
lean_ctor_set(v___x_932_, 0, v_x_927_);
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_x_927_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_x_926_);
v___x_935_ = v_reuseFailAlloc_939_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_929_);
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(v_x_926_, v___x_937_, v_tail_930_);
return v___x_938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
if (lean_obj_tag(v_x_941_) == 0)
{
lean_object* v___x_943_; 
lean_dec(v_x_942_);
v___x_943_ = lean_box(0);
return v___x_943_;
}
else
{
lean_object* v_tail_944_; 
v_tail_944_ = lean_ctor_get(v_x_941_, 1);
if (lean_obj_tag(v_tail_944_) == 0)
{
lean_object* v_head_945_; lean_object* v___x_946_; 
lean_dec(v_x_942_);
v_head_945_ = lean_ctor_get(v_x_941_, 0);
lean_inc(v_head_945_);
lean_dec_ref_known(v_x_941_, 2);
v___x_946_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_945_);
return v___x_946_;
}
else
{
lean_object* v_head_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_inc(v_tail_944_);
v_head_947_ = lean_ctor_get(v_x_941_, 0);
lean_inc(v_head_947_);
lean_dec_ref_known(v_x_941_, 2);
v___x_948_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_947_);
v___x_949_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(v_x_942_, v___x_948_, v_tail_944_);
return v___x_949_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0));
v___x_952_ = lean_string_length(v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5);
v___x_954_ = lean_nat_to_int(v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(lean_object* v_xs_963_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_964_ = lean_array_get_size(v_xs_963_);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = lean_nat_dec_eq(v___x_964_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_967_ = lean_array_to_list(v_xs_963_);
v___x_968_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3));
v___x_969_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(v___x_967_, v___x_968_);
v___x_970_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6, &l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6);
v___x_971_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7));
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___x_969_);
v___x_973_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8));
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_970_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_Std_Format_fill(v___x_975_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; 
lean_dec_ref(v_xs_963_);
v___x_977_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10));
return v___x_977_;
}
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_unsigned_to_nat(8u);
v___x_982_ = lean_nat_to_int(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_unsigned_to_nat(9u);
v___x_987_ = lean_nat_to_int(v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___redArg(lean_object* v_x_988_){
_start:
{
lean_object* v_caption_989_; lean_object* v_inputs_990_; uint64_t v_hash_991_; lean_object* v_mtime_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_caption_989_ = lean_ctor_get(v_x_988_, 0);
lean_inc_ref(v_caption_989_);
v_inputs_990_ = lean_ctor_get(v_x_988_, 1);
lean_inc_ref(v_inputs_990_);
v_hash_991_ = lean_ctor_get_uint64(v_x_988_, sizeof(void*)*3);
v_mtime_992_ = lean_ctor_get(v_x_988_, 2);
lean_inc_ref(v_mtime_992_);
lean_dec_ref(v_x_988_);
v___x_993_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__5));
v___x_994_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__3));
v___x_995_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__4, &l_Lake_instReprBuildTrace_repr___redArg___closed__4_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4);
v___x_996_ = l_String_quote(v_caption_989_);
v___x_997_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
v___x_998_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_995_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = 0;
v___x_1000_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*1, v___x_999_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_994_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2));
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_box(1);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__6));
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_993_);
v___x_1009_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__7, &l_Lake_instReprBuildTrace_repr___redArg___closed__7_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7);
v___x_1010_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(v_inputs_990_);
v___x_1011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*1, v___x_999_);
v___x_1013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1008_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_1002_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_1004_);
v___x_1016_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__9));
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___x_993_);
v___x_1019_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__10, &l_Lake_instReprBuildTrace_repr___redArg___closed__10_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10);
v___x_1020_ = l_Lake_instReprHash_repr___redArg(v_hash_991_);
v___x_1021_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set_uint8(v___x_1022_, sizeof(void*)*1, v___x_999_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1018_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_1002_);
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1004_);
v___x_1026_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__12));
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___x_993_);
v___x_1029_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__13, &l_Lake_instReprBuildTrace_repr___redArg___closed__13_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13);
v___x_1030_ = l_IO_FS_instReprSystemTime_repr___redArg(v_mtime_992_);
lean_dec_ref(v_mtime_992_);
v___x_1031_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*1, v___x_999_);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1028_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_obj_once(&l_Lake_instReprHash_repr___redArg___closed__10, &l_Lake_instReprHash_repr___redArg___closed__10_once, _init_l_Lake_instReprHash_repr___redArg___closed__10);
v___x_1035_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__11));
v___x_1036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v___x_1033_);
v___x_1037_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__12));
v___x_1038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1034_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set_uint8(v___x_1040_, sizeof(void*)*1, v___x_999_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1041_, lean_object* v_x_1042_, lean_object* v_x_1043_){
_start:
{
if (lean_obj_tag(v_x_1043_) == 0)
{
lean_dec(v_x_1041_);
return v_x_1042_;
}
else
{
lean_object* v_head_1044_; lean_object* v_tail_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1055_; 
v_head_1044_ = lean_ctor_get(v_x_1043_, 0);
v_tail_1045_ = lean_ctor_get(v_x_1043_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_x_1043_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1047_ = v_x_1043_;
v_isShared_1048_ = v_isSharedCheck_1055_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_tail_1045_);
lean_inc(v_head_1044_);
lean_dec(v_x_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1055_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
lean_inc(v_x_1041_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 5);
lean_ctor_set(v___x_1047_, 1, v_x_1041_);
lean_ctor_set(v___x_1047_, 0, v_x_1042_);
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_x_1042_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_x_1041_);
v___x_1050_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_1044_);
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v_x_1042_ = v___x_1052_;
v_x_1043_ = v_tail_1045_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr(lean_object* v_x_1056_, lean_object* v_prec_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lake_instReprBuildTrace_repr___redArg(v_x_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___boxed(lean_object* v_x_1059_, lean_object* v_prec_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lake_instReprBuildTrace_repr(v_x_1059_, v_prec_1060_);
lean_dec(v_prec_1060_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption(lean_object* v_caption_1064_, lean_object* v_self_1065_){
_start:
{
lean_object* v_inputs_1066_; uint64_t v_hash_1067_; lean_object* v_mtime_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_inputs_1066_ = lean_ctor_get(v_self_1065_, 1);
v_hash_1067_ = lean_ctor_get_uint64(v_self_1065_, sizeof(void*)*3);
v_mtime_1068_ = lean_ctor_get(v_self_1065_, 2);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_self_1065_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v_self_1065_, 0);
lean_dec(v_unused_1076_);
v___x_1070_ = v_self_1065_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_mtime_1068_);
lean_inc(v_inputs_1066_);
lean_dec(v_self_1065_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v_caption_1064_);
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_caption_1064_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_inputs_1066_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_mtime_1068_);
lean_ctor_set_uint64(v_reuseFailAlloc_1074_, sizeof(void*)*3, v_hash_1067_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs(lean_object* v_self_1079_){
_start:
{
lean_object* v_caption_1080_; uint64_t v_hash_1081_; lean_object* v_mtime_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1090_; 
v_caption_1080_ = lean_ctor_get(v_self_1079_, 0);
v_hash_1081_ = lean_ctor_get_uint64(v_self_1079_, sizeof(void*)*3);
v_mtime_1082_ = lean_ctor_get(v_self_1079_, 2);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_self_1079_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_self_1079_, 1);
lean_dec(v_unused_1091_);
v___x_1084_ = v_self_1079_;
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_mtime_1082_);
lean_inc(v_caption_1080_);
lean_dec(v_self_1079_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 1, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_caption_1080_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_mtime_1082_);
lean_ctor_set_uint64(v_reuseFailAlloc_1089_, sizeof(void*)*3, v_hash_1081_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
lean_object* l_Lake_BuildTrace_ofHash(uint64_t v_hash_1092_, lean_object* v_caption_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1095_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1096_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1096_, 0, v_caption_1093_);
lean_ctor_set(v___x_1096_, 1, v___x_1094_);
lean_ctor_set(v___x_1096_, 2, v___x_1095_);
lean_ctor_set_uint64(v___x_1096_, sizeof(void*)*3, v_hash_1092_);
return v___x_1096_;
}
}
LEAN_EXPORT void l_Lake_BuildTrace_ofHash_0interp(lean_interpreter_value* stack)
{
uint64_t v_hash_1092_ = stack[0].m_num;
lean_object* v_caption_1093_ = stack[1].m_obj;
lean_object* v_res_1097_;
v_res_1097_ = l_Lake_BuildTrace_ofHash(v_hash_1092_, v_caption_1093_);
stack->m_obj
 = v_res_1097_;
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash___boxed(lean_object* v_hash_1098_, lean_object* v_caption_1099_){
_start:
{
uint64_t v_hash_boxed_1100_; lean_object* v_res_1101_; 
v_hash_boxed_1100_ = lean_unbox_uint64(v_hash_1098_);
lean_dec_ref(v_hash_1098_);
v_res_1101_ = l_Lake_BuildTrace_ofHash(v_hash_boxed_1100_, v_caption_1099_);
return v_res_1101_;
}
}
lean_object* l_Lake_BuildTrace_instCoeHash___lam__0(uint64_t v_hash_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1104_ = ((lean_object*)(l_Lake_BuildTrace_instCoeHash___lam__0___closed__0));
v___x_1105_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1106_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1107_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1107_, 0, v___x_1104_);
lean_ctor_set(v___x_1107_, 1, v___x_1105_);
lean_ctor_set(v___x_1107_, 2, v___x_1106_);
lean_ctor_set_uint64(v___x_1107_, sizeof(void*)*3, v_hash_1103_);
return v___x_1107_;
}
}
LEAN_EXPORT void l_Lake_BuildTrace_instCoeHash___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_hash_1103_ = stack[0].m_num;
lean_object* v_res_1108_;
v_res_1108_ = l_Lake_BuildTrace_instCoeHash___lam__0(v_hash_1103_);
stack->m_obj
 = v_res_1108_;
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___boxed(lean_object* v_hash_1109_){
_start:
{
uint64_t v_hash_boxed_1110_; lean_object* v_res_1111_; 
v_hash_boxed_1110_ = lean_unbox_uint64(v_hash_1109_);
lean_dec_ref(v_hash_1109_);
v_res_1111_ = l_Lake_BuildTrace_instCoeHash___lam__0(v_hash_boxed_1110_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofMTime(lean_object* v_mtime_1114_, lean_object* v_caption_1115_){
_start:
{
lean_object* v___x_1116_; uint64_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1117_ = 1723ULL;
v___x_1118_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1118_, 0, v_caption_1115_);
lean_ctor_set(v___x_1118_, 1, v___x_1116_);
lean_ctor_set(v___x_1118_, 2, v_mtime_1114_);
lean_ctor_set_uint64(v___x_1118_, sizeof(void*)*3, v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0(lean_object* v_mtime_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; uint64_t v___x_1123_; lean_object* v___x_1124_; 
v___x_1121_ = ((lean_object*)(l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0));
v___x_1122_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1123_ = 1723ULL;
v___x_1124_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1124_, 0, v___x_1121_);
lean_ctor_set(v___x_1124_, 1, v___x_1122_);
lean_ctor_set(v___x_1124_, 2, v_mtime_1120_);
lean_ctor_set_uint64(v___x_1124_, sizeof(void*)*3, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_nil(lean_object* v_caption_1127_){
_start:
{
lean_object* v___x_1128_; uint64_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1128_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1129_ = 1723ULL;
v___x_1130_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1131_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1131_, 0, v_caption_1127_);
lean_ctor_set(v___x_1131_, 1, v___x_1128_);
lean_ctor_set(v___x_1131_, 2, v___x_1130_);
lean_ctor_set_uint64(v___x_1131_, sizeof(void*)*3, v___x_1129_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace___closed__1(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l_Lake_BuildTrace_instNilTrace___closed__0));
v___x_1134_ = l_Lake_BuildTrace_nil(v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace(void){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_obj_once(&l_Lake_BuildTrace_instNilTrace___closed__1, &l_Lake_BuildTrace_instNilTrace___closed__1_once, _init_l_Lake_BuildTrace_instNilTrace___closed__1);
return v___x_1135_;
}
}
lean_object* l_Lake_BuildTrace_compute___redArg(lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_info_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_inc(v_info_1140_);
v___x_1142_ = lean_apply_1(v_inst_1137_, v_info_1140_);
v___x_1143_ = lean_apply_3(v_inst_1138_, lean_box(0), v___x_1142_, lean_box(0));
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
lean_inc(v_info_1140_);
v___x_1145_ = lean_apply_2(v_inst_1139_, v_info_1140_, lean_box(0));
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1157_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1157_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1157_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint64_t v___x_1153_; lean_object* v___x_1155_; 
v___x_1150_ = lean_apply_1(v_inst_1136_, v_info_1140_);
v___x_1151_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1152_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
lean_ctor_set(v___x_1152_, 2, v_a_1146_);
v___x_1153_ = lean_unbox_uint64(v_a_1144_);
lean_dec(v_a_1144_);
lean_ctor_set_uint64(v___x_1152_, sizeof(void*)*3, v___x_1153_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1152_);
v___x_1155_ = v___x_1148_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1152_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_a_1144_);
lean_dec(v_info_1140_);
lean_dec_ref(v_inst_1136_);
v_a_1158_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1145_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1145_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec(v_info_1140_);
lean_dec_ref(v_inst_1139_);
lean_dec_ref(v_inst_1136_);
v_a_1166_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1143_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1143_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_BuildTrace_compute___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1136_ = stack[0].m_obj;
lean_object* v_inst_1137_ = stack[1].m_obj;
lean_object* v_inst_1138_ = stack[2].m_obj;
lean_object* v_inst_1139_ = stack[3].m_obj;
lean_object* v_info_1140_ = stack[4].m_obj;
lean_object* v_res_1174_;
v_res_1174_ = l_Lake_BuildTrace_compute___redArg(v_inst_1136_, v_inst_1137_, v_inst_1138_, v_inst_1139_, v_info_1140_);
stack->m_obj
 = v_res_1174_;
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg___boxed(lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_info_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lake_BuildTrace_compute___redArg(v_inst_1175_, v_inst_1176_, v_inst_1177_, v_inst_1178_, v_info_1179_);
return v_res_1181_;
}
}
lean_object* l_Lake_BuildTrace_compute(lean_object* v_00_u03b1_1182_, lean_object* v_m_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_info_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lake_BuildTrace_compute___redArg(v_inst_1184_, v_inst_1185_, v_inst_1186_, v_inst_1187_, v_info_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT void l_Lake_BuildTrace_compute_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1184_ = stack[2].m_obj;
lean_object* v_inst_1185_ = stack[3].m_obj;
lean_object* v_inst_1186_ = stack[4].m_obj;
lean_object* v_inst_1187_ = stack[5].m_obj;
lean_object* v_info_1188_ = stack[6].m_obj;
lean_object* v_res_1191_;
v_res_1191_ = l_Lake_BuildTrace_compute(lean_box(0), lean_box(0), v_inst_1184_, v_inst_1185_, v_inst_1186_, v_inst_1187_, v_info_1188_);
stack->m_obj
 = v_res_1191_;
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_m_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_info_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lake_BuildTrace_compute(v_00_u03b1_1192_, v_m_1193_, v_inst_1194_, v_inst_1195_, v_inst_1196_, v_inst_1197_, v_info_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime___redArg(lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(v___x_1205_, 0, lean_box(0));
lean_closure_set(v___x_1205_, 1, lean_box(0));
lean_closure_set(v___x_1205_, 2, v_inst_1201_);
lean_closure_set(v___x_1205_, 3, v_inst_1202_);
lean_closure_set(v___x_1205_, 4, v_inst_1203_);
lean_closure_set(v___x_1205_, 5, v_inst_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(lean_object* v_00_u03b1_1206_, lean_object* v_m_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(v___x_1212_, 0, lean_box(0));
lean_closure_set(v___x_1212_, 1, lean_box(0));
lean_closure_set(v___x_1212_, 2, v_inst_1208_);
lean_closure_set(v___x_1212_, 3, v_inst_1209_);
lean_closure_set(v___x_1212_, 4, v_inst_1210_);
lean_closure_set(v___x_1212_, 5, v_inst_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_mix(lean_object* v_t1_1213_, lean_object* v_t2_1214_){
_start:
{
lean_object* v_caption_1215_; lean_object* v_inputs_1216_; uint64_t v_hash_1217_; lean_object* v_mtime_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1233_; 
v_caption_1215_ = lean_ctor_get(v_t1_1213_, 0);
v_inputs_1216_ = lean_ctor_get(v_t1_1213_, 1);
v_hash_1217_ = lean_ctor_get_uint64(v_t1_1213_, sizeof(void*)*3);
v_mtime_1218_ = lean_ctor_get(v_t1_1213_, 2);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_t1_1213_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1220_ = v_t1_1213_;
v_isShared_1221_ = v_isSharedCheck_1233_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_mtime_1218_);
lean_inc(v_inputs_1216_);
lean_inc(v_caption_1215_);
lean_dec(v_t1_1213_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1233_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
uint64_t v_hash_1222_; lean_object* v_mtime_1223_; lean_object* v___x_1224_; uint64_t v___x_1225_; uint8_t v___x_1226_; 
v_hash_1222_ = lean_ctor_get_uint64(v_t2_1214_, sizeof(void*)*3);
v_mtime_1223_ = lean_ctor_get(v_t2_1214_, 2);
lean_inc_ref(v_mtime_1223_);
v___x_1224_ = lean_array_push(v_inputs_1216_, v_t2_1214_);
v___x_1225_ = lean_uint64_mix_hash(v_hash_1217_, v_hash_1222_);
v___x_1226_ = l_IO_FS_instOrdSystemTime_ord(v_mtime_1218_, v_mtime_1223_);
if (v___x_1226_ == 2)
{
lean_object* v___x_1228_; 
lean_dec_ref(v_mtime_1223_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v___x_1224_);
v___x_1228_ = v___x_1220_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_caption_1215_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_mtime_1218_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_ctor_set_uint64(v___x_1228_, sizeof(void*)*3, v___x_1225_);
return v___x_1228_;
}
}
else
{
lean_object* v___x_1231_; 
lean_dec_ref(v_mtime_1218_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 2, v_mtime_1223_);
lean_ctor_set(v___x_1220_, 1, v___x_1224_);
v___x_1231_ = v___x_1220_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_caption_1215_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v_mtime_1223_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_ctor_set_uint64(v___x_1231_, sizeof(void*)*3, v___x_1225_);
return v___x_1231_;
}
}
}
}
}
uint8_t l_Lake_BuildTrace_checkAgainstHash___redArg(lean_object* v_inst_1236_, lean_object* v_info_1237_, uint64_t v_hash_1238_, lean_object* v_self_1239_){
_start:
{
uint64_t v_hash_1241_; uint8_t v___x_1242_; 
v_hash_1241_ = lean_ctor_get_uint64(v_self_1239_, sizeof(void*)*3);
v___x_1242_ = lean_uint64_dec_eq(v_hash_1238_, v_hash_1241_);
if (v___x_1242_ == 0)
{
lean_dec(v_info_1237_);
lean_dec_ref(v_inst_1236_);
return v___x_1242_;
}
else
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = lean_apply_2(v_inst_1236_, v_info_1237_, lean_box(0));
v___x_1244_ = lean_unbox(v___x_1243_);
return v___x_1244_;
}
}
}
LEAN_EXPORT void l_Lake_BuildTrace_checkAgainstHash___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1236_ = stack[0].m_obj;
lean_object* v_info_1237_ = stack[1].m_obj;
uint64_t v_hash_1238_ = stack[2].m_num;
lean_object* v_self_1239_ = stack[3].m_obj;
uint8_t v_res_1245_;
v_res_1245_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1236_, v_info_1237_, v_hash_1238_, v_self_1239_);
stack->m_num = v_res_1245_;
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(lean_object* v_inst_1246_, lean_object* v_info_1247_, lean_object* v_hash_1248_, lean_object* v_self_1249_, lean_object* v_a_1250_){
_start:
{
uint64_t v_hash_boxed_1251_; uint8_t v_res_1252_; lean_object* v_r_1253_; 
v_hash_boxed_1251_ = lean_unbox_uint64(v_hash_1248_);
lean_dec_ref(v_hash_1248_);
v_res_1252_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1246_, v_info_1247_, v_hash_boxed_1251_, v_self_1249_);
lean_dec_ref(v_self_1249_);
v_r_1253_ = lean_box(v_res_1252_);
return v_r_1253_;
}
}
uint8_t l_Lake_BuildTrace_checkAgainstHash(lean_object* v_i_1254_, lean_object* v_inst_1255_, lean_object* v_info_1256_, uint64_t v_hash_1257_, lean_object* v_self_1258_){
_start:
{
uint8_t v___x_1260_; 
v___x_1260_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1255_, v_info_1256_, v_hash_1257_, v_self_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT void l_Lake_BuildTrace_checkAgainstHash_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1255_ = stack[1].m_obj;
lean_object* v_info_1256_ = stack[2].m_obj;
uint64_t v_hash_1257_ = stack[3].m_num;
lean_object* v_self_1258_ = stack[4].m_obj;
uint8_t v_res_1261_;
v_res_1261_ = l_Lake_BuildTrace_checkAgainstHash(lean_box(0), v_inst_1255_, v_info_1256_, v_hash_1257_, v_self_1258_);
stack->m_num = v_res_1261_;
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___boxed(lean_object* v_i_1262_, lean_object* v_inst_1263_, lean_object* v_info_1264_, lean_object* v_hash_1265_, lean_object* v_self_1266_, lean_object* v_a_1267_){
_start:
{
uint64_t v_hash_boxed_1268_; uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_hash_boxed_1268_ = lean_unbox_uint64(v_hash_1265_);
lean_dec_ref(v_hash_1265_);
v_res_1269_ = l_Lake_BuildTrace_checkAgainstHash(v_i_1262_, v_inst_1263_, v_info_1264_, v_hash_boxed_1268_, v_self_1266_);
lean_dec_ref(v_self_1266_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
uint8_t l_Lake_BuildTrace_checkAgainstTime___redArg(lean_object* v_inst_1271_, lean_object* v_info_1272_, lean_object* v_self_1273_){
_start:
{
lean_object* v_mtime_1275_; uint8_t v___x_1276_; 
v_mtime_1275_ = lean_ctor_get(v_self_1273_, 2);
v___x_1276_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1271_, v_info_1272_, v_mtime_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT void l_Lake_BuildTrace_checkAgainstTime___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1271_ = stack[0].m_obj;
lean_object* v_info_1272_ = stack[1].m_obj;
lean_object* v_self_1273_ = stack[2].m_obj;
uint8_t v_res_1277_;
v_res_1277_ = l_Lake_BuildTrace_checkAgainstTime___redArg(v_inst_1271_, v_info_1272_, v_self_1273_);
stack->m_num = v_res_1277_;
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___redArg___boxed(lean_object* v_inst_1278_, lean_object* v_info_1279_, lean_object* v_self_1280_, lean_object* v_a_1281_){
_start:
{
uint8_t v_res_1282_; lean_object* v_r_1283_; 
v_res_1282_ = l_Lake_BuildTrace_checkAgainstTime___redArg(v_inst_1278_, v_info_1279_, v_self_1280_);
lean_dec_ref(v_self_1280_);
v_r_1283_ = lean_box(v_res_1282_);
return v_r_1283_;
}
}
uint8_t l_Lake_BuildTrace_checkAgainstTime(lean_object* v_i_1284_, lean_object* v_inst_1285_, lean_object* v_info_1286_, lean_object* v_self_1287_){
_start:
{
lean_object* v_mtime_1289_; uint8_t v___x_1290_; 
v_mtime_1289_ = lean_ctor_get(v_self_1287_, 2);
v___x_1290_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1285_, v_info_1286_, v_mtime_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT void l_Lake_BuildTrace_checkAgainstTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1285_ = stack[1].m_obj;
lean_object* v_info_1286_ = stack[2].m_obj;
lean_object* v_self_1287_ = stack[3].m_obj;
uint8_t v_res_1291_;
v_res_1291_ = l_Lake_BuildTrace_checkAgainstTime(lean_box(0), v_inst_1285_, v_info_1286_, v_self_1287_);
stack->m_num = v_res_1291_;
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___boxed(lean_object* v_i_1292_, lean_object* v_inst_1293_, lean_object* v_info_1294_, lean_object* v_self_1295_, lean_object* v_a_1296_){
_start:
{
uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_res_1297_ = l_Lake_BuildTrace_checkAgainstTime(v_i_1292_, v_inst_1293_, v_info_1294_, v_self_1295_);
lean_dec_ref(v_self_1295_);
v_r_1298_ = lean_box(v_res_1297_);
return v_r_1298_;
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
