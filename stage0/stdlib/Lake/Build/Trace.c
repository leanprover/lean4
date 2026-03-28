// Lean compiler output
// Module: Lake.Build.Trace
// Imports: public import Lean.Data.Json import Init.Data.Nat.Fold meta import Init.Data.Nat.Fold import Lake.Util.String public import Init.Data.String.Search public import Init.Data.String.Extra import Init.Data.Option.Coe
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
LEAN_EXPORT uint8_t l_Lake_MTime_instBEq___aux__1(lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
uint8_t v___x_763_; 
v___x_763_ = l_IO_FS_instBEqSystemTime_beq(v_x_761_, v_x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instBEq___aux__1___boxed(lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_Lake_MTime_instBEq___aux__1(v_x_764_, v_x_765_);
lean_dec_ref(v_x_765_);
lean_dec_ref(v_x_764_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___redArg(lean_object* v_x_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___redArg___boxed(lean_object* v_x_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lake_MTime_instRepr___aux__1___redArg(v_x_772_);
lean_dec_ref(v_x_772_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1(lean_object* v_x_774_, lean_object* v_prec_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr___aux__1___boxed(lean_object* v_x_777_, lean_object* v_prec_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lake_MTime_instRepr___aux__1(v_x_777_, v_prec_778_);
lean_dec(v_prec_778_);
lean_dec_ref(v_x_777_);
return v_res_779_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_instOrd___aux__1(lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
uint8_t v___x_784_; 
v___x_784_ = l_IO_FS_instOrdSystemTime_ord(v_x_782_, v_x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instOrd___aux__1___boxed(lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Lake_MTime_instOrd___aux__1(v_x_785_, v_x_786_);
lean_dec_ref(v_x_786_);
lean_dec_ref(v_x_785_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
static lean_object* _init_l_Lake_MTime_instLT(void){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = lean_box(0);
return v___x_791_;
}
}
static lean_object* _init_l_Lake_MTime_instLE(void){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = lean_box(0);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0(lean_object* v_x_793_, lean_object* v_y_794_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = l_IO_FS_instOrdSystemTime_ord(v_x_793_, v_y_794_);
if (v___x_795_ == 2)
{
lean_inc_ref(v_y_794_);
return v_y_794_;
}
else
{
lean_inc_ref(v_x_793_);
return v_x_793_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0___boxed(lean_object* v_x_796_, lean_object* v_y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lake_MTime_instMin___lam__0(v_x_796_, v_y_797_);
lean_dec_ref(v_y_797_);
lean_dec_ref(v_x_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0(lean_object* v_x_801_, lean_object* v_y_802_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = l_IO_FS_instOrdSystemTime_ord(v_x_801_, v_y_802_);
if (v___x_803_ == 2)
{
lean_inc_ref(v_x_801_);
return v_x_801_;
}
else
{
lean_inc_ref(v_y_802_);
return v_y_802_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0___boxed(lean_object* v_x_804_, lean_object* v_y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lake_MTime_instMax___lam__0(v_x_804_, v_y_805_);
lean_dec_ref(v_y_805_);
lean_dec_ref(v_x_804_);
return v_res_806_;
}
}
static lean_object* _init_l_Lake_MTime_instNilTrace(void){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(lean_object* v_inst_811_){
_start:
{
lean_inc_ref(v_inst_811_);
return v_inst_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(lean_object* v_inst_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(v_inst_812_);
lean_dec_ref(v_inst_812_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(lean_object* v_00_u03b1_814_, lean_object* v_inst_815_){
_start:
{
lean_inc_ref(v_inst_815_);
return v_inst_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___boxed(lean_object* v_00_u03b1_816_, lean_object* v_inst_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(v_00_u03b1_816_, v_inst_817_);
lean_dec_ref(v_inst_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime(lean_object* v_file_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = lean_io_metadata(v_file_819_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_830_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_830_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_modified_826_; lean_object* v___x_828_; 
v_modified_826_ = lean_ctor_get(v_a_822_, 1);
lean_inc_ref(v_modified_826_);
lean_dec(v_a_822_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_modified_826_);
v___x_828_ = v___x_824_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_modified_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
v_a_831_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_821_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_821_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime___boxed(lean_object* v_file_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lake_getFileMTime(v_file_839_);
lean_dec_ref(v_file_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0(lean_object* v_x_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_io_metadata(v_x_844_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_855_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_855_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_modified_851_; lean_object* v___x_853_; 
v_modified_851_ = lean_ctor_get(v_a_847_, 1);
lean_inc_ref(v_modified_851_);
lean_dec(v_a_847_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v_modified_851_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_modified_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_a_856_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_846_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_846_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0___boxed(lean_object* v_x_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lake_instGetMTimeTextFilePath___lam__0(v_x_864_);
lean_dec_ref(v_x_864_);
return v_res_866_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object* v_inst_869_, lean_object* v_info_870_, lean_object* v_self_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = lean_apply_2(v_inst_869_, v_info_870_, lean_box(0));
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; uint8_t v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref(v___x_873_);
v___x_875_ = l_IO_FS_instOrdSystemTime_ord(v_self_871_, v_a_874_);
lean_dec(v_a_874_);
if (v___x_875_ == 0)
{
uint8_t v___x_876_; 
v___x_876_ = 1;
return v___x_876_;
}
else
{
uint8_t v___x_877_; 
v___x_877_ = 0;
return v___x_877_;
}
}
else
{
uint8_t v___x_878_; 
lean_dec_ref(v___x_873_);
v___x_878_ = 0;
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___redArg___boxed(lean_object* v_inst_879_, lean_object* v_info_880_, lean_object* v_self_881_, lean_object* v_a_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_879_, v_info_880_, v_self_881_);
lean_dec_ref(v_self_881_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate(lean_object* v_i_885_, lean_object* v_inst_886_, lean_object* v_info_887_, lean_object* v_self_888_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_886_, v_info_887_, v_self_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___boxed(lean_object* v_i_891_, lean_object* v_inst_892_, lean_object* v_info_893_, lean_object* v_self_894_, lean_object* v_a_895_){
_start:
{
uint8_t v_res_896_; lean_object* v_r_897_; 
v_res_896_ = l_Lake_MTime_checkUpToDate(v_i_891_, v_inst_892_, v_info_893_, v_self_894_);
lean_dec_ref(v_self_894_);
v_r_897_ = lean_box(v_res_896_);
return v_r_897_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_unsigned_to_nat(11u);
v___x_908_ = lean_nat_to_int(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_unsigned_to_nat(10u);
v___x_916_ = lean_nat_to_int(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(lean_object* v_x_920_, lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
if (lean_obj_tag(v_x_922_) == 0)
{
lean_dec(v_x_920_);
return v_x_921_;
}
else
{
lean_object* v_head_923_; lean_object* v_tail_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_934_; 
v_head_923_ = lean_ctor_get(v_x_922_, 0);
v_tail_924_ = lean_ctor_get(v_x_922_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_x_922_);
if (v_isSharedCheck_934_ == 0)
{
v___x_926_ = v_x_922_;
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_tail_924_);
lean_inc(v_head_923_);
lean_dec(v_x_922_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_934_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
lean_inc(v_x_920_);
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 5);
lean_ctor_set(v___x_926_, 1, v_x_920_);
lean_ctor_set(v___x_926_, 0, v_x_921_);
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_x_921_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_x_920_);
v___x_929_ = v_reuseFailAlloc_933_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_923_);
v___x_931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(v_x_920_, v___x_931_, v_tail_924_);
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
if (lean_obj_tag(v_x_935_) == 0)
{
lean_object* v___x_937_; 
lean_dec(v_x_936_);
v___x_937_ = lean_box(0);
return v___x_937_;
}
else
{
lean_object* v_tail_938_; 
v_tail_938_ = lean_ctor_get(v_x_935_, 1);
if (lean_obj_tag(v_tail_938_) == 0)
{
lean_object* v_head_939_; lean_object* v___x_940_; 
lean_dec(v_x_936_);
v_head_939_ = lean_ctor_get(v_x_935_, 0);
lean_inc(v_head_939_);
lean_dec_ref(v_x_935_);
v___x_940_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_939_);
return v___x_940_;
}
else
{
lean_object* v_head_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_inc(v_tail_938_);
v_head_941_ = lean_ctor_get(v_x_935_, 0);
lean_inc(v_head_941_);
lean_dec_ref(v_x_935_);
v___x_942_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_941_);
v___x_943_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(v_x_936_, v___x_942_, v_tail_938_);
return v___x_943_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0));
v___x_946_ = lean_string_length(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5);
v___x_948_ = lean_nat_to_int(v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(lean_object* v_xs_957_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_958_ = lean_array_get_size(v_xs_957_);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_nat_dec_eq(v___x_958_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_961_ = lean_array_to_list(v_xs_957_);
v___x_962_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3));
v___x_963_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(v___x_961_, v___x_962_);
v___x_964_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6, &l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6);
v___x_965_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7));
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_963_);
v___x_967_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8));
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_964_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = l_Std_Format_fill(v___x_969_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; 
lean_dec_ref(v_xs_957_);
v___x_971_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10));
return v___x_971_;
}
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_unsigned_to_nat(8u);
v___x_976_ = lean_nat_to_int(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_unsigned_to_nat(9u);
v___x_981_ = lean_nat_to_int(v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___redArg(lean_object* v_x_982_){
_start:
{
lean_object* v_caption_983_; lean_object* v_inputs_984_; uint64_t v_hash_985_; lean_object* v_mtime_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_caption_983_ = lean_ctor_get(v_x_982_, 0);
lean_inc_ref(v_caption_983_);
v_inputs_984_ = lean_ctor_get(v_x_982_, 1);
lean_inc_ref(v_inputs_984_);
v_hash_985_ = lean_ctor_get_uint64(v_x_982_, sizeof(void*)*3);
v_mtime_986_ = lean_ctor_get(v_x_982_, 2);
lean_inc_ref(v_mtime_986_);
lean_dec_ref(v_x_982_);
v___x_987_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__5));
v___x_988_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__3));
v___x_989_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__4, &l_Lake_instReprBuildTrace_repr___redArg___closed__4_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4);
v___x_990_ = l_String_quote(v_caption_983_);
v___x_991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
v___x_992_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_989_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = 0;
v___x_994_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*1, v___x_993_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_988_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2));
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_box(1);
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__6));
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_987_);
v___x_1003_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__7, &l_Lake_instReprBuildTrace_repr___redArg___closed__7_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7);
v___x_1004_ = l_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(v_inputs_984_);
v___x_1005_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*1, v___x_993_);
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1002_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_996_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_998_);
v___x_1010_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__9));
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_987_);
v___x_1013_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__10, &l_Lake_instReprBuildTrace_repr___redArg___closed__10_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10);
v___x_1014_ = l_Lake_instReprHash_repr___redArg(v_hash_985_);
v___x_1015_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set_uint8(v___x_1016_, sizeof(void*)*1, v___x_993_);
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1012_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___x_996_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_998_);
v___x_1020_ = ((lean_object*)(l_Lake_instReprBuildTrace_repr___redArg___closed__12));
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___x_987_);
v___x_1023_ = lean_obj_once(&l_Lake_instReprBuildTrace_repr___redArg___closed__13, &l_Lake_instReprBuildTrace_repr___redArg___closed__13_once, _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13);
v___x_1024_ = l_IO_FS_instReprSystemTime_repr___redArg(v_mtime_986_);
lean_dec_ref(v_mtime_986_);
v___x_1025_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set_uint8(v___x_1026_, sizeof(void*)*1, v___x_993_);
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1022_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_obj_once(&l_Lake_instReprHash_repr___redArg___closed__10, &l_Lake_instReprHash_repr___redArg___closed__10_once, _init_l_Lake_instReprHash_repr___redArg___closed__10);
v___x_1029_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__11));
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_1027_);
v___x_1031_ = ((lean_object*)(l_Lake_instReprHash_repr___redArg___closed__12));
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1028_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set_uint8(v___x_1034_, sizeof(void*)*1, v___x_993_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
if (lean_obj_tag(v_x_1037_) == 0)
{
lean_dec(v_x_1035_);
return v_x_1036_;
}
else
{
lean_object* v_head_1038_; lean_object* v_tail_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1049_; 
v_head_1038_ = lean_ctor_get(v_x_1037_, 0);
v_tail_1039_ = lean_ctor_get(v_x_1037_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_x_1037_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1041_ = v_x_1037_;
v_isShared_1042_ = v_isSharedCheck_1049_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_tail_1039_);
lean_inc(v_head_1038_);
lean_dec(v_x_1037_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1049_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
lean_inc(v_x_1035_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set_tag(v___x_1041_, 5);
lean_ctor_set(v___x_1041_, 1, v_x_1035_);
lean_ctor_set(v___x_1041_, 0, v_x_1036_);
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_x_1036_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_x_1035_);
v___x_1044_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = l_Lake_instReprBuildTrace_repr___redArg(v_head_1038_);
v___x_1046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v_x_1036_ = v___x_1046_;
v_x_1037_ = v_tail_1039_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr(lean_object* v_x_1050_, lean_object* v_prec_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lake_instReprBuildTrace_repr___redArg(v_x_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___boxed(lean_object* v_x_1053_, lean_object* v_prec_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lake_instReprBuildTrace_repr(v_x_1053_, v_prec_1054_);
lean_dec(v_prec_1054_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption(lean_object* v_caption_1058_, lean_object* v_self_1059_){
_start:
{
lean_object* v_inputs_1060_; uint64_t v_hash_1061_; lean_object* v_mtime_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_inputs_1060_ = lean_ctor_get(v_self_1059_, 1);
v_hash_1061_ = lean_ctor_get_uint64(v_self_1059_, sizeof(void*)*3);
v_mtime_1062_ = lean_ctor_get(v_self_1059_, 2);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_self_1059_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; 
v_unused_1070_ = lean_ctor_get(v_self_1059_, 0);
lean_dec(v_unused_1070_);
v___x_1064_ = v_self_1059_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_mtime_1062_);
lean_inc(v_inputs_1060_);
lean_dec(v_self_1059_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v_caption_1058_);
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_caption_1058_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_inputs_1060_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_mtime_1062_);
lean_ctor_set_uint64(v_reuseFailAlloc_1068_, sizeof(void*)*3, v_hash_1061_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs(lean_object* v_self_1073_){
_start:
{
lean_object* v_caption_1074_; uint64_t v_hash_1075_; lean_object* v_mtime_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1084_; 
v_caption_1074_ = lean_ctor_get(v_self_1073_, 0);
v_hash_1075_ = lean_ctor_get_uint64(v_self_1073_, sizeof(void*)*3);
v_mtime_1076_ = lean_ctor_get(v_self_1073_, 2);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_self_1073_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v_self_1073_, 1);
lean_dec(v_unused_1085_);
v___x_1078_ = v_self_1073_;
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_mtime_1076_);
lean_inc(v_caption_1074_);
lean_dec(v_self_1073_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 1, v___x_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_caption_1074_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_mtime_1076_);
lean_ctor_set_uint64(v_reuseFailAlloc_1083_, sizeof(void*)*3, v_hash_1075_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash(uint64_t v_hash_1086_, lean_object* v_caption_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1089_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1090_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1090_, 0, v_caption_1087_);
lean_ctor_set(v___x_1090_, 1, v___x_1088_);
lean_ctor_set(v___x_1090_, 2, v___x_1089_);
lean_ctor_set_uint64(v___x_1090_, sizeof(void*)*3, v_hash_1086_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash___boxed(lean_object* v_hash_1091_, lean_object* v_caption_1092_){
_start:
{
uint64_t v_hash_boxed_1093_; lean_object* v_res_1094_; 
v_hash_boxed_1093_ = lean_unbox_uint64(v_hash_1091_);
lean_dec_ref(v_hash_1091_);
v_res_1094_ = l_Lake_BuildTrace_ofHash(v_hash_boxed_1093_, v_caption_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0(uint64_t v_hash_1096_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1097_ = ((lean_object*)(l_Lake_BuildTrace_instCoeHash___lam__0___closed__0));
v___x_1098_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1099_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1100_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1100_, 0, v___x_1097_);
lean_ctor_set(v___x_1100_, 1, v___x_1098_);
lean_ctor_set(v___x_1100_, 2, v___x_1099_);
lean_ctor_set_uint64(v___x_1100_, sizeof(void*)*3, v_hash_1096_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___boxed(lean_object* v_hash_1101_){
_start:
{
uint64_t v_hash_boxed_1102_; lean_object* v_res_1103_; 
v_hash_boxed_1102_ = lean_unbox_uint64(v_hash_1101_);
lean_dec_ref(v_hash_1101_);
v_res_1103_ = l_Lake_BuildTrace_instCoeHash___lam__0(v_hash_boxed_1102_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofMTime(lean_object* v_mtime_1106_, lean_object* v_caption_1107_){
_start:
{
lean_object* v___x_1108_; uint64_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1109_ = 1723ULL;
v___x_1110_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1110_, 0, v_caption_1107_);
lean_ctor_set(v___x_1110_, 1, v___x_1108_);
lean_ctor_set(v___x_1110_, 2, v_mtime_1106_);
lean_ctor_set_uint64(v___x_1110_, sizeof(void*)*3, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0(lean_object* v_mtime_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; uint64_t v___x_1115_; lean_object* v___x_1116_; 
v___x_1113_ = ((lean_object*)(l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0));
v___x_1114_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1115_ = 1723ULL;
v___x_1116_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1116_, 0, v___x_1113_);
lean_ctor_set(v___x_1116_, 1, v___x_1114_);
lean_ctor_set(v___x_1116_, 2, v_mtime_1112_);
lean_ctor_set_uint64(v___x_1116_, sizeof(void*)*3, v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_nil(lean_object* v_caption_1119_){
_start:
{
lean_object* v___x_1120_; uint64_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1120_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1121_ = 1723ULL;
v___x_1122_ = lean_obj_once(&l_Lake_MTime_instOfNat___closed__0, &l_Lake_MTime_instOfNat___closed__0_once, _init_l_Lake_MTime_instOfNat___closed__0);
v___x_1123_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1123_, 0, v_caption_1119_);
lean_ctor_set(v___x_1123_, 1, v___x_1120_);
lean_ctor_set(v___x_1123_, 2, v___x_1122_);
lean_ctor_set_uint64(v___x_1123_, sizeof(void*)*3, v___x_1121_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace___closed__1(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lake_BuildTrace_instNilTrace___closed__0));
v___x_1126_ = l_Lake_BuildTrace_nil(v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace(void){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_obj_once(&l_Lake_BuildTrace_instNilTrace___closed__1, &l_Lake_BuildTrace_instNilTrace___closed__1_once, _init_l_Lake_BuildTrace_instNilTrace___closed__1);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg(lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_info_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_inc(v_info_1132_);
v___x_1134_ = lean_apply_1(v_inst_1129_, v_info_1132_);
v___x_1135_ = lean_apply_3(v_inst_1130_, lean_box(0), v___x_1134_, lean_box(0));
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1137_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v___x_1135_);
lean_inc(v_info_1132_);
v___x_1137_ = lean_apply_2(v_inst_1131_, v_info_1132_, lean_box(0));
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1149_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1149_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1149_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint64_t v___x_1145_; lean_object* v___x_1147_; 
v___x_1142_ = lean_apply_1(v_inst_1128_, v_info_1132_);
v___x_1143_ = ((lean_object*)(l_Lake_BuildTrace_withoutInputs___closed__0));
v___x_1144_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
lean_ctor_set(v___x_1144_, 2, v_a_1138_);
v___x_1145_ = lean_unbox_uint64(v_a_1136_);
lean_dec(v_a_1136_);
lean_ctor_set_uint64(v___x_1144_, sizeof(void*)*3, v___x_1145_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1144_);
v___x_1147_ = v___x_1140_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1144_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_a_1136_);
lean_dec(v_info_1132_);
lean_dec_ref(v_inst_1128_);
v_a_1150_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1137_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1137_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_info_1132_);
lean_dec_ref(v_inst_1131_);
lean_dec_ref(v_inst_1128_);
v_a_1158_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1135_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1135_);
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
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg___boxed(lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_info_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lake_BuildTrace_compute___redArg(v_inst_1166_, v_inst_1167_, v_inst_1168_, v_inst_1169_, v_info_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute(lean_object* v_00_u03b1_1173_, lean_object* v_m_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_info_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lake_BuildTrace_compute___redArg(v_inst_1175_, v_inst_1176_, v_inst_1177_, v_inst_1178_, v_info_1179_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_m_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_info_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lake_BuildTrace_compute(v_00_u03b1_1182_, v_m_1183_, v_inst_1184_, v_inst_1185_, v_inst_1186_, v_inst_1187_, v_info_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime___redArg(lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(v___x_1195_, 0, lean_box(0));
lean_closure_set(v___x_1195_, 1, lean_box(0));
lean_closure_set(v___x_1195_, 2, v_inst_1191_);
lean_closure_set(v___x_1195_, 3, v_inst_1192_);
lean_closure_set(v___x_1195_, 4, v_inst_1193_);
lean_closure_set(v___x_1195_, 5, v_inst_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(lean_object* v_00_u03b1_1196_, lean_object* v_m_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(v___x_1202_, 0, lean_box(0));
lean_closure_set(v___x_1202_, 1, lean_box(0));
lean_closure_set(v___x_1202_, 2, v_inst_1198_);
lean_closure_set(v___x_1202_, 3, v_inst_1199_);
lean_closure_set(v___x_1202_, 4, v_inst_1200_);
lean_closure_set(v___x_1202_, 5, v_inst_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_mix(lean_object* v_t1_1203_, lean_object* v_t2_1204_){
_start:
{
lean_object* v_caption_1205_; lean_object* v_inputs_1206_; uint64_t v_hash_1207_; lean_object* v_mtime_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1223_; 
v_caption_1205_ = lean_ctor_get(v_t1_1203_, 0);
v_inputs_1206_ = lean_ctor_get(v_t1_1203_, 1);
v_hash_1207_ = lean_ctor_get_uint64(v_t1_1203_, sizeof(void*)*3);
v_mtime_1208_ = lean_ctor_get(v_t1_1203_, 2);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_t1_1203_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1210_ = v_t1_1203_;
v_isShared_1211_ = v_isSharedCheck_1223_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_mtime_1208_);
lean_inc(v_inputs_1206_);
lean_inc(v_caption_1205_);
lean_dec(v_t1_1203_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1223_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
uint64_t v_hash_1212_; lean_object* v_mtime_1213_; lean_object* v___x_1214_; uint64_t v___x_1215_; uint8_t v___x_1216_; 
v_hash_1212_ = lean_ctor_get_uint64(v_t2_1204_, sizeof(void*)*3);
v_mtime_1213_ = lean_ctor_get(v_t2_1204_, 2);
lean_inc_ref(v_mtime_1213_);
v___x_1214_ = lean_array_push(v_inputs_1206_, v_t2_1204_);
v___x_1215_ = lean_uint64_mix_hash(v_hash_1207_, v_hash_1212_);
v___x_1216_ = l_IO_FS_instOrdSystemTime_ord(v_mtime_1208_, v_mtime_1213_);
if (v___x_1216_ == 2)
{
lean_object* v___x_1218_; 
lean_dec_ref(v_mtime_1213_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v___x_1214_);
v___x_1218_ = v___x_1210_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_caption_1205_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_mtime_1208_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_ctor_set_uint64(v___x_1218_, sizeof(void*)*3, v___x_1215_);
return v___x_1218_;
}
}
else
{
lean_object* v___x_1221_; 
lean_dec_ref(v_mtime_1208_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 2, v_mtime_1213_);
lean_ctor_set(v___x_1210_, 1, v___x_1214_);
v___x_1221_ = v___x_1210_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_caption_1205_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_mtime_1213_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_ctor_set_uint64(v___x_1221_, sizeof(void*)*3, v___x_1215_);
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash___redArg(lean_object* v_inst_1226_, lean_object* v_info_1227_, uint64_t v_hash_1228_, lean_object* v_self_1229_){
_start:
{
uint64_t v_hash_1231_; uint8_t v___x_1232_; 
v_hash_1231_ = lean_ctor_get_uint64(v_self_1229_, sizeof(void*)*3);
v___x_1232_ = lean_uint64_dec_eq(v_hash_1228_, v_hash_1231_);
if (v___x_1232_ == 0)
{
lean_dec(v_info_1227_);
lean_dec_ref(v_inst_1226_);
return v___x_1232_;
}
else
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_apply_2(v_inst_1226_, v_info_1227_, lean_box(0));
v___x_1234_ = lean_unbox(v___x_1233_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(lean_object* v_inst_1235_, lean_object* v_info_1236_, lean_object* v_hash_1237_, lean_object* v_self_1238_, lean_object* v_a_1239_){
_start:
{
uint64_t v_hash_boxed_1240_; uint8_t v_res_1241_; lean_object* v_r_1242_; 
v_hash_boxed_1240_ = lean_unbox_uint64(v_hash_1237_);
lean_dec_ref(v_hash_1237_);
v_res_1241_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1235_, v_info_1236_, v_hash_boxed_1240_, v_self_1238_);
lean_dec_ref(v_self_1238_);
v_r_1242_ = lean_box(v_res_1241_);
return v_r_1242_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash(lean_object* v_i_1243_, lean_object* v_inst_1244_, lean_object* v_info_1245_, uint64_t v_hash_1246_, lean_object* v_self_1247_){
_start:
{
uint8_t v___x_1249_; 
v___x_1249_ = l_Lake_BuildTrace_checkAgainstHash___redArg(v_inst_1244_, v_info_1245_, v_hash_1246_, v_self_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___boxed(lean_object* v_i_1250_, lean_object* v_inst_1251_, lean_object* v_info_1252_, lean_object* v_hash_1253_, lean_object* v_self_1254_, lean_object* v_a_1255_){
_start:
{
uint64_t v_hash_boxed_1256_; uint8_t v_res_1257_; lean_object* v_r_1258_; 
v_hash_boxed_1256_ = lean_unbox_uint64(v_hash_1253_);
lean_dec_ref(v_hash_1253_);
v_res_1257_ = l_Lake_BuildTrace_checkAgainstHash(v_i_1250_, v_inst_1251_, v_info_1252_, v_hash_boxed_1256_, v_self_1254_);
lean_dec_ref(v_self_1254_);
v_r_1258_ = lean_box(v_res_1257_);
return v_r_1258_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime___redArg(lean_object* v_inst_1259_, lean_object* v_info_1260_, lean_object* v_self_1261_){
_start:
{
lean_object* v_mtime_1263_; uint8_t v___x_1264_; 
v_mtime_1263_ = lean_ctor_get(v_self_1261_, 2);
v___x_1264_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1259_, v_info_1260_, v_mtime_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___redArg___boxed(lean_object* v_inst_1265_, lean_object* v_info_1266_, lean_object* v_self_1267_, lean_object* v_a_1268_){
_start:
{
uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_res_1269_ = l_Lake_BuildTrace_checkAgainstTime___redArg(v_inst_1265_, v_info_1266_, v_self_1267_);
lean_dec_ref(v_self_1267_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime(lean_object* v_i_1271_, lean_object* v_inst_1272_, lean_object* v_info_1273_, lean_object* v_self_1274_){
_start:
{
lean_object* v_mtime_1276_; uint8_t v___x_1277_; 
v_mtime_1276_ = lean_ctor_get(v_self_1274_, 2);
v___x_1277_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1272_, v_info_1273_, v_mtime_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___boxed(lean_object* v_i_1278_, lean_object* v_inst_1279_, lean_object* v_info_1280_, lean_object* v_self_1281_, lean_object* v_a_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_Lake_BuildTrace_checkAgainstTime(v_i_1278_, v_inst_1279_, v_info_1280_, v_self_1281_);
lean_dec_ref(v_self_1281_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
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
