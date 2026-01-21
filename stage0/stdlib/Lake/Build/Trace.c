// Lean compiler output
// Module: Lake.Build.Trace
// Imports: public import Lean.Data.Json import Init.Data.Nat.Fold import Lake.Util.String import Lake.Util.IO public import Init.Data.String.Search public import Init.Data.String.Extra
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
uint8_t lean_uint8_sub(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_MTime_instOrd;
static lean_object* l_Lake_mixTraceArray___redArg___closed__9;
static lean_object* l_Lake_MTime_instBEq___closed__0;
static lean_object* l_Lake_instReprHash_repr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_instToString;
LEAN_EXPORT uint64_t l_Lake_Hash_ofHex(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringTextFilePath;
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildTrace_instMixTrace___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_pureHash___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__1;
static lean_object* l_Lake_instReprHash_repr___redArg___closed__0;
lean_object* l_String_Slice_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_instToJson;
LEAN_EXPORT lean_object* l_Lake_instComputeHashFilePathIO;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofNat(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofBool(uint8_t);
LEAN_EXPORT lean_object* l_Lake_computeHash(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_mix(uint64_t, uint64_t);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeListTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instBEq;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_MTime_instMax___closed__0;
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_pureHash___redArg(lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*);
static lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_Hash_ofDecimal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofBool___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_toJson___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofNat___boxed(lean_object*);
static lean_object* l_Lake_instReprHash_repr___redArg___closed__10;
lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object*);
static lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10;
static lean_object* l_Lake_BuildTrace_withoutInputs___closed__0;
uint64_t lean_string_hash(lean_object*);
lean_object* l_Lake_lpad(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeHash___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_toJson(uint64_t);
LEAN_EXPORT lean_object* l_Lake_computeFileHash(lean_object*, uint8_t);
static lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Hash_fromJson_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofText___boxed(lean_object*);
static lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4;
static lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_Hash_toString___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instMin;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_hex(uint64_t);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__1;
static lean_object* l_Lake_instReprHash_repr___redArg___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_IO_FS_instReprSystemTime_repr___boxed(lean_object*, lean_object*);
uint8_t l_Lake_isHex(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
static lean_object* l_Lake_mixTraceArray___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0(uint64_t, lean_object*, uint64_t);
static lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5;
static lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___redArg(lean_object*);
static lean_object* l_Lake_instComputeHashStringId___closed__0;
lean_object* l_String_crlfToLf(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Hash_fromJson_x3f___closed__6;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__0;
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__11;
static lean_object* l_Lake_MTime_instOrd___closed__0;
static lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1;
static lean_object* l_Lake_mixTraceArray___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__6;
static lean_object* l_Lake_Hash_instHashable___closed__0;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_instHashable;
LEAN_EXPORT lean_object* l_Lake_getFileMTime___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_Hash_fromJson_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_instReprHash;
static lean_object* l_Lake_BuildTrace_instCoeMTime___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instNilTrace;
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instComputeHashTextFilePathIO___closed__0;
uint64_t lean_uint8_to_uint64(uint8_t);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___boxed__const__1;
static lean_object* l_Lake_Hash_instToJson___closed__0;
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___redArg(uint64_t);
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashBoolId;
static lean_object* l_Lake_instCoeTextFilePathFilePath___closed__0;
LEAN_EXPORT lean_object* l_Lake_Hash_instFromJson;
static lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__5;
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lake_instCheckExistsFilePath;
LEAN_EXPORT lean_object* l_Lake_pureHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instNilTrace;
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__8;
LEAN_EXPORT uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace(lean_object*, lean_object*);
static lean_object* l_Lake_Hash_fromJson_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_inline(lean_object*, lean_object*);
static lean_object* l_Lake_instReprHash_repr___redArg___closed__6;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofMTime(lean_object*, lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_instHashable___lam__0___boxed(lean_object*);
static lean_object* l_Lake_Hash_fromJson_x3f___closed__3;
static lean_object* l_Lake_instReprHash___closed__0;
LEAN_EXPORT lean_object* l_Lake_Hash_toString(uint64_t);
static lean_object* l_Lake_mixTraceArray___redArg___closed__3;
LEAN_EXPORT uint64_t l_Lake_Hash_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_hex___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0(lean_object*);
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lake_instComputeHashStringId;
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__7;
lean_object* l_IO_FS_instOrdSystemTime_ord___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashTextFilePathIO;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofText(lean_object*);
static lean_object* l_Lake_BuildTrace_instNilTrace___closed__0;
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr(uint64_t, lean_object*);
static lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instMixTrace;
static lean_object* l_Lake_instReprHash_repr___redArg___closed__7;
static lean_object* l_Lake_instReprHash_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeFileHash___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__9;
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_mixTraceArray___redArg___closed__7;
LEAN_EXPORT uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint64_t);
static lean_object* l_Lake_Hash_fromJson_x3f___closed__5;
static lean_object* l_Lake_instReprHash_repr___redArg___closed__11;
static lean_object* l_Lake_Hash_instToString___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mixTraceArray___redArg___closed__0;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprHash_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqHash(uint64_t, uint64_t);
static lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9;
static lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_mix___boxed(lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instOfNat;
static lean_object* l_Lake_Hash_instFromJson___closed__0;
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0(uint64_t);
lean_object* l_IO_FS_readFile(lean_object*);
static lean_object* l_Lake_instReprHash_repr___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lake_instGetMTimeFilePath;
static lean_object* l_Lake_instReprBuildTrace___closed__0;
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Hash_instMixTrace___closed__0;
static lean_object* l_Lake_instReprHash_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mixTraceArray___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash(uint64_t, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instMax;
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr;
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getFileMTime(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceList(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_nil;
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqHash_decEq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace;
static lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instCheckExistsFilePath___closed__0;
static lean_object* l_Lake_Hash_fromJson_x3f___closed__0;
LEAN_EXPORT uint64_t l_Lake_Hash_instNilTrace;
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprHash_repr___redArg___closed__8;
lean_object* l_Int_toNat(lean_object*);
static lean_object* l_Lake_mixTraceArray___redArg___closed__4;
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_instComputeHashBoolId___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofByteArray___boxed(lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime;
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash___redArg(lean_object*, lean_object*, uint64_t, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instGetMTimeTextFilePath___closed__0;
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_MTime_instOfNat___closed__0;
LEAN_EXPORT uint64_t l_Lake_pureHash(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprHash_repr___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instLT;
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instMixTrace;
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath;
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instLE;
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash;
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg___boxed(lean_object*);
static lean_object* l_Lake_BuildTrace_instNilTrace___closed__1;
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash(lean_object*);
static lean_object* l_Lake_mixTraceArray___redArg___closed__5;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f___boxed(lean_object*);
static lean_object* l_Lake_instComputeTraceListOfMonad___redArg___closed__0;
static lean_object* l_Lake_instGetMTimeFilePath___closed__0;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildTrace_instCoeHash___closed__0;
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
static lean_object* l_Lake_mixTraceArray___redArg___closed__8;
static lean_object* l_Lake_instComputeHashFilePathIO___closed__0;
static lean_object* l_Lake_instReprHash_repr___redArg___closed__1;
static lean_object* l_Lake_Hash_ofJsonNumber_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
static lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8;
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__0;
lean_object* l_IO_FS_instBEqSystemTime_beq___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instReprBuildTrace_repr___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lake_Hash_instMixTrace;
LEAN_EXPORT lean_object* l_Lake_Hash_ofString___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofByteArray(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
lean_object* l_List_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_MTime_instMin___closed__0;
LEAN_EXPORT uint64_t l_Lake_Hash_instHashable___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lake_computeTrace___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_MTime_instRepr___closed__0;
static lean_object* _init_l_Lake_instCheckExistsFilePath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_FilePath_pathExists___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instCheckExistsFilePath() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instCheckExistsFilePath___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_computeTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_computeTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_1(x_5, x_7);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_inhabitedOfNilTrace___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_inhabitedOfNilTrace(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceList___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldl___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_mixTraceArray___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_mixTraceArray___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_mixTraceArray___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_mixTraceArray___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_mixTraceArray___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_mixTraceArray___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_mixTraceArray___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_mixTraceArray___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_mixTraceArray___redArg___closed__1;
x_2 = l_Lake_mixTraceArray___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mixTraceArray___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_mixTraceArray___redArg___closed__5;
x_2 = l_Lake_mixTraceArray___redArg___closed__4;
x_3 = l_Lake_mixTraceArray___redArg___closed__3;
x_4 = l_Lake_mixTraceArray___redArg___closed__2;
x_5 = l_Lake_mixTraceArray___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_mixTraceArray___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_mixTraceArray___redArg___closed__6;
x_2 = l_Lake_mixTraceArray___redArg___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceArray___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = l_Lake_mixTraceArray___redArg___closed__9;
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_alloc_closure((void*)(l_Lake_mixTraceArray___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
if (x_7 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_3);
return x_2;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_8, x_3, x_10, x_11, x_2);
return x_12;
}
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_8, x_3, x_13, x_14, x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_mixTraceArray___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_2(x_1, x_2, x_4);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__0), 4, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_2);
x_9 = lean_apply_1(x_3, x_7);
x_10 = lean_apply_2(x_4, lean_box(0), x_9);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_8);
x_11 = l_List_foldlM___redArg(x_5, x_10, x_2, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_6);
lean_closure_set(x_14, 3, x_8);
lean_closure_set(x_14, 4, x_12);
x_15 = l_List_foldlM___redArg(x_9, x_14, x_5, x_10);
return x_15;
}
}
static lean_object* _init_l_Lake_instComputeTraceListOfMonad___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftT___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lake_instComputeTraceListOfMonad___redArg___closed__0;
x_6 = lean_alloc_closure((void*)(l_Lake_computeListTrace), 10, 9);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, lean_box(0));
lean_closure_set(x_6, 3, x_1);
lean_closure_set(x_6, 4, x_2);
lean_closure_set(x_6, 5, x_3);
lean_closure_set(x_6, 6, lean_box(0));
lean_closure_set(x_6, 7, x_5);
lean_closure_set(x_6, 8, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_instComputeTraceListOfMonad___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_6);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_apply_2(x_9, lean_box(0), x_2);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_inc(x_8);
lean_inc(x_9);
x_14 = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_8);
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
if (x_12 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_14);
lean_inc(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_16 = lean_apply_2(x_9, lean_box(0), x_2);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_11);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_5, x_14, x_6, x_17, x_18, x_2);
return x_19;
}
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_11);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_5, x_14, x_6, x_20, x_21, x_2);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_10);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_13);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_17 = lean_apply_2(x_13, lean_box(0), x_5);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_inc(x_12);
lean_inc(x_13);
x_18 = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_8);
lean_closure_set(x_18, 4, x_12);
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
if (x_16 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_18);
lean_inc(x_13);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_20 = lean_apply_2(x_13, lean_box(0), x_5);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_9, x_18, x_10, x_21, x_22, x_5);
return x_23;
}
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_15);
x_26 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_9, x_18, x_10, x_24, x_25, x_5);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lake_instComputeTraceListOfMonad___redArg___closed__0;
x_6 = lean_alloc_closure((void*)(l_Lake_computeArrayTrace), 10, 9);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, lean_box(0));
lean_closure_set(x_6, 3, x_1);
lean_closure_set(x_6, 4, x_2);
lean_closure_set(x_6, 5, x_3);
lean_closure_set(x_6, 6, lean_box(0));
lean_closure_set(x_6, 7, x_5);
lean_closure_set(x_6, 8, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_instComputeTraceArrayOfMonad___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprHash_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("val", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprHash_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instReprHash_repr___redArg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprHash_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instReprHash_repr___redArg___closed__5;
x_2 = l_Lake_instReprHash_repr___redArg___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprHash_repr___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprHash_repr___redArg___closed__9;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprHash_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprHash_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprHash_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___redArg(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = l_Lake_instReprHash_repr___redArg___closed__6;
x_3 = l_Lake_instReprHash_repr___redArg___closed__7;
x_4 = lean_uint64_to_nat(x_1);
x_5 = l_Nat_reprFast(x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lake_instReprHash_repr___redArg___closed__10;
x_12 = l_Lake_instReprHash_repr___redArg___closed__11;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = l_Lake_instReprHash_repr___redArg___closed__12;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___redArg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_instReprHash_repr___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprHash_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprHash_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lake_instReprHash_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprHash___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instReprHash_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprHash() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprHash___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqHash_decEq(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lake_instDecidableEqHash_decEq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqHash(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lake_instDecidableEqHash(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_instHashable___lam__0(uint64_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_instHashable___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_Hash_instHashable___lam__0(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Hash_instHashable___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_instHashable___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_instHashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Hash_instHashable___closed__0;
return x_1;
}
}
static uint64_t _init_l_Lake_Hash_nil() {
_start:
{
uint64_t x_1; 
x_1 = 1723;
return x_1;
}
}
static uint64_t _init_l_Lake_Hash_instNilTrace() {
_start:
{
uint64_t x_1; 
x_1 = 1723;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofNat(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofNat___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_Hash_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("number is not a natural", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Hash_ofJsonNumber_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("number too big", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Hash_ofJsonNumber_x3f___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Hash_ofJsonNumber_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_14; uint8_t x_15; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
x_4 = x_15;
goto block_13;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lake_Hash_ofJsonNumber_x3f___closed__5;
x_17 = lean_int_dec_le(x_16, x_2);
x_4 = x_17;
goto block_13;
}
block_13:
{
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lake_Hash_ofJsonNumber_x3f___closed__1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Int_toNat(x_2);
x_7 = l_Lake_Hash_ofJsonNumber_x3f___closed__2;
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = l_Lake_Hash_ofJsonNumber_x3f___closed__4;
return x_9;
}
else
{
uint64_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_uint64_of_nat(x_6);
lean_dec(x_6);
x_11 = lean_box_uint64(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofJsonNumber_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Hash_ofJsonNumber_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
x_9 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
x_10 = lean_string_get_byte_fast(x_1, x_9);
x_11 = 57;
x_12 = lean_uint8_dec_le(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; 
x_13 = 97;
x_14 = lean_uint8_dec_le(x_13, x_10);
if (x_14 == 0)
{
uint64_t x_15; uint64_t x_16; uint8_t x_17; uint8_t x_18; uint64_t x_19; uint64_t x_20; 
x_15 = 4;
x_16 = lean_uint64_shift_left(x_4, x_15);
x_17 = 55;
x_18 = lean_uint8_sub(x_10, x_17);
x_19 = lean_uint8_to_uint64(x_18);
x_20 = lean_uint64_add(x_16, x_19);
x_3 = x_8;
x_4 = x_20;
goto _start;
}
else
{
uint64_t x_22; uint64_t x_23; uint8_t x_24; uint8_t x_25; uint64_t x_26; uint64_t x_27; 
x_22 = 4;
x_23 = lean_uint64_shift_left(x_4, x_22);
x_24 = 87;
x_25 = lean_uint8_sub(x_10, x_24);
x_26 = lean_uint8_to_uint64(x_25);
x_27 = lean_uint64_add(x_23, x_26);
x_3 = x_8;
x_4 = x_27;
goto _start;
}
}
else
{
uint64_t x_29; uint64_t x_30; uint8_t x_31; uint8_t x_32; uint64_t x_33; uint64_t x_34; 
x_29 = 4;
x_30 = lean_uint64_shift_left(x_4, x_29);
x_31 = 48;
x_32 = lean_uint8_sub(x_10, x_31);
x_33 = lean_uint8_to_uint64(x_32);
x_34 = lean_uint64_add(x_30, x_33);
x_3 = x_8;
x_4 = x_34;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; uint64_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_6 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(x_1, x_2, x_3, x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = lean_box_uint64(x_6);
return x_7;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofHex(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(x_1, x_2, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_Hash_ofHex(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint64_t x_5) {
_start:
{
uint64_t x_6; 
x_6 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; uint64_t x_7; lean_object* x_8; 
x_6 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_7 = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Hash_ofHex_spec__0(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
x_8 = lean_box_uint64(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_string_utf8_byte_size(x_1);
x_9 = lean_unsigned_to_nat(16u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
x_2 = x_10;
goto block_7;
}
else
{
uint8_t x_11; 
x_11 = l_Lake_isHex(x_1);
x_2 = x_11;
goto block_7;
}
block_7:
{
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint64_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lake_Hash_ofHex(x_1);
x_5 = lean_box_uint64(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofHex_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Hash_ofHex_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_hex(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_uint64_to_nat(x_1);
x_4 = l_Nat_toDigits(x_2, x_3);
x_5 = lean_string_mk(x_4);
x_6 = 48;
x_7 = l_Lake_lpad(x_5, x_6, x_2);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_hex___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_Hash_hex(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofDecimal_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_toNat_x3f(x_4);
lean_dec_ref(x_4);
x_6 = l_inline(lean_box(0), x_5);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_uint64_of_nat(x_9);
lean_dec(x_9);
x_11 = lean_box_uint64(x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_uint64_of_nat(x_12);
lean_dec(x_12);
x_14 = lean_box_uint64(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Hash_ofHex_x3f(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Hash_ofString_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lake_Hash_ofHex_x3f(x_4);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec_ref(x_3);
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Hash_load_x3f(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_mix(uint64_t x_1, uint64_t x_2) {
_start:
{
uint64_t x_3; 
x_3 = lean_uint64_mix_hash(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_mix___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lake_Hash_mix(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_Hash_instMixTrace___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_mix___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_instMixTrace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Hash_instMixTrace___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toString(uint64_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Hash_hex(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toString___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_Hash_toString(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Hash_instToString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_instToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Hash_instToString___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofString(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 1723;
x_3 = lean_string_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_Hash_ofString(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofText(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = l_String_crlfToLf(x_1);
x_3 = 1723;
x_4 = lean_string_hash(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofText___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_Hash_ofText(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofByteArray(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_byte_array_hash(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofByteArray___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_Hash_ofByteArray(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofBool(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint64_t x_2; 
x_2 = 13;
return x_2;
}
else
{
uint64_t x_3; 
x_3 = 11;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_Hash_ofBool(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_Hash_hex(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_Hash_toJson(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Hash_instToJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_toJson___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Hash_instToJson___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_fromJson_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid hash: expected hexadecimal string", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Hash_fromJson_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Hash_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid hash: expected hexadecimal string of length 16", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Hash_fromJson_x3f___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Hash_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid hash: ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid hash: expected string or number", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_fromJson_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Hash_fromJson_x3f___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_fromJson_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lake_isHex(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_free_object(x_1);
lean_dec_ref(x_3);
x_5 = l_Lake_Hash_fromJson_x3f___closed__1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_utf8_byte_size(x_3);
x_7 = lean_unsigned_to_nat(16u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_free_object(x_1);
lean_dec_ref(x_3);
x_9 = l_Lake_Hash_fromJson_x3f___closed__3;
return x_9;
}
else
{
uint64_t x_10; lean_object* x_11; 
x_10 = l_Lake_Hash_ofHex(x_3);
lean_dec_ref(x_3);
x_11 = lean_box_uint64(x_10);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lake_isHex(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_12);
x_14 = l_Lake_Hash_fromJson_x3f___closed__1;
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_string_utf8_byte_size(x_12);
x_16 = lean_unsigned_to_nat(16u);
x_17 = lean_nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_12);
x_18 = l_Lake_Hash_fromJson_x3f___closed__3;
return x_18;
}
else
{
uint64_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lake_Hash_ofHex(x_12);
lean_dec_ref(x_12);
x_20 = lean_box_uint64(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
case 2:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = l_Lake_Hash_ofJsonNumber_x3f(x_22);
lean_dec_ref(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lake_Hash_fromJson_x3f___closed__4;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l_Lake_Hash_fromJson_x3f___closed__4;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
return x_23;
}
}
default: 
{
lean_object* x_32; 
lean_dec(x_1);
x_32 = l_Lake_Hash_fromJson_x3f___closed__6;
return x_32;
}
}
}
}
static lean_object* _init_l_Lake_Hash_instFromJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Hash_instFromJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Hash_instFromJson___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instComputeTraceHashOfComputeHash___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instComputeTraceHashOfComputeHash(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lake_pureHash___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox_uint64(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_pureHash___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_Lake_pureHash___redArg(x_1, x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lake_pureHash(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_unbox_uint64(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_pureHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = l_Lake_pureHash(x_1, x_2, x_3);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_instComputeHashBoolId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_ofBool___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instComputeHashBoolId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instComputeHashBoolId___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instComputeHashStringId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_ofString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instComputeHashStringId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instComputeHashStringId___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readBinFile(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_byte_array_hash(x_5);
lean_dec(x_5);
x_7 = lean_box_uint64(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_byte_array_hash(x_8);
lean_dec(x_8);
x_10 = lean_box_uint64(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeBinFileHash(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instComputeHashFilePathIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_computeBinFileHash___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instComputeHashFilePathIO() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instComputeHashFilePathIO___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_String_crlfToLf(x_5);
lean_dec(x_5);
x_7 = 1723;
x_8 = lean_string_hash(x_6);
lean_dec_ref(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_box_uint64(x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_String_crlfToLf(x_11);
lean_dec(x_11);
x_13 = 1723;
x_14 = lean_string_hash(x_12);
lean_dec_ref(x_12);
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = lean_box_uint64(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeTextFileHash(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeTextFilePathFilePath___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instCoeTextFilePathFilePath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeTextFilePathFilePath___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeTextFilePathFilePath() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instCoeTextFilePathFilePath___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instComputeHashTextFilePathIO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_computeTextFileHash___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instComputeHashTextFilePathIO() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instComputeHashTextFilePathIO___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instToStringTextFilePath() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instCoeTextFilePathFilePath___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_4; 
x_4 = l_Lake_computeBinFileHash(x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lake_computeTextFileHash(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lake_computeFileHash(x_1, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0(uint64_t x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_uint64_mix_hash(x_1, x_3);
x_5 = lean_box_uint64(x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_6 = l_Lake_computeArrayHash___redArg___lam__0(x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box_uint64(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
x_8 = lean_apply_1(x_2, x_5);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_7 = l_Lake_computeArrayHash___redArg___lam__1(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_Lake_computeArrayHash___redArg___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 1723;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = l_Lake_computeArrayHash___redArg___boxed__const__1;
x_11 = lean_apply_2(x_6, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_inc(x_5);
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_5);
x_13 = lean_nat_dec_le(x_8, x_8);
if (x_13 == 0)
{
if (x_9 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_12);
lean_inc(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_14 = l_Lake_computeArrayHash___redArg___boxed__const__1;
x_15 = lean_apply_2(x_6, lean_box(0), x_14);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_8);
x_18 = l_Lake_computeArrayHash___redArg___boxed__const__1;
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_12, x_3, x_16, x_17, x_18);
return x_19;
}
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_8);
x_22 = l_Lake_computeArrayHash___redArg___boxed__const__1;
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_12, x_3, x_20, x_21, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lake_computeArrayHash___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 1723;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_5);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_12 = l_Lake_computeArrayHash___boxed__const__1;
x_13 = lean_apply_2(x_8, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_inc(x_7);
lean_inc(x_8);
x_14 = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_7);
x_15 = lean_nat_dec_le(x_10, x_10);
if (x_15 == 0)
{
if (x_11 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_14);
lean_inc(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_16 = l_Lake_computeArrayHash___boxed__const__1;
x_17 = lean_apply_2(x_8, lean_box(0), x_16);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_10);
x_20 = l_Lake_computeArrayHash___boxed__const__1;
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_4, x_14, x_5, x_18, x_19, x_20);
return x_21;
}
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_10);
x_24 = l_Lake_computeArrayHash___boxed__const__1;
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_4, x_14, x_5, x_22, x_23, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_computeArrayHash), 5, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lake_computeArrayHash), 5, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_MTime_instOfNat___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Hash_ofJsonNumber_x3f___closed__5;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_MTime_instOfNat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_MTime_instOfNat___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instBEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instBEqSystemTime_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instBEq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_MTime_instBEq___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instRepr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instReprSystemTime_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_MTime_instRepr___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instOrd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_instOrdSystemTime_ord___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_MTime_instOrd___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instLT() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instLE() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_IO_FS_instOrdSystemTime_ord(x_1, x_2);
if (x_3 == 2)
{
lean_inc_ref(x_2);
return x_2;
}
else
{
lean_inc_ref(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_MTime_instMin___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_MTime_instMin___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_MTime_instMin___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instMin() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_MTime_instMin___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_IO_FS_instOrdSystemTime_ord(x_1, x_2);
if (x_3 == 2)
{
lean_inc_ref(x_1);
return x_1;
}
else
{
lean_inc_ref(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_MTime_instMax___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_MTime_instMax___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_MTime_instMax___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instMax() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_MTime_instMax___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instNilTrace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_MTime_instOfNat___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instMixTrace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_MTime_instMax___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Trace_0__Lake_instComputeTraceIOMTimeOfGetMTime(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_getFileMTime(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instGetMTimeFilePath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getFileMTime___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instGetMTimeFilePath() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instGetMTimeFilePath___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instGetMTimeTextFilePath___lam__0(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instGetMTimeTextFilePath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instGetMTimeTextFilePath___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instGetMTimeTextFilePath() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instGetMTimeTextFilePath___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_IO_FS_instOrdSystemTime_ord(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec_ref(x_5);
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lake_MTime_checkUpToDate___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lake_MTime_checkUpToDate(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("caption", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprBuildTrace_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instReprBuildTrace_repr___redArg___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instReprHash_repr___redArg___closed__5;
x_2 = l_Lake_instReprBuildTrace_repr___redArg___closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(11u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputs", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprBuildTrace_repr___redArg___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = l_Lake_instReprBuildTrace_repr___redArg(x_5);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(x_1, x_8, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_1);
x_13 = l_Lake_instReprBuildTrace_repr___redArg(x_10);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(x_1, x_14, x_11);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Lake_instReprBuildTrace_repr___redArg(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lake_instReprBuildTrace_repr___redArg(x_7);
x_9 = l_List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1(x_2, x_8, x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[]", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_array_to_list(x_1);
x_6 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3;
x_7 = l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0(x_5, x_6);
x_8 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6;
x_9 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_11 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Std_Format_fill(x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10;
return x_15;
}
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hash", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprBuildTrace_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mtime", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprBuildTrace_repr___redArg___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = l_Lake_instReprHash_repr___redArg___closed__5;
x_7 = l_Lake_instReprBuildTrace_repr___redArg___closed__3;
x_8 = l_Lake_instReprBuildTrace_repr___redArg___closed__4;
x_9 = l_String_quote(x_2);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = 0;
x_13 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lake_instReprBuildTrace_repr___redArg___closed__6;
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
x_22 = l_Lake_instReprBuildTrace_repr___redArg___closed__7;
x_23 = l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0(x_3);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_12);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_15);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_17);
x_29 = l_Lake_instReprBuildTrace_repr___redArg___closed__9;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
x_32 = l_Lake_instReprBuildTrace_repr___redArg___closed__10;
x_33 = l_Lake_instReprHash_repr___redArg(x_4);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_12);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_15);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_17);
x_39 = l_Lake_instReprBuildTrace_repr___redArg___closed__12;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_6);
x_42 = l_Lake_instReprBuildTrace_repr___redArg___closed__13;
x_43 = l_IO_FS_instReprSystemTime_repr___redArg(x_5);
lean_dec_ref(x_5);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_12);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lake_instReprHash_repr___redArg___closed__10;
x_48 = l_Lake_instReprHash_repr___redArg___closed__11;
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
x_50 = l_Lake_instReprHash_repr___redArg___closed__12;
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_12);
return x_53;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = l_Lake_instReprBuildTrace_repr___redArg(x_5);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_2 = x_8;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_1);
x_13 = l_Lake_instReprBuildTrace_repr___redArg(x_10);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_2 = x_14;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprBuildTrace_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprBuildTrace_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instReprBuildTrace_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprBuildTrace___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_inc(x_5);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set_uint64(x_8, sizeof(void*)*3, x_6);
return x_8;
}
}
}
static lean_object* _init_l_Lake_BuildTrace_withoutInputs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lake_BuildTrace_withoutInputs___closed__0;
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_inc(x_5);
lean_dec(x_1);
x_8 = l_Lake_BuildTrace_withoutInputs___closed__0;
x_9 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set_uint64(x_9, sizeof(void*)*3, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_BuildTrace_withoutInputs___closed__0;
x_4 = l_Lake_MTime_instOfNat___closed__0;
x_5 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint64(x_5, sizeof(void*)*3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lake_BuildTrace_ofHash(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_BuildTrace_instCoeHash___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<hash>", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_BuildTrace_instCoeHash___lam__0___closed__0;
x_3 = l_Lake_BuildTrace_withoutInputs___closed__0;
x_4 = l_Lake_MTime_instOfNat___closed__0;
x_5 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint64(x_5, sizeof(void*)*3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_BuildTrace_instCoeHash___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildTrace_instCoeHash___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildTrace_instCoeHash___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildTrace_instCoeHash() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_BuildTrace_instCoeHash___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofMTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; lean_object* x_5; 
x_3 = l_Lake_BuildTrace_withoutInputs___closed__0;
x_4 = 1723;
x_5 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint64(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<mtime>", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; lean_object* x_5; 
x_2 = l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0;
x_3 = l_Lake_BuildTrace_withoutInputs___closed__0;
x_4 = 1723;
x_5 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint64(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_BuildTrace_instCoeMTime___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildTrace_instCoeMTime___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildTrace_instCoeMTime() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_BuildTrace_instCoeMTime___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_nil(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_BuildTrace_withoutInputs___closed__0;
x_3 = 1723;
x_4 = l_Lake_MTime_instOfNat___closed__0;
x_5 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint64(x_5, sizeof(void*)*3, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_BuildTrace_instNilTrace___closed__0;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_BuildTrace_instNilTrace___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_apply_3(x_3, lean_box(0), x_7, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_5);
x_10 = lean_apply_2(x_4, x_5, lean_box(0));
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_apply_1(x_1, x_5);
x_14 = l_Lake_BuildTrace_withoutInputs___closed__0;
x_15 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_12);
x_16 = lean_unbox_uint64(x_9);
lean_dec(x_9);
lean_ctor_set_uint64(x_15, sizeof(void*)*3, x_16);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_apply_1(x_1, x_5);
x_19 = l_Lake_BuildTrace_withoutInputs___closed__0;
x_20 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
x_21 = lean_unbox_uint64(x_9);
lean_dec(x_9);
lean_ctor_set_uint64(x_20, sizeof(void*)*3, x_21);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_10, 0);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_BuildTrace_compute___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_BuildTrace_compute___redArg(x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_BuildTrace_compute(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_1);
lean_closure_set(x_5, 3, x_2);
lean_closure_set(x_5, 4, x_3);
lean_closure_set(x_5, 5, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute___boxed), 8, 6);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_4);
lean_closure_set(x_7, 4, x_5);
lean_closure_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_mix(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_8 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_8);
x_9 = lean_array_push(x_4, x_2);
x_10 = lean_uint64_mix_hash(x_5, x_7);
x_11 = l_IO_FS_instOrdSystemTime_ord(x_6, x_8);
if (x_11 == 2)
{
lean_dec_ref(x_8);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set_uint64(x_1, sizeof(void*)*3, x_10);
return x_1;
}
else
{
lean_dec_ref(x_6);
lean_ctor_set(x_1, 2, x_8);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set_uint64(x_1, sizeof(void*)*3, x_10);
return x_1;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_16 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_17 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_17);
x_18 = lean_array_push(x_13, x_2);
x_19 = lean_uint64_mix_hash(x_14, x_16);
x_20 = l_IO_FS_instOrdSystemTime_ord(x_15, x_17);
if (x_20 == 2)
{
lean_object* x_21; 
lean_dec_ref(x_17);
x_21 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set_uint64(x_21, sizeof(void*)*3, x_19);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_15);
x_22 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set_uint64(x_22, sizeof(void*)*3, x_19);
return x_22;
}
}
}
}
static lean_object* _init_l_Lake_BuildTrace_instMixTrace___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildTrace_mix), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildTrace_instMixTrace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_BuildTrace_instMixTrace___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash___redArg(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
uint64_t x_6; uint8_t x_7; 
x_6 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_7 = lean_uint64_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_apply_2(x_1, x_2, lean_box(0));
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_7 = l_Lake_BuildTrace_checkAgainstHash___redArg(x_1, x_2, x_6, x_4);
lean_dec_ref(x_4);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstHash(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = l_Lake_BuildTrace_checkAgainstHash___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Lake_BuildTrace_checkAgainstHash(x_1, x_2, x_3, x_7, x_5);
lean_dec_ref(x_5);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lake_MTime_checkUpToDate___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lake_BuildTrace_checkAgainstTime___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildTrace_checkAgainstTime(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 2);
x_7 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lake_BuildTrace_checkAgainstTime(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Fold(uint8_t builtin);
lean_object* initialize_Lake_Util_String(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin);
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
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instCheckExistsFilePath___closed__0 = _init_l_Lake_instCheckExistsFilePath___closed__0();
lean_mark_persistent(l_Lake_instCheckExistsFilePath___closed__0);
l_Lake_instCheckExistsFilePath = _init_l_Lake_instCheckExistsFilePath();
lean_mark_persistent(l_Lake_instCheckExistsFilePath);
l_Lake_mixTraceArray___redArg___closed__0 = _init_l_Lake_mixTraceArray___redArg___closed__0();
lean_mark_persistent(l_Lake_mixTraceArray___redArg___closed__0);
l_Lake_mixTraceArray___redArg___closed__1 = _init_l_Lake_mixTraceArray___redArg___closed__1();
lean_mark_persistent(l_Lake_mixTraceArray___redArg___closed__1);
l_Lake_mixTraceArray___redArg___closed__2 = _init_l_Lake_mixTraceArray___redArg___closed__2();
lean_mark_persistent(l_Lake_mixTraceArray___redArg___closed__2);
l_Lake_mixTraceArray___redArg___closed__3 = _init_l_Lake_mixTraceArray___redArg___closed__3();
lean_mark_persistent(l_Lake_mixTraceArray___redArg___closed__3);
l_Lake_mixTraceArray___redArg___closed__4 = _init_l_Lake_mixTraceArray___redArg___closed__4();
lean_mark_persistent(l_Lake_mixTraceArray___redArg___closed__4);
l_Lake_mixTraceArray___redArg___closed__5 = _init_l_Lake_mixTraceArray___redArg___closed__5();
lean_mark_persistent(l_Lake_mixTraceArray___redArg___closed__5);
l_Lake_mixTraceArray___redArg___closed__6 = _init_l_Lake_mixTraceArray___redArg___closed__6();
lean_mark_persistent(l_Lake_mixTraceArray___redArg___closed__6);
l_Lake_mixTraceArray___redArg___closed__7 = _init_l_Lake_mixTraceArray___redArg___closed__7();
lean_mark_persistent(l_Lake_mixTraceArray___redArg___closed__7);
l_Lake_mixTraceArray___redArg___closed__8 = _init_l_Lake_mixTraceArray___redArg___closed__8();
lean_mark_persistent(l_Lake_mixTraceArray___redArg___closed__8);
l_Lake_mixTraceArray___redArg___closed__9 = _init_l_Lake_mixTraceArray___redArg___closed__9();
lean_mark_persistent(l_Lake_mixTraceArray___redArg___closed__9);
l_Lake_instComputeTraceListOfMonad___redArg___closed__0 = _init_l_Lake_instComputeTraceListOfMonad___redArg___closed__0();
lean_mark_persistent(l_Lake_instComputeTraceListOfMonad___redArg___closed__0);
l_Lake_instReprHash_repr___redArg___closed__0 = _init_l_Lake_instReprHash_repr___redArg___closed__0();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__0);
l_Lake_instReprHash_repr___redArg___closed__1 = _init_l_Lake_instReprHash_repr___redArg___closed__1();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__1);
l_Lake_instReprHash_repr___redArg___closed__2 = _init_l_Lake_instReprHash_repr___redArg___closed__2();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__2);
l_Lake_instReprHash_repr___redArg___closed__3 = _init_l_Lake_instReprHash_repr___redArg___closed__3();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__3);
l_Lake_instReprHash_repr___redArg___closed__4 = _init_l_Lake_instReprHash_repr___redArg___closed__4();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__4);
l_Lake_instReprHash_repr___redArg___closed__5 = _init_l_Lake_instReprHash_repr___redArg___closed__5();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__5);
l_Lake_instReprHash_repr___redArg___closed__6 = _init_l_Lake_instReprHash_repr___redArg___closed__6();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__6);
l_Lake_instReprHash_repr___redArg___closed__7 = _init_l_Lake_instReprHash_repr___redArg___closed__7();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__7);
l_Lake_instReprHash_repr___redArg___closed__8 = _init_l_Lake_instReprHash_repr___redArg___closed__8();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__8);
l_Lake_instReprHash_repr___redArg___closed__9 = _init_l_Lake_instReprHash_repr___redArg___closed__9();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__9);
l_Lake_instReprHash_repr___redArg___closed__10 = _init_l_Lake_instReprHash_repr___redArg___closed__10();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__10);
l_Lake_instReprHash_repr___redArg___closed__11 = _init_l_Lake_instReprHash_repr___redArg___closed__11();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__11);
l_Lake_instReprHash_repr___redArg___closed__12 = _init_l_Lake_instReprHash_repr___redArg___closed__12();
lean_mark_persistent(l_Lake_instReprHash_repr___redArg___closed__12);
l_Lake_instReprHash___closed__0 = _init_l_Lake_instReprHash___closed__0();
lean_mark_persistent(l_Lake_instReprHash___closed__0);
l_Lake_instReprHash = _init_l_Lake_instReprHash();
lean_mark_persistent(l_Lake_instReprHash);
l_Lake_Hash_instHashable___closed__0 = _init_l_Lake_Hash_instHashable___closed__0();
lean_mark_persistent(l_Lake_Hash_instHashable___closed__0);
l_Lake_Hash_instHashable = _init_l_Lake_Hash_instHashable();
lean_mark_persistent(l_Lake_Hash_instHashable);
l_Lake_Hash_nil = _init_l_Lake_Hash_nil();
l_Lake_Hash_instNilTrace = _init_l_Lake_Hash_instNilTrace();
l_Lake_Hash_ofJsonNumber_x3f___closed__0 = _init_l_Lake_Hash_ofJsonNumber_x3f___closed__0();
lean_mark_persistent(l_Lake_Hash_ofJsonNumber_x3f___closed__0);
l_Lake_Hash_ofJsonNumber_x3f___closed__1 = _init_l_Lake_Hash_ofJsonNumber_x3f___closed__1();
lean_mark_persistent(l_Lake_Hash_ofJsonNumber_x3f___closed__1);
l_Lake_Hash_ofJsonNumber_x3f___closed__2 = _init_l_Lake_Hash_ofJsonNumber_x3f___closed__2();
lean_mark_persistent(l_Lake_Hash_ofJsonNumber_x3f___closed__2);
l_Lake_Hash_ofJsonNumber_x3f___closed__3 = _init_l_Lake_Hash_ofJsonNumber_x3f___closed__3();
lean_mark_persistent(l_Lake_Hash_ofJsonNumber_x3f___closed__3);
l_Lake_Hash_ofJsonNumber_x3f___closed__4 = _init_l_Lake_Hash_ofJsonNumber_x3f___closed__4();
lean_mark_persistent(l_Lake_Hash_ofJsonNumber_x3f___closed__4);
l_Lake_Hash_ofJsonNumber_x3f___closed__5 = _init_l_Lake_Hash_ofJsonNumber_x3f___closed__5();
lean_mark_persistent(l_Lake_Hash_ofJsonNumber_x3f___closed__5);
l_Lake_Hash_instMixTrace___closed__0 = _init_l_Lake_Hash_instMixTrace___closed__0();
lean_mark_persistent(l_Lake_Hash_instMixTrace___closed__0);
l_Lake_Hash_instMixTrace = _init_l_Lake_Hash_instMixTrace();
lean_mark_persistent(l_Lake_Hash_instMixTrace);
l_Lake_Hash_instToString___closed__0 = _init_l_Lake_Hash_instToString___closed__0();
lean_mark_persistent(l_Lake_Hash_instToString___closed__0);
l_Lake_Hash_instToString = _init_l_Lake_Hash_instToString();
lean_mark_persistent(l_Lake_Hash_instToString);
l_Lake_Hash_instToJson___closed__0 = _init_l_Lake_Hash_instToJson___closed__0();
lean_mark_persistent(l_Lake_Hash_instToJson___closed__0);
l_Lake_Hash_instToJson = _init_l_Lake_Hash_instToJson();
lean_mark_persistent(l_Lake_Hash_instToJson);
l_Lake_Hash_fromJson_x3f___closed__0 = _init_l_Lake_Hash_fromJson_x3f___closed__0();
lean_mark_persistent(l_Lake_Hash_fromJson_x3f___closed__0);
l_Lake_Hash_fromJson_x3f___closed__1 = _init_l_Lake_Hash_fromJson_x3f___closed__1();
lean_mark_persistent(l_Lake_Hash_fromJson_x3f___closed__1);
l_Lake_Hash_fromJson_x3f___closed__2 = _init_l_Lake_Hash_fromJson_x3f___closed__2();
lean_mark_persistent(l_Lake_Hash_fromJson_x3f___closed__2);
l_Lake_Hash_fromJson_x3f___closed__3 = _init_l_Lake_Hash_fromJson_x3f___closed__3();
lean_mark_persistent(l_Lake_Hash_fromJson_x3f___closed__3);
l_Lake_Hash_fromJson_x3f___closed__4 = _init_l_Lake_Hash_fromJson_x3f___closed__4();
lean_mark_persistent(l_Lake_Hash_fromJson_x3f___closed__4);
l_Lake_Hash_fromJson_x3f___closed__5 = _init_l_Lake_Hash_fromJson_x3f___closed__5();
lean_mark_persistent(l_Lake_Hash_fromJson_x3f___closed__5);
l_Lake_Hash_fromJson_x3f___closed__6 = _init_l_Lake_Hash_fromJson_x3f___closed__6();
lean_mark_persistent(l_Lake_Hash_fromJson_x3f___closed__6);
l_Lake_Hash_instFromJson___closed__0 = _init_l_Lake_Hash_instFromJson___closed__0();
lean_mark_persistent(l_Lake_Hash_instFromJson___closed__0);
l_Lake_Hash_instFromJson = _init_l_Lake_Hash_instFromJson();
lean_mark_persistent(l_Lake_Hash_instFromJson);
l_Lake_instComputeHashBoolId___closed__0 = _init_l_Lake_instComputeHashBoolId___closed__0();
lean_mark_persistent(l_Lake_instComputeHashBoolId___closed__0);
l_Lake_instComputeHashBoolId = _init_l_Lake_instComputeHashBoolId();
lean_mark_persistent(l_Lake_instComputeHashBoolId);
l_Lake_instComputeHashStringId___closed__0 = _init_l_Lake_instComputeHashStringId___closed__0();
lean_mark_persistent(l_Lake_instComputeHashStringId___closed__0);
l_Lake_instComputeHashStringId = _init_l_Lake_instComputeHashStringId();
lean_mark_persistent(l_Lake_instComputeHashStringId);
l_Lake_instComputeHashFilePathIO___closed__0 = _init_l_Lake_instComputeHashFilePathIO___closed__0();
lean_mark_persistent(l_Lake_instComputeHashFilePathIO___closed__0);
l_Lake_instComputeHashFilePathIO = _init_l_Lake_instComputeHashFilePathIO();
lean_mark_persistent(l_Lake_instComputeHashFilePathIO);
l_Lake_instCoeTextFilePathFilePath___closed__0 = _init_l_Lake_instCoeTextFilePathFilePath___closed__0();
lean_mark_persistent(l_Lake_instCoeTextFilePathFilePath___closed__0);
l_Lake_instCoeTextFilePathFilePath = _init_l_Lake_instCoeTextFilePathFilePath();
lean_mark_persistent(l_Lake_instCoeTextFilePathFilePath);
l_Lake_instComputeHashTextFilePathIO___closed__0 = _init_l_Lake_instComputeHashTextFilePathIO___closed__0();
lean_mark_persistent(l_Lake_instComputeHashTextFilePathIO___closed__0);
l_Lake_instComputeHashTextFilePathIO = _init_l_Lake_instComputeHashTextFilePathIO();
lean_mark_persistent(l_Lake_instComputeHashTextFilePathIO);
l_Lake_instToStringTextFilePath = _init_l_Lake_instToStringTextFilePath();
lean_mark_persistent(l_Lake_instToStringTextFilePath);
l_Lake_computeArrayHash___redArg___boxed__const__1 = _init_l_Lake_computeArrayHash___redArg___boxed__const__1();
lean_mark_persistent(l_Lake_computeArrayHash___redArg___boxed__const__1);
l_Lake_computeArrayHash___boxed__const__1 = _init_l_Lake_computeArrayHash___boxed__const__1();
lean_mark_persistent(l_Lake_computeArrayHash___boxed__const__1);
l_Lake_MTime_instOfNat___closed__0 = _init_l_Lake_MTime_instOfNat___closed__0();
lean_mark_persistent(l_Lake_MTime_instOfNat___closed__0);
l_Lake_MTime_instOfNat = _init_l_Lake_MTime_instOfNat();
lean_mark_persistent(l_Lake_MTime_instOfNat);
l_Lake_MTime_instBEq___closed__0 = _init_l_Lake_MTime_instBEq___closed__0();
lean_mark_persistent(l_Lake_MTime_instBEq___closed__0);
l_Lake_MTime_instBEq = _init_l_Lake_MTime_instBEq();
lean_mark_persistent(l_Lake_MTime_instBEq);
l_Lake_MTime_instRepr___closed__0 = _init_l_Lake_MTime_instRepr___closed__0();
lean_mark_persistent(l_Lake_MTime_instRepr___closed__0);
l_Lake_MTime_instRepr = _init_l_Lake_MTime_instRepr();
lean_mark_persistent(l_Lake_MTime_instRepr);
l_Lake_MTime_instOrd___closed__0 = _init_l_Lake_MTime_instOrd___closed__0();
lean_mark_persistent(l_Lake_MTime_instOrd___closed__0);
l_Lake_MTime_instOrd = _init_l_Lake_MTime_instOrd();
lean_mark_persistent(l_Lake_MTime_instOrd);
l_Lake_MTime_instLT = _init_l_Lake_MTime_instLT();
lean_mark_persistent(l_Lake_MTime_instLT);
l_Lake_MTime_instLE = _init_l_Lake_MTime_instLE();
lean_mark_persistent(l_Lake_MTime_instLE);
l_Lake_MTime_instMin___closed__0 = _init_l_Lake_MTime_instMin___closed__0();
lean_mark_persistent(l_Lake_MTime_instMin___closed__0);
l_Lake_MTime_instMin = _init_l_Lake_MTime_instMin();
lean_mark_persistent(l_Lake_MTime_instMin);
l_Lake_MTime_instMax___closed__0 = _init_l_Lake_MTime_instMax___closed__0();
lean_mark_persistent(l_Lake_MTime_instMax___closed__0);
l_Lake_MTime_instMax = _init_l_Lake_MTime_instMax();
lean_mark_persistent(l_Lake_MTime_instMax);
l_Lake_MTime_instNilTrace = _init_l_Lake_MTime_instNilTrace();
lean_mark_persistent(l_Lake_MTime_instNilTrace);
l_Lake_MTime_instMixTrace = _init_l_Lake_MTime_instMixTrace();
lean_mark_persistent(l_Lake_MTime_instMixTrace);
l_Lake_instGetMTimeFilePath___closed__0 = _init_l_Lake_instGetMTimeFilePath___closed__0();
lean_mark_persistent(l_Lake_instGetMTimeFilePath___closed__0);
l_Lake_instGetMTimeFilePath = _init_l_Lake_instGetMTimeFilePath();
lean_mark_persistent(l_Lake_instGetMTimeFilePath);
l_Lake_instGetMTimeTextFilePath___closed__0 = _init_l_Lake_instGetMTimeTextFilePath___closed__0();
lean_mark_persistent(l_Lake_instGetMTimeTextFilePath___closed__0);
l_Lake_instGetMTimeTextFilePath = _init_l_Lake_instGetMTimeTextFilePath();
lean_mark_persistent(l_Lake_instGetMTimeTextFilePath);
l_Lake_instReprBuildTrace_repr___redArg___closed__0 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__0();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__0);
l_Lake_instReprBuildTrace_repr___redArg___closed__1 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__1();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__1);
l_Lake_instReprBuildTrace_repr___redArg___closed__2 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__2();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__2);
l_Lake_instReprBuildTrace_repr___redArg___closed__3 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__3();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__3);
l_Lake_instReprBuildTrace_repr___redArg___closed__4 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__4();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__4);
l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1 = _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__1);
l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2 = _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__2);
l_Lake_instReprBuildTrace_repr___redArg___closed__5 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__5();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__5);
l_Lake_instReprBuildTrace_repr___redArg___closed__6 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__6();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__6);
l_Lake_instReprBuildTrace_repr___redArg___closed__7 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__7();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__7);
l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3 = _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__3);
l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0 = _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__0);
l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5 = _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__5);
l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6 = _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__6);
l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7 = _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__7);
l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4 = _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__4);
l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8 = _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__8);
l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9 = _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__9);
l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10 = _init_l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10();
lean_mark_persistent(l_Array_Array_repr___at___00Lake_instReprBuildTrace_repr_spec__0___closed__10);
l_Lake_instReprBuildTrace_repr___redArg___closed__8 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__8();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__8);
l_Lake_instReprBuildTrace_repr___redArg___closed__9 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__9();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__9);
l_Lake_instReprBuildTrace_repr___redArg___closed__10 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__10();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__10);
l_Lake_instReprBuildTrace_repr___redArg___closed__11 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__11();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__11);
l_Lake_instReprBuildTrace_repr___redArg___closed__12 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__12();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__12);
l_Lake_instReprBuildTrace_repr___redArg___closed__13 = _init_l_Lake_instReprBuildTrace_repr___redArg___closed__13();
lean_mark_persistent(l_Lake_instReprBuildTrace_repr___redArg___closed__13);
l_Lake_instReprBuildTrace___closed__0 = _init_l_Lake_instReprBuildTrace___closed__0();
lean_mark_persistent(l_Lake_instReprBuildTrace___closed__0);
l_Lake_instReprBuildTrace = _init_l_Lake_instReprBuildTrace();
lean_mark_persistent(l_Lake_instReprBuildTrace);
l_Lake_BuildTrace_withoutInputs___closed__0 = _init_l_Lake_BuildTrace_withoutInputs___closed__0();
lean_mark_persistent(l_Lake_BuildTrace_withoutInputs___closed__0);
l_Lake_BuildTrace_instCoeHash___lam__0___closed__0 = _init_l_Lake_BuildTrace_instCoeHash___lam__0___closed__0();
lean_mark_persistent(l_Lake_BuildTrace_instCoeHash___lam__0___closed__0);
l_Lake_BuildTrace_instCoeHash___closed__0 = _init_l_Lake_BuildTrace_instCoeHash___closed__0();
lean_mark_persistent(l_Lake_BuildTrace_instCoeHash___closed__0);
l_Lake_BuildTrace_instCoeHash = _init_l_Lake_BuildTrace_instCoeHash();
lean_mark_persistent(l_Lake_BuildTrace_instCoeHash);
l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0 = _init_l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0();
lean_mark_persistent(l_Lake_BuildTrace_instCoeMTime___lam__0___closed__0);
l_Lake_BuildTrace_instCoeMTime___closed__0 = _init_l_Lake_BuildTrace_instCoeMTime___closed__0();
lean_mark_persistent(l_Lake_BuildTrace_instCoeMTime___closed__0);
l_Lake_BuildTrace_instCoeMTime = _init_l_Lake_BuildTrace_instCoeMTime();
lean_mark_persistent(l_Lake_BuildTrace_instCoeMTime);
l_Lake_BuildTrace_instNilTrace___closed__0 = _init_l_Lake_BuildTrace_instNilTrace___closed__0();
lean_mark_persistent(l_Lake_BuildTrace_instNilTrace___closed__0);
l_Lake_BuildTrace_instNilTrace___closed__1 = _init_l_Lake_BuildTrace_instNilTrace___closed__1();
lean_mark_persistent(l_Lake_BuildTrace_instNilTrace___closed__1);
l_Lake_BuildTrace_instNilTrace = _init_l_Lake_BuildTrace_instNilTrace();
lean_mark_persistent(l_Lake_BuildTrace_instNilTrace);
l_Lake_BuildTrace_instMixTrace___closed__0 = _init_l_Lake_BuildTrace_instMixTrace___closed__0();
lean_mark_persistent(l_Lake_BuildTrace_instMixTrace___closed__0);
l_Lake_BuildTrace_instMixTrace = _init_l_Lake_BuildTrace_instMixTrace();
lean_mark_persistent(l_Lake_BuildTrace_instMixTrace);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
