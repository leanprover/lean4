// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Parser
// Imports: Init.System.IO Std.Tactic.BVDecide.LRAT.Actions Std.Internal.Parsec
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1;
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object*);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___closed__1;
extern lean_object* l_Int_instInhabited;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseLit(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___rarg(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString___spec__1___closed__1;
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4;
extern lean_object* l_Std_Internal_Parsec_expectedEndOfInput;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__6;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1;
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object*);
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1;
uint64_t lean_uint64_land(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(lean_object*);
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause___spec__1(lean_object*);
static lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object*);
uint64_t lean_uint8_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
extern lean_object* l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_object* l_outOfBounds___rarg(lean_object*);
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__1;
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__5;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(lean_object*, lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object*, lean_object*);
uint8_t lean_uint64_to_uint8(uint64_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___lambda__1___boxed(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___spec__1(lean_object*, lean_object*);
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t, uint64_t, lean_object*);
uint8_t lean_uint8_complement(uint8_t);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__2(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3;
lean_object* lean_mk_empty_byte_array(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_digits(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5;
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
extern lean_object* l_ByteArray_instInhabited;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object*, uint64_t);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___rarg(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
static uint8_t l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___lambda__1___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object*);
static uint8_t l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___closed__1;
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__8;
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
static lean_object* l_Std_Internal_Parsec_satisfy___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__7;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___lambda__1(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints___spec__2(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3;
LEAN_EXPORT lean_object* l_panic___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___spec__1(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2;
static lean_object* _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Int_instInhabited;
x_6 = l_outOfBounds___rarg(x_5);
x_7 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_8 = lean_int_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_nat_abs(x_6);
lean_dec(x_6);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_nat_abs(x_6);
lean_dec(x_6);
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_array_fget(x_1, x_3);
x_18 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_19 = lean_int_dec_lt(x_18, x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_nat_abs(x_17);
lean_dec(x_17);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_nat_abs(x_17);
lean_dec(x_17);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_1);
lean_dec(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 10;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\r\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2;
x_2 = lean_string_to_utf8(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1;
x_2 = lean_uint8_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4;
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected: '", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6;
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7;
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = lean_nat_dec_eq(x_3, x_3);
lean_dec(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
x_10 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_21 = lean_byte_array_fget(x_2, x_3);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1;
x_26 = lean_uint8_dec_eq(x_21, x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_24);
x_27 = lean_nat_dec_eq(x_3, x_3);
lean_dec(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
x_31 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_30, x_1);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 1);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 1, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_1, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_1, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_1, 1, x_45);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_24);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("id was 0", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_Parsec_ByteArray_digits(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_13 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 45;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1;
x_2 = lean_uint8_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2;
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6;
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4;
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_8 = lean_byte_array_fget(x_2, x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1;
x_13 = lean_uint8_dec_eq(x_8, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_nat_to_int(x_18);
x_20 = lean_int_neg(x_19);
lean_dec(x_19);
lean_ctor_set(x_16, 1, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_nat_to_int(x_22);
x_24 = lean_int_neg(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(x_1);
return x_2;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 48;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
x_2 = lean_uint8_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2;
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6;
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4;
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_8 = lean_byte_array_fget(x_2, x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
x_13 = lean_uint8_dec_eq(x_8, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 32;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_2 = lean_uint8_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2;
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6;
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4;
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_byte_array_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_10 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_10);
return x_2;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_11 = lean_byte_array_fget(x_6, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_16 = lean_uint8_dec_eq(x_11, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_5);
x_17 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_17);
return x_2;
}
else
{
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_byte_array_size(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_24 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_26 = lean_byte_array_fget(x_20, x_21);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_21, x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_31 = lean_uint8_dec_eq(x_26, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_19);
x_32 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_18);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_19);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_2, 0);
lean_dec(x_36);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_push(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_dec(x_10);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_1);
return x_20;
}
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
x_3 = l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___spec__1(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 100;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1;
x_2 = lean_uint8_to_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2;
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6;
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4;
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_8 = lean_byte_array_fget(x_2, x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1;
x_13 = lean_uint8_dec_eq(x_8, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_14 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
x_19 = lean_nat_dec_lt(x_10, x_4);
lean_dec(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_2);
x_20 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_22 = lean_byte_array_fget(x_2, x_10);
x_23 = lean_nat_add(x_10, x_9);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_23);
x_24 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_25 = lean_uint8_dec_eq(x_22, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_26 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_11);
x_28 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_1);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_byte_array_size(x_32);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_36 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_36);
return x_28;
}
else
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; 
x_37 = lean_byte_array_fget(x_32, x_33);
x_38 = lean_nat_add(x_33, x_9);
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
x_41 = lean_uint8_dec_eq(x_37, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_31);
x_42 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5;
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_42);
return x_28;
}
else
{
lean_object* x_43; 
lean_dec(x_30);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_28, 1, x_43);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
x_48 = lean_byte_array_size(x_46);
x_49 = lean_nat_dec_lt(x_47, x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_50 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
else
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_52 = lean_byte_array_fget(x_46, x_47);
x_53 = lean_nat_add(x_47, x_9);
lean_dec(x_47);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
x_56 = lean_uint8_dec_eq(x_52, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_54);
lean_dec(x_45);
x_57 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_44);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_45);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_28);
if (x_61 == 0)
{
return x_28;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_28, 0);
x_63 = lean_ctor_get(x_28, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_28);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_1);
x_65 = lean_nat_dec_lt(x_10, x_4);
lean_dec(x_4);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_10);
lean_dec(x_2);
x_66 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_11);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
else
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; 
x_68 = lean_byte_array_fget(x_2, x_10);
x_69 = lean_nat_add(x_10, x_9);
lean_dec(x_10);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_2);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_72 = lean_uint8_dec_eq(x_68, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_70);
x_73 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_11);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_11);
x_75 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_70);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
x_81 = lean_byte_array_size(x_79);
x_82 = lean_nat_dec_lt(x_80, x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_77);
x_83 = l_Std_Internal_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_78)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_78;
 lean_ctor_set_tag(x_84, 1);
}
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
else
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; 
x_85 = lean_byte_array_fget(x_79, x_80);
x_86 = lean_nat_add(x_80, x_9);
lean_dec(x_80);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
x_89 = lean_uint8_dec_eq(x_85, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_87);
lean_dec(x_77);
x_90 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5;
if (lean_is_scalar(x_78)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_78;
 lean_ctor_set_tag(x_91, 1);
}
lean_ctor_set(x_91, 0, x_76);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_76);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_77);
if (lean_is_scalar(x_78)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_78;
}
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_75, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_75, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_96 = x_75;
} else {
 lean_dec_ref(x_75);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_byte_array_fget(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_9 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1;
x_10 = lean_uint8_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(x_1);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_nat_to_int(x_13);
lean_ctor_set(x_11, 1, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_nat_to_int(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
x_23 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(x_1);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_byte_array_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_10 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_10);
return x_2;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_11 = lean_byte_array_fget(x_6, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_16 = lean_uint8_dec_eq(x_11, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_5);
x_17 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_17);
return x_2;
}
else
{
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_byte_array_size(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_24 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_26 = lean_byte_array_fget(x_20, x_21);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_21, x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_31 = lean_uint8_dec_eq(x_26, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_19);
x_32 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_18);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_19);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_2, 0);
lean_dec(x_36);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_push(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_dec(x_10);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_1);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
x_3 = l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause___spec__1(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_byte_array_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_11 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_12 = lean_byte_array_fget(x_7, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_8, x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
x_17 = lean_uint8_dec_eq(x_12, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_6);
x_18 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_18);
return x_3;
}
else
{
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_byte_array_size(x_21);
x_24 = lean_nat_dec_lt(x_22, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_25 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_27 = lean_byte_array_fget(x_21, x_22);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_22, x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
x_32 = lean_uint8_dec_eq(x_27, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_20);
x_33 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_19);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_20);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_3);
if (x_36 == 0)
{
return x_3;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_3, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_3);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_byte_array_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_10 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_10);
return x_2;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_11 = lean_byte_array_fget(x_6, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_16 = lean_uint8_dec_eq(x_11, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_5);
x_17 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_17);
return x_2;
}
else
{
uint8_t x_18; 
lean_free_object(x_2);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_4, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 0);
lean_dec(x_20);
x_21 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_nat_abs(x_5);
lean_dec(x_5);
lean_ctor_set(x_4, 1, x_23);
lean_ctor_set(x_4, 0, x_24);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_nat_abs(x_5);
lean_dec(x_5);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_4, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_4);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_4);
x_33 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_14);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_nat_abs(x_5);
lean_dec(x_5);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_5);
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_42 = x_33;
} else {
 lean_dec_ref(x_33);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_2);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
x_48 = lean_byte_array_size(x_46);
x_49 = lean_nat_dec_lt(x_47, x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_50 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
else
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; 
x_52 = lean_byte_array_fget(x_46, x_47);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_47, x_53);
lean_dec(x_47);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_57 = lean_uint8_dec_eq(x_52, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_45);
x_58 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_60 = x_44;
} else {
 lean_dec_ref(x_44);
 x_60 = lean_box(0);
}
x_61 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_55);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_nat_abs(x_45);
lean_dec(x_45);
if (lean_is_scalar(x_60)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_60;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_60);
lean_dec(x_45);
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_70 = x_61;
} else {
 lean_dec_ref(x_61);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_2);
if (x_72 == 0)
{
return x_2;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_2);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_push(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_nat_dec_eq(x_11, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_dec(x_9);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_nat_dec_eq(x_14, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_1);
return x_17;
}
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("There cannot be any ratHints for adding the empty clause", 56, 56);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_byte_array_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_12 = lean_byte_array_fget(x_7, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_8, x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_17 = lean_uint8_dec_eq(x_12, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_18 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_18);
return x_3;
}
else
{
uint8_t x_19; 
lean_free_object(x_3);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_5, 0);
lean_dec(x_21);
x_22 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
x_26 = l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___spec__1(x_25, x_23);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = lean_byte_array_size(x_30);
x_33 = lean_nat_dec_lt(x_31, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_free_object(x_5);
lean_dec(x_6);
lean_dec(x_1);
x_34 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_34);
return x_26;
}
else
{
uint8_t x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; 
x_35 = lean_byte_array_fget(x_30, x_31);
x_36 = lean_nat_add(x_31, x_13);
lean_dec(x_31);
lean_ctor_set(x_5, 1, x_36);
lean_ctor_set(x_5, 0, x_30);
x_37 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
x_38 = lean_uint8_dec_eq(x_35, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_5);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_1);
x_39 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5;
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_39);
return x_26;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_28, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_28, 0);
lean_dec(x_42);
x_43 = lean_array_get_size(x_6);
x_44 = lean_array_get_size(x_29);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_eq(x_43, x_45);
lean_dec(x_43);
if (x_46 == 0)
{
uint8_t x_47; 
lean_free_object(x_28);
x_47 = lean_nat_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_6);
x_49 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_6);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_24);
lean_ctor_set(x_49, 4, x_29);
lean_ctor_set(x_26, 1, x_49);
lean_ctor_set(x_26, 0, x_5);
return x_26;
}
else
{
lean_object* x_50; 
lean_dec(x_29);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_6);
lean_ctor_set(x_50, 2, x_24);
lean_ctor_set(x_26, 1, x_50);
lean_ctor_set(x_26, 0, x_5);
return x_26;
}
}
else
{
uint8_t x_51; 
lean_dec(x_29);
lean_dec(x_6);
x_51 = lean_nat_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_51 == 0)
{
lean_object* x_52; 
lean_free_object(x_28);
lean_dec(x_24);
lean_dec(x_1);
x_52 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1;
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_52);
lean_ctor_set(x_26, 0, x_5);
return x_26;
}
else
{
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_26, 1, x_28);
lean_ctor_set(x_26, 0, x_5);
return x_26;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_28);
x_53 = lean_array_get_size(x_6);
x_54 = lean_array_get_size(x_29);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_nat_dec_eq(x_53, x_55);
lean_dec(x_53);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = lean_nat_dec_eq(x_54, x_55);
lean_dec(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_6);
x_59 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_6);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set(x_59, 3, x_24);
lean_ctor_set(x_59, 4, x_29);
lean_ctor_set(x_26, 1, x_59);
lean_ctor_set(x_26, 0, x_5);
return x_26;
}
else
{
lean_object* x_60; 
lean_dec(x_29);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_6);
lean_ctor_set(x_60, 2, x_24);
lean_ctor_set(x_26, 1, x_60);
lean_ctor_set(x_26, 0, x_5);
return x_26;
}
}
else
{
uint8_t x_61; 
lean_dec(x_29);
lean_dec(x_6);
x_61 = lean_nat_dec_eq(x_54, x_55);
lean_dec(x_54);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_24);
lean_dec(x_1);
x_62 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1;
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_62);
lean_ctor_set(x_26, 0, x_5);
return x_26;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_24);
lean_ctor_set(x_26, 1, x_63);
lean_ctor_set(x_26, 0, x_5);
return x_26;
}
}
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_26, 0);
x_65 = lean_ctor_get(x_26, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_26);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
x_68 = lean_byte_array_size(x_66);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_24);
lean_free_object(x_5);
lean_dec(x_6);
lean_dec(x_1);
x_70 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
else
{
uint8_t x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; 
x_72 = lean_byte_array_fget(x_66, x_67);
x_73 = lean_nat_add(x_67, x_13);
lean_dec(x_67);
lean_ctor_set(x_5, 1, x_73);
lean_ctor_set(x_5, 0, x_66);
x_74 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
x_75 = lean_uint8_dec_eq(x_72, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_5);
lean_dec(x_65);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_1);
x_76 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_78 = x_64;
} else {
 lean_dec_ref(x_64);
 x_78 = lean_box(0);
}
x_79 = lean_array_get_size(x_6);
x_80 = lean_array_get_size(x_65);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_nat_dec_eq(x_79, x_81);
lean_dec(x_79);
if (x_82 == 0)
{
uint8_t x_83; 
lean_dec(x_78);
x_83 = lean_nat_dec_eq(x_80, x_81);
lean_dec(x_80);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_6);
x_85 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_6);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_24);
lean_ctor_set(x_85, 4, x_65);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_5);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_65);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_6);
lean_ctor_set(x_87, 2, x_24);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_5);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_65);
lean_dec(x_6);
x_89 = lean_nat_dec_eq(x_80, x_81);
lean_dec(x_80);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_78);
lean_dec(x_24);
lean_dec(x_1);
x_90 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_5);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; 
if (lean_is_scalar(x_78)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_78;
}
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_24);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_5);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_24);
lean_free_object(x_5);
lean_dec(x_6);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_26);
if (x_94 == 0)
{
return x_26;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_26, 0);
x_96 = lean_ctor_get(x_26, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_26);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_free_object(x_5);
lean_dec(x_6);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_22);
if (x_98 == 0)
{
return x_22;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_22, 0);
x_100 = lean_ctor_get(x_22, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_22);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; 
lean_dec(x_5);
x_102 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_15);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
x_106 = l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___spec__1(x_105, x_103);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
x_112 = lean_byte_array_size(x_110);
x_113 = lean_nat_dec_lt(x_111, x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_6);
lean_dec(x_1);
x_114 = l_Std_Internal_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_109)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_109;
 lean_ctor_set_tag(x_115, 1);
}
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
else
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_120; 
x_116 = lean_byte_array_fget(x_110, x_111);
x_117 = lean_nat_add(x_111, x_13);
lean_dec(x_111);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_110);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
x_120 = lean_uint8_dec_eq(x_116, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_118);
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_6);
lean_dec(x_1);
x_121 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5;
if (lean_is_scalar(x_109)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_109;
 lean_ctor_set_tag(x_122, 1);
}
lean_ctor_set(x_122, 0, x_107);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_123 = x_107;
} else {
 lean_dec_ref(x_107);
 x_123 = lean_box(0);
}
x_124 = lean_array_get_size(x_6);
x_125 = lean_array_get_size(x_108);
x_126 = lean_unsigned_to_nat(0u);
x_127 = lean_nat_dec_eq(x_124, x_126);
lean_dec(x_124);
if (x_127 == 0)
{
uint8_t x_128; 
lean_dec(x_123);
x_128 = lean_nat_dec_eq(x_125, x_126);
lean_dec(x_125);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_6);
x_130 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_130, 0, x_1);
lean_ctor_set(x_130, 1, x_6);
lean_ctor_set(x_130, 2, x_129);
lean_ctor_set(x_130, 3, x_104);
lean_ctor_set(x_130, 4, x_108);
if (lean_is_scalar(x_109)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_109;
}
lean_ctor_set(x_131, 0, x_118);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_108);
x_132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_132, 1, x_6);
lean_ctor_set(x_132, 2, x_104);
if (lean_is_scalar(x_109)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_109;
}
lean_ctor_set(x_133, 0, x_118);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
else
{
uint8_t x_134; 
lean_dec(x_108);
lean_dec(x_6);
x_134 = lean_nat_dec_eq(x_125, x_126);
lean_dec(x_125);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_123);
lean_dec(x_104);
lean_dec(x_1);
x_135 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1;
if (lean_is_scalar(x_109)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_109;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_118);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
if (lean_is_scalar(x_123)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_123;
}
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_104);
if (lean_is_scalar(x_109)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_109;
}
lean_ctor_set(x_138, 0, x_118);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_104);
lean_dec(x_6);
lean_dec(x_1);
x_139 = lean_ctor_get(x_106, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_106, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_141 = x_106;
} else {
 lean_dec_ref(x_106);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_6);
lean_dec(x_1);
x_143 = lean_ctor_get(x_102, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_102, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_145 = x_102;
} else {
 lean_dec_ref(x_102);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_147 = lean_ctor_get(x_3, 0);
x_148 = lean_ctor_get(x_3, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_3);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
x_151 = lean_byte_array_size(x_149);
x_152 = lean_nat_dec_lt(x_150, x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_1);
x_153 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_147);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
else
{
uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_160; 
x_155 = lean_byte_array_fget(x_149, x_150);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_nat_add(x_150, x_156);
lean_dec(x_150);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_149);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_160 = lean_uint8_dec_eq(x_155, x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_158);
lean_dec(x_148);
lean_dec(x_1);
x_161 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_147);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; 
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_163 = x_147;
} else {
 lean_dec_ref(x_147);
 x_163 = lean_box(0);
}
x_164 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_158);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
x_168 = l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___spec__1(x_167, x_165);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
x_174 = lean_byte_array_size(x_172);
x_175 = lean_nat_dec_lt(x_173, x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_170);
lean_dec(x_166);
lean_dec(x_163);
lean_dec(x_148);
lean_dec(x_1);
x_176 = l_Std_Internal_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_171)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_171;
 lean_ctor_set_tag(x_177, 1);
}
lean_ctor_set(x_177, 0, x_169);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
else
{
uint8_t x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_182; 
x_178 = lean_byte_array_fget(x_172, x_173);
x_179 = lean_nat_add(x_173, x_156);
lean_dec(x_173);
if (lean_is_scalar(x_163)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_163;
}
lean_ctor_set(x_180, 0, x_172);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1;
x_182 = lean_uint8_dec_eq(x_178, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_180);
lean_dec(x_170);
lean_dec(x_166);
lean_dec(x_148);
lean_dec(x_1);
x_183 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5;
if (lean_is_scalar(x_171)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_171;
 lean_ctor_set_tag(x_184, 1);
}
lean_ctor_set(x_184, 0, x_169);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_185 = x_169;
} else {
 lean_dec_ref(x_169);
 x_185 = lean_box(0);
}
x_186 = lean_array_get_size(x_148);
x_187 = lean_array_get_size(x_170);
x_188 = lean_unsigned_to_nat(0u);
x_189 = lean_nat_dec_eq(x_186, x_188);
lean_dec(x_186);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_185);
x_190 = lean_nat_dec_eq(x_187, x_188);
lean_dec(x_187);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_148);
x_192 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_192, 0, x_1);
lean_ctor_set(x_192, 1, x_148);
lean_ctor_set(x_192, 2, x_191);
lean_ctor_set(x_192, 3, x_166);
lean_ctor_set(x_192, 4, x_170);
if (lean_is_scalar(x_171)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_171;
}
lean_ctor_set(x_193, 0, x_180);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_170);
x_194 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_194, 0, x_1);
lean_ctor_set(x_194, 1, x_148);
lean_ctor_set(x_194, 2, x_166);
if (lean_is_scalar(x_171)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_171;
}
lean_ctor_set(x_195, 0, x_180);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
else
{
uint8_t x_196; 
lean_dec(x_170);
lean_dec(x_148);
x_196 = lean_nat_dec_eq(x_187, x_188);
lean_dec(x_187);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_185);
lean_dec(x_166);
lean_dec(x_1);
x_197 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1;
if (lean_is_scalar(x_171)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_171;
 lean_ctor_set_tag(x_198, 1);
}
lean_ctor_set(x_198, 0, x_180);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; 
if (lean_is_scalar(x_185)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_185;
}
lean_ctor_set(x_199, 0, x_1);
lean_ctor_set(x_199, 1, x_166);
if (lean_is_scalar(x_171)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_171;
}
lean_ctor_set(x_200, 0, x_180);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_166);
lean_dec(x_163);
lean_dec(x_148);
lean_dec(x_1);
x_201 = lean_ctor_get(x_168, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_168, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_203 = x_168;
} else {
 lean_dec_ref(x_168);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_163);
lean_dec(x_148);
lean_dec(x_1);
x_205 = lean_ctor_get(x_164, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_164, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_207 = x_164;
} else {
 lean_dec_ref(x_164);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_1);
x_209 = !lean_is_exclusive(x_3);
if (x_209 == 0)
{
return x_3;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_3, 0);
x_211 = lean_ctor_get(x_3, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_3);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_byte_array_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_10 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_10);
return x_2;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_11 = lean_byte_array_fget(x_6, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
lean_inc(x_13);
lean_inc(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_16 = lean_uint8_dec_eq(x_11, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_17 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_17);
return x_2;
}
else
{
uint8_t x_18; 
lean_dec(x_4);
x_18 = lean_nat_dec_lt(x_13, x_8);
lean_dec(x_8);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
x_19 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; 
lean_free_object(x_2);
x_20 = lean_byte_array_fget(x_6, x_13);
lean_dec(x_13);
lean_dec(x_6);
x_21 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1;
x_22 = lean_uint8_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(x_5, x_14);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_5);
x_24 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(x_14);
return x_24;
}
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_byte_array_size(x_27);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_31 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; 
x_33 = lean_byte_array_fget(x_27, x_28);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_28, x_34);
lean_dec(x_28);
lean_inc(x_35);
lean_inc(x_27);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1;
x_38 = lean_uint8_dec_eq(x_33, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
x_39 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_25);
x_41 = lean_nat_dec_lt(x_35, x_29);
lean_dec(x_29);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_35);
lean_dec(x_27);
lean_dec(x_26);
x_42 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
else
{
uint8_t x_44; uint8_t x_45; uint8_t x_46; 
x_44 = lean_byte_array_fget(x_27, x_35);
lean_dec(x_35);
lean_dec(x_27);
x_45 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1;
x_46 = lean_uint8_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(x_26, x_36);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec(x_26);
x_48 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(x_36);
return x_48;
}
}
}
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_2);
if (x_49 == 0)
{
return x_2;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_2, 0);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_2);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_satisfy___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("condition not satisfied", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_satisfy___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_byte_array_fget(x_3, x_4);
x_10 = lean_box(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = l_Std_Internal_Parsec_satisfy___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__1___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_2, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 0);
lean_dec(x_17);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_19);
x_20 = lean_box(x_9);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
lean_dec(x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(x_9);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
static uint8_t _init_l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___lambda__1___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 13;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___lambda__1(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1;
x_3 = lean_uint8_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; uint8_t x_5; 
x_4 = l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___lambda__1___closed__1;
x_5 = lean_uint8_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
static lean_object* _init_l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___closed__1;
lean_inc(x_2);
x_4 = l_Std_Internal_Parsec_satisfy___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__1(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_dec(x_11);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_1);
return x_21;
}
}
}
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 99;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_byte_array_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_15 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_17 = lean_byte_array_fget(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_18 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__1;
x_19 = lean_uint8_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_inc(x_2);
x_20 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(x_2);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 0);
lean_dec(x_23);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_26 = x_20;
} else {
 lean_dec_ref(x_20);
 x_26 = lean_box(0);
}
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
x_38 = lean_byte_array_size(x_36);
x_39 = lean_nat_dec_lt(x_37, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_dec(x_36);
lean_free_object(x_2);
x_40 = lean_nat_dec_eq(x_37, x_37);
lean_dec(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_1);
x_41 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
x_44 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_43, x_24);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_27 = x_45;
goto block_35;
}
else
{
uint8_t x_46; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_44);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; 
x_50 = lean_byte_array_fget(x_36, x_37);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_37, x_51);
lean_ctor_set(x_2, 1, x_52);
lean_ctor_set(x_2, 0, x_36);
x_53 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1;
x_54 = lean_uint8_dec_eq(x_50, x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_2);
x_55 = lean_nat_dec_eq(x_37, x_37);
lean_dec(x_37);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_1);
x_56 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_24);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
x_59 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_58, x_24);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_27 = x_60;
goto block_35;
}
else
{
uint8_t x_61; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_59);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_24);
x_27 = x_2;
goto block_35;
}
}
block_35:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_array_push(x_1, x_25);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_byte_array_size(x_29);
lean_dec(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
if (lean_is_scalar(x_26)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_26;
}
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
else
{
lean_dec(x_26);
x_1 = x_28;
x_2 = x_27;
goto _start;
}
}
}
else
{
uint8_t x_65; 
lean_free_object(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_20);
if (x_65 == 0)
{
return x_20;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_20, 0);
x_67 = lean_ctor_get(x_20, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_20);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_69 = lean_ctor_get(x_20, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_20, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_71 = x_20;
} else {
 lean_dec_ref(x_20);
 x_71 = lean_box(0);
}
x_81 = lean_ctor_get(x_69, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_69, 1);
lean_inc(x_82);
x_83 = lean_byte_array_size(x_81);
x_84 = lean_nat_dec_lt(x_82, x_83);
lean_dec(x_83);
if (x_84 == 0)
{
uint8_t x_85; 
lean_dec(x_81);
x_85 = lean_nat_dec_eq(x_82, x_82);
lean_dec(x_82);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_1);
x_86 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_69);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
x_89 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_88, x_69);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec(x_89);
x_72 = x_90;
goto block_80;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_1);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_93 = x_89;
} else {
 lean_dec_ref(x_89);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; 
x_95 = lean_byte_array_fget(x_81, x_82);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_add(x_82, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_81);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1;
x_100 = lean_uint8_dec_eq(x_95, x_99);
if (x_100 == 0)
{
uint8_t x_101; 
lean_dec(x_98);
x_101 = lean_nat_dec_eq(x_82, x_82);
lean_dec(x_82);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_1);
x_102 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_69);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
x_105 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_104, x_69);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec(x_105);
x_72 = x_106;
goto block_80;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_1);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_109 = x_105;
} else {
 lean_dec_ref(x_105);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
lean_dec(x_82);
lean_dec(x_69);
x_72 = x_98;
goto block_80;
}
}
block_80:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_array_push(x_1, x_70);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
x_76 = lean_byte_array_size(x_74);
lean_dec(x_74);
x_77 = lean_nat_dec_lt(x_75, x_76);
lean_dec(x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; 
if (lean_is_scalar(x_71)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_71;
}
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_73);
return x_78;
}
else
{
lean_dec(x_71);
x_1 = x_73;
x_2 = x_72;
goto _start;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_1);
x_111 = lean_ctor_get(x_20, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_20, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_113 = x_20;
} else {
 lean_dec_ref(x_20);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
lean_inc(x_2);
x_116 = l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2(x_115, x_2);
x_117 = !lean_is_exclusive(x_2);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_2, 1);
lean_dec(x_118);
x_119 = lean_ctor_get(x_2, 0);
lean_dec(x_119);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_116);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_116, 0);
x_122 = lean_ctor_get(x_116, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
x_125 = lean_byte_array_size(x_123);
x_126 = lean_nat_dec_lt(x_124, x_125);
lean_dec(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_123);
lean_free_object(x_2);
x_127 = lean_nat_dec_eq(x_124, x_124);
lean_dec(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_1);
x_128 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_116, 1);
lean_ctor_set(x_116, 1, x_128);
return x_116;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_free_object(x_116);
x_129 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
x_130 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_129, x_121);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec(x_130);
x_3 = x_131;
goto block_10;
}
else
{
uint8_t x_132; 
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_130);
if (x_132 == 0)
{
return x_130;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_130, 0);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_130);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
else
{
uint8_t x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_140; 
x_136 = lean_byte_array_fget(x_123, x_124);
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_add(x_124, x_137);
lean_ctor_set(x_2, 1, x_138);
lean_ctor_set(x_2, 0, x_123);
x_139 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1;
x_140 = lean_uint8_dec_eq(x_136, x_139);
if (x_140 == 0)
{
uint8_t x_141; 
lean_dec(x_2);
x_141 = lean_nat_dec_eq(x_124, x_124);
lean_dec(x_124);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec(x_1);
x_142 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9;
lean_ctor_set_tag(x_116, 1);
lean_ctor_set(x_116, 1, x_142);
return x_116;
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_free_object(x_116);
x_143 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
x_144 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_143, x_121);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec(x_144);
x_3 = x_145;
goto block_10;
}
else
{
uint8_t x_146; 
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_144);
if (x_146 == 0)
{
return x_144;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_144, 0);
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_144);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
else
{
lean_dec(x_124);
lean_free_object(x_116);
lean_dec(x_121);
x_3 = x_2;
goto block_10;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_116, 0);
lean_inc(x_150);
lean_dec(x_116);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
x_153 = lean_byte_array_size(x_151);
x_154 = lean_nat_dec_lt(x_152, x_153);
lean_dec(x_153);
if (x_154 == 0)
{
uint8_t x_155; 
lean_dec(x_151);
lean_free_object(x_2);
x_155 = lean_nat_dec_eq(x_152, x_152);
lean_dec(x_152);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_1);
x_156 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_150);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
x_159 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_158, x_150);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec(x_159);
x_3 = x_160;
goto block_10;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_1);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_163 = x_159;
} else {
 lean_dec_ref(x_159);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
uint8_t x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_169; 
x_165 = lean_byte_array_fget(x_151, x_152);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_add(x_152, x_166);
lean_ctor_set(x_2, 1, x_167);
lean_ctor_set(x_2, 0, x_151);
x_168 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1;
x_169 = lean_uint8_dec_eq(x_165, x_168);
if (x_169 == 0)
{
uint8_t x_170; 
lean_dec(x_2);
x_170 = lean_nat_dec_eq(x_152, x_152);
lean_dec(x_152);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_1);
x_171 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9;
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_150);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
x_174 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_173, x_150);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec(x_174);
x_3 = x_175;
goto block_10;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_1);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_178 = x_174;
} else {
 lean_dec_ref(x_174);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
}
else
{
lean_dec(x_152);
lean_dec(x_150);
x_3 = x_2;
goto block_10;
}
}
}
}
else
{
uint8_t x_180; 
lean_free_object(x_2);
lean_dec(x_1);
x_180 = !lean_is_exclusive(x_116);
if (x_180 == 0)
{
return x_116;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_116, 0);
x_182 = lean_ctor_get(x_116, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_116);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_184 = lean_ctor_get(x_116, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_185 = x_116;
} else {
 lean_dec_ref(x_116);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
x_188 = lean_byte_array_size(x_186);
x_189 = lean_nat_dec_lt(x_187, x_188);
lean_dec(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
x_190 = lean_nat_dec_eq(x_187, x_187);
lean_dec(x_187);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_1);
x_191 = l_Std_Internal_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_185)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_185;
 lean_ctor_set_tag(x_192, 1);
}
lean_ctor_set(x_192, 0, x_184);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_185);
x_193 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
x_194 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_193, x_184);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec(x_194);
x_3 = x_195;
goto block_10;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_1);
x_196 = lean_ctor_get(x_194, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_198 = x_194;
} else {
 lean_dec_ref(x_194);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
else
{
uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; uint8_t x_205; 
x_200 = lean_byte_array_fget(x_186, x_187);
x_201 = lean_unsigned_to_nat(1u);
x_202 = lean_nat_add(x_187, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_186);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1;
x_205 = lean_uint8_dec_eq(x_200, x_204);
if (x_205 == 0)
{
uint8_t x_206; 
lean_dec(x_203);
x_206 = lean_nat_dec_eq(x_187, x_187);
lean_dec(x_187);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_1);
x_207 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9;
if (lean_is_scalar(x_185)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_185;
 lean_ctor_set_tag(x_208, 1);
}
lean_ctor_set(x_208, 0, x_184);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_185);
x_209 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3;
x_210 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_209, x_184);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec(x_210);
x_3 = x_211;
goto block_10;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_1);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_214 = x_210;
} else {
 lean_dec_ref(x_210);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
}
else
{
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_184);
x_3 = x_203;
goto block_10;
}
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_1);
x_216 = lean_ctor_get(x_116, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_116, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_218 = x_116;
} else {
 lean_dec_ref(x_116);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
}
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_byte_array_size(x_4);
lean_dec(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
x_2 = x_3;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6;
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2;
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = 0;
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_byte_array_fget(x_3, x_4);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_uint8_dec_eq(x_9, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
x_14 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid zero byte in literal", 28, 28);
return x_1;
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 15;
x_2 = lean_uint8_complement(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Excessive literal", 17, 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_byte_array_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_45; uint8_t x_46; 
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_byte_array_fget(x_4, x_5);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_15);
x_45 = 28;
x_46 = lean_uint64_dec_eq(x_2, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
x_16 = x_47;
goto block_44;
}
else
{
uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; 
x_48 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2;
x_49 = lean_uint8_land(x_13, x_48);
x_50 = 0;
x_51 = lean_uint8_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_3);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_box(0);
x_16 = x_54;
goto block_44;
}
}
block_44:
{
uint8_t x_17; uint8_t x_18; 
lean_dec(x_16);
x_17 = 0;
x_18 = lean_uint8_dec_eq(x_13, x_17);
if (x_18 == 0)
{
uint8_t x_19; uint8_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; 
x_19 = 127;
x_20 = lean_uint8_land(x_13, x_19);
x_21 = lean_uint8_to_uint64(x_20);
x_22 = lean_uint64_shift_left(x_21, x_2);
x_23 = lean_uint64_lor(x_1, x_22);
x_24 = 128;
x_25 = lean_uint8_land(x_13, x_24);
x_26 = lean_uint8_dec_eq(x_25, x_17);
if (x_26 == 0)
{
uint64_t x_27; uint64_t x_28; 
x_27 = 7;
x_28 = lean_uint64_add(x_2, x_27);
x_1 = x_23;
x_2 = x_28;
goto _start;
}
else
{
uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint8_t x_34; 
x_30 = 1;
x_31 = lean_uint64_shift_right(x_23, x_30);
x_32 = lean_uint64_land(x_30, x_23);
x_33 = 0;
x_34 = lean_uint64_dec_eq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_uint64_to_nat(x_31);
x_36 = lean_nat_to_int(x_35);
x_37 = lean_int_neg(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_uint64_to_nat(x_31);
x_40 = lean_nat_to_int(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_3);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_88; uint8_t x_89; 
lean_dec(x_3);
x_55 = lean_byte_array_fget(x_4, x_5);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_5, x_56);
lean_dec(x_5);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_57);
x_88 = 28;
x_89 = lean_uint64_dec_eq(x_2, x_88);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_box(0);
x_59 = x_90;
goto block_87;
}
else
{
uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; 
x_91 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2;
x_92 = lean_uint8_land(x_55, x_91);
x_93 = 0;
x_94 = lean_uint8_dec_eq(x_92, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_58);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
else
{
lean_object* x_97; 
x_97 = lean_box(0);
x_59 = x_97;
goto block_87;
}
}
block_87:
{
uint8_t x_60; uint8_t x_61; 
lean_dec(x_59);
x_60 = 0;
x_61 = lean_uint8_dec_eq(x_55, x_60);
if (x_61 == 0)
{
uint8_t x_62; uint8_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; 
x_62 = 127;
x_63 = lean_uint8_land(x_55, x_62);
x_64 = lean_uint8_to_uint64(x_63);
x_65 = lean_uint64_shift_left(x_64, x_2);
x_66 = lean_uint64_lor(x_1, x_65);
x_67 = 128;
x_68 = lean_uint8_land(x_55, x_67);
x_69 = lean_uint8_dec_eq(x_68, x_60);
if (x_69 == 0)
{
uint64_t x_70; uint64_t x_71; 
x_70 = 7;
x_71 = lean_uint64_add(x_2, x_70);
x_1 = x_66;
x_2 = x_71;
x_3 = x_58;
goto _start;
}
else
{
uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint8_t x_77; 
x_73 = 1;
x_74 = lean_uint64_shift_right(x_66, x_73);
x_75 = lean_uint64_land(x_73, x_66);
x_76 = 0;
x_77 = lean_uint64_dec_eq(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_uint64_to_nat(x_74);
x_79 = lean_nat_to_int(x_78);
x_80 = lean_int_neg(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_58);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_uint64_to_nat(x_74);
x_83 = lean_nat_to_int(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_58);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_58);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = 0;
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(x_2, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("parsed non negative lit where negative was expected", 51, 51);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_6 = lean_int_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_8; 
x_8 = lean_nat_abs(x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_8);
return x_2;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_12 = lean_int_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_nat_abs(x_10);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("parsed non positive lit where positive was expected", 51, 51);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_6 = lean_int_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_8; 
x_8 = lean_nat_abs(x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_8);
return x_2;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_12 = lean_int_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_nat_abs(x_10);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_6 = lean_int_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_8; 
x_8 = lean_nat_abs(x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_8);
return x_2;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_12 = lean_int_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_nat_abs(x_10);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_byte_array_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_10 = lean_byte_array_fget(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_11 = 0;
x_12 = lean_uint8_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_push(x_2, x_15);
x_2 = x_16;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_2);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_byte_array_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_byte_array_fget(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_11 = 1;
x_12 = lean_uint8_land(x_11, x_10);
x_13 = 0;
x_14 = lean_uint8_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_uint8_dec_eq(x_10, x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_1);
x_17 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_push(x_2, x_19);
x_2 = x_20;
x_3 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_2);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_9 = lean_byte_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_10 = 1;
x_11 = lean_uint8_land(x_10, x_9);
x_12 = 0;
x_13 = lean_uint8_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_1);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_uint8_dec_eq(x_9, x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_2);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_21 = lean_int_dec_lt(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_1);
x_22 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_22);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_16);
x_23 = lean_nat_abs(x_19);
lean_dec(x_19);
x_24 = lean_array_push(x_1, x_23);
x_1 = x_24;
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_29 = lean_int_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_1);
x_30 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_nat_abs(x_27);
lean_dec(x_27);
x_33 = lean_array_push(x_1, x_32);
x_1 = x_33;
x_2 = x_26;
goto _start;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_16;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_1);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_byte_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_10 = 0;
x_11 = lean_uint8_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_push(x_1, x_14);
x_1 = x_15;
x_2 = x_13;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause___spec__2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause___spec__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_7 = lean_int_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_free_object(x_2);
x_9 = lean_nat_abs(x_5);
lean_dec(x_5);
x_10 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__1(x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_24 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_25 = lean_int_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
x_26 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_nat_abs(x_23);
lean_dec(x_23);
x_29 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__1(x_22);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_31);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_28);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_37 = x_29;
} else {
 lean_dec_ref(x_29);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_2);
if (x_39 == 0)
{
return x_2;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_2);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_byte_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_10 = 0;
x_11 = lean_uint8_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_push(x_1, x_14);
x_1 = x_15;
x_2 = x_13;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints___spec__2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints___spec__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_7 = lean_int_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_free_object(x_2);
x_9 = lean_nat_abs(x_5);
lean_dec(x_5);
x_10 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause___spec__1(x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = 0;
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_byte_array_size(x_15);
x_18 = lean_nat_dec_lt(x_16, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
x_19 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_19);
return x_10;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_byte_array_fget(x_15, x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_16, x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_uint8_dec_eq(x_20, x_14);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_9);
x_25 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_25);
return x_10;
}
else
{
uint8_t x_26; 
lean_free_object(x_10);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_12, 0);
lean_dec(x_28);
x_29 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__1(x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints___spec__1(x_30);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
x_38 = lean_byte_array_size(x_36);
x_39 = lean_nat_dec_lt(x_37, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_free_object(x_12);
lean_dec(x_13);
lean_dec(x_9);
x_40 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_40);
return x_32;
}
else
{
uint8_t x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_byte_array_fget(x_36, x_37);
x_42 = lean_nat_add(x_37, x_21);
lean_dec(x_37);
lean_ctor_set(x_12, 1, x_42);
lean_ctor_set(x_12, 0, x_36);
x_43 = lean_uint8_dec_eq(x_41, x_14);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_9);
x_44 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_44);
return x_32;
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_34, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_34, 0);
lean_dec(x_47);
x_48 = lean_array_get_size(x_13);
x_49 = lean_array_get_size(x_35);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_eq(x_48, x_50);
lean_dec(x_48);
if (x_51 == 0)
{
uint8_t x_52; 
lean_free_object(x_34);
x_52 = lean_nat_dec_eq(x_49, x_50);
lean_dec(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_13);
x_54 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_54, 0, x_9);
lean_ctor_set(x_54, 1, x_13);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_31);
lean_ctor_set(x_54, 4, x_35);
lean_ctor_set(x_32, 1, x_54);
lean_ctor_set(x_32, 0, x_12);
return x_32;
}
else
{
lean_object* x_55; 
lean_dec(x_35);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_9);
lean_ctor_set(x_55, 1, x_13);
lean_ctor_set(x_55, 2, x_31);
lean_ctor_set(x_32, 1, x_55);
lean_ctor_set(x_32, 0, x_12);
return x_32;
}
}
else
{
uint8_t x_56; 
lean_dec(x_35);
lean_dec(x_13);
x_56 = lean_nat_dec_eq(x_49, x_50);
lean_dec(x_49);
if (x_56 == 0)
{
lean_object* x_57; 
lean_free_object(x_34);
lean_dec(x_31);
lean_dec(x_9);
x_57 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1;
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_57);
lean_ctor_set(x_32, 0, x_12);
return x_32;
}
else
{
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 0, x_9);
lean_ctor_set(x_32, 1, x_34);
lean_ctor_set(x_32, 0, x_12);
return x_32;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_34);
x_58 = lean_array_get_size(x_13);
x_59 = lean_array_get_size(x_35);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_eq(x_58, x_60);
lean_dec(x_58);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = lean_nat_dec_eq(x_59, x_60);
lean_dec(x_59);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_13);
x_64 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_64, 0, x_9);
lean_ctor_set(x_64, 1, x_13);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_31);
lean_ctor_set(x_64, 4, x_35);
lean_ctor_set(x_32, 1, x_64);
lean_ctor_set(x_32, 0, x_12);
return x_32;
}
else
{
lean_object* x_65; 
lean_dec(x_35);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_9);
lean_ctor_set(x_65, 1, x_13);
lean_ctor_set(x_65, 2, x_31);
lean_ctor_set(x_32, 1, x_65);
lean_ctor_set(x_32, 0, x_12);
return x_32;
}
}
else
{
uint8_t x_66; 
lean_dec(x_35);
lean_dec(x_13);
x_66 = lean_nat_dec_eq(x_59, x_60);
lean_dec(x_59);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_31);
lean_dec(x_9);
x_67 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1;
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_67);
lean_ctor_set(x_32, 0, x_12);
return x_32;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_9);
lean_ctor_set(x_68, 1, x_31);
lean_ctor_set(x_32, 1, x_68);
lean_ctor_set(x_32, 0, x_12);
return x_32;
}
}
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_32, 0);
x_70 = lean_ctor_get(x_32, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_32);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
x_73 = lean_byte_array_size(x_71);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_31);
lean_free_object(x_12);
lean_dec(x_13);
lean_dec(x_9);
x_75 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
else
{
uint8_t x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_byte_array_fget(x_71, x_72);
x_78 = lean_nat_add(x_72, x_21);
lean_dec(x_72);
lean_ctor_set(x_12, 1, x_78);
lean_ctor_set(x_12, 0, x_71);
x_79 = lean_uint8_dec_eq(x_77, x_14);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_12);
lean_dec(x_70);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_9);
x_80 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_82 = x_69;
} else {
 lean_dec_ref(x_69);
 x_82 = lean_box(0);
}
x_83 = lean_array_get_size(x_13);
x_84 = lean_array_get_size(x_70);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_eq(x_83, x_85);
lean_dec(x_83);
if (x_86 == 0)
{
uint8_t x_87; 
lean_dec(x_82);
x_87 = lean_nat_dec_eq(x_84, x_85);
lean_dec(x_84);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_13);
x_89 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_89, 0, x_9);
lean_ctor_set(x_89, 1, x_13);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_31);
lean_ctor_set(x_89, 4, x_70);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_12);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_70);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_9);
lean_ctor_set(x_91, 1, x_13);
lean_ctor_set(x_91, 2, x_31);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_12);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_dec(x_70);
lean_dec(x_13);
x_93 = lean_nat_dec_eq(x_84, x_85);
lean_dec(x_84);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_82);
lean_dec(x_31);
lean_dec(x_9);
x_94 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_12);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
if (lean_is_scalar(x_82)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_82;
}
lean_ctor_set(x_96, 0, x_9);
lean_ctor_set(x_96, 1, x_31);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_12);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_31);
lean_free_object(x_12);
lean_dec(x_13);
lean_dec(x_9);
x_98 = !lean_is_exclusive(x_32);
if (x_98 == 0)
{
return x_32;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_32, 0);
x_100 = lean_ctor_get(x_32, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_32);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_free_object(x_12);
lean_dec(x_13);
lean_dec(x_9);
x_102 = !lean_is_exclusive(x_29);
if (x_102 == 0)
{
return x_29;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_29, 0);
x_104 = lean_ctor_get(x_29, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_29);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_12);
x_106 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__1(x_23);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints___spec__1(x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
x_115 = lean_byte_array_size(x_113);
x_116 = lean_nat_dec_lt(x_114, x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_13);
lean_dec(x_9);
x_117 = l_Std_Internal_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_112)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_112;
 lean_ctor_set_tag(x_118, 1);
}
lean_ctor_set(x_118, 0, x_110);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
else
{
uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_byte_array_fget(x_113, x_114);
x_120 = lean_nat_add(x_114, x_21);
lean_dec(x_114);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_uint8_dec_eq(x_119, x_14);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_121);
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_13);
lean_dec(x_9);
x_123 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
if (lean_is_scalar(x_112)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_112;
 lean_ctor_set_tag(x_124, 1);
}
lean_ctor_set(x_124, 0, x_110);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_125 = x_110;
} else {
 lean_dec_ref(x_110);
 x_125 = lean_box(0);
}
x_126 = lean_array_get_size(x_13);
x_127 = lean_array_get_size(x_111);
x_128 = lean_unsigned_to_nat(0u);
x_129 = lean_nat_dec_eq(x_126, x_128);
lean_dec(x_126);
if (x_129 == 0)
{
uint8_t x_130; 
lean_dec(x_125);
x_130 = lean_nat_dec_eq(x_127, x_128);
lean_dec(x_127);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_13);
x_132 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_132, 0, x_9);
lean_ctor_set(x_132, 1, x_13);
lean_ctor_set(x_132, 2, x_131);
lean_ctor_set(x_132, 3, x_108);
lean_ctor_set(x_132, 4, x_111);
if (lean_is_scalar(x_112)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_112;
}
lean_ctor_set(x_133, 0, x_121);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_111);
x_134 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_134, 0, x_9);
lean_ctor_set(x_134, 1, x_13);
lean_ctor_set(x_134, 2, x_108);
if (lean_is_scalar(x_112)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_112;
}
lean_ctor_set(x_135, 0, x_121);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_dec(x_111);
lean_dec(x_13);
x_136 = lean_nat_dec_eq(x_127, x_128);
lean_dec(x_127);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
lean_dec(x_108);
lean_dec(x_9);
x_137 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1;
if (lean_is_scalar(x_112)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_112;
 lean_ctor_set_tag(x_138, 1);
}
lean_ctor_set(x_138, 0, x_121);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; 
if (lean_is_scalar(x_125)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_125;
}
lean_ctor_set(x_139, 0, x_9);
lean_ctor_set(x_139, 1, x_108);
if (lean_is_scalar(x_112)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_112;
}
lean_ctor_set(x_140, 0, x_121);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_108);
lean_dec(x_13);
lean_dec(x_9);
x_141 = lean_ctor_get(x_109, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_109, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_143 = x_109;
} else {
 lean_dec_ref(x_109);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_13);
lean_dec(x_9);
x_145 = lean_ctor_get(x_106, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_106, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_147 = x_106;
} else {
 lean_dec_ref(x_106);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_149 = lean_ctor_get(x_10, 0);
x_150 = lean_ctor_get(x_10, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_10);
x_151 = 0;
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
x_154 = lean_byte_array_size(x_152);
x_155 = lean_nat_dec_lt(x_153, x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_9);
x_156 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_149);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
else
{
uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_158 = lean_byte_array_fget(x_152, x_153);
x_159 = lean_unsigned_to_nat(1u);
x_160 = lean_nat_add(x_153, x_159);
lean_dec(x_153);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_152);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_uint8_dec_eq(x_158, x_151);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_161);
lean_dec(x_150);
lean_dec(x_9);
x_163 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_149);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; 
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_165 = x_149;
} else {
 lean_dec_ref(x_149);
 x_165 = lean_box(0);
}
x_166 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__1(x_161);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints___spec__1(x_167);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_170, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_170, 1);
lean_inc(x_174);
x_175 = lean_byte_array_size(x_173);
x_176 = lean_nat_dec_lt(x_174, x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_168);
lean_dec(x_165);
lean_dec(x_150);
lean_dec(x_9);
x_177 = l_Std_Internal_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_172)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_172;
 lean_ctor_set_tag(x_178, 1);
}
lean_ctor_set(x_178, 0, x_170);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
else
{
uint8_t x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_179 = lean_byte_array_fget(x_173, x_174);
x_180 = lean_nat_add(x_174, x_159);
lean_dec(x_174);
if (lean_is_scalar(x_165)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_165;
}
lean_ctor_set(x_181, 0, x_173);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_uint8_dec_eq(x_179, x_151);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_181);
lean_dec(x_171);
lean_dec(x_168);
lean_dec(x_150);
lean_dec(x_9);
x_183 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
if (lean_is_scalar(x_172)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_172;
 lean_ctor_set_tag(x_184, 1);
}
lean_ctor_set(x_184, 0, x_170);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_185 = x_170;
} else {
 lean_dec_ref(x_170);
 x_185 = lean_box(0);
}
x_186 = lean_array_get_size(x_150);
x_187 = lean_array_get_size(x_171);
x_188 = lean_unsigned_to_nat(0u);
x_189 = lean_nat_dec_eq(x_186, x_188);
lean_dec(x_186);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_185);
x_190 = lean_nat_dec_eq(x_187, x_188);
lean_dec(x_187);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_150);
x_192 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_192, 0, x_9);
lean_ctor_set(x_192, 1, x_150);
lean_ctor_set(x_192, 2, x_191);
lean_ctor_set(x_192, 3, x_168);
lean_ctor_set(x_192, 4, x_171);
if (lean_is_scalar(x_172)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_172;
}
lean_ctor_set(x_193, 0, x_181);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_171);
x_194 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_194, 0, x_9);
lean_ctor_set(x_194, 1, x_150);
lean_ctor_set(x_194, 2, x_168);
if (lean_is_scalar(x_172)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_172;
}
lean_ctor_set(x_195, 0, x_181);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
else
{
uint8_t x_196; 
lean_dec(x_171);
lean_dec(x_150);
x_196 = lean_nat_dec_eq(x_187, x_188);
lean_dec(x_187);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_185);
lean_dec(x_168);
lean_dec(x_9);
x_197 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1;
if (lean_is_scalar(x_172)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_172;
 lean_ctor_set_tag(x_198, 1);
}
lean_ctor_set(x_198, 0, x_181);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; 
if (lean_is_scalar(x_185)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_185;
}
lean_ctor_set(x_199, 0, x_9);
lean_ctor_set(x_199, 1, x_168);
if (lean_is_scalar(x_172)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_172;
}
lean_ctor_set(x_200, 0, x_181);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_168);
lean_dec(x_165);
lean_dec(x_150);
lean_dec(x_9);
x_201 = lean_ctor_get(x_169, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_169, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_203 = x_169;
} else {
 lean_dec_ref(x_169);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_165);
lean_dec(x_150);
lean_dec(x_9);
x_205 = lean_ctor_get(x_166, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_166, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_207 = x_166;
} else {
 lean_dec_ref(x_166);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_9);
x_209 = !lean_is_exclusive(x_10);
if (x_209 == 0)
{
return x_10;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_10, 0);
x_211 = lean_ctor_get(x_10, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_10);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_213 = lean_ctor_get(x_2, 0);
x_214 = lean_ctor_get(x_2, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_2);
x_215 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_216 = lean_int_dec_lt(x_215, x_214);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_214);
x_217 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1;
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_213);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_nat_abs(x_214);
lean_dec(x_214);
x_220 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause___spec__1(x_213);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_224 = 0;
x_225 = lean_ctor_get(x_221, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_221, 1);
lean_inc(x_226);
x_227 = lean_byte_array_size(x_225);
x_228 = lean_nat_dec_lt(x_226, x_227);
lean_dec(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_222);
lean_dec(x_219);
x_229 = l_Std_Internal_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_223)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_223;
 lean_ctor_set_tag(x_230, 1);
}
lean_ctor_set(x_230, 0, x_221);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
else
{
uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_231 = lean_byte_array_fget(x_225, x_226);
x_232 = lean_unsigned_to_nat(1u);
x_233 = lean_nat_add(x_226, x_232);
lean_dec(x_226);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_225);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_uint8_dec_eq(x_231, x_224);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_234);
lean_dec(x_222);
lean_dec(x_219);
x_236 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
if (lean_is_scalar(x_223)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_223;
 lean_ctor_set_tag(x_237, 1);
}
lean_ctor_set(x_237, 0, x_221);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_223);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_238 = x_221;
} else {
 lean_dec_ref(x_221);
 x_238 = lean_box(0);
}
x_239 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__1(x_234);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints___spec__1(x_240);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_245 = x_242;
} else {
 lean_dec_ref(x_242);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_243, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_243, 1);
lean_inc(x_247);
x_248 = lean_byte_array_size(x_246);
x_249 = lean_nat_dec_lt(x_247, x_248);
lean_dec(x_248);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_244);
lean_dec(x_241);
lean_dec(x_238);
lean_dec(x_222);
lean_dec(x_219);
x_250 = l_Std_Internal_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_245)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_245;
 lean_ctor_set_tag(x_251, 1);
}
lean_ctor_set(x_251, 0, x_243);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
else
{
uint8_t x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_252 = lean_byte_array_fget(x_246, x_247);
x_253 = lean_nat_add(x_247, x_232);
lean_dec(x_247);
if (lean_is_scalar(x_238)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_238;
}
lean_ctor_set(x_254, 0, x_246);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_uint8_dec_eq(x_252, x_224);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_254);
lean_dec(x_244);
lean_dec(x_241);
lean_dec(x_222);
lean_dec(x_219);
x_256 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
if (lean_is_scalar(x_245)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_245;
 lean_ctor_set_tag(x_257, 1);
}
lean_ctor_set(x_257, 0, x_243);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_258 = x_243;
} else {
 lean_dec_ref(x_243);
 x_258 = lean_box(0);
}
x_259 = lean_array_get_size(x_222);
x_260 = lean_array_get_size(x_244);
x_261 = lean_unsigned_to_nat(0u);
x_262 = lean_nat_dec_eq(x_259, x_261);
lean_dec(x_259);
if (x_262 == 0)
{
uint8_t x_263; 
lean_dec(x_258);
x_263 = lean_nat_dec_eq(x_260, x_261);
lean_dec(x_260);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_222);
x_265 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_265, 0, x_219);
lean_ctor_set(x_265, 1, x_222);
lean_ctor_set(x_265, 2, x_264);
lean_ctor_set(x_265, 3, x_241);
lean_ctor_set(x_265, 4, x_244);
if (lean_is_scalar(x_245)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_245;
}
lean_ctor_set(x_266, 0, x_254);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_244);
x_267 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_267, 0, x_219);
lean_ctor_set(x_267, 1, x_222);
lean_ctor_set(x_267, 2, x_241);
if (lean_is_scalar(x_245)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_245;
}
lean_ctor_set(x_268, 0, x_254);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
else
{
uint8_t x_269; 
lean_dec(x_244);
lean_dec(x_222);
x_269 = lean_nat_dec_eq(x_260, x_261);
lean_dec(x_260);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_258);
lean_dec(x_241);
lean_dec(x_219);
x_270 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1;
if (lean_is_scalar(x_245)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_245;
 lean_ctor_set_tag(x_271, 1);
}
lean_ctor_set(x_271, 0, x_254);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; 
if (lean_is_scalar(x_258)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_258;
}
lean_ctor_set(x_272, 0, x_219);
lean_ctor_set(x_272, 1, x_241);
if (lean_is_scalar(x_245)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_245;
}
lean_ctor_set(x_273, 0, x_254);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_241);
lean_dec(x_238);
lean_dec(x_222);
lean_dec(x_219);
x_274 = lean_ctor_get(x_242, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_242, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_276 = x_242;
} else {
 lean_dec_ref(x_242);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_238);
lean_dec(x_222);
lean_dec(x_219);
x_278 = lean_ctor_get(x_239, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_239, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_280 = x_239;
} else {
 lean_dec_ref(x_239);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_219);
x_282 = lean_ctor_get(x_220, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_220, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_284 = x_220;
} else {
 lean_dec_ref(x_220);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
}
}
else
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_2);
if (x_286 == 0)
{
return x_2;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_2, 0);
x_288 = lean_ctor_get(x_2, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_2);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList___spec__1(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = 0;
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_byte_array_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_11 = l_Std_Internal_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_11);
return x_2;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_byte_array_fget(x_7, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_8, x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_uint8_dec_eq(x_12, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_5);
x_17 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_17);
return x_2;
}
else
{
lean_object* x_18; 
lean_dec(x_4);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_2, 0, x_15);
return x_2;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_21 = 0;
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
x_24 = lean_byte_array_size(x_22);
x_25 = lean_nat_dec_lt(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
x_26 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_byte_array_fget(x_22, x_23);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_23, x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_uint8_dec_eq(x_28, x_21);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_20);
x_33 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_19);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_20);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_2);
if (x_37 == 0)
{
return x_2;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_2);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static uint8_t _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 97;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected a or d got: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_byte_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_13);
x_14 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1;
x_15 = lean_uint8_dec_eq(x_11, x_14);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; 
x_16 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1;
x_17 = lean_uint8_dec_eq(x_11, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_uint8_to_nat(x_11);
x_19 = l___private_Init_Data_Repr_0__Nat_reprFast(x_18);
x_20 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__2;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(x_1);
return x_25;
}
}
else
{
lean_object* x_26; 
x_26 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(x_1);
return x_26;
}
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
lean_dec(x_1);
x_27 = lean_byte_array_fget(x_2, x_3);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_3, x_28);
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1;
x_32 = lean_uint8_dec_eq(x_27, x_31);
if (x_32 == 0)
{
uint8_t x_33; uint8_t x_34; 
x_33 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1;
x_34 = lean_uint8_dec_eq(x_27, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_uint8_to_nat(x_27);
x_36 = l___private_Init_Data_Repr_0__Nat_reprFast(x_35);
x_37 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__2;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(x_30);
return x_42;
}
}
else
{
lean_object* x_43; 
x_43 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(x_30);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_push(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_dec(x_10);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_1);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1;
x_3 = l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions___spec__1(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_byte_array_size(x_7);
lean_dec(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; 
lean_dec(x_6);
x_11 = l_Std_Internal_Parsec_expectedEndOfInput;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_byte_array_size(x_14);
lean_dec(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_19 = l_Std_Internal_Parsec_expectedEndOfInput;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Std_Internal_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_byte_array_fget(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_9 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1;
x_10 = lean_uint8_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1;
x_12 = lean_uint8_dec_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(x_1);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(x_1);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(x_1);
return x_15;
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_loadLRATProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readBinFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof___closed__1;
x_7 = l_Std_Internal_Parsec_ByteArray_Parser_run___rarg(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 18);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof___closed__1;
x_15 = l_Std_Internal_Parsec_ByteArray_Parser_run___rarg(x_14, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_17 = x_15;
} else {
 lean_dec_ref(x_15);
 x_17 = lean_box(0);
}
if (lean_is_scalar(x_17)) {
 x_18 = lean_alloc_ctor(18, 1, 0);
} else {
 x_18 = x_17;
 lean_ctor_set_tag(x_18, 18);
}
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof___closed__1;
x_3 = l_Std_Internal_Parsec_ByteArray_Parser_run___rarg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_6);
x_8 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_4, x_11);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_12;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_11 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_4 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_11 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_10 = lean_int_dec_lt(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_nat_abs(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_13 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_4, x_16);
lean_dec(x_16);
x_2 = x_8;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_nat_abs(x_6);
lean_dec(x_6);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_22 = lean_nat_add(x_21, x_20);
lean_dec(x_21);
x_23 = l___private_Init_Data_Repr_0__Nat_reprFast(x_22);
x_24 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_string_append(x_4, x_29);
lean_dec(x_29);
x_2 = x_8;
x_4 = x_30;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_11 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" 0 ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("0", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("0 ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("1 d ", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_5 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_3);
lean_dec(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2;
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l___private_Init_Data_Repr_0__Nat_reprFast(x_13);
x_17 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(x_14);
lean_dec(x_14);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_15);
lean_dec(x_15);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2;
x_28 = lean_string_append(x_26, x_27);
return x_28;
}
case 2:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 4);
lean_inc(x_32);
lean_dec(x_1);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_29);
x_34 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(x_30);
lean_dec(x_30);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_31);
lean_dec(x_31);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = lean_string_append(x_43, x_34);
x_45 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(x_32);
lean_dec(x_32);
x_46 = lean_string_append(x_44, x_45);
lean_dec(x_45);
x_47 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2;
x_48 = lean_string_append(x_46, x_47);
return x_48;
}
default: 
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_dec(x_1);
x_50 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_49);
lean_dec(x_49);
x_51 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__4;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2;
x_54 = lean_string_append(x_52, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec(x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString___spec__1___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3;
x_11 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToString(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1;
x_3 = lean_byte_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object* x_1, uint64_t x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; 
x_3 = 0;
x_4 = lean_uint64_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint64_t x_5; uint8_t x_6; uint64_t x_7; uint64_t x_8; 
x_5 = 127;
x_6 = lean_uint64_dec_lt(x_5, x_2);
x_7 = 7;
x_8 = lean_uint64_shift_right(x_2, x_7);
if (x_6 == 0)
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_uint64_to_uint8(x_2);
x_10 = 127;
x_11 = lean_uint8_land(x_9, x_10);
x_12 = lean_byte_array_push(x_1, x_11);
x_1 = x_12;
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_uint64_to_uint8(x_2);
x_15 = 127;
x_16 = lean_uint8_land(x_14, x_15);
x_17 = 128;
x_18 = lean_uint8_lor(x_16, x_17);
x_19 = lean_byte_array_push(x_1, x_18);
x_1 = x_19;
x_2 = x_8;
goto _start;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_ByteArray_instInhabited;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mapped ≤ (2^64 - 1) -- our parser \"only\" supports 64 bit literals\n    ", 72, 70);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3;
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Tactic.BVDecide.LRAT.Parser", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Tactic.BVDecide.LRAT.lratProofToBinary.addInt", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__6;
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__7;
x_3 = lean_unsigned_to_nat(384u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1;
x_4 = lean_int_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_nat_abs(x_2);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_mul(x_6, x_5);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2;
x_11 = lean_nat_dec_le(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__8;
x_13 = l_panic___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___spec__1(x_12);
return x_13;
}
else
{
uint64_t x_14; lean_object* x_15; 
x_14 = lean_uint64_of_nat(x_9);
lean_dec(x_9);
x_15 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(x_1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_nat_abs(x_2);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_mul(x_17, x_16);
lean_dec(x_16);
x_19 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2;
x_20 = lean_nat_dec_le(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_1);
x_21 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__8;
x_22 = l_panic___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___spec__1(x_21);
return x_22;
}
else
{
uint64_t x_23; lean_object* x_24; 
x_23 = lean_uint64_of_nat(x_18);
lean_dec(x_18);
x_24 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(x_1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 0;
x_3 = lean_byte_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_nat_to_int(x_2);
x_4 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1;
x_3 = lean_byte_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_nat_to_int(x_6);
x_8 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_7);
lean_dec(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; size_t x_15; size_t x_16; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_nat_to_int(x_7);
x_9 = lean_int_neg(x_8);
lean_dec(x_8);
x_10 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
x_2 = x_16;
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_12, x_12);
if (x_18 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
x_2 = x_16;
x_4 = x_10;
goto _start;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__1(x_11, x_20, x_21, x_10);
lean_dec(x_11);
x_2 = x_16;
x_4 = x_22;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1;
x_12 = lean_byte_array_push(x_3, x_11);
x_13 = lean_nat_to_int(x_9);
x_14 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_12, x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = lean_byte_array_push(x_14, x_15);
x_17 = lean_array_get_size(x_10);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_10);
x_20 = lean_byte_array_push(x_16, x_15);
x_2 = x_8;
x_3 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_17, x_17);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_10);
x_23 = lean_byte_array_push(x_16, x_15);
x_2 = x_8;
x_3 = x_23;
goto _start;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__1(x_10, x_25, x_26, x_16);
lean_dec(x_10);
x_28 = lean_byte_array_push(x_27, x_15);
x_2 = x_8;
x_3 = x_28;
goto _start;
}
}
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_6, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 2);
lean_inc(x_32);
lean_dec(x_6);
x_33 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1;
x_34 = lean_byte_array_push(x_3, x_33);
x_35 = lean_nat_to_int(x_30);
x_36 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_34, x_35);
lean_dec(x_35);
x_37 = lean_array_get_size(x_31);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_lt(x_38, x_37);
x_40 = 0;
x_41 = lean_array_get_size(x_32);
x_42 = lean_nat_dec_lt(x_38, x_41);
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec(x_31);
x_43 = x_36;
goto block_55;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_37, x_37);
if (x_56 == 0)
{
lean_dec(x_37);
lean_dec(x_31);
x_43 = x_36;
goto block_55;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_59 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__2(x_31, x_57, x_58, x_36);
lean_dec(x_31);
x_43 = x_59;
goto block_55;
}
}
block_55:
{
lean_object* x_44; 
x_44 = lean_byte_array_push(x_43, x_40);
if (x_42 == 0)
{
lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_32);
x_45 = lean_byte_array_push(x_44, x_40);
x_2 = x_8;
x_3 = x_45;
goto _start;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_41, x_41);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_41);
lean_dec(x_32);
x_48 = lean_byte_array_push(x_44, x_40);
x_2 = x_8;
x_3 = x_48;
goto _start;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = 0;
x_51 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_52 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__1(x_32, x_50, x_51, x_44);
lean_dec(x_32);
x_53 = lean_byte_array_push(x_52, x_40);
x_2 = x_8;
x_3 = x_53;
goto _start;
}
}
}
}
case 2:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_60 = lean_ctor_get(x_6, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_6, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_6, 4);
lean_inc(x_63);
lean_dec(x_6);
x_64 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1;
x_65 = lean_byte_array_push(x_3, x_64);
x_66 = lean_nat_to_int(x_60);
x_67 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_65, x_66);
lean_dec(x_66);
x_68 = lean_array_get_size(x_61);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_lt(x_69, x_68);
x_71 = 0;
x_72 = lean_array_get_size(x_62);
x_73 = lean_nat_dec_lt(x_69, x_72);
x_74 = lean_array_get_size(x_63);
x_75 = lean_nat_dec_lt(x_69, x_74);
if (x_70 == 0)
{
lean_dec(x_68);
lean_dec(x_61);
x_76 = x_67;
goto block_111;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_68, x_68);
if (x_112 == 0)
{
lean_dec(x_68);
lean_dec(x_61);
x_76 = x_67;
goto block_111;
}
else
{
size_t x_113; size_t x_114; lean_object* x_115; 
x_113 = 0;
x_114 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_115 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__2(x_61, x_113, x_114, x_67);
lean_dec(x_61);
x_76 = x_115;
goto block_111;
}
}
block_111:
{
lean_object* x_77; 
x_77 = lean_byte_array_push(x_76, x_71);
if (x_73 == 0)
{
lean_dec(x_72);
lean_dec(x_62);
if (x_75 == 0)
{
lean_object* x_78; 
lean_dec(x_74);
lean_dec(x_63);
x_78 = lean_byte_array_push(x_77, x_71);
x_2 = x_8;
x_3 = x_78;
goto _start;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_74, x_74);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_74);
lean_dec(x_63);
x_81 = lean_byte_array_push(x_77, x_71);
x_2 = x_8;
x_3 = x_81;
goto _start;
}
else
{
size_t x_83; size_t x_84; lean_object* x_85; lean_object* x_86; 
x_83 = 0;
x_84 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_85 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__3(x_63, x_83, x_84, x_77);
lean_dec(x_63);
x_86 = lean_byte_array_push(x_85, x_71);
x_2 = x_8;
x_3 = x_86;
goto _start;
}
}
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_72, x_72);
if (x_88 == 0)
{
lean_dec(x_72);
lean_dec(x_62);
if (x_75 == 0)
{
lean_object* x_89; 
lean_dec(x_74);
lean_dec(x_63);
x_89 = lean_byte_array_push(x_77, x_71);
x_2 = x_8;
x_3 = x_89;
goto _start;
}
else
{
uint8_t x_91; 
x_91 = lean_nat_dec_le(x_74, x_74);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_74);
lean_dec(x_63);
x_92 = lean_byte_array_push(x_77, x_71);
x_2 = x_8;
x_3 = x_92;
goto _start;
}
else
{
size_t x_94; size_t x_95; lean_object* x_96; lean_object* x_97; 
x_94 = 0;
x_95 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_96 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__3(x_63, x_94, x_95, x_77);
lean_dec(x_63);
x_97 = lean_byte_array_push(x_96, x_71);
x_2 = x_8;
x_3 = x_97;
goto _start;
}
}
}
else
{
size_t x_99; size_t x_100; lean_object* x_101; 
x_99 = 0;
x_100 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_101 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__1(x_62, x_99, x_100, x_77);
lean_dec(x_62);
if (x_75 == 0)
{
lean_object* x_102; 
lean_dec(x_74);
lean_dec(x_63);
x_102 = lean_byte_array_push(x_101, x_71);
x_2 = x_8;
x_3 = x_102;
goto _start;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_74, x_74);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_74);
lean_dec(x_63);
x_105 = lean_byte_array_push(x_101, x_71);
x_2 = x_8;
x_3 = x_105;
goto _start;
}
else
{
size_t x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_108 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__3(x_63, x_99, x_107, x_101);
lean_dec(x_63);
x_109 = lean_byte_array_push(x_108, x_71);
x_2 = x_8;
x_3 = x_109;
goto _start;
}
}
}
}
}
}
default: 
{
lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_122; 
x_116 = lean_ctor_get(x_6, 0);
lean_inc(x_116);
lean_dec(x_6);
x_117 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1;
x_118 = lean_byte_array_push(x_3, x_117);
x_119 = lean_array_get_size(x_116);
x_120 = lean_unsigned_to_nat(0u);
x_121 = lean_nat_dec_lt(x_120, x_119);
x_122 = 0;
if (x_121 == 0)
{
lean_object* x_123; 
lean_dec(x_119);
lean_dec(x_116);
x_123 = lean_byte_array_push(x_118, x_122);
x_2 = x_8;
x_3 = x_123;
goto _start;
}
else
{
uint8_t x_125; 
x_125 = lean_nat_dec_le(x_119, x_119);
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec(x_119);
lean_dec(x_116);
x_126 = lean_byte_array_push(x_118, x_122);
x_2 = x_8;
x_3 = x_126;
goto _start;
}
else
{
size_t x_128; size_t x_129; lean_object* x_130; lean_object* x_131; 
x_128 = 0;
x_129 = lean_usize_of_nat(x_119);
lean_dec(x_119);
x_130 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__1(x_116, x_128, x_129, x_118);
lean_dec(x_116);
x_131 = lean_byte_array_push(x_130, x_122);
x_2 = x_8;
x_3 = x_131;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(4u);
x_4 = lean_nat_mul(x_3, x_2);
lean_dec(x_2);
x_5 = lean_mk_empty_byte_array(x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(x_1, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (x_3 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_Tactic_BVDecide_LRAT_lratProofToString(x_2);
x_6 = lean_string_to_utf8(x_5);
lean_dec(x_5);
x_7 = l_IO_FS_writeBinFile(x_1, x_6, x_4);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(x_2);
x_9 = l_IO_FS_writeBinFile(x_1, x_8, x_4);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_1, x_2, x_5, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1 = _init_l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1();
lean_mark_persistent(l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___closed__1);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__1();
l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__2);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__3);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__4);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__5);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__6);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__7);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__8);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline___closed__9);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos___closed__1);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__1();
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__2);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__3);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__4);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg___closed__5);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__1();
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__2);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__3);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__4);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero___closed__5);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__1();
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__2);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__3);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__4);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs___closed__5);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList___closed__1);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__1();
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__2);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__3);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__4);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete___closed__5);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat___closed__1);
l_Std_Internal_Parsec_satisfy___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__1___closed__1 = _init_l_Std_Internal_Parsec_satisfy___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__1___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_satisfy___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__1___closed__1);
l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___lambda__1___closed__1 = _init_l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___lambda__1___closed__1();
l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___closed__1 = _init_l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___closed__1();
lean_mark_persistent(l_Std_Internal_Parsec_manyCore___at_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___spec__2___closed__1);
l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go___closed__1();
l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__1);
l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__2);
l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero___closed__3);
l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__1);
l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__2();
l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___closed__3);
l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg___closed__1);
l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos___closed__1);
l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__1();
l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__2 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__2);
l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3 = _init_l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction___closed__3);
l_Std_Tactic_BVDecide_LRAT_loadLRATProof___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_loadLRATProof___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_loadLRATProof___closed__1);
l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___spec__1___closed__1);
l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint___closed__1);
l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__1);
l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__2);
l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__3);
l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__4 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize___closed__4);
l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Std_Tactic_BVDecide_LRAT_lratProofToString___spec__1___closed__1);
l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__1);
l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__2);
l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__3);
l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__4);
l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__5 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__5();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__5);
l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__6 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__6();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__6);
l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__7 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__7();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__7);
l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__8 = _init_l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__8();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
