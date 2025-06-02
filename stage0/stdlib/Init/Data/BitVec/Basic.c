// Lean compiler output
// Module: Init.Data.BitVec.Basic
// Imports: Init.Data.Fin.Basic Init.Data.Nat.Bitwise.Lemmas Init.Data.Nat.Power2 Init.Data.Int.Bitwise Init.Data.BitVec.BasicAux
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
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_abs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_toInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_setWidth___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofBool___boxed(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instPowNat(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getLsb_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__20;
lean_object* l_BitVec_ofNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofNatLt(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeft___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__7;
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instAndOp(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_neg___boxed(lean_object*, lean_object*);
static lean_object* l_BitVec_BitVec_repr___closed__3;
LEAN_EXPORT lean_object* l_BitVec_instHShiftRightNat(lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__21;
LEAN_EXPORT uint8_t l_BitVec_usubOverflow___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smtSDiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smod___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_replicate(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_instHShiftRightNat___closed__1;
LEAN_EXPORT lean_object* l_BitVec_truncate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_srem___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_BitVec_replicate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_smulOverflow(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__10;
static lean_object* l_BitVec_term_____x23_x27_______closed__2;
LEAN_EXPORT lean_object* l_BitVec_append___boxed(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_getMsbD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___boxed(lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1;
LEAN_EXPORT lean_object* l_BitVec_term_____x23_x27____;
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_instMod___closed__1;
LEAN_EXPORT lean_object* l_BitVec_or(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_udiv(lean_object*);
static lean_object* l_BitVec_instDiv___closed__1;
LEAN_EXPORT lean_object* l_BitVec_xor___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_umulOverflow(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__12;
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_append(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
static lean_object* l_BitVec_BitVec_repr___closed__1;
static lean_object* l_BitVec_term_____x23_x27_______closed__1;
LEAN_EXPORT lean_object* l_BitVec_instMod___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_or___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sshiftRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_fill___boxed(lean_object*, lean_object*);
static lean_object* l_BitVec_instOrOp___closed__1;
LEAN_EXPORT lean_object* l_BitVec_and___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_signExtend___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_xor___boxed(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_getMsb_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_or___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_getLsb_x27___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__6;
LEAN_EXPORT lean_object* l_BitVec_and___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofNatLt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_reverse(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instXor___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_fill(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_smtUDiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_twoPow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instOrOp(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_allOnes(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_natCastInst(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___rarg(lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__16;
LEAN_EXPORT lean_object* l_BitVec_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRepr___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4;
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4;
LEAN_EXPORT lean_object* l_BitVec_instInhabited___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_concat___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_usubOverflow(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getLsbD(lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__6;
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_umod___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_BitVec_hash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_neg(lean_object*, lean_object*);
static lean_object* l_BitVec_instAndOp___closed__1;
LEAN_EXPORT lean_object* l_BitVec_getLsb_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_umod___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_umulOverflow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_saddOverflow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_udiv___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_msb___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_not(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_zero(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_and___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_x27_______closed__4;
LEAN_EXPORT lean_object* l_BitVec_getLsb_x27(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeftNat(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ssubOverflow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_toHex___boxed(lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_x27_______closed__5;
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5;
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___boxed(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_negOverflow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ule___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___rarg(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3;
LEAN_EXPORT lean_object* l_BitVec_append___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getMsbD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smtSDiv(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_ofBool___closed__2;
LEAN_EXPORT lean_object* l_BitVec_getLsb_x27___boxed(lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getLsbD___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_x27_______closed__6;
LEAN_EXPORT lean_object* l_BitVec_extractLsb___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instToString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_concat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instNeg(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smtUDiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_slt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_srem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_concat(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ule___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1;
LEAN_EXPORT lean_object* l_BitVec_sdiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instAndOp___boxed(lean_object*);
lean_object* l_List_replicateTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat___rarg(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ushiftRight(lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__13;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_instXor___closed__1;
lean_object* lean_nat_land(lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_x27_______closed__7;
LEAN_EXPORT lean_object* l_BitVec_shiftConcat(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__1;
LEAN_EXPORT lean_object* l_BitVec_sdiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ule(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_zeroExtend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smulOverflow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateLeft___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_toHex___boxed__const__1;
LEAN_EXPORT lean_object* l_BitVec_instDiv(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cast___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRepr(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT uint8_t l_BitVec_instGetElemNatBoolLt___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__4;
LEAN_EXPORT lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_sdivOverflow(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__17;
LEAN_EXPORT lean_object* l_BitVec_sdivOverflow___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__18;
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_slt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_umod(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__14;
LEAN_EXPORT lean_object* l_BitVec_append___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateRight(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_saddOverflow___closed__1;
LEAN_EXPORT lean_object* l_BitVec_instXor(lean_object*);
lean_object* l_Int_shiftRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_ssubOverflow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__9;
LEAN_EXPORT lean_object* l_BitVec_twoPow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instOrOp___boxed(lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11;
LEAN_EXPORT lean_object* l_BitVec_abs___boxed(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getMsb_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_zeroExtend___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_truncate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_and(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_pow___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__11;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6;
LEAN_EXPORT lean_object* l_BitVec_signExtend(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instIntCast(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_udiv___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cons(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofNatLt___rarg(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_uaddOverflow(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_saddOverflow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofNatLt___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftConcat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getLsbD___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getMsb_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7;
LEAN_EXPORT lean_object* l_BitVec_toInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_uaddOverflow___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_msb(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cons___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__5;
LEAN_EXPORT uint8_t l_BitVec_ule___rarg(lean_object*, lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9;
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___boxed(lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10;
LEAN_EXPORT uint8_t l_BitVec_getLsbD___rarg(lean_object*, lean_object*);
static lean_object* l_BitVec_ofBool___closed__1;
LEAN_EXPORT lean_object* l_BitVec_umod___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getLsb_x27___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_BitVec_BitVec_repr___closed__2;
static lean_object* l_BitVec_nil___closed__1;
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8;
LEAN_EXPORT lean_object* l_BitVec_allOnes___boxed(lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__13;
LEAN_EXPORT lean_object* l_BitVec_or___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftRightNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smod(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__3;
LEAN_EXPORT lean_object* l_BitVec_reverse___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ult___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_mul___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__15;
LEAN_EXPORT lean_object* l_BitVec_pow(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2;
static lean_object* l_BitVec_term_____x23_x27_______closed__3;
LEAN_EXPORT lean_object* l_BitVec_ofInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_mul(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3;
LEAN_EXPORT lean_object* l_BitVec_sle___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5;
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_concat___rarg(lean_object*, uint8_t);
static lean_object* l_BitVec_term_____x23_______closed__19;
static lean_object* l_BitVec_term_____x23_x27_______closed__8;
LEAN_EXPORT lean_object* l_BitVec_xor(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_negOverflow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ult___boxed(lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12;
LEAN_EXPORT lean_object* l_BitVec_not___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_zero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_toHex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2;
LEAN_EXPORT lean_object* l_BitVec_instDiv___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_ult___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_term_____x23____;
LEAN_EXPORT lean_object* l_BitVec_cast___rarg(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMul(lean_object*);
static lean_object* l_BitVec_term_____x23_______closed__8;
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMod(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHashable(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___rarg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_udiv___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ult(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getMsb_x27___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_xor___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_BitVec_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instComplement(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofBool(uint8_t);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_nil;
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___boxed(lean_object*);
lean_object* l_BitVec_sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_sle(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofNatLt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofNatLt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_ofNatLt___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofNatLt___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_ofNatLt___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofNatLt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_ofNatLt(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_natCastInst(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_ofNat___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_nil___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_BitVec_ofNat(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_nil() {
_start:
{
lean_object* x_1; 
x_1 = l_BitVec_nil___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_BitVec_zero(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_zero___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_zero(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instInhabited___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instInhabited(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_allOnes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_2, x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_allOnes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_allOnes(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_BitVec_getLsb_x27___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Nat_testBit(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_getLsb_x27___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb_x27___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_BitVec_getLsb_x27___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_getLsb_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Nat_testBit(x_2, x_3);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_getLsb_x3f(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_BitVec_getMsb_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = lean_nat_sub(x_5, x_3);
lean_dec(x_5);
x_7 = l_Nat_testBit(x_2, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsb_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_BitVec_getMsb_x27(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsb_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_nat_sub(x_7, x_3);
lean_dec(x_7);
x_9 = l_Nat_testBit(x_2, x_8);
lean_dec(x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsb_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_getMsb_x3f(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_BitVec_getLsbD___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Nat_testBit(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsbD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_getLsbD___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsbD___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_BitVec_getLsbD___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsbD___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_getLsbD(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_BitVec_getMsbD(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_3, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_nat_sub(x_7, x_3);
lean_dec(x_7);
x_9 = l_Nat_testBit(x_2, x_8);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsbD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_BitVec_getMsbD(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_BitVec_msb(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_nat_sub(x_7, x_3);
lean_dec(x_7);
x_9 = l_Nat_testBit(x_2, x_8);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_msb___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_BitVec_msb(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_BitVec_instGetElemNatBoolLt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Nat_testBit(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_instGetElemNatBoolLt___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_BitVec_instGetElemNatBoolLt___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instGetElemNatBoolLt(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_toInt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_3, x_2);
x_5 = lean_nat_pow(x_3, x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_nat_to_int(x_2);
x_8 = lean_nat_to_int(x_5);
x_9 = lean_int_sub(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_nat_to_int(x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_toInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_toInt(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofInt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_pow(x_3, x_1);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_int_emod(x_2, x_5);
lean_dec(x_5);
x_7 = l_Int_toNat(x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_ofInt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_instIntCast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_ofInt___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BitVec", 6, 6);
return x_1;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term__#__", 9, 9);
return x_1;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_BitVec_term_____x23_______closed__1;
x_2 = l_BitVec_term_____x23_______closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_BitVec_term_____x23_______closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_BitVec_term_____x23_______closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_BitVec_term_____x23_______closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("noWs", 4, 4);
return x_1;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_BitVec_term_____x23_______closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_BitVec_term_____x23_______closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_BitVec_term_____x23_______closed__5;
x_2 = l_BitVec_term_____x23_______closed__8;
x_3 = l_BitVec_term_____x23_______closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_BitVec_term_____x23_______closed__13;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_BitVec_term_____x23_______closed__5;
x_2 = l_BitVec_term_____x23_______closed__12;
x_3 = l_BitVec_term_____x23_______closed__14;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_BitVec_term_____x23_______closed__5;
x_2 = l_BitVec_term_____x23_______closed__15;
x_3 = l_BitVec_term_____x23_______closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_BitVec_term_____x23_______closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_BitVec_term_____x23_______closed__18;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_BitVec_term_____x23_______closed__5;
x_2 = l_BitVec_term_____x23_______closed__16;
x_3 = l_BitVec_term_____x23_______closed__19;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_BitVec_term_____x23_______closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_BitVec_term_____x23_______closed__3;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_BitVec_term_____x23_______closed__20;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_BitVec_term_____x23____() {
_start:
{
lean_object* x_1; 
x_1 = l_BitVec_term_____x23_______closed__21;
return x_1;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1;
x_2 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2;
x_3 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3;
x_4 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BitVec.ofNat", 12, 12);
return x_1;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_BitVec_term_____x23_______closed__1;
x_2 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_BitVec_term_____x23_______closed__3;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_BitVec_term_____x23_______closed__7;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 5);
lean_inc(x_16);
x_17 = 0;
x_18 = l_Lean_SourceInfo_fromRef(x_16, x_17);
lean_dec(x_16);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9;
x_22 = l_Lean_addMacroScope(x_20, x_21, x_19);
x_23 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7;
x_24 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11;
lean_inc(x_18);
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_24);
x_26 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__13;
lean_inc(x_18);
x_27 = l_Lean_Syntax_node2(x_18, x_26, x_15, x_9);
x_28 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5;
x_29 = l_Lean_Syntax_node2(x_18, x_28, x_25, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(2u);
lean_inc(x_9);
x_11 = l_Lean_Syntax_matchesNull(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_9, x_14);
x_16 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_17 = l_BitVec_term_____x23_______closed__7;
lean_inc(x_16);
x_18 = l_Lean_Syntax_isOfKind(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = 0;
x_22 = l_Lean_SourceInfo_fromRef(x_2, x_21);
x_23 = l_BitVec_term_____x23_______closed__13;
lean_inc(x_22);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_BitVec_term_____x23_______closed__3;
x_26 = l_Lean_Syntax_node3(x_22, x_25, x_16, x_24, x_15);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_unexpandBitVecOfNat(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_BitVec_term_____x23_x27_______closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term__#'__", 10, 10);
return x_1;
}
}
static lean_object* _init_l_BitVec_term_____x23_x27_______closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_BitVec_term_____x23_______closed__1;
x_2 = l_BitVec_term_____x23_x27_______closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_BitVec_term_____x23_x27_______closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#'", 2, 2);
return x_1;
}
}
static lean_object* _init_l_BitVec_term_____x23_x27_______closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_BitVec_term_____x23_x27_______closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_term_____x23_x27_______closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_BitVec_term_____x23_______closed__5;
x_2 = l_BitVec_term_____x23_______closed__11;
x_3 = l_BitVec_term_____x23_x27_______closed__4;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_BitVec_term_____x23_x27_______closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_BitVec_term_____x23_______closed__5;
x_2 = l_BitVec_term_____x23_x27_______closed__5;
x_3 = l_BitVec_term_____x23_______closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_BitVec_term_____x23_x27_______closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_BitVec_term_____x23_______closed__5;
x_2 = l_BitVec_term_____x23_x27_______closed__6;
x_3 = l_BitVec_term_____x23_______closed__19;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_BitVec_term_____x23_x27_______closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_BitVec_term_____x23_x27_______closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_BitVec_term_____x23_x27_______closed__7;
x_4 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_BitVec_term_____x23_x27____() {
_start:
{
lean_object* x_1; 
x_1 = l_BitVec_term_____x23_x27_______closed__8;
return x_1;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BitVec.ofNatLT", 14, 14);
return x_1;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNatLT", 7, 7);
return x_1;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_BitVec_term_____x23_______closed__1;
x_2 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_BitVec_term_____x23_x27_______closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_12, x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4;
x_18 = l_Lean_addMacroScope(x_16, x_17, x_15);
x_19 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2;
x_20 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__6;
lean_inc(x_14);
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
x_22 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__13;
lean_inc(x_14);
x_23 = l_Lean_Syntax_node2(x_14, x_22, x_9, x_11);
x_24 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5;
x_25 = l_Lean_Syntax_node2(x_14, x_24, x_21, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(2u);
lean_inc(x_9);
x_11 = l_Lean_Syntax_matchesNull(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_9, x_14);
x_16 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_17 = 0;
x_18 = l_Lean_SourceInfo_fromRef(x_2, x_17);
x_19 = l_BitVec_term_____x23_x27_______closed__3;
lean_inc(x_18);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_BitVec_term_____x23_x27_______closed__2;
x_22 = l_Lean_Syntax_node3(x_18, x_21, x_15, x_20, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_unexpandBitVecOfNatLt(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_BitVec_toHex___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 48;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_toHex(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Nat_toDigits(x_3, x_2);
x_5 = lean_string_mk(x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = lean_string_length(x_5);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = l_BitVec_toHex___boxed__const__1;
x_13 = l_List_replicateTR___rarg(x_11, x_12);
x_14 = lean_string_mk(x_13);
x_15 = lean_string_append(x_14, x_5);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_BitVec_toHex___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_toHex(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_BitVec_BitVec_repr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("0x", 2, 2);
return x_1;
}
}
static lean_object* _init_l_BitVec_BitVec_repr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_BitVec_BitVec_repr___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_BitVec_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_BitVec_term_____x23_______closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_BitVec_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_BitVec_toHex(x_1, x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_BitVec_BitVec_repr___closed__2;
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_BitVec_BitVec_repr___closed__3;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_BitVec_repr(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_instRepr(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_instToString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_BitVec_BitVec_repr(x_1, x_2);
x_4 = l_Std_Format_defWidth;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_format_pretty(x_3, x_4, x_5, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BitVec_neg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_pow(x_3, x_1);
x_5 = lean_nat_sub(x_4, x_2);
lean_dec(x_4);
x_6 = l_BitVec_ofNat(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BitVec_neg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_neg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_instNeg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_neg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_abs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_1);
if (x_4 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = lean_nat_sub(x_6, x_3);
lean_dec(x_6);
x_8 = l_Nat_testBit(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_9; 
x_9 = l_BitVec_neg(x_1, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_abs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_abs(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_mul(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_mul(x_2, x_3);
x_5 = l_BitVec_ofNat(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_mul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_mul(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMul(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_mul___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_pow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = l_BitVec_pow(x_1, x_2, x_7);
lean_dec(x_7);
x_9 = l_BitVec_mul(x_1, x_8, x_2);
lean_dec(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_BitVec_ofNat(x_1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_pow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_pow(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_pow___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_udiv___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_udiv___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_udiv(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_instDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_BitVec_udiv___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDiv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instDiv___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDiv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instDiv(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_umod___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_umod___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_umod(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_instMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_BitVec_umod___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMod(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instMod___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMod___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instMod(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtUDiv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_BitVec_ofNat(x_1, x_4);
x_6 = lean_nat_dec_eq(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_nat_div(x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_BitVec_allOnes(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtUDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_smtUDiv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_nat_div(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_nat_sub(x_8, x_4);
lean_dec(x_8);
x_10 = l_Nat_testBit(x_2, x_9);
x_11 = l_Nat_testBit(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_nat_div(x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_BitVec_neg(x_1, x_3);
x_14 = lean_nat_div(x_2, x_13);
lean_dec(x_13);
x_15 = l_BitVec_neg(x_1, x_14);
lean_dec(x_14);
return x_15;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_BitVec_neg(x_1, x_2);
x_17 = lean_nat_div(x_16, x_3);
lean_dec(x_16);
x_18 = l_BitVec_neg(x_1, x_17);
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_BitVec_neg(x_1, x_2);
x_20 = l_BitVec_neg(x_1, x_3);
x_21 = lean_nat_div(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_sdiv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_BitVec_smtUDiv(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_nat_sub(x_8, x_4);
lean_dec(x_8);
x_10 = l_Nat_testBit(x_2, x_9);
x_11 = l_Nat_testBit(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_BitVec_smtUDiv(x_1, x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_BitVec_neg(x_1, x_3);
x_14 = l_BitVec_smtUDiv(x_1, x_2, x_13);
lean_dec(x_13);
x_15 = l_BitVec_neg(x_1, x_14);
lean_dec(x_14);
return x_15;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_BitVec_neg(x_1, x_2);
x_17 = l_BitVec_smtUDiv(x_1, x_16, x_3);
lean_dec(x_16);
x_18 = l_BitVec_neg(x_1, x_17);
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_BitVec_neg(x_1, x_2);
x_20 = l_BitVec_neg(x_1, x_3);
x_21 = l_BitVec_smtUDiv(x_1, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_smtSDiv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_srem(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_nat_mod(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_nat_sub(x_8, x_4);
lean_dec(x_8);
x_10 = l_Nat_testBit(x_2, x_9);
x_11 = l_Nat_testBit(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_nat_mod(x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_BitVec_neg(x_1, x_3);
x_14 = lean_nat_mod(x_2, x_13);
lean_dec(x_13);
return x_14;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_BitVec_neg(x_1, x_2);
x_16 = lean_nat_mod(x_15, x_3);
lean_dec(x_15);
x_17 = l_BitVec_neg(x_1, x_16);
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_BitVec_neg(x_1, x_2);
x_19 = l_BitVec_neg(x_1, x_3);
x_20 = lean_nat_mod(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = l_BitVec_neg(x_1, x_20);
lean_dec(x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_srem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_srem(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_smod(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_nat_mod(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_nat_sub(x_8, x_4);
lean_dec(x_8);
x_10 = l_Nat_testBit(x_2, x_9);
x_11 = l_Nat_testBit(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_nat_mod(x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_BitVec_neg(x_1, x_3);
x_14 = lean_nat_mod(x_2, x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_eq(x_14, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_BitVec_add(x_1, x_14, x_3);
lean_dec(x_14);
return x_16;
}
else
{
return x_14;
}
}
}
else
{
if (x_11 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_BitVec_neg(x_1, x_2);
x_18 = lean_nat_mod(x_17, x_3);
lean_dec(x_17);
x_19 = lean_nat_dec_eq(x_18, x_4);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_BitVec_sub(x_1, x_3, x_18);
lean_dec(x_18);
return x_20;
}
else
{
return x_18;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_BitVec_neg(x_1, x_2);
x_22 = l_BitVec_neg(x_1, x_3);
x_23 = lean_nat_mod(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = l_BitVec_neg(x_1, x_23);
lean_dec(x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_smod(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_BitVec_ofBool___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_BitVec_ofNat(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_BitVec_ofBool___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_BitVec_ofNat(x_1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBool(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_BitVec_ofBool___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_BitVec_ofBool___closed__2;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_BitVec_ofBool(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_fill(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_BitVec_ofNat(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_BitVec_ofNat(x_1, x_5);
x_7 = l_BitVec_neg(x_1, x_6);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_fill___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_BitVec_fill(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_BitVec_ult___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_ult___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_BitVec_ult___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_ult(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_BitVec_ule___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_ule___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_BitVec_ule___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_ule(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_BitVec_slt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_BitVec_toInt(x_1, x_2);
x_5 = l_BitVec_toInt(x_1, x_3);
x_6 = lean_int_dec_lt(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BitVec_slt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_BitVec_slt(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_BitVec_sle(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_BitVec_toInt(x_1, x_2);
x_5 = l_BitVec_toInt(x_1, x_3);
x_6 = lean_int_dec_le(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BitVec_sle___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_BitVec_sle(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_BitVec_cast___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_cast___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_cast(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_shiftr(x_3, x_1);
x_5 = l_BitVec_ofNat(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_extractLsb_x27___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_extractLsb_x27___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_extractLsb_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_nat_sub(x_1, x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = l_BitVec_extractLsb_x27___rarg(x_2, x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_extractLsb___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_extractLsb___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_extractLsb(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_BitVec_setWidth_x27___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_setWidth_x27___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_setWidth_x27(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_shiftl(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_shiftLeftZeroExtend___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_shiftLeftZeroExtend___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_shiftLeftZeroExtend(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_le(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_BitVec_ofNat(x_2, x_3);
return x_5;
}
else
{
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_setWidth(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_zeroExtend(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_setWidth(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_zeroExtend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_zeroExtend(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_truncate(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_setWidth(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_truncate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_truncate(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_signExtend(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_BitVec_toInt(x_1, x_3);
x_5 = l_BitVec_ofInt(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_signExtend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_signExtend(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_land(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_and(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_and___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_and___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_and(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_instAndOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_BitVec_and___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_BitVec_instAndOp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instAndOp___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instAndOp___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instAndOp(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_lor(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_or(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_or___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_or___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_or(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_instOrOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_BitVec_or___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_BitVec_instOrOp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instOrOp___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instOrOp___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instOrOp(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_lxor(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_xor___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_xor___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_xor(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_instXor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_BitVec_xor___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_BitVec_instXor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instXor___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instXor___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instXor(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_not(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_BitVec_allOnes(x_1);
x_4 = lean_nat_lxor(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_not___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_not(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_instComplement(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_not___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_shiftl(x_2, x_3);
x_5 = l_BitVec_ofNat(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_shiftLeft(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeftNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_shiftLeft___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_shiftr(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_ushiftRight___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_ushiftRight___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_ushiftRight(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_BitVec_instHShiftRightNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_BitVec_ushiftRight___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRightNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instHShiftRightNat___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRightNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instHShiftRightNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_BitVec_toInt(x_1, x_2);
x_5 = l_Int_shiftRight(x_4, x_3);
lean_dec(x_4);
x_6 = l_BitVec_ofInt(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_sshiftRight(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BitVec_shiftLeft(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BitVec_instHShiftLeft(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_shiftr(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_BitVec_instHShiftRight___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_instHShiftRight___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_instHShiftRight(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BitVec_sshiftRight(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BitVec_sshiftRight_x27(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_BitVec_shiftLeft(x_1, x_2, x_3);
x_5 = lean_nat_sub(x_1, x_3);
x_6 = lean_nat_shiftr(x_2, x_5);
lean_dec(x_5);
x_7 = lean_nat_lor(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_rotateLeftAux(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_mod(x_3, x_1);
x_5 = l_BitVec_rotateLeftAux(x_1, x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_rotateLeft(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_nat_shiftr(x_2, x_3);
x_5 = lean_nat_sub(x_1, x_3);
x_6 = l_BitVec_shiftLeft(x_1, x_2, x_5);
lean_dec(x_5);
x_7 = lean_nat_lor(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_rotateRightAux(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_mod(x_3, x_1);
x_5 = l_BitVec_rotateRightAux(x_1, x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_rotateRight(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_shiftl(x_2, x_1);
x_5 = lean_nat_lor(x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_append(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_append___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_append___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_append(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_append___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_instHAppendHAddNat___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_instHAppendHAddNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_nat_mul(x_1, x_7);
x_9 = l_BitVec_replicate(x_1, x_7, x_3);
lean_dec(x_7);
x_10 = l_BitVec_append___rarg(x_8, x_3, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_BitVec_nil___closed__1;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_replicate(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___rarg(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_BitVec_ofBool(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_BitVec_append___rarg(x_4, x_1, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_concat___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_BitVec_concat___rarg(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_concat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_1, x_4);
x_6 = l_BitVec_concat___rarg(x_2, x_3);
x_7 = l_BitVec_setWidth(x_5, x_1, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_BitVec_shiftConcat(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_cons(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_BitVec_ofBool(x_2);
x_5 = l_BitVec_append___rarg(x_1, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_cons___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_BitVec_cons(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_BitVec_ofNat(x_1, x_3);
x_5 = l_BitVec_shiftLeft(x_1, x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_twoPow(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint64_t l_BitVec_hash(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(64u);
x_4 = lean_nat_dec_le(x_1, x_3);
if (x_4 == 0)
{
uint64_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; 
x_5 = lean_uint64_of_nat(x_2);
x_6 = lean_nat_sub(x_1, x_3);
x_7 = lean_nat_shiftr(x_2, x_3);
x_8 = l_BitVec_setWidth(x_1, x_6, x_7);
lean_dec(x_7);
x_9 = l_BitVec_hash(x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
x_10 = lean_uint64_mix_hash(x_5, x_9);
return x_10;
}
else
{
uint64_t x_11; 
x_11 = lean_uint64_of_nat(x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_hash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_BitVec_hash(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHashable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_hash___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_BitVec_nil___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_List_lengthTRAux___rarg(x_4, x_5);
x_7 = l_BitVec_ofBoolListBE(x_4);
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_BitVec_cons(x_6, x_8, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_BitVec_nil___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_BitVec_ofBoolListLE(x_4);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_BitVec_concat___rarg(x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_BitVec_uaddOverflow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_pow(x_4, x_1);
x_6 = lean_nat_add(x_2, x_3);
x_7 = lean_nat_dec_le(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BitVec_uaddOverflow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_BitVec_uaddOverflow(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_BitVec_saddOverflow___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_BitVec_saddOverflow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = l_BitVec_saddOverflow___closed__1;
x_7 = l_Int_pow(x_6, x_5);
lean_dec(x_5);
x_8 = l_BitVec_toInt(x_1, x_2);
x_9 = l_BitVec_toInt(x_1, x_3);
x_10 = lean_int_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_int_dec_le(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_int_neg(x_7);
lean_dec(x_7);
x_13 = lean_int_dec_lt(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_7);
x_14 = 1;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_saddOverflow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_BitVec_saddOverflow(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_BitVec_usubOverflow___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_BitVec_usubOverflow___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_BitVec_usubOverflow___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BitVec_usubOverflow(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_BitVec_ssubOverflow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = l_BitVec_saddOverflow___closed__1;
x_7 = l_Int_pow(x_6, x_5);
lean_dec(x_5);
x_8 = l_BitVec_toInt(x_1, x_2);
x_9 = l_BitVec_toInt(x_1, x_3);
x_10 = lean_int_sub(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_int_dec_le(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_int_neg(x_7);
lean_dec(x_7);
x_13 = lean_int_dec_lt(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_7);
x_14 = 1;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ssubOverflow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_BitVec_ssubOverflow(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_BitVec_negOverflow(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = l_BitVec_toInt(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = l_BitVec_saddOverflow___closed__1;
x_7 = l_Int_pow(x_6, x_5);
lean_dec(x_5);
x_8 = lean_int_neg(x_7);
lean_dec(x_7);
x_9 = lean_int_dec_eq(x_3, x_8);
lean_dec(x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_BitVec_negOverflow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_BitVec_negOverflow(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_BitVec_sdivOverflow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = l_BitVec_saddOverflow___closed__1;
x_7 = l_Int_pow(x_6, x_5);
lean_dec(x_5);
x_8 = l_BitVec_toInt(x_1, x_2);
x_9 = l_BitVec_toInt(x_1, x_3);
x_10 = lean_int_ediv(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_int_dec_le(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_int_neg(x_7);
lean_dec(x_7);
x_13 = lean_int_dec_lt(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_7);
x_14 = 1;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sdivOverflow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_BitVec_sdivOverflow(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = lean_nat_add(x_6, x_5);
x_8 = l_BitVec_setWidth(x_7, x_6, x_2);
x_9 = l_BitVec_reverse(x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
x_10 = lean_nat_dec_lt(x_3, x_7);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
lean_dec(x_7);
x_11 = 0;
x_12 = l_BitVec_concat___rarg(x_9, x_11);
lean_dec(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_nat_sub(x_7, x_5);
lean_dec(x_7);
x_14 = lean_nat_sub(x_13, x_3);
lean_dec(x_13);
x_15 = l_Nat_testBit(x_2, x_14);
lean_dec(x_14);
x_16 = l_BitVec_concat___rarg(x_9, x_15);
lean_dec(x_9);
return x_16;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_reverse(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_BitVec_umulOverflow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_pow(x_4, x_1);
x_6 = lean_nat_mul(x_2, x_3);
x_7 = lean_nat_dec_le(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BitVec_umulOverflow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_BitVec_umulOverflow(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_BitVec_smulOverflow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = l_BitVec_saddOverflow___closed__1;
x_7 = l_Int_pow(x_6, x_5);
lean_dec(x_5);
x_8 = l_BitVec_toInt(x_1, x_2);
x_9 = l_BitVec_toInt(x_1, x_3);
x_10 = lean_int_mul(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_int_dec_le(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_int_neg(x_7);
lean_dec(x_7);
x_13 = lean_int_dec_lt(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_7);
x_14 = 1;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smulOverflow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_BitVec_smulOverflow(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Fin_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Power2(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Bitwise(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_BasicAux(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Fin_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Power2(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Bitwise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_BasicAux(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_BitVec_nil___closed__1 = _init_l_BitVec_nil___closed__1();
lean_mark_persistent(l_BitVec_nil___closed__1);
l_BitVec_nil = _init_l_BitVec_nil();
lean_mark_persistent(l_BitVec_nil);
l_BitVec_term_____x23_______closed__1 = _init_l_BitVec_term_____x23_______closed__1();
lean_mark_persistent(l_BitVec_term_____x23_______closed__1);
l_BitVec_term_____x23_______closed__2 = _init_l_BitVec_term_____x23_______closed__2();
lean_mark_persistent(l_BitVec_term_____x23_______closed__2);
l_BitVec_term_____x23_______closed__3 = _init_l_BitVec_term_____x23_______closed__3();
lean_mark_persistent(l_BitVec_term_____x23_______closed__3);
l_BitVec_term_____x23_______closed__4 = _init_l_BitVec_term_____x23_______closed__4();
lean_mark_persistent(l_BitVec_term_____x23_______closed__4);
l_BitVec_term_____x23_______closed__5 = _init_l_BitVec_term_____x23_______closed__5();
lean_mark_persistent(l_BitVec_term_____x23_______closed__5);
l_BitVec_term_____x23_______closed__6 = _init_l_BitVec_term_____x23_______closed__6();
lean_mark_persistent(l_BitVec_term_____x23_______closed__6);
l_BitVec_term_____x23_______closed__7 = _init_l_BitVec_term_____x23_______closed__7();
lean_mark_persistent(l_BitVec_term_____x23_______closed__7);
l_BitVec_term_____x23_______closed__8 = _init_l_BitVec_term_____x23_______closed__8();
lean_mark_persistent(l_BitVec_term_____x23_______closed__8);
l_BitVec_term_____x23_______closed__9 = _init_l_BitVec_term_____x23_______closed__9();
lean_mark_persistent(l_BitVec_term_____x23_______closed__9);
l_BitVec_term_____x23_______closed__10 = _init_l_BitVec_term_____x23_______closed__10();
lean_mark_persistent(l_BitVec_term_____x23_______closed__10);
l_BitVec_term_____x23_______closed__11 = _init_l_BitVec_term_____x23_______closed__11();
lean_mark_persistent(l_BitVec_term_____x23_______closed__11);
l_BitVec_term_____x23_______closed__12 = _init_l_BitVec_term_____x23_______closed__12();
lean_mark_persistent(l_BitVec_term_____x23_______closed__12);
l_BitVec_term_____x23_______closed__13 = _init_l_BitVec_term_____x23_______closed__13();
lean_mark_persistent(l_BitVec_term_____x23_______closed__13);
l_BitVec_term_____x23_______closed__14 = _init_l_BitVec_term_____x23_______closed__14();
lean_mark_persistent(l_BitVec_term_____x23_______closed__14);
l_BitVec_term_____x23_______closed__15 = _init_l_BitVec_term_____x23_______closed__15();
lean_mark_persistent(l_BitVec_term_____x23_______closed__15);
l_BitVec_term_____x23_______closed__16 = _init_l_BitVec_term_____x23_______closed__16();
lean_mark_persistent(l_BitVec_term_____x23_______closed__16);
l_BitVec_term_____x23_______closed__17 = _init_l_BitVec_term_____x23_______closed__17();
lean_mark_persistent(l_BitVec_term_____x23_______closed__17);
l_BitVec_term_____x23_______closed__18 = _init_l_BitVec_term_____x23_______closed__18();
lean_mark_persistent(l_BitVec_term_____x23_______closed__18);
l_BitVec_term_____x23_______closed__19 = _init_l_BitVec_term_____x23_______closed__19();
lean_mark_persistent(l_BitVec_term_____x23_______closed__19);
l_BitVec_term_____x23_______closed__20 = _init_l_BitVec_term_____x23_______closed__20();
lean_mark_persistent(l_BitVec_term_____x23_______closed__20);
l_BitVec_term_____x23_______closed__21 = _init_l_BitVec_term_____x23_______closed__21();
lean_mark_persistent(l_BitVec_term_____x23_______closed__21);
l_BitVec_term_____x23____ = _init_l_BitVec_term_____x23____();
lean_mark_persistent(l_BitVec_term_____x23____);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__13 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__13();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__13);
l_BitVec_term_____x23_x27_______closed__1 = _init_l_BitVec_term_____x23_x27_______closed__1();
lean_mark_persistent(l_BitVec_term_____x23_x27_______closed__1);
l_BitVec_term_____x23_x27_______closed__2 = _init_l_BitVec_term_____x23_x27_______closed__2();
lean_mark_persistent(l_BitVec_term_____x23_x27_______closed__2);
l_BitVec_term_____x23_x27_______closed__3 = _init_l_BitVec_term_____x23_x27_______closed__3();
lean_mark_persistent(l_BitVec_term_____x23_x27_______closed__3);
l_BitVec_term_____x23_x27_______closed__4 = _init_l_BitVec_term_____x23_x27_______closed__4();
lean_mark_persistent(l_BitVec_term_____x23_x27_______closed__4);
l_BitVec_term_____x23_x27_______closed__5 = _init_l_BitVec_term_____x23_x27_______closed__5();
lean_mark_persistent(l_BitVec_term_____x23_x27_______closed__5);
l_BitVec_term_____x23_x27_______closed__6 = _init_l_BitVec_term_____x23_x27_______closed__6();
lean_mark_persistent(l_BitVec_term_____x23_x27_______closed__6);
l_BitVec_term_____x23_x27_______closed__7 = _init_l_BitVec_term_____x23_x27_______closed__7();
lean_mark_persistent(l_BitVec_term_____x23_x27_______closed__7);
l_BitVec_term_____x23_x27_______closed__8 = _init_l_BitVec_term_____x23_x27_______closed__8();
lean_mark_persistent(l_BitVec_term_____x23_x27_______closed__8);
l_BitVec_term_____x23_x27____ = _init_l_BitVec_term_____x23_x27____();
lean_mark_persistent(l_BitVec_term_____x23_x27____);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5);
l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__6 = _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__6();
lean_mark_persistent(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__6);
l_BitVec_toHex___boxed__const__1 = _init_l_BitVec_toHex___boxed__const__1();
lean_mark_persistent(l_BitVec_toHex___boxed__const__1);
l_BitVec_BitVec_repr___closed__1 = _init_l_BitVec_BitVec_repr___closed__1();
lean_mark_persistent(l_BitVec_BitVec_repr___closed__1);
l_BitVec_BitVec_repr___closed__2 = _init_l_BitVec_BitVec_repr___closed__2();
lean_mark_persistent(l_BitVec_BitVec_repr___closed__2);
l_BitVec_BitVec_repr___closed__3 = _init_l_BitVec_BitVec_repr___closed__3();
lean_mark_persistent(l_BitVec_BitVec_repr___closed__3);
l_BitVec_instDiv___closed__1 = _init_l_BitVec_instDiv___closed__1();
lean_mark_persistent(l_BitVec_instDiv___closed__1);
l_BitVec_instMod___closed__1 = _init_l_BitVec_instMod___closed__1();
lean_mark_persistent(l_BitVec_instMod___closed__1);
l_BitVec_ofBool___closed__1 = _init_l_BitVec_ofBool___closed__1();
lean_mark_persistent(l_BitVec_ofBool___closed__1);
l_BitVec_ofBool___closed__2 = _init_l_BitVec_ofBool___closed__2();
lean_mark_persistent(l_BitVec_ofBool___closed__2);
l_BitVec_instAndOp___closed__1 = _init_l_BitVec_instAndOp___closed__1();
lean_mark_persistent(l_BitVec_instAndOp___closed__1);
l_BitVec_instOrOp___closed__1 = _init_l_BitVec_instOrOp___closed__1();
lean_mark_persistent(l_BitVec_instOrOp___closed__1);
l_BitVec_instXor___closed__1 = _init_l_BitVec_instXor___closed__1();
lean_mark_persistent(l_BitVec_instXor___closed__1);
l_BitVec_instHShiftRightNat___closed__1 = _init_l_BitVec_instHShiftRightNat___closed__1();
lean_mark_persistent(l_BitVec_instHShiftRightNat___closed__1);
l_BitVec_saddOverflow___closed__1 = _init_l_BitVec_saddOverflow___closed__1();
lean_mark_persistent(l_BitVec_saddOverflow___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
