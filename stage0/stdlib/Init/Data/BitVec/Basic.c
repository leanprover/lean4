// Lean compiler output
// Module: Init.Data.BitVec.Basic
// Imports: public import Init.Data.Int.Bitwise.Basic public import Init.Data.Bool public import Init.Data.Int.DivMod.Basic public import Init.WF import Init.Data.Nat.Bitwise.Lemmas import Init.Data.Nat.Lemmas import Init.Data.Nat.Internal.Linear import Init.Meta.Defs import Init.Omega import Init.WFTactics
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
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* l_Int_shiftRight(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Nat_shiftRight___boxed(lean_object*, lean_object*);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_sub(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instNatCast___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instNatCast___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instNatCast(lean_object*);
static lean_once_cell_t l_BitVec_nil___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_BitVec_nil___closed__0;
LEAN_EXPORT lean_object* l_BitVec_nil;
LEAN_EXPORT lean_object* l_BitVec_zero___redArg();
LEAN_EXPORT lean_object* l_BitVec_zero___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_zero(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_zero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instInhabited___redArg();
LEAN_EXPORT lean_object* l_BitVec_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instInhabited___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_allOnes(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_allOnes___boxed(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_getLsb___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getLsb___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_getLsb(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getLsb___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getLsb_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getLsb_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_getMsb(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getMsb___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getMsb_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getMsb_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_getLsbD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getLsbD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_getLsbD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getLsbD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_getMsbD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_getMsbD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_msb(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_msb___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_instGetElemNatBoolLt___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_BitVec_instGetElemNatBoolLt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_BitVec_instGetElemNatBoolLt___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instGetElemNatBoolLt___redArg___closed__0 = (const lean_object*)&l_BitVec_instGetElemNatBoolLt___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___redArg();
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00BitVec_toInt_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_toInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_toInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instIntCast(lean_object*);
static const lean_string_object l_BitVec_term_____x23_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_BitVec_term_____x23_____00__closed__0 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__0_value;
static const lean_string_object l_BitVec_term_____x23_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term__#__"};
static const lean_object* l_BitVec_term_____x23_____00__closed__1 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__1_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_BitVec_term_____x23_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__2_value_aux_0),((lean_object*)&l_BitVec_term_____x23_____00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(14, 106, 244, 245, 0, 94, 14, 228)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__2 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__2_value;
static const lean_string_object l_BitVec_term_____x23_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_BitVec_term_____x23_____00__closed__3 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__3_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_BitVec_term_____x23_____00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__4 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__4_value;
static const lean_string_object l_BitVec_term_____x23_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_BitVec_term_____x23_____00__closed__5 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__5_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_BitVec_term_____x23_____00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__6 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__6_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__6_value)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__7 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__7_value;
static const lean_string_object l_BitVec_term_____x23_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noWs"};
static const lean_object* l_BitVec_term_____x23_____00__closed__8 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__8_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_BitVec_term_____x23_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(92, 29, 204, 148, 167, 109, 242, 21)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__9 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__9_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__9_value)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__10 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__10_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__4_value),((lean_object*)&l_BitVec_term_____x23_____00__closed__7_value),((lean_object*)&l_BitVec_term_____x23_____00__closed__10_value)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__11 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__11_value;
static const lean_string_object l_BitVec_term_____x23_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_BitVec_term_____x23_____00__closed__12 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__12_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__12_value)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__13 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__13_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__4_value),((lean_object*)&l_BitVec_term_____x23_____00__closed__11_value),((lean_object*)&l_BitVec_term_____x23_____00__closed__13_value)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__14 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__14_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__4_value),((lean_object*)&l_BitVec_term_____x23_____00__closed__14_value),((lean_object*)&l_BitVec_term_____x23_____00__closed__10_value)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__15 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__15_value;
static const lean_string_object l_BitVec_term_____x23_____00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_BitVec_term_____x23_____00__closed__16 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__16_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_BitVec_term_____x23_____00__closed__16_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__17 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__17_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__17_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_BitVec_term_____x23_____00__closed__18 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__18_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__4_value),((lean_object*)&l_BitVec_term_____x23_____00__closed__15_value),((lean_object*)&l_BitVec_term_____x23_____00__closed__18_value)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__19 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__19_value;
static const lean_ctor_object l_BitVec_term_____x23_____00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_BitVec_term_____x23_____00__closed__19_value)}};
static const lean_object* l_BitVec_term_____x23_____00__closed__20 = (const lean_object*)&l_BitVec_term_____x23_____00__closed__20_value;
LEAN_EXPORT const lean_object* l_BitVec_term_____x23____ = (const lean_object*)&l_BitVec_term_____x23_____00__closed__20_value;
static const lean_string_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__0 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__0_value;
static const lean_string_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1_value;
static const lean_string_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2_value;
static const lean_string_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3_value;
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value_aux_0),((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value_aux_1),((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value_aux_2),((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4_value;
static const lean_string_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "BitVec.ofNat"};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5_value;
static lean_once_cell_t l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6;
static const lean_string_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7_value;
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_BitVec_term_____x23_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8_value_aux_0),((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8_value;
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9_value;
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10_value;
static const lean_string_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11_value;
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12_value;
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_BitVec_term_____x23_x27_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term__#'__"};
static const lean_object* l_BitVec_term_____x23_x27_____00__closed__0 = (const lean_object*)&l_BitVec_term_____x23_x27_____00__closed__0_value;
static const lean_ctor_object l_BitVec_term_____x23_x27_____00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_BitVec_term_____x23_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_BitVec_term_____x23_x27_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_x27_____00__closed__1_value_aux_0),((lean_object*)&l_BitVec_term_____x23_x27_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 111, 91, 190, 189, 100, 156, 31)}};
static const lean_object* l_BitVec_term_____x23_x27_____00__closed__1 = (const lean_object*)&l_BitVec_term_____x23_x27_____00__closed__1_value;
static const lean_string_object l_BitVec_term_____x23_x27_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#'"};
static const lean_object* l_BitVec_term_____x23_x27_____00__closed__2 = (const lean_object*)&l_BitVec_term_____x23_x27_____00__closed__2_value;
static const lean_ctor_object l_BitVec_term_____x23_x27_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_x27_____00__closed__2_value)}};
static const lean_object* l_BitVec_term_____x23_x27_____00__closed__3 = (const lean_object*)&l_BitVec_term_____x23_x27_____00__closed__3_value;
static const lean_ctor_object l_BitVec_term_____x23_x27_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__4_value),((lean_object*)&l_BitVec_term_____x23_____00__closed__10_value),((lean_object*)&l_BitVec_term_____x23_x27_____00__closed__3_value)}};
static const lean_object* l_BitVec_term_____x23_x27_____00__closed__4 = (const lean_object*)&l_BitVec_term_____x23_x27_____00__closed__4_value;
static const lean_ctor_object l_BitVec_term_____x23_x27_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__4_value),((lean_object*)&l_BitVec_term_____x23_x27_____00__closed__4_value),((lean_object*)&l_BitVec_term_____x23_____00__closed__10_value)}};
static const lean_object* l_BitVec_term_____x23_x27_____00__closed__5 = (const lean_object*)&l_BitVec_term_____x23_x27_____00__closed__5_value;
static const lean_ctor_object l_BitVec_term_____x23_x27_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__4_value),((lean_object*)&l_BitVec_term_____x23_x27_____00__closed__5_value),((lean_object*)&l_BitVec_term_____x23_____00__closed__18_value)}};
static const lean_object* l_BitVec_term_____x23_x27_____00__closed__6 = (const lean_object*)&l_BitVec_term_____x23_x27_____00__closed__6_value;
static const lean_ctor_object l_BitVec_term_____x23_x27_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_x27_____00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_BitVec_term_____x23_x27_____00__closed__6_value)}};
static const lean_object* l_BitVec_term_____x23_x27_____00__closed__7 = (const lean_object*)&l_BitVec_term_____x23_x27_____00__closed__7_value;
LEAN_EXPORT const lean_object* l_BitVec_term_____x23_x27____ = (const lean_object*)&l_BitVec_term_____x23_x27_____00__closed__7_value;
static const lean_string_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "BitVec.ofNatLT"};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__0 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__0_value;
static lean_once_cell_t l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1;
static const lean_string_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ofNatLT"};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2_value;
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_BitVec_term_____x23_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3_value_aux_0),((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 44, 243, 4, 118, 78, 150, 28)}};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3_value;
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4_value;
static const lean_ctor_object l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5 = (const lean_object*)&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5_value;
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_toHex___boxed__const__1;
LEAN_EXPORT lean_object* l_BitVec_toHex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_toHex___boxed(lean_object*, lean_object*);
static const lean_string_object l_BitVec_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "0x"};
static const lean_object* l_BitVec_repr___closed__0 = (const lean_object*)&l_BitVec_repr___closed__0_value;
static const lean_ctor_object l_BitVec_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_BitVec_repr___closed__0_value)}};
static const lean_object* l_BitVec_repr___closed__1 = (const lean_object*)&l_BitVec_repr___closed__1_value;
static const lean_ctor_object l_BitVec_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_BitVec_term_____x23_____00__closed__12_value)}};
static const lean_object* l_BitVec_repr___closed__2 = (const lean_object*)&l_BitVec_repr___closed__2_value;
LEAN_EXPORT lean_object* l_BitVec_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRepr___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRepr___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRepr(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instToString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instToString(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_neg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_neg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instNeg(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_abs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_abs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_mul___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMul(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_pow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_pow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instPowNat___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instPowNat___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instPowNat(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_udiv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_udiv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_udiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_udiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instDiv(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_umod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_umod___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_umod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_umod___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMod(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smtUDiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smtUDiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sdiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sdiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smtSDiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smtSDiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_srem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_srem___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smod___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_BitVec_ofBool___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_BitVec_ofBool___closed__0;
static lean_once_cell_t l_BitVec_ofBool___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_BitVec_ofBool___closed__1;
LEAN_EXPORT lean_object* l_BitVec_ofBool(uint8_t);
LEAN_EXPORT lean_object* l_BitVec_ofBool___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_fill(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_fill___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_ult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ult___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_ult(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ult___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_ule___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ule___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_ule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ule___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_slt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_slt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_sle(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sle___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractLsb___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_setWidth___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_zeroExtend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_zeroExtend___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_truncate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_truncate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_signExtend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_signExtend___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_and___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_and___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_and(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_and___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instAndOp(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_or___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_or___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_or(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_or___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instOrOp(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_xor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_xor___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_xor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_xor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instXorOp(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_not(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_not___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instComplement(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeft___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeftNat(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ushiftRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftRightNat(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sshiftRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___boxed(lean_object*, lean_object*);
static const lean_closure_object l_BitVec_instHShiftRight___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instHShiftRight___redArg___closed__0 = (const lean_object*)&l_BitVec_instHShiftRight___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___redArg();
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateLeft___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_rotateRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_append___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_append(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_append___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_replicate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_replicate___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_concat___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_concat___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_concat(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_concat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftConcat(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_shiftConcat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cons(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cons___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_twoPow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_twoPow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_intMin(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_intMin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_intMax(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_intMax___boxed(lean_object*);
LEAN_EXPORT uint64_t l_BitVec_hash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instHashable(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE___boxed(lean_object*);
LEAN_EXPORT uint8_t l_BitVec_uaddOverflow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_uaddOverflow___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_BitVec_saddOverflow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_BitVec_saddOverflow___closed__0;
LEAN_EXPORT uint8_t l_BitVec_saddOverflow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_saddOverflow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_usubOverflow___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_usubOverflow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_ssubOverflow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ssubOverflow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_negOverflow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_negOverflow___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_sdivOverflow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sdivOverflow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_reverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_reverse___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_umulOverflow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_umulOverflow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_smulOverflow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_smulOverflow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_clz(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_clz___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ctz(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ctz___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_BitVec_instMin___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_BitVec_instMin___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instMin___redArg___closed__0 = (const lean_object*)&l_BitVec_instMin___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg();
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMin(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_BitVec_instMax___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_BitVec_instMax___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instMax___redArg___closed__0 = (const lean_object*)&l_BitVec_instMax___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg();
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMax(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instNatCast___lam__0(lean_object* v_w_1_, lean_object* v_x_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_BitVec_ofNat(v_w_1_, v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instNatCast___lam__0___boxed(lean_object* v_w_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_BitVec_instNatCast___lam__0(v_w_4_, v_x_5_);
lean_dec(v_x_5_);
lean_dec(v_w_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instNatCast(lean_object* v_w_7_){
_start:
{
lean_object* v___f_8_; 
v___f_8_ = lean_alloc_closure((void*)(l_BitVec_instNatCast___lam__0___boxed), 2, 1);
lean_closure_set(v___f_8_, 0, v_w_7_);
return v___f_8_;
}
}
static lean_object* _init_l_BitVec_nil___closed__0(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = l_BitVec_ofNat(v___x_9_, v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l_BitVec_nil(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_11_;
}
}
lean_object* l_BitVec_zero___redArg(){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_unsigned_to_nat(0u);
return v___x_13_;
}
}
LEAN_EXPORT void l_BitVec_zero___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_14_;
v_res_14_ = l_BitVec_zero___redArg();
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_BitVec_zero___redArg___boxed(lean_object* v___dummy_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_BitVec_zero___redArg();
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zero(lean_object* v_n_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(0u);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zero___boxed(lean_object* v_n_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_BitVec_zero(v_n_19_);
lean_dec(v_n_19_);
return v_res_20_;
}
}
lean_object* l_BitVec_instInhabited___redArg(){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(0u);
return v___x_22_;
}
}
LEAN_EXPORT void l_BitVec_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_23_;
v_res_23_ = l_BitVec_instInhabited___redArg();
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l_BitVec_instInhabited___redArg___boxed(lean_object* v___dummy_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_BitVec_instInhabited___redArg();
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instInhabited(lean_object* v_n_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_unsigned_to_nat(0u);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instInhabited___boxed(lean_object* v_n_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_BitVec_instInhabited(v_n_28_);
lean_dec(v_n_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_BitVec_allOnes(lean_object* v_n_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_31_ = lean_unsigned_to_nat(2u);
v___x_32_ = lean_nat_pow(v___x_31_, v_n_30_);
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_sub(v___x_32_, v___x_33_);
lean_dec(v___x_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_BitVec_allOnes___boxed(lean_object* v_n_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_BitVec_allOnes(v_n_35_);
lean_dec(v_n_35_);
return v_res_36_;
}
}
uint8_t l_BitVec_getLsb___redArg(lean_object* v_x_37_, lean_object* v_i_38_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = l_Nat_testBit(v_x_37_, v_i_38_);
return v___x_39_;
}
}
LEAN_EXPORT void l_BitVec_getLsb___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_37_ = stack[0].m_obj;
lean_object* v_i_38_ = stack[1].m_obj;
uint8_t v_res_40_;
v_res_40_ = l_BitVec_getLsb___redArg(v_x_37_, v_i_38_);
stack->m_num = v_res_40_;
}
LEAN_EXPORT lean_object* l_BitVec_getLsb___redArg___boxed(lean_object* v_x_41_, lean_object* v_i_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_BitVec_getLsb___redArg(v_x_41_, v_i_42_);
lean_dec(v_i_42_);
lean_dec(v_x_41_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
uint8_t l_BitVec_getLsb(lean_object* v_w_45_, lean_object* v_x_46_, lean_object* v_i_47_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = l_Nat_testBit(v_x_46_, v_i_47_);
return v___x_48_;
}
}
LEAN_EXPORT void l_BitVec_getLsb_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_45_ = stack[0].m_obj;
lean_object* v_x_46_ = stack[1].m_obj;
lean_object* v_i_47_ = stack[2].m_obj;
uint8_t v_res_49_;
v_res_49_ = l_BitVec_getLsb(v_w_45_, v_x_46_, v_i_47_);
stack->m_num = v_res_49_;
}
LEAN_EXPORT lean_object* l_BitVec_getLsb___boxed(lean_object* v_w_50_, lean_object* v_x_51_, lean_object* v_i_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_BitVec_getLsb(v_w_50_, v_x_51_, v_i_52_);
lean_dec(v_i_52_);
lean_dec(v_x_51_);
lean_dec(v_w_50_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb_x3f(lean_object* v_w_55_, lean_object* v_x_56_, lean_object* v_i_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = lean_nat_dec_lt(v_i_57_, v_w_55_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; 
v___x_59_ = lean_box(0);
return v___x_59_;
}
else
{
uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = l_Nat_testBit(v_x_56_, v_i_57_);
v___x_61_ = lean_box(v___x_60_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb_x3f___boxed(lean_object* v_w_63_, lean_object* v_x_64_, lean_object* v_i_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_BitVec_getLsb_x3f(v_w_63_, v_x_64_, v_i_65_);
lean_dec(v_i_65_);
lean_dec(v_x_64_);
lean_dec(v_w_63_);
return v_res_66_;
}
}
uint8_t l_BitVec_getMsb(lean_object* v_w_67_, lean_object* v_x_68_, lean_object* v_i_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_sub(v_w_67_, v___x_70_);
v___x_72_ = lean_nat_sub(v___x_71_, v_i_69_);
lean_dec(v___x_71_);
v___x_73_ = l_Nat_testBit(v_x_68_, v___x_72_);
lean_dec(v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT void l_BitVec_getMsb_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_67_ = stack[0].m_obj;
lean_object* v_x_68_ = stack[1].m_obj;
lean_object* v_i_69_ = stack[2].m_obj;
uint8_t v_res_74_;
v_res_74_ = l_BitVec_getMsb(v_w_67_, v_x_68_, v_i_69_);
stack->m_num = v_res_74_;
}
LEAN_EXPORT lean_object* l_BitVec_getMsb___boxed(lean_object* v_w_75_, lean_object* v_x_76_, lean_object* v_i_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_BitVec_getMsb(v_w_75_, v_x_76_, v_i_77_);
lean_dec(v_i_77_);
lean_dec(v_x_76_);
lean_dec(v_w_75_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsb_x3f(lean_object* v_w_80_, lean_object* v_x_81_, lean_object* v_i_82_){
_start:
{
uint8_t v___x_83_; 
v___x_83_ = lean_nat_dec_lt(v_i_82_, v_w_80_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_sub(v_w_80_, v___x_85_);
v___x_87_ = lean_nat_sub(v___x_86_, v_i_82_);
lean_dec(v___x_86_);
v___x_88_ = l_Nat_testBit(v_x_81_, v___x_87_);
lean_dec(v___x_87_);
v___x_89_ = lean_box(v___x_88_);
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsb_x3f___boxed(lean_object* v_w_91_, lean_object* v_x_92_, lean_object* v_i_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_BitVec_getMsb_x3f(v_w_91_, v_x_92_, v_i_93_);
lean_dec(v_i_93_);
lean_dec(v_x_92_);
lean_dec(v_w_91_);
return v_res_94_;
}
}
uint8_t l_BitVec_getLsbD___redArg(lean_object* v_x_95_, lean_object* v_i_96_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = l_Nat_testBit(v_x_95_, v_i_96_);
return v___x_97_;
}
}
LEAN_EXPORT void l_BitVec_getLsbD___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_95_ = stack[0].m_obj;
lean_object* v_i_96_ = stack[1].m_obj;
uint8_t v_res_98_;
v_res_98_ = l_BitVec_getLsbD___redArg(v_x_95_, v_i_96_);
stack->m_num = v_res_98_;
}
LEAN_EXPORT lean_object* l_BitVec_getLsbD___redArg___boxed(lean_object* v_x_99_, lean_object* v_i_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_BitVec_getLsbD___redArg(v_x_99_, v_i_100_);
lean_dec(v_i_100_);
lean_dec(v_x_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
uint8_t l_BitVec_getLsbD(lean_object* v_w_103_, lean_object* v_x_104_, lean_object* v_i_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = l_Nat_testBit(v_x_104_, v_i_105_);
return v___x_106_;
}
}
LEAN_EXPORT void l_BitVec_getLsbD_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_103_ = stack[0].m_obj;
lean_object* v_x_104_ = stack[1].m_obj;
lean_object* v_i_105_ = stack[2].m_obj;
uint8_t v_res_107_;
v_res_107_ = l_BitVec_getLsbD(v_w_103_, v_x_104_, v_i_105_);
stack->m_num = v_res_107_;
}
LEAN_EXPORT lean_object* l_BitVec_getLsbD___boxed(lean_object* v_w_108_, lean_object* v_x_109_, lean_object* v_i_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_BitVec_getLsbD(v_w_108_, v_x_109_, v_i_110_);
lean_dec(v_i_110_);
lean_dec(v_x_109_);
lean_dec(v_w_108_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
uint8_t l_BitVec_getMsbD(lean_object* v_w_113_, lean_object* v_x_114_, lean_object* v_i_115_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = lean_nat_dec_lt(v_i_115_, v_w_113_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_sub(v_w_113_, v___x_117_);
v___x_119_ = lean_nat_sub(v___x_118_, v_i_115_);
lean_dec(v___x_118_);
v___x_120_ = l_Nat_testBit(v_x_114_, v___x_119_);
lean_dec(v___x_119_);
return v___x_120_;
}
}
}
LEAN_EXPORT void l_BitVec_getMsbD_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_113_ = stack[0].m_obj;
lean_object* v_x_114_ = stack[1].m_obj;
lean_object* v_i_115_ = stack[2].m_obj;
uint8_t v_res_121_;
v_res_121_ = l_BitVec_getMsbD(v_w_113_, v_x_114_, v_i_115_);
stack->m_num = v_res_121_;
}
LEAN_EXPORT lean_object* l_BitVec_getMsbD___boxed(lean_object* v_w_122_, lean_object* v_x_123_, lean_object* v_i_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_BitVec_getMsbD(v_w_122_, v_x_123_, v_i_124_);
lean_dec(v_i_124_);
lean_dec(v_x_123_);
lean_dec(v_w_122_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
uint8_t l_BitVec_msb(lean_object* v_n_127_, lean_object* v_x_128_){
_start:
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_nat_dec_lt(v___x_129_, v_n_127_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = lean_nat_sub(v_n_127_, v___x_131_);
v___x_133_ = l_Nat_testBit(v_x_128_, v___x_132_);
lean_dec(v___x_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT void l_BitVec_msb_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_127_ = stack[0].m_obj;
lean_object* v_x_128_ = stack[1].m_obj;
uint8_t v_res_134_;
v_res_134_ = l_BitVec_msb(v_n_127_, v_x_128_);
stack->m_num = v_res_134_;
}
LEAN_EXPORT lean_object* l_BitVec_msb___boxed(lean_object* v_n_135_, lean_object* v_x_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_BitVec_msb(v_n_135_, v_x_136_);
lean_dec(v_x_136_);
lean_dec(v_n_135_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
uint8_t l_BitVec_instGetElemNatBoolLt___redArg___lam__0(lean_object* v_xs_139_, lean_object* v_i_140_, lean_object* v_h_141_){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = l_Nat_testBit(v_xs_139_, v_i_140_);
return v___x_142_;
}
}
LEAN_EXPORT void l_BitVec_instGetElemNatBoolLt___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_139_ = stack[0].m_obj;
lean_object* v_i_140_ = stack[1].m_obj;
uint8_t v_res_143_;
v_res_143_ = l_BitVec_instGetElemNatBoolLt___redArg___lam__0(v_xs_139_, v_i_140_, lean_box(0));
stack->m_num = v_res_143_;
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___redArg___lam__0___boxed(lean_object* v_xs_144_, lean_object* v_i_145_, lean_object* v_h_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_BitVec_instGetElemNatBoolLt___redArg___lam__0(v_xs_144_, v_i_145_, v_h_146_);
lean_dec(v_i_145_);
lean_dec(v_xs_144_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
lean_object* l_BitVec_instGetElemNatBoolLt___redArg(){
_start:
{
lean_object* v___f_151_; 
v___f_151_ = ((lean_object*)(l_BitVec_instGetElemNatBoolLt___redArg___closed__0));
return v___f_151_;
}
}
LEAN_EXPORT void l_BitVec_instGetElemNatBoolLt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_152_;
v_res_152_ = l_BitVec_instGetElemNatBoolLt___redArg();
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___redArg___boxed(lean_object* v___dummy_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_BitVec_instGetElemNatBoolLt___redArg();
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt(lean_object* v_w_155_){
_start:
{
lean_object* v___f_156_; 
v___f_156_ = ((lean_object*)(l_BitVec_instGetElemNatBoolLt___redArg___closed__0));
return v___f_156_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___boxed(lean_object* v_w_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_BitVec_instGetElemNatBoolLt(v_w_157_);
lean_dec(v_w_157_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00BitVec_toInt_spec__0(lean_object* v_a_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_nat_to_int(v_a_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_BitVec_toInt(lean_object* v_n_161_, lean_object* v_x_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_163_ = lean_unsigned_to_nat(2u);
v___x_164_ = lean_nat_mul(v___x_163_, v_x_162_);
v___x_165_ = lean_nat_pow(v___x_163_, v_n_161_);
v___x_166_ = lean_nat_dec_lt(v___x_164_, v___x_165_);
lean_dec(v___x_164_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_nat_to_int(v_x_162_);
v___x_168_ = lean_nat_to_int(v___x_165_);
v___x_169_ = lean_int_sub(v___x_167_, v___x_168_);
lean_dec(v___x_168_);
lean_dec(v___x_167_);
return v___x_169_;
}
else
{
lean_object* v___x_170_; 
lean_dec(v___x_165_);
v___x_170_ = lean_nat_to_int(v_x_162_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_toInt___boxed(lean_object* v_n_171_, lean_object* v_x_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_BitVec_toInt(v_n_171_, v_x_172_);
lean_dec(v_n_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofInt(lean_object* v_n_174_, lean_object* v_i_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_176_ = lean_unsigned_to_nat(2u);
v___x_177_ = lean_nat_pow(v___x_176_, v_n_174_);
v___x_178_ = lean_nat_to_int(v___x_177_);
v___x_179_ = lean_int_emod(v_i_175_, v___x_178_);
lean_dec(v___x_178_);
v___x_180_ = l_Int_toNat(v___x_179_);
lean_dec(v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofInt___boxed(lean_object* v_n_181_, lean_object* v_i_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_BitVec_ofInt(v_n_181_, v_i_182_);
lean_dec(v_i_182_);
lean_dec(v_n_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instIntCast(lean_object* v_w_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_closure((void*)(l_BitVec_ofInt___boxed), 2, 1);
lean_closure_set(v___x_185_, 0, v_w_184_);
return v___x_185_;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5));
v___x_245_ = l_String_toRawSubstring_x27(v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1(lean_object* v_x_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__2));
lean_inc(v_x_259_);
v___x_263_ = l_Lean_Syntax_isOfKind(v_x_259_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_x_259_);
v___x_264_ = lean_box(1);
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_a_261_);
return v___x_265_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = l_Lean_Syntax_getArg(v_x_259_, v___x_266_);
v___x_268_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__6));
lean_inc(v___x_267_);
v___x_269_ = l_Lean_Syntax_isOfKind(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec(v___x_267_);
lean_dec(v_x_259_);
v___x_270_ = lean_box(1);
v___x_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v_a_261_);
return v___x_271_;
}
else
{
lean_object* v_quotContext_272_; lean_object* v_currMacroScope_273_; lean_object* v_ref_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_quotContext_272_ = lean_ctor_get(v_a_260_, 1);
v_currMacroScope_273_ = lean_ctor_get(v_a_260_, 2);
v_ref_274_ = lean_ctor_get(v_a_260_, 5);
v___x_275_ = lean_unsigned_to_nat(2u);
v___x_276_ = l_Lean_Syntax_getArg(v_x_259_, v___x_275_);
lean_dec(v_x_259_);
v___x_277_ = 0;
v___x_278_ = l_Lean_SourceInfo_fromRef(v_ref_274_, v___x_277_);
v___x_279_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
v___x_280_ = lean_obj_once(&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6, &l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6_once, _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6);
v___x_281_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8));
lean_inc(v_currMacroScope_273_);
lean_inc(v_quotContext_272_);
v___x_282_ = l_Lean_addMacroScope(v_quotContext_272_, v___x_281_, v_currMacroScope_273_);
v___x_283_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10));
lean_inc_n(v___x_278_, 2);
v___x_284_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_284_, 0, v___x_278_);
lean_ctor_set(v___x_284_, 1, v___x_280_);
lean_ctor_set(v___x_284_, 2, v___x_282_);
lean_ctor_set(v___x_284_, 3, v___x_283_);
v___x_285_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12));
v___x_286_ = l_Lean_Syntax_node2(v___x_278_, v___x_285_, v___x_276_, v___x_267_);
v___x_287_ = l_Lean_Syntax_node2(v___x_278_, v___x_279_, v___x_284_, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_a_261_);
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___boxed(lean_object* v_x_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1(v_x_289_, v_a_290_, v_a_291_);
lean_dec_ref(v_a_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat(lean_object* v_x_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
lean_inc(v_x_293_);
v___x_297_ = l_Lean_Syntax_isOfKind(v_x_293_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v_x_293_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_a_295_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = l_Lean_Syntax_getArg(v_x_293_, v___x_300_);
lean_dec(v_x_293_);
v___x_302_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_301_);
v___x_303_ = l_Lean_Syntax_matchesNull(v___x_301_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v_a_295_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_306_ = l_Lean_Syntax_getArg(v___x_301_, v___x_300_);
v___x_307_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__6));
lean_inc(v___x_306_);
v___x_308_ = l_Lean_Syntax_isOfKind(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v___x_306_);
lean_dec(v___x_301_);
v___x_309_ = lean_box(0);
v___x_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v_a_295_);
return v___x_310_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = l_Lean_Syntax_getArg(v___x_301_, v___x_311_);
lean_dec(v___x_301_);
v___x_313_ = 0;
v___x_314_ = l_Lean_SourceInfo_fromRef(v_a_294_, v___x_313_);
v___x_315_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__2));
v___x_316_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__12));
lean_inc(v___x_314_);
v___x_317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_314_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = l_Lean_Syntax_node3(v___x_314_, v___x_315_, v___x_306_, v___x_317_, v___x_312_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_a_295_);
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat___boxed(lean_object* v_x_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_BitVec_unexpandBitVecOfNat(v_x_320_, v_a_321_, v_a_322_);
lean_dec(v_a_321_);
return v_res_323_;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__0));
v___x_350_ = l_String_toRawSubstring_x27(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1(lean_object* v_x_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = ((lean_object*)(l_BitVec_term_____x23_x27_____00__closed__1));
lean_inc(v_x_361_);
v___x_365_ = l_Lean_Syntax_isOfKind(v_x_361_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec(v_x_361_);
v___x_366_ = lean_box(1);
v___x_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_a_363_);
return v___x_367_;
}
else
{
lean_object* v_quotContext_368_; lean_object* v_currMacroScope_369_; lean_object* v_ref_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_quotContext_368_ = lean_ctor_get(v_a_362_, 1);
v_currMacroScope_369_ = lean_ctor_get(v_a_362_, 2);
v_ref_370_ = lean_ctor_get(v_a_362_, 5);
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = l_Lean_Syntax_getArg(v_x_361_, v___x_371_);
v___x_373_ = lean_unsigned_to_nat(2u);
v___x_374_ = l_Lean_Syntax_getArg(v_x_361_, v___x_373_);
lean_dec(v_x_361_);
v___x_375_ = 0;
v___x_376_ = l_Lean_SourceInfo_fromRef(v_ref_370_, v___x_375_);
v___x_377_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
v___x_378_ = lean_obj_once(&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1, &l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1_once, _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1);
v___x_379_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3));
lean_inc(v_currMacroScope_369_);
lean_inc(v_quotContext_368_);
v___x_380_ = l_Lean_addMacroScope(v_quotContext_368_, v___x_379_, v_currMacroScope_369_);
v___x_381_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5));
lean_inc_n(v___x_376_, 2);
v___x_382_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_382_, 0, v___x_376_);
lean_ctor_set(v___x_382_, 1, v___x_378_);
lean_ctor_set(v___x_382_, 2, v___x_380_);
lean_ctor_set(v___x_382_, 3, v___x_381_);
v___x_383_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12));
v___x_384_ = l_Lean_Syntax_node2(v___x_376_, v___x_383_, v___x_372_, v___x_374_);
v___x_385_ = l_Lean_Syntax_node2(v___x_376_, v___x_377_, v___x_382_, v___x_384_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v_a_363_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___boxed(lean_object* v_x_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1(v_x_387_, v_a_388_, v_a_389_);
lean_dec_ref(v_a_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt(lean_object* v_x_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
lean_inc(v_x_391_);
v___x_395_ = l_Lean_Syntax_isOfKind(v_x_391_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec(v_x_391_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v_a_393_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = l_Lean_Syntax_getArg(v_x_391_, v___x_398_);
lean_dec(v_x_391_);
v___x_400_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_399_);
v___x_401_ = l_Lean_Syntax_matchesNull(v___x_399_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v_a_393_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = l_Lean_Syntax_getArg(v___x_399_, v___x_404_);
v___x_406_ = l_Lean_Syntax_getArg(v___x_399_, v___x_398_);
lean_dec(v___x_399_);
v___x_407_ = 0;
v___x_408_ = l_Lean_SourceInfo_fromRef(v_a_392_, v___x_407_);
v___x_409_ = ((lean_object*)(l_BitVec_term_____x23_x27_____00__closed__1));
v___x_410_ = ((lean_object*)(l_BitVec_term_____x23_x27_____00__closed__2));
lean_inc(v___x_408_);
v___x_411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_408_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = l_Lean_Syntax_node3(v___x_408_, v___x_409_, v___x_405_, v___x_411_, v___x_406_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_a_393_);
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt___boxed(lean_object* v_x_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_BitVec_unexpandBitVecOfNatLt(v_x_414_, v_a_415_, v_a_416_);
lean_dec(v_a_415_);
return v_res_417_;
}
}
static lean_object* _init_l_BitVec_toHex___boxed__const__1(void){
_start:
{
uint32_t v___x_418_; lean_object* v___x_419_; 
v___x_418_ = 48;
v___x_419_ = lean_box_uint32(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_BitVec_toHex(lean_object* v_n_420_, lean_object* v_x_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v_s_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_t_433_; lean_object* v___x_434_; 
v___x_422_ = lean_unsigned_to_nat(16u);
v___x_423_ = l_Nat_toDigits(v___x_422_, v_x_421_);
v_s_424_ = lean_string_mk(v___x_423_);
v___x_425_ = lean_unsigned_to_nat(3u);
v___x_426_ = lean_nat_add(v_n_420_, v___x_425_);
v___x_427_ = lean_unsigned_to_nat(2u);
v___x_428_ = lean_nat_shiftr(v___x_426_, v___x_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_string_length(v_s_424_);
v___x_430_ = lean_nat_sub(v___x_428_, v___x_429_);
lean_dec(v___x_429_);
lean_dec(v___x_428_);
v___x_431_ = l_BitVec_toHex___boxed__const__1;
v___x_432_ = l_List_replicateTR___redArg(v___x_430_, v___x_431_);
v_t_433_ = lean_string_mk(v___x_432_);
v___x_434_ = lean_string_append(v_t_433_, v_s_424_);
lean_dec_ref(v_s_424_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_BitVec_toHex___boxed(lean_object* v_n_435_, lean_object* v_x_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_BitVec_toHex(v_n_435_, v_x_436_);
lean_dec(v_n_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_BitVec_repr(lean_object* v_n_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_445_ = ((lean_object*)(l_BitVec_repr___closed__1));
v___x_446_ = l_BitVec_toHex(v_n_443_, v_a_444_);
v___x_447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
v___x_448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_445_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = ((lean_object*)(l_BitVec_repr___closed__2));
v___x_450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = l_Nat_reprFast(v_n_443_);
v___x_452_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_450_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr___lam__0(lean_object* v_n_454_, lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_BitVec_repr(v_n_454_, v_a_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr___lam__0___boxed(lean_object* v_n_458_, lean_object* v_a_459_, lean_object* v_x_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_BitVec_instRepr___lam__0(v_n_458_, v_a_459_, v_x_460_);
lean_dec(v_x_460_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr(lean_object* v_n_462_){
_start:
{
lean_object* v___f_463_; 
v___f_463_ = lean_alloc_closure((void*)(l_BitVec_instRepr___lam__0___boxed), 3, 1);
lean_closure_set(v___f_463_, 0, v_n_462_);
return v___f_463_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instToString___lam__0(lean_object* v_n_464_, lean_object* v_a_465_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_466_ = l_BitVec_repr(v_n_464_, v_a_465_);
v___x_467_ = l_Std_Format_defWidth;
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = l_Std_Format_pretty(v___x_466_, v___x_467_, v___x_468_, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instToString(lean_object* v_n_470_){
_start:
{
lean_object* v___f_471_; 
v___f_471_ = lean_alloc_closure((void*)(l_BitVec_instToString___lam__0), 2, 1);
lean_closure_set(v___f_471_, 0, v_n_470_);
return v___f_471_;
}
}
LEAN_EXPORT lean_object* l_BitVec_neg(lean_object* v_n_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = lean_unsigned_to_nat(2u);
v___x_475_ = lean_nat_pow(v___x_474_, v_n_472_);
v___x_476_ = lean_nat_sub(v___x_475_, v_x_473_);
lean_dec(v___x_475_);
v___x_477_ = l_BitVec_ofNat(v_n_472_, v___x_476_);
lean_dec(v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_BitVec_neg___boxed(lean_object* v_n_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_BitVec_neg(v_n_478_, v_x_479_);
lean_dec(v_x_479_);
lean_dec(v_n_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instNeg(lean_object* v_n_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = lean_alloc_closure((void*)(l_BitVec_neg___boxed), 2, 1);
lean_closure_set(v___x_482_, 0, v_n_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_BitVec_abs(lean_object* v_n_483_, lean_object* v_x_484_){
_start:
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_nat_dec_lt(v___x_485_, v_n_483_);
if (v___x_486_ == 0)
{
lean_inc(v_x_484_);
return v_x_484_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_sub(v_n_483_, v___x_487_);
v___x_489_ = l_Nat_testBit(v_x_484_, v___x_488_);
lean_dec(v___x_488_);
if (v___x_489_ == 0)
{
lean_inc(v_x_484_);
return v_x_484_;
}
else
{
lean_object* v___x_490_; 
v___x_490_ = l_BitVec_neg(v_n_483_, v_x_484_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_abs___boxed(lean_object* v_n_491_, lean_object* v_x_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_BitVec_abs(v_n_491_, v_x_492_);
lean_dec(v_x_492_);
lean_dec(v_n_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mul(lean_object* v_n_494_, lean_object* v_x_495_, lean_object* v_y_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_nat_mul(v_x_495_, v_y_496_);
v___x_498_ = l_BitVec_ofNat(v_n_494_, v___x_497_);
lean_dec(v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mul___boxed(lean_object* v_n_499_, lean_object* v_x_500_, lean_object* v_y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_BitVec_mul(v_n_499_, v_x_500_, v_y_501_);
lean_dec(v_y_501_);
lean_dec(v_x_500_);
lean_dec(v_n_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMul(lean_object* v_n_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lean_alloc_closure((void*)(l_BitVec_mul___boxed), 3, 1);
lean_closure_set(v___x_504_, 0, v_n_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_BitVec_pow(lean_object* v_n_505_, lean_object* v_x_506_, lean_object* v_y_507_){
_start:
{
lean_object* v_zero_508_; uint8_t v_isZero_509_; 
v_zero_508_ = lean_unsigned_to_nat(0u);
v_isZero_509_ = lean_nat_dec_eq(v_y_507_, v_zero_508_);
if (v_isZero_509_ == 1)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = l_BitVec_ofNat(v_n_505_, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v_one_512_; lean_object* v_n_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_one_512_ = lean_unsigned_to_nat(1u);
v_n_513_ = lean_nat_sub(v_y_507_, v_one_512_);
v___x_514_ = l_BitVec_pow(v_n_505_, v_x_506_, v_n_513_);
lean_dec(v_n_513_);
v___x_515_ = l_BitVec_mul(v_n_505_, v___x_514_, v_x_506_);
lean_dec(v___x_514_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_pow___boxed(lean_object* v_n_516_, lean_object* v_x_517_, lean_object* v_y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_BitVec_pow(v_n_516_, v_x_517_, v_y_518_);
lean_dec(v_y_518_);
lean_dec(v_x_517_);
lean_dec(v_n_516_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat___lam__0(lean_object* v_n_520_, lean_object* v_x_521_, lean_object* v_y_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_BitVec_pow(v_n_520_, v_x_521_, v_y_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat___lam__0___boxed(lean_object* v_n_524_, lean_object* v_x_525_, lean_object* v_y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_BitVec_instPowNat___lam__0(v_n_524_, v_x_525_, v_y_526_);
lean_dec(v_y_526_);
lean_dec(v_x_525_);
lean_dec(v_n_524_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat(lean_object* v_n_528_){
_start:
{
lean_object* v___f_529_; 
v___f_529_ = lean_alloc_closure((void*)(l_BitVec_instPowNat___lam__0___boxed), 3, 1);
lean_closure_set(v___f_529_, 0, v_n_528_);
return v___f_529_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___redArg(lean_object* v_x_530_, lean_object* v_y_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_nat_div(v_x_530_, v_y_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___redArg___boxed(lean_object* v_x_533_, lean_object* v_y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_BitVec_udiv___redArg(v_x_533_, v_y_534_);
lean_dec(v_y_534_);
lean_dec(v_x_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv(lean_object* v_n_536_, lean_object* v_x_537_, lean_object* v_y_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_nat_div(v_x_537_, v_y_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___boxed(lean_object* v_n_540_, lean_object* v_x_541_, lean_object* v_y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_BitVec_udiv(v_n_540_, v_x_541_, v_y_542_);
lean_dec(v_y_542_);
lean_dec(v_x_541_);
lean_dec(v_n_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDiv(lean_object* v_n_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_alloc_closure((void*)(l_BitVec_udiv___boxed), 3, 1);
lean_closure_set(v___x_545_, 0, v_n_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___redArg(lean_object* v_x_546_, lean_object* v_y_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lean_nat_mod(v_x_546_, v_y_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___redArg___boxed(lean_object* v_x_549_, lean_object* v_y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_BitVec_umod___redArg(v_x_549_, v_y_550_);
lean_dec(v_y_550_);
lean_dec(v_x_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod(lean_object* v_n_552_, lean_object* v_x_553_, lean_object* v_y_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = lean_nat_mod(v_x_553_, v_y_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___boxed(lean_object* v_n_556_, lean_object* v_x_557_, lean_object* v_y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_BitVec_umod(v_n_556_, v_x_557_, v_y_558_);
lean_dec(v_y_558_);
lean_dec(v_x_557_);
lean_dec(v_n_556_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMod(lean_object* v_n_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_closure((void*)(l_BitVec_umod___boxed), 3, 1);
lean_closure_set(v___x_561_, 0, v_n_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtUDiv(lean_object* v_n_562_, lean_object* v_x_563_, lean_object* v_y_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = l_BitVec_ofNat(v_n_562_, v___x_565_);
v___x_567_ = lean_nat_dec_eq(v_y_564_, v___x_566_);
lean_dec(v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
v___x_568_ = lean_nat_div(v_x_563_, v_y_564_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = l_BitVec_allOnes(v_n_562_);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtUDiv___boxed(lean_object* v_n_570_, lean_object* v_x_571_, lean_object* v_y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_BitVec_smtUDiv(v_n_570_, v_x_571_, v_y_572_);
lean_dec(v_y_572_);
lean_dec(v_x_571_);
lean_dec(v_n_570_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv(lean_object* v_n_574_, lean_object* v_x_575_, lean_object* v_y_576_){
_start:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_nat_dec_lt(v___x_592_, v_n_574_);
if (v___x_593_ == 0)
{
goto v___jp_577_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = lean_nat_sub(v_n_574_, v___x_594_);
v___x_596_ = l_Nat_testBit(v_x_575_, v___x_595_);
if (v___x_596_ == 0)
{
lean_dec(v___x_595_);
goto v___jp_577_;
}
else
{
if (v___x_593_ == 0)
{
lean_dec(v___x_595_);
goto v___jp_588_;
}
else
{
uint8_t v___x_597_; 
v___x_597_ = l_Nat_testBit(v_y_576_, v___x_595_);
lean_dec(v___x_595_);
if (v___x_597_ == 0)
{
goto v___jp_588_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = l_BitVec_neg(v_n_574_, v_x_575_);
v___x_599_ = l_BitVec_neg(v_n_574_, v_y_576_);
v___x_600_ = lean_nat_div(v___x_598_, v___x_599_);
lean_dec(v___x_599_);
lean_dec(v___x_598_);
return v___x_600_;
}
}
}
}
v___jp_577_:
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = lean_nat_dec_lt(v___x_578_, v_n_574_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_nat_div(v_x_575_, v_y_576_);
return v___x_580_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_nat_sub(v_n_574_, v___x_581_);
v___x_583_ = l_Nat_testBit(v_y_576_, v___x_582_);
lean_dec(v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_nat_div(v_x_575_, v_y_576_);
return v___x_584_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = l_BitVec_neg(v_n_574_, v_y_576_);
v___x_586_ = lean_nat_div(v_x_575_, v___x_585_);
lean_dec(v___x_585_);
v___x_587_ = l_BitVec_neg(v_n_574_, v___x_586_);
lean_dec(v___x_586_);
return v___x_587_;
}
}
}
v___jp_588_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = l_BitVec_neg(v_n_574_, v_x_575_);
v___x_590_ = lean_nat_div(v___x_589_, v_y_576_);
lean_dec(v___x_589_);
v___x_591_ = l_BitVec_neg(v_n_574_, v___x_590_);
lean_dec(v___x_590_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv___boxed(lean_object* v_n_601_, lean_object* v_x_602_, lean_object* v_y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_BitVec_sdiv(v_n_601_, v_x_602_, v_y_603_);
lean_dec(v_y_603_);
lean_dec(v_x_602_);
lean_dec(v_n_601_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv(lean_object* v_n_605_, lean_object* v_x_606_, lean_object* v_y_607_){
_start:
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_nat_dec_lt(v___x_623_, v_n_605_);
if (v___x_624_ == 0)
{
goto v___jp_608_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_sub(v_n_605_, v___x_625_);
v___x_627_ = l_Nat_testBit(v_x_606_, v___x_626_);
if (v___x_627_ == 0)
{
lean_dec(v___x_626_);
goto v___jp_608_;
}
else
{
if (v___x_624_ == 0)
{
lean_dec(v___x_626_);
goto v___jp_619_;
}
else
{
uint8_t v___x_628_; 
v___x_628_ = l_Nat_testBit(v_y_607_, v___x_626_);
lean_dec(v___x_626_);
if (v___x_628_ == 0)
{
goto v___jp_619_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = l_BitVec_neg(v_n_605_, v_x_606_);
v___x_630_ = l_BitVec_neg(v_n_605_, v_y_607_);
v___x_631_ = l_BitVec_smtUDiv(v_n_605_, v___x_629_, v___x_630_);
lean_dec(v___x_630_);
lean_dec(v___x_629_);
return v___x_631_;
}
}
}
}
v___jp_608_:
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = lean_nat_dec_lt(v___x_609_, v_n_605_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; 
v___x_611_ = l_BitVec_smtUDiv(v_n_605_, v_x_606_, v_y_607_);
return v___x_611_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_nat_sub(v_n_605_, v___x_612_);
v___x_614_ = l_Nat_testBit(v_y_607_, v___x_613_);
lean_dec(v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
v___x_615_ = l_BitVec_smtUDiv(v_n_605_, v_x_606_, v_y_607_);
return v___x_615_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = l_BitVec_neg(v_n_605_, v_y_607_);
v___x_617_ = l_BitVec_smtUDiv(v_n_605_, v_x_606_, v___x_616_);
lean_dec(v___x_616_);
v___x_618_ = l_BitVec_neg(v_n_605_, v___x_617_);
lean_dec(v___x_617_);
return v___x_618_;
}
}
}
v___jp_619_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = l_BitVec_neg(v_n_605_, v_x_606_);
v___x_621_ = l_BitVec_smtUDiv(v_n_605_, v___x_620_, v_y_607_);
lean_dec(v___x_620_);
v___x_622_ = l_BitVec_neg(v_n_605_, v___x_621_);
lean_dec(v___x_621_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv___boxed(lean_object* v_n_632_, lean_object* v_x_633_, lean_object* v_y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_BitVec_smtSDiv(v_n_632_, v_x_633_, v_y_634_);
lean_dec(v_y_634_);
lean_dec(v_x_633_);
lean_dec(v_n_632_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_BitVec_srem(lean_object* v_n_636_, lean_object* v_x_637_, lean_object* v_y_638_){
_start:
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_nat_dec_lt(v___x_653_, v_n_636_);
if (v___x_654_ == 0)
{
goto v___jp_639_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_unsigned_to_nat(1u);
v___x_656_ = lean_nat_sub(v_n_636_, v___x_655_);
v___x_657_ = l_Nat_testBit(v_x_637_, v___x_656_);
if (v___x_657_ == 0)
{
lean_dec(v___x_656_);
goto v___jp_639_;
}
else
{
if (v___x_654_ == 0)
{
lean_dec(v___x_656_);
goto v___jp_649_;
}
else
{
uint8_t v___x_658_; 
v___x_658_ = l_Nat_testBit(v_y_638_, v___x_656_);
lean_dec(v___x_656_);
if (v___x_658_ == 0)
{
goto v___jp_649_;
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_659_ = l_BitVec_neg(v_n_636_, v_x_637_);
v___x_660_ = l_BitVec_neg(v_n_636_, v_y_638_);
v___x_661_ = lean_nat_mod(v___x_659_, v___x_660_);
lean_dec(v___x_660_);
lean_dec(v___x_659_);
v___x_662_ = l_BitVec_neg(v_n_636_, v___x_661_);
lean_dec(v___x_661_);
return v___x_662_;
}
}
}
}
v___jp_639_:
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_nat_dec_lt(v___x_640_, v_n_636_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_nat_mod(v_x_637_, v_y_638_);
return v___x_642_;
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_sub(v_n_636_, v___x_643_);
v___x_645_ = l_Nat_testBit(v_y_638_, v___x_644_);
lean_dec(v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
v___x_646_ = lean_nat_mod(v_x_637_, v_y_638_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = l_BitVec_neg(v_n_636_, v_y_638_);
v___x_648_ = lean_nat_mod(v_x_637_, v___x_647_);
lean_dec(v___x_647_);
return v___x_648_;
}
}
}
v___jp_649_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = l_BitVec_neg(v_n_636_, v_x_637_);
v___x_651_ = lean_nat_mod(v___x_650_, v_y_638_);
lean_dec(v___x_650_);
v___x_652_ = l_BitVec_neg(v_n_636_, v___x_651_);
lean_dec(v___x_651_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_srem___boxed(lean_object* v_n_663_, lean_object* v_x_664_, lean_object* v_y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_BitVec_srem(v_n_663_, v_x_664_, v_y_665_);
lean_dec(v_y_665_);
lean_dec(v_x_664_);
lean_dec(v_n_663_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smod(lean_object* v_m_667_, lean_object* v_x_668_, lean_object* v_y_669_){
_start:
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_nat_dec_lt(v___x_688_, v_m_667_);
if (v___x_689_ == 0)
{
goto v___jp_670_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_sub(v_m_667_, v___x_690_);
v___x_692_ = l_Nat_testBit(v_x_668_, v___x_691_);
if (v___x_692_ == 0)
{
lean_dec(v___x_691_);
goto v___jp_670_;
}
else
{
if (v___x_689_ == 0)
{
lean_dec(v___x_691_);
goto v___jp_682_;
}
else
{
uint8_t v___x_693_; 
v___x_693_ = l_Nat_testBit(v_y_669_, v___x_691_);
lean_dec(v___x_691_);
if (v___x_693_ == 0)
{
goto v___jp_682_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_694_ = l_BitVec_neg(v_m_667_, v_x_668_);
v___x_695_ = l_BitVec_neg(v_m_667_, v_y_669_);
v___x_696_ = lean_nat_mod(v___x_694_, v___x_695_);
lean_dec(v___x_695_);
lean_dec(v___x_694_);
v___x_697_ = l_BitVec_neg(v_m_667_, v___x_696_);
lean_dec(v___x_696_);
return v___x_697_;
}
}
}
}
v___jp_670_:
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_nat_dec_lt(v___x_671_, v_m_667_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
v___x_673_ = lean_nat_mod(v_x_668_, v_y_669_);
return v___x_673_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_sub(v_m_667_, v___x_674_);
v___x_676_ = l_Nat_testBit(v_y_669_, v___x_675_);
lean_dec(v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
v___x_677_ = lean_nat_mod(v_x_668_, v_y_669_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v_u_679_; uint8_t v___x_680_; 
v___x_678_ = l_BitVec_neg(v_m_667_, v_y_669_);
v_u_679_ = lean_nat_mod(v_x_668_, v___x_678_);
lean_dec(v___x_678_);
v___x_680_ = lean_nat_dec_eq(v_u_679_, v___x_671_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
v___x_681_ = l_BitVec_add(v_m_667_, v_u_679_, v_y_669_);
lean_dec(v_u_679_);
return v___x_681_;
}
else
{
return v_u_679_;
}
}
}
}
v___jp_682_:
{
lean_object* v___x_683_; lean_object* v_u_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_683_ = l_BitVec_neg(v_m_667_, v_x_668_);
v_u_684_ = lean_nat_mod(v___x_683_, v_y_669_);
lean_dec(v___x_683_);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_nat_dec_eq(v_u_684_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
v___x_687_ = l_BitVec_sub(v_m_667_, v_y_669_, v_u_684_);
lean_dec(v_u_684_);
return v___x_687_;
}
else
{
return v_u_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smod___boxed(lean_object* v_m_698_, lean_object* v_x_699_, lean_object* v_y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_BitVec_smod(v_m_698_, v_x_699_, v_y_700_);
lean_dec(v_y_700_);
lean_dec(v_x_699_);
lean_dec(v_m_698_);
return v_res_701_;
}
}
static lean_object* _init_l_BitVec_ofBool___closed__0(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = l_BitVec_ofNat(v___x_703_, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l_BitVec_ofBool___closed__1(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = l_BitVec_ofNat(v___x_705_, v___x_705_);
return v___x_706_;
}
}
lean_object* l_BitVec_ofBool(uint8_t v_b_707_){
_start:
{
if (v_b_707_ == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_once(&l_BitVec_ofBool___closed__0, &l_BitVec_ofBool___closed__0_once, _init_l_BitVec_ofBool___closed__0);
return v___x_708_;
}
else
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_BitVec_ofBool___closed__1, &l_BitVec_ofBool___closed__1_once, _init_l_BitVec_ofBool___closed__1);
return v___x_709_;
}
}
}
LEAN_EXPORT void l_BitVec_ofBool_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_707_ = stack[0].m_num;
lean_object* v_res_710_;
v_res_710_ = l_BitVec_ofBool(v_b_707_);
stack->m_obj
 = v_res_710_;
}
LEAN_EXPORT lean_object* l_BitVec_ofBool___boxed(lean_object* v_b_711_){
_start:
{
uint8_t v_b_boxed_712_; lean_object* v_res_713_; 
v_b_boxed_712_ = lean_unbox(v_b_711_);
v_res_713_ = l_BitVec_ofBool(v_b_boxed_712_);
return v_res_713_;
}
}
lean_object* l_BitVec_fill(lean_object* v_w_714_, uint8_t v_b_715_){
_start:
{
if (v_b_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = l_BitVec_ofNat(v_w_714_, v___x_716_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = l_BitVec_ofNat(v_w_714_, v___x_718_);
v___x_720_ = l_BitVec_neg(v_w_714_, v___x_719_);
lean_dec(v___x_719_);
return v___x_720_;
}
}
}
LEAN_EXPORT void l_BitVec_fill_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_714_ = stack[0].m_obj;
uint8_t v_b_715_ = stack[1].m_num;
lean_object* v_res_721_;
v_res_721_ = l_BitVec_fill(v_w_714_, v_b_715_);
stack->m_obj
 = v_res_721_;
}
LEAN_EXPORT lean_object* l_BitVec_fill___boxed(lean_object* v_w_722_, lean_object* v_b_723_){
_start:
{
uint8_t v_b_boxed_724_; lean_object* v_res_725_; 
v_b_boxed_724_ = lean_unbox(v_b_723_);
v_res_725_ = l_BitVec_fill(v_w_722_, v_b_boxed_724_);
lean_dec(v_w_722_);
return v_res_725_;
}
}
uint8_t l_BitVec_ult___redArg(lean_object* v_x_726_, lean_object* v_y_727_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = lean_nat_dec_lt(v_x_726_, v_y_727_);
return v___x_728_;
}
}
LEAN_EXPORT void l_BitVec_ult___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_726_ = stack[0].m_obj;
lean_object* v_y_727_ = stack[1].m_obj;
uint8_t v_res_729_;
v_res_729_ = l_BitVec_ult___redArg(v_x_726_, v_y_727_);
stack->m_num = v_res_729_;
}
LEAN_EXPORT lean_object* l_BitVec_ult___redArg___boxed(lean_object* v_x_730_, lean_object* v_y_731_){
_start:
{
uint8_t v_res_732_; lean_object* v_r_733_; 
v_res_732_ = l_BitVec_ult___redArg(v_x_730_, v_y_731_);
lean_dec(v_y_731_);
lean_dec(v_x_730_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
uint8_t l_BitVec_ult(lean_object* v_n_734_, lean_object* v_x_735_, lean_object* v_y_736_){
_start:
{
uint8_t v___x_737_; 
v___x_737_ = lean_nat_dec_lt(v_x_735_, v_y_736_);
return v___x_737_;
}
}
LEAN_EXPORT void l_BitVec_ult_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_734_ = stack[0].m_obj;
lean_object* v_x_735_ = stack[1].m_obj;
lean_object* v_y_736_ = stack[2].m_obj;
uint8_t v_res_738_;
v_res_738_ = l_BitVec_ult(v_n_734_, v_x_735_, v_y_736_);
stack->m_num = v_res_738_;
}
LEAN_EXPORT lean_object* l_BitVec_ult___boxed(lean_object* v_n_739_, lean_object* v_x_740_, lean_object* v_y_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l_BitVec_ult(v_n_739_, v_x_740_, v_y_741_);
lean_dec(v_y_741_);
lean_dec(v_x_740_);
lean_dec(v_n_739_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
uint8_t l_BitVec_ule___redArg(lean_object* v_x_744_, lean_object* v_y_745_){
_start:
{
uint8_t v___x_746_; 
v___x_746_ = lean_nat_dec_le(v_x_744_, v_y_745_);
return v___x_746_;
}
}
LEAN_EXPORT void l_BitVec_ule___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_744_ = stack[0].m_obj;
lean_object* v_y_745_ = stack[1].m_obj;
uint8_t v_res_747_;
v_res_747_ = l_BitVec_ule___redArg(v_x_744_, v_y_745_);
stack->m_num = v_res_747_;
}
LEAN_EXPORT lean_object* l_BitVec_ule___redArg___boxed(lean_object* v_x_748_, lean_object* v_y_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_BitVec_ule___redArg(v_x_748_, v_y_749_);
lean_dec(v_y_749_);
lean_dec(v_x_748_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
uint8_t l_BitVec_ule(lean_object* v_n_752_, lean_object* v_x_753_, lean_object* v_y_754_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = lean_nat_dec_le(v_x_753_, v_y_754_);
return v___x_755_;
}
}
LEAN_EXPORT void l_BitVec_ule_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_752_ = stack[0].m_obj;
lean_object* v_x_753_ = stack[1].m_obj;
lean_object* v_y_754_ = stack[2].m_obj;
uint8_t v_res_756_;
v_res_756_ = l_BitVec_ule(v_n_752_, v_x_753_, v_y_754_);
stack->m_num = v_res_756_;
}
LEAN_EXPORT lean_object* l_BitVec_ule___boxed(lean_object* v_n_757_, lean_object* v_x_758_, lean_object* v_y_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_BitVec_ule(v_n_757_, v_x_758_, v_y_759_);
lean_dec(v_y_759_);
lean_dec(v_x_758_);
lean_dec(v_n_757_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
uint8_t l_BitVec_slt(lean_object* v_n_762_, lean_object* v_x_763_, lean_object* v_y_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_765_ = l_BitVec_toInt(v_n_762_, v_x_763_);
v___x_766_ = l_BitVec_toInt(v_n_762_, v_y_764_);
v___x_767_ = lean_int_dec_lt(v___x_765_, v___x_766_);
lean_dec(v___x_766_);
lean_dec(v___x_765_);
return v___x_767_;
}
}
LEAN_EXPORT void l_BitVec_slt_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_762_ = stack[0].m_obj;
lean_object* v_x_763_ = stack[1].m_obj;
lean_object* v_y_764_ = stack[2].m_obj;
uint8_t v_res_768_;
v_res_768_ = l_BitVec_slt(v_n_762_, v_x_763_, v_y_764_);
stack->m_num = v_res_768_;
}
LEAN_EXPORT lean_object* l_BitVec_slt___boxed(lean_object* v_n_769_, lean_object* v_x_770_, lean_object* v_y_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_BitVec_slt(v_n_769_, v_x_770_, v_y_771_);
lean_dec(v_n_769_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
uint8_t l_BitVec_sle(lean_object* v_n_774_, lean_object* v_x_775_, lean_object* v_y_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_777_ = l_BitVec_toInt(v_n_774_, v_x_775_);
v___x_778_ = l_BitVec_toInt(v_n_774_, v_y_776_);
v___x_779_ = lean_int_dec_le(v___x_777_, v___x_778_);
lean_dec(v___x_778_);
lean_dec(v___x_777_);
return v___x_779_;
}
}
LEAN_EXPORT void l_BitVec_sle_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_774_ = stack[0].m_obj;
lean_object* v_x_775_ = stack[1].m_obj;
lean_object* v_y_776_ = stack[2].m_obj;
uint8_t v_res_780_;
v_res_780_ = l_BitVec_sle(v_n_774_, v_x_775_, v_y_776_);
stack->m_num = v_res_780_;
}
LEAN_EXPORT lean_object* l_BitVec_sle___boxed(lean_object* v_n_781_, lean_object* v_x_782_, lean_object* v_y_783_){
_start:
{
uint8_t v_res_784_; lean_object* v_r_785_; 
v_res_784_ = l_BitVec_sle(v_n_781_, v_x_782_, v_y_783_);
lean_dec(v_n_781_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___redArg(lean_object* v_x_786_){
_start:
{
lean_inc(v_x_786_);
return v_x_786_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___redArg___boxed(lean_object* v_x_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_BitVec_cast___redArg(v_x_787_);
lean_dec(v_x_787_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast(lean_object* v_n_789_, lean_object* v_m_790_, lean_object* v_eq_791_, lean_object* v_x_792_){
_start:
{
lean_inc(v_x_792_);
return v_x_792_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___boxed(lean_object* v_n_793_, lean_object* v_m_794_, lean_object* v_eq_795_, lean_object* v_x_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_BitVec_cast(v_n_793_, v_m_794_, v_eq_795_, v_x_796_);
lean_dec(v_x_796_);
lean_dec(v_m_794_);
lean_dec(v_n_793_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___redArg(lean_object* v_start_798_, lean_object* v_len_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_nat_shiftr(v_x_800_, v_start_798_);
v___x_802_ = l_BitVec_ofNat(v_len_799_, v___x_801_);
lean_dec(v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___redArg___boxed(lean_object* v_start_803_, lean_object* v_len_804_, lean_object* v_x_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_BitVec_extractLsb_x27___redArg(v_start_803_, v_len_804_, v_x_805_);
lean_dec(v_x_805_);
lean_dec(v_len_804_);
lean_dec(v_start_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27(lean_object* v_n_807_, lean_object* v_start_808_, lean_object* v_len_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_BitVec_extractLsb_x27___redArg(v_start_808_, v_len_809_, v_x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___boxed(lean_object* v_n_812_, lean_object* v_start_813_, lean_object* v_len_814_, lean_object* v_x_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_BitVec_extractLsb_x27(v_n_812_, v_start_813_, v_len_814_, v_x_815_);
lean_dec(v_x_815_);
lean_dec(v_len_814_);
lean_dec(v_start_813_);
lean_dec(v_n_812_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___redArg(lean_object* v_hi_817_, lean_object* v_lo_818_, lean_object* v_x_819_){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_820_ = lean_nat_sub(v_hi_817_, v_lo_818_);
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_nat_add(v___x_820_, v___x_821_);
lean_dec(v___x_820_);
v___x_823_ = l_BitVec_extractLsb_x27___redArg(v_lo_818_, v___x_822_, v_x_819_);
lean_dec(v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___redArg___boxed(lean_object* v_hi_824_, lean_object* v_lo_825_, lean_object* v_x_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_BitVec_extractLsb___redArg(v_hi_824_, v_lo_825_, v_x_826_);
lean_dec(v_x_826_);
lean_dec(v_lo_825_);
lean_dec(v_hi_824_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb(lean_object* v_n_828_, lean_object* v_hi_829_, lean_object* v_lo_830_, lean_object* v_x_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_BitVec_extractLsb___redArg(v_hi_829_, v_lo_830_, v_x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___boxed(lean_object* v_n_833_, lean_object* v_hi_834_, lean_object* v_lo_835_, lean_object* v_x_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_BitVec_extractLsb(v_n_833_, v_hi_834_, v_lo_835_, v_x_836_);
lean_dec(v_x_836_);
lean_dec(v_lo_835_);
lean_dec(v_hi_834_);
lean_dec(v_n_833_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___redArg(lean_object* v_x_838_){
_start:
{
lean_inc(v_x_838_);
return v_x_838_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___redArg___boxed(lean_object* v_x_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_BitVec_setWidth_x27___redArg(v_x_839_);
lean_dec(v_x_839_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27(lean_object* v_n_841_, lean_object* v_w_842_, lean_object* v_le_843_, lean_object* v_x_844_){
_start:
{
lean_inc(v_x_844_);
return v_x_844_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___boxed(lean_object* v_n_845_, lean_object* v_w_846_, lean_object* v_le_847_, lean_object* v_x_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_BitVec_setWidth_x27(v_n_845_, v_w_846_, v_le_847_, v_x_848_);
lean_dec(v_x_848_);
lean_dec(v_w_846_);
lean_dec(v_n_845_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___redArg(lean_object* v_msbs_850_, lean_object* v_m_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = lean_nat_shiftl(v_msbs_850_, v_m_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___redArg___boxed(lean_object* v_msbs_853_, lean_object* v_m_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_BitVec_shiftLeftZeroExtend___redArg(v_msbs_853_, v_m_854_);
lean_dec(v_m_854_);
lean_dec(v_msbs_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend(lean_object* v_w_856_, lean_object* v_msbs_857_, lean_object* v_m_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = lean_nat_shiftl(v_msbs_857_, v_m_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___boxed(lean_object* v_w_860_, lean_object* v_msbs_861_, lean_object* v_m_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_BitVec_shiftLeftZeroExtend(v_w_860_, v_msbs_861_, v_m_862_);
lean_dec(v_m_862_);
lean_dec(v_msbs_861_);
lean_dec(v_w_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth(lean_object* v_w_864_, lean_object* v_v_865_, lean_object* v_x_866_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_nat_dec_le(v_w_864_, v_v_865_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
v___x_868_ = l_BitVec_ofNat(v_v_865_, v_x_866_);
return v___x_868_;
}
else
{
lean_inc(v_x_866_);
return v_x_866_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth___boxed(lean_object* v_w_869_, lean_object* v_v_870_, lean_object* v_x_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_BitVec_setWidth(v_w_869_, v_v_870_, v_x_871_);
lean_dec(v_x_871_);
lean_dec(v_v_870_);
lean_dec(v_w_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zeroExtend(lean_object* v_w_873_, lean_object* v_v_874_, lean_object* v_x_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_BitVec_setWidth(v_w_873_, v_v_874_, v_x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zeroExtend___boxed(lean_object* v_w_877_, lean_object* v_v_878_, lean_object* v_x_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_BitVec_zeroExtend(v_w_877_, v_v_878_, v_x_879_);
lean_dec(v_x_879_);
lean_dec(v_v_878_);
lean_dec(v_w_877_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_BitVec_truncate(lean_object* v_w_881_, lean_object* v_v_882_, lean_object* v_x_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_BitVec_setWidth(v_w_881_, v_v_882_, v_x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_BitVec_truncate___boxed(lean_object* v_w_885_, lean_object* v_v_886_, lean_object* v_x_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_BitVec_truncate(v_w_885_, v_v_886_, v_x_887_);
lean_dec(v_x_887_);
lean_dec(v_v_886_);
lean_dec(v_w_885_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_BitVec_signExtend(lean_object* v_w_889_, lean_object* v_v_890_, lean_object* v_x_891_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = l_BitVec_toInt(v_w_889_, v_x_891_);
v___x_893_ = l_BitVec_ofInt(v_v_890_, v___x_892_);
lean_dec(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_BitVec_signExtend___boxed(lean_object* v_w_894_, lean_object* v_v_895_, lean_object* v_x_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_BitVec_signExtend(v_w_894_, v_v_895_, v_x_896_);
lean_dec(v_v_895_);
lean_dec(v_w_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___redArg(lean_object* v_x_898_, lean_object* v_y_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_nat_land(v_x_898_, v_y_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___redArg___boxed(lean_object* v_x_901_, lean_object* v_y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_BitVec_and___redArg(v_x_901_, v_y_902_);
lean_dec(v_y_902_);
lean_dec(v_x_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and(lean_object* v_n_904_, lean_object* v_x_905_, lean_object* v_y_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = lean_nat_land(v_x_905_, v_y_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___boxed(lean_object* v_n_908_, lean_object* v_x_909_, lean_object* v_y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_BitVec_and(v_n_908_, v_x_909_, v_y_910_);
lean_dec(v_y_910_);
lean_dec(v_x_909_);
lean_dec(v_n_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instAndOp(lean_object* v_w_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = lean_alloc_closure((void*)(l_BitVec_and___boxed), 3, 1);
lean_closure_set(v___x_913_, 0, v_w_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___redArg(lean_object* v_x_914_, lean_object* v_y_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_nat_lor(v_x_914_, v_y_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___redArg___boxed(lean_object* v_x_917_, lean_object* v_y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_BitVec_or___redArg(v_x_917_, v_y_918_);
lean_dec(v_y_918_);
lean_dec(v_x_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or(lean_object* v_n_920_, lean_object* v_x_921_, lean_object* v_y_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = lean_nat_lor(v_x_921_, v_y_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___boxed(lean_object* v_n_924_, lean_object* v_x_925_, lean_object* v_y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_BitVec_or(v_n_924_, v_x_925_, v_y_926_);
lean_dec(v_y_926_);
lean_dec(v_x_925_);
lean_dec(v_n_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instOrOp(lean_object* v_w_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_closure((void*)(l_BitVec_or___boxed), 3, 1);
lean_closure_set(v___x_929_, 0, v_w_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___redArg(lean_object* v_x_930_, lean_object* v_y_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = lean_nat_lxor(v_x_930_, v_y_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___redArg___boxed(lean_object* v_x_933_, lean_object* v_y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_BitVec_xor___redArg(v_x_933_, v_y_934_);
lean_dec(v_y_934_);
lean_dec(v_x_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor(lean_object* v_n_936_, lean_object* v_x_937_, lean_object* v_y_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = lean_nat_lxor(v_x_937_, v_y_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___boxed(lean_object* v_n_940_, lean_object* v_x_941_, lean_object* v_y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_BitVec_xor(v_n_940_, v_x_941_, v_y_942_);
lean_dec(v_y_942_);
lean_dec(v_x_941_);
lean_dec(v_n_940_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instXorOp(lean_object* v_w_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_closure((void*)(l_BitVec_xor___boxed), 3, 1);
lean_closure_set(v___x_945_, 0, v_w_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_BitVec_not(lean_object* v_n_946_, lean_object* v_x_947_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = l_BitVec_allOnes(v_n_946_);
v___x_949_ = lean_nat_lxor(v___x_948_, v_x_947_);
lean_dec(v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_BitVec_not___boxed(lean_object* v_n_950_, lean_object* v_x_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_BitVec_not(v_n_950_, v_x_951_);
lean_dec(v_x_951_);
lean_dec(v_n_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instComplement(lean_object* v_w_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_closure((void*)(l_BitVec_not___boxed), 2, 1);
lean_closure_set(v___x_954_, 0, v_w_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeft(lean_object* v_n_955_, lean_object* v_x_956_, lean_object* v_s_957_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_nat_shiftl(v_x_956_, v_s_957_);
v___x_959_ = l_BitVec_ofNat(v_n_955_, v___x_958_);
lean_dec(v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeft___boxed(lean_object* v_n_960_, lean_object* v_x_961_, lean_object* v_s_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_BitVec_shiftLeft(v_n_960_, v_x_961_, v_s_962_);
lean_dec(v_s_962_);
lean_dec(v_x_961_);
lean_dec(v_n_960_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeftNat(lean_object* v_w_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_closure((void*)(l_BitVec_shiftLeft___boxed), 3, 1);
lean_closure_set(v___x_965_, 0, v_w_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___redArg(lean_object* v_x_966_, lean_object* v_s_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = lean_nat_shiftr(v_x_966_, v_s_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___redArg___boxed(lean_object* v_x_969_, lean_object* v_s_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_BitVec_ushiftRight___redArg(v_x_969_, v_s_970_);
lean_dec(v_s_970_);
lean_dec(v_x_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight(lean_object* v_n_972_, lean_object* v_x_973_, lean_object* v_s_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = lean_nat_shiftr(v_x_973_, v_s_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___boxed(lean_object* v_n_976_, lean_object* v_x_977_, lean_object* v_s_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_BitVec_ushiftRight(v_n_976_, v_x_977_, v_s_978_);
lean_dec(v_s_978_);
lean_dec(v_x_977_);
lean_dec(v_n_976_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRightNat(lean_object* v_w_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = lean_alloc_closure((void*)(l_BitVec_ushiftRight___boxed), 3, 1);
lean_closure_set(v___x_981_, 0, v_w_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight(lean_object* v_n_982_, lean_object* v_x_983_, lean_object* v_s_984_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_985_ = l_BitVec_toInt(v_n_982_, v_x_983_);
v___x_986_ = l_Int_shiftRight(v___x_985_, v_s_984_);
lean_dec(v___x_985_);
v___x_987_ = l_BitVec_ofInt(v_n_982_, v___x_986_);
lean_dec(v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight___boxed(lean_object* v_n_988_, lean_object* v_x_989_, lean_object* v_s_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_BitVec_sshiftRight(v_n_988_, v_x_989_, v_s_990_);
lean_dec(v_s_990_);
lean_dec(v_n_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg___lam__0(lean_object* v_m_992_, lean_object* v_x_993_, lean_object* v_y_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_BitVec_shiftLeft(v_m_992_, v_x_993_, v_y_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg___lam__0___boxed(lean_object* v_m_996_, lean_object* v_x_997_, lean_object* v_y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_BitVec_instHShiftLeft___redArg___lam__0(v_m_996_, v_x_997_, v_y_998_);
lean_dec(v_y_998_);
lean_dec(v_x_997_);
lean_dec(v_m_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg(lean_object* v_m_1000_){
_start:
{
lean_object* v___f_1001_; 
v___f_1001_ = lean_alloc_closure((void*)(l_BitVec_instHShiftLeft___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1001_, 0, v_m_1000_);
return v___f_1001_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft(lean_object* v_m_1002_, lean_object* v_n_1003_){
_start:
{
lean_object* v___f_1004_; 
v___f_1004_ = lean_alloc_closure((void*)(l_BitVec_instHShiftLeft___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1004_, 0, v_m_1002_);
return v___f_1004_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___boxed(lean_object* v_m_1005_, lean_object* v_n_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_BitVec_instHShiftLeft(v_m_1005_, v_n_1006_);
lean_dec(v_n_1006_);
return v_res_1007_;
}
}
lean_object* l_BitVec_instHShiftRight___redArg(){
_start:
{
lean_object* v___f_1010_; 
v___f_1010_ = ((lean_object*)(l_BitVec_instHShiftRight___redArg___closed__0));
return v___f_1010_;
}
}
LEAN_EXPORT void l_BitVec_instHShiftRight___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1011_;
v_res_1011_ = l_BitVec_instHShiftRight___redArg();
stack->m_obj
 = v_res_1011_;
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___redArg___boxed(lean_object* v___dummy_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_BitVec_instHShiftRight___redArg();
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight(lean_object* v_m_1014_, lean_object* v_n_1015_){
_start:
{
lean_object* v___f_1016_; 
v___f_1016_ = ((lean_object*)(l_BitVec_instHShiftRight___redArg___closed__0));
return v___f_1016_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___boxed(lean_object* v_m_1017_, lean_object* v_n_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_BitVec_instHShiftRight(v_m_1017_, v_n_1018_);
lean_dec(v_n_1018_);
lean_dec(v_m_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg(lean_object* v_n_1020_, lean_object* v_a_1021_, lean_object* v_s_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_BitVec_sshiftRight(v_n_1020_, v_a_1021_, v_s_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg___boxed(lean_object* v_n_1024_, lean_object* v_a_1025_, lean_object* v_s_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_BitVec_sshiftRight_x27___redArg(v_n_1024_, v_a_1025_, v_s_1026_);
lean_dec(v_s_1026_);
lean_dec(v_n_1024_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27(lean_object* v_n_1028_, lean_object* v_m_1029_, lean_object* v_a_1030_, lean_object* v_s_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_BitVec_sshiftRight(v_n_1028_, v_a_1030_, v_s_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___boxed(lean_object* v_n_1033_, lean_object* v_m_1034_, lean_object* v_a_1035_, lean_object* v_s_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_BitVec_sshiftRight_x27(v_n_1033_, v_m_1034_, v_a_1035_, v_s_1036_);
lean_dec(v_s_1036_);
lean_dec(v_m_1034_);
lean_dec(v_n_1033_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux(lean_object* v_w_1038_, lean_object* v_x_1039_, lean_object* v_n_1040_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1041_ = l_BitVec_shiftLeft(v_w_1038_, v_x_1039_, v_n_1040_);
v___x_1042_ = lean_nat_sub(v_w_1038_, v_n_1040_);
v___x_1043_ = lean_nat_shiftr(v_x_1039_, v___x_1042_);
lean_dec(v___x_1042_);
v___x_1044_ = lean_nat_lor(v___x_1041_, v___x_1043_);
lean_dec(v___x_1043_);
lean_dec(v___x_1041_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux___boxed(lean_object* v_w_1045_, lean_object* v_x_1046_, lean_object* v_n_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_BitVec_rotateLeftAux(v_w_1045_, v_x_1046_, v_n_1047_);
lean_dec(v_n_1047_);
lean_dec(v_x_1046_);
lean_dec(v_w_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft(lean_object* v_w_1049_, lean_object* v_x_1050_, lean_object* v_n_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_nat_mod(v_n_1051_, v_w_1049_);
v___x_1053_ = l_BitVec_rotateLeftAux(v_w_1049_, v_x_1050_, v___x_1052_);
lean_dec(v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft___boxed(lean_object* v_w_1054_, lean_object* v_x_1055_, lean_object* v_n_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_BitVec_rotateLeft(v_w_1054_, v_x_1055_, v_n_1056_);
lean_dec(v_n_1056_);
lean_dec(v_x_1055_);
lean_dec(v_w_1054_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux(lean_object* v_w_1058_, lean_object* v_x_1059_, lean_object* v_n_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = lean_nat_shiftr(v_x_1059_, v_n_1060_);
v___x_1062_ = lean_nat_sub(v_w_1058_, v_n_1060_);
v___x_1063_ = l_BitVec_shiftLeft(v_w_1058_, v_x_1059_, v___x_1062_);
lean_dec(v___x_1062_);
v___x_1064_ = lean_nat_lor(v___x_1061_, v___x_1063_);
lean_dec(v___x_1063_);
lean_dec(v___x_1061_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux___boxed(lean_object* v_w_1065_, lean_object* v_x_1066_, lean_object* v_n_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_BitVec_rotateRightAux(v_w_1065_, v_x_1066_, v_n_1067_);
lean_dec(v_n_1067_);
lean_dec(v_x_1066_);
lean_dec(v_w_1065_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight(lean_object* v_w_1069_, lean_object* v_x_1070_, lean_object* v_n_1071_){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_nat_mod(v_n_1071_, v_w_1069_);
v___x_1073_ = l_BitVec_rotateRightAux(v_w_1069_, v_x_1070_, v___x_1072_);
lean_dec(v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight___boxed(lean_object* v_w_1074_, lean_object* v_x_1075_, lean_object* v_n_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_BitVec_rotateRight(v_w_1074_, v_x_1075_, v_n_1076_);
lean_dec(v_n_1076_);
lean_dec(v_x_1075_);
lean_dec(v_w_1074_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___redArg(lean_object* v_m_1078_, lean_object* v_msbs_1079_, lean_object* v_lsbs_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_nat_shiftl(v_msbs_1079_, v_m_1078_);
v___x_1082_ = lean_nat_lor(v___x_1081_, v_lsbs_1080_);
lean_dec(v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___redArg___boxed(lean_object* v_m_1083_, lean_object* v_msbs_1084_, lean_object* v_lsbs_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_BitVec_append___redArg(v_m_1083_, v_msbs_1084_, v_lsbs_1085_);
lean_dec(v_lsbs_1085_);
lean_dec(v_msbs_1084_);
lean_dec(v_m_1083_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append(lean_object* v_n_1087_, lean_object* v_m_1088_, lean_object* v_msbs_1089_, lean_object* v_lsbs_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_BitVec_append___redArg(v_m_1088_, v_msbs_1089_, v_lsbs_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___boxed(lean_object* v_n_1092_, lean_object* v_m_1093_, lean_object* v_msbs_1094_, lean_object* v_lsbs_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_BitVec_append(v_n_1092_, v_m_1093_, v_msbs_1094_, v_lsbs_1095_);
lean_dec(v_lsbs_1095_);
lean_dec(v_msbs_1094_);
lean_dec(v_m_1093_);
lean_dec(v_n_1092_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat(lean_object* v_w_1097_, lean_object* v_v_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_alloc_closure((void*)(l_BitVec_append___boxed), 4, 2);
lean_closure_set(v___x_1099_, 0, v_w_1097_);
lean_closure_set(v___x_1099_, 1, v_v_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate(lean_object* v_w_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
lean_object* v_zero_1103_; uint8_t v_isZero_1104_; 
v_zero_1103_ = lean_unsigned_to_nat(0u);
v_isZero_1104_ = lean_nat_dec_eq(v_x_1101_, v_zero_1103_);
if (v_isZero_1104_ == 1)
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1105_;
}
else
{
lean_object* v_one_1106_; lean_object* v_n_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_one_1106_ = lean_unsigned_to_nat(1u);
v_n_1107_ = lean_nat_sub(v_x_1101_, v_one_1106_);
v___x_1108_ = lean_nat_mul(v_w_1100_, v_n_1107_);
v___x_1109_ = l_BitVec_replicate(v_w_1100_, v_n_1107_, v_x_1102_);
lean_dec(v_n_1107_);
v___x_1110_ = l_BitVec_append___redArg(v___x_1108_, v_x_1102_, v___x_1109_);
lean_dec(v___x_1109_);
lean_dec(v___x_1108_);
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate___boxed(lean_object* v_w_1111_, lean_object* v_x_1112_, lean_object* v_x_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_BitVec_replicate(v_w_1111_, v_x_1112_, v_x_1113_);
lean_dec(v_x_1113_);
lean_dec(v_x_1112_);
lean_dec(v_w_1111_);
return v_res_1114_;
}
}
lean_object* l_BitVec_concat___redArg(lean_object* v_msbs_1115_, uint8_t v_lsb_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = l_BitVec_ofBool(v_lsb_1116_);
v___x_1119_ = l_BitVec_append___redArg(v___x_1117_, v_msbs_1115_, v___x_1118_);
lean_dec(v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT void l_BitVec_concat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msbs_1115_ = stack[0].m_obj;
uint8_t v_lsb_1116_ = stack[1].m_num;
lean_object* v_res_1120_;
v_res_1120_ = l_BitVec_concat___redArg(v_msbs_1115_, v_lsb_1116_);
stack->m_obj
 = v_res_1120_;
}
LEAN_EXPORT lean_object* l_BitVec_concat___redArg___boxed(lean_object* v_msbs_1121_, lean_object* v_lsb_1122_){
_start:
{
uint8_t v_lsb_boxed_1123_; lean_object* v_res_1124_; 
v_lsb_boxed_1123_ = lean_unbox(v_lsb_1122_);
v_res_1124_ = l_BitVec_concat___redArg(v_msbs_1121_, v_lsb_boxed_1123_);
lean_dec(v_msbs_1121_);
return v_res_1124_;
}
}
lean_object* l_BitVec_concat(lean_object* v_n_1125_, lean_object* v_msbs_1126_, uint8_t v_lsb_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_BitVec_concat___redArg(v_msbs_1126_, v_lsb_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT void l_BitVec_concat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1125_ = stack[0].m_obj;
lean_object* v_msbs_1126_ = stack[1].m_obj;
uint8_t v_lsb_1127_ = stack[2].m_num;
lean_object* v_res_1129_;
v_res_1129_ = l_BitVec_concat(v_n_1125_, v_msbs_1126_, v_lsb_1127_);
stack->m_obj
 = v_res_1129_;
}
LEAN_EXPORT lean_object* l_BitVec_concat___boxed(lean_object* v_n_1130_, lean_object* v_msbs_1131_, lean_object* v_lsb_1132_){
_start:
{
uint8_t v_lsb_boxed_1133_; lean_object* v_res_1134_; 
v_lsb_boxed_1133_ = lean_unbox(v_lsb_1132_);
v_res_1134_ = l_BitVec_concat(v_n_1130_, v_msbs_1131_, v_lsb_boxed_1133_);
lean_dec(v_msbs_1131_);
lean_dec(v_n_1130_);
return v_res_1134_;
}
}
lean_object* l_BitVec_shiftConcat(lean_object* v_n_1135_, lean_object* v_x_1136_, uint8_t v_b_1137_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1138_ = lean_unsigned_to_nat(1u);
v___x_1139_ = lean_nat_add(v_n_1135_, v___x_1138_);
v___x_1140_ = l_BitVec_concat___redArg(v_x_1136_, v_b_1137_);
v___x_1141_ = l_BitVec_setWidth(v___x_1139_, v_n_1135_, v___x_1140_);
lean_dec(v___x_1140_);
lean_dec(v___x_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT void l_BitVec_shiftConcat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1135_ = stack[0].m_obj;
lean_object* v_x_1136_ = stack[1].m_obj;
uint8_t v_b_1137_ = stack[2].m_num;
lean_object* v_res_1142_;
v_res_1142_ = l_BitVec_shiftConcat(v_n_1135_, v_x_1136_, v_b_1137_);
stack->m_obj
 = v_res_1142_;
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat___boxed(lean_object* v_n_1143_, lean_object* v_x_1144_, lean_object* v_b_1145_){
_start:
{
uint8_t v_b_boxed_1146_; lean_object* v_res_1147_; 
v_b_boxed_1146_ = lean_unbox(v_b_1145_);
v_res_1147_ = l_BitVec_shiftConcat(v_n_1143_, v_x_1144_, v_b_boxed_1146_);
lean_dec(v_x_1144_);
lean_dec(v_n_1143_);
return v_res_1147_;
}
}
lean_object* l_BitVec_cons(lean_object* v_n_1148_, uint8_t v_msb_1149_, lean_object* v_lsbs_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = l_BitVec_ofBool(v_msb_1149_);
v___x_1152_ = l_BitVec_append___redArg(v_n_1148_, v___x_1151_, v_lsbs_1150_);
lean_dec(v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT void l_BitVec_cons_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1148_ = stack[0].m_obj;
uint8_t v_msb_1149_ = stack[1].m_num;
lean_object* v_lsbs_1150_ = stack[2].m_obj;
lean_object* v_res_1153_;
v_res_1153_ = l_BitVec_cons(v_n_1148_, v_msb_1149_, v_lsbs_1150_);
stack->m_obj
 = v_res_1153_;
}
LEAN_EXPORT lean_object* l_BitVec_cons___boxed(lean_object* v_n_1154_, lean_object* v_msb_1155_, lean_object* v_lsbs_1156_){
_start:
{
uint8_t v_msb_boxed_1157_; lean_object* v_res_1158_; 
v_msb_boxed_1157_ = lean_unbox(v_msb_1155_);
v_res_1158_ = l_BitVec_cons(v_n_1154_, v_msb_boxed_1157_, v_lsbs_1156_);
lean_dec(v_lsbs_1156_);
lean_dec(v_n_1154_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow(lean_object* v_w_1159_, lean_object* v_i_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = l_BitVec_ofNat(v_w_1159_, v___x_1161_);
v___x_1163_ = l_BitVec_shiftLeft(v_w_1159_, v___x_1162_, v_i_1160_);
lean_dec(v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow___boxed(lean_object* v_w_1164_, lean_object* v_i_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_BitVec_twoPow(v_w_1164_, v_i_1165_);
lean_dec(v_i_1165_);
lean_dec(v_w_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMin(lean_object* v_w_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = lean_unsigned_to_nat(1u);
v___x_1169_ = lean_nat_sub(v_w_1167_, v___x_1168_);
v___x_1170_ = l_BitVec_twoPow(v_w_1167_, v___x_1169_);
lean_dec(v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMin___boxed(lean_object* v_w_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_BitVec_intMin(v_w_1171_);
lean_dec(v_w_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMax(lean_object* v_w_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
v___x_1175_ = lean_nat_sub(v_w_1173_, v___x_1174_);
v___x_1176_ = l_BitVec_twoPow(v_w_1173_, v___x_1175_);
lean_dec(v___x_1175_);
v___x_1177_ = l_BitVec_ofNat(v_w_1173_, v___x_1174_);
v___x_1178_ = l_BitVec_sub(v_w_1173_, v___x_1176_, v___x_1177_);
lean_dec(v___x_1177_);
lean_dec(v___x_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMax___boxed(lean_object* v_w_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_BitVec_intMax(v_w_1179_);
lean_dec(v_w_1179_);
return v_res_1180_;
}
}
uint64_t l_BitVec_hash(lean_object* v_n_1181_, lean_object* v_bv_1182_){
_start:
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_unsigned_to_nat(64u);
v___x_1184_ = lean_nat_dec_le(v_n_1181_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint64_t v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint64_t v___x_1189_; uint64_t v___x_1190_; 
v___x_1185_ = lean_uint64_of_nat(v_bv_1182_);
v___x_1186_ = lean_nat_sub(v_n_1181_, v___x_1183_);
v___x_1187_ = lean_nat_shiftr(v_bv_1182_, v___x_1183_);
v___x_1188_ = l_BitVec_setWidth(v_n_1181_, v___x_1186_, v___x_1187_);
lean_dec(v___x_1187_);
v___x_1189_ = l_BitVec_hash(v___x_1186_, v___x_1188_);
lean_dec(v___x_1188_);
lean_dec(v___x_1186_);
v___x_1190_ = lean_uint64_mix_hash(v___x_1185_, v___x_1189_);
return v___x_1190_;
}
else
{
uint64_t v___x_1191_; 
v___x_1191_ = lean_uint64_of_nat(v_bv_1182_);
return v___x_1191_;
}
}
}
LEAN_EXPORT void l_BitVec_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1181_ = stack[0].m_obj;
lean_object* v_bv_1182_ = stack[1].m_obj;
uint64_t v_res_1192_;
v_res_1192_ = l_BitVec_hash(v_n_1181_, v_bv_1182_);
stack->m_num = v_res_1192_;
}
LEAN_EXPORT lean_object* l_BitVec_hash___boxed(lean_object* v_n_1193_, lean_object* v_bv_1194_){
_start:
{
uint64_t v_res_1195_; lean_object* v_r_1196_; 
v_res_1195_ = l_BitVec_hash(v_n_1193_, v_bv_1194_);
lean_dec(v_bv_1194_);
lean_dec(v_n_1193_);
v_r_1196_ = lean_box_uint64(v_res_1195_);
return v_r_1196_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHashable(lean_object* v_n_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_closure((void*)(l_BitVec_hash___boxed), 2, 1);
lean_closure_set(v___x_1198_, 0, v_n_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE(lean_object* v_x_1199_){
_start:
{
if (lean_obj_tag(v_x_1199_) == 0)
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1200_;
}
else
{
lean_object* v_head_1201_; lean_object* v_tail_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; lean_object* v___x_1206_; 
v_head_1201_ = lean_ctor_get(v_x_1199_, 0);
v_tail_1202_ = lean_ctor_get(v_x_1199_, 1);
v___x_1203_ = l_List_lengthTR___redArg(v_tail_1202_);
v___x_1204_ = l_BitVec_ofBoolListBE(v_tail_1202_);
v___x_1205_ = lean_unbox(v_head_1201_);
v___x_1206_ = l_BitVec_cons(v___x_1203_, v___x_1205_, v___x_1204_);
lean_dec(v___x_1204_);
lean_dec(v___x_1203_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE___boxed(lean_object* v_x_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_BitVec_ofBoolListBE(v_x_1207_);
lean_dec(v_x_1207_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE(lean_object* v_x_1209_){
_start:
{
if (lean_obj_tag(v_x_1209_) == 0)
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1210_;
}
else
{
lean_object* v_head_1211_; lean_object* v_tail_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; 
v_head_1211_ = lean_ctor_get(v_x_1209_, 0);
v_tail_1212_ = lean_ctor_get(v_x_1209_, 1);
v___x_1213_ = l_BitVec_ofBoolListLE(v_tail_1212_);
v___x_1214_ = lean_unbox(v_head_1211_);
v___x_1215_ = l_BitVec_concat___redArg(v___x_1213_, v___x_1214_);
lean_dec(v___x_1213_);
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE___boxed(lean_object* v_x_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_BitVec_ofBoolListLE(v_x_1216_);
lean_dec(v_x_1216_);
return v_res_1217_;
}
}
uint8_t l_BitVec_uaddOverflow(lean_object* v_w_1218_, lean_object* v_x_1219_, lean_object* v_y_1220_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1221_ = lean_unsigned_to_nat(2u);
v___x_1222_ = lean_nat_pow(v___x_1221_, v_w_1218_);
v___x_1223_ = lean_nat_add(v_x_1219_, v_y_1220_);
v___x_1224_ = lean_nat_dec_le(v___x_1222_, v___x_1223_);
lean_dec(v___x_1223_);
lean_dec(v___x_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT void l_BitVec_uaddOverflow_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1218_ = stack[0].m_obj;
lean_object* v_x_1219_ = stack[1].m_obj;
lean_object* v_y_1220_ = stack[2].m_obj;
uint8_t v_res_1225_;
v_res_1225_ = l_BitVec_uaddOverflow(v_w_1218_, v_x_1219_, v_y_1220_);
stack->m_num = v_res_1225_;
}
LEAN_EXPORT lean_object* l_BitVec_uaddOverflow___boxed(lean_object* v_w_1226_, lean_object* v_x_1227_, lean_object* v_y_1228_){
_start:
{
uint8_t v_res_1229_; lean_object* v_r_1230_; 
v_res_1229_ = l_BitVec_uaddOverflow(v_w_1226_, v_x_1227_, v_y_1228_);
lean_dec(v_y_1228_);
lean_dec(v_x_1227_);
lean_dec(v_w_1226_);
v_r_1230_ = lean_box(v_res_1229_);
return v_r_1230_;
}
}
static lean_object* _init_l_BitVec_saddOverflow___closed__0(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_unsigned_to_nat(2u);
v___x_1232_ = lean_nat_to_int(v___x_1231_);
return v___x_1232_;
}
}
uint8_t l_BitVec_saddOverflow(lean_object* v_w_1233_, lean_object* v_x_1234_, lean_object* v_y_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1236_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = lean_nat_sub(v_w_1233_, v___x_1237_);
v___x_1239_ = l_Int_pow(v___x_1236_, v___x_1238_);
lean_dec(v___x_1238_);
v___x_1240_ = l_BitVec_toInt(v_w_1233_, v_x_1234_);
v___x_1241_ = l_BitVec_toInt(v_w_1233_, v_y_1235_);
v___x_1242_ = lean_int_add(v___x_1240_, v___x_1241_);
lean_dec(v___x_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_int_dec_le(v___x_1239_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = lean_int_neg(v___x_1239_);
lean_dec(v___x_1239_);
v___x_1245_ = lean_int_dec_lt(v___x_1242_, v___x_1244_);
lean_dec(v___x_1244_);
lean_dec(v___x_1242_);
return v___x_1245_;
}
else
{
lean_dec(v___x_1242_);
lean_dec(v___x_1239_);
return v___x_1243_;
}
}
}
LEAN_EXPORT void l_BitVec_saddOverflow_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1233_ = stack[0].m_obj;
lean_object* v_x_1234_ = stack[1].m_obj;
lean_object* v_y_1235_ = stack[2].m_obj;
uint8_t v_res_1246_;
v_res_1246_ = l_BitVec_saddOverflow(v_w_1233_, v_x_1234_, v_y_1235_);
stack->m_num = v_res_1246_;
}
LEAN_EXPORT lean_object* l_BitVec_saddOverflow___boxed(lean_object* v_w_1247_, lean_object* v_x_1248_, lean_object* v_y_1249_){
_start:
{
uint8_t v_res_1250_; lean_object* v_r_1251_; 
v_res_1250_ = l_BitVec_saddOverflow(v_w_1247_, v_x_1248_, v_y_1249_);
lean_dec(v_w_1247_);
v_r_1251_ = lean_box(v_res_1250_);
return v_r_1251_;
}
}
uint8_t l_BitVec_usubOverflow___redArg(lean_object* v_x_1252_, lean_object* v_y_1253_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_nat_dec_lt(v_x_1252_, v_y_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT void l_BitVec_usubOverflow___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1252_ = stack[0].m_obj;
lean_object* v_y_1253_ = stack[1].m_obj;
uint8_t v_res_1255_;
v_res_1255_ = l_BitVec_usubOverflow___redArg(v_x_1252_, v_y_1253_);
stack->m_num = v_res_1255_;
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___redArg___boxed(lean_object* v_x_1256_, lean_object* v_y_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l_BitVec_usubOverflow___redArg(v_x_1256_, v_y_1257_);
lean_dec(v_y_1257_);
lean_dec(v_x_1256_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
uint8_t l_BitVec_usubOverflow(lean_object* v_w_1260_, lean_object* v_x_1261_, lean_object* v_y_1262_){
_start:
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_nat_dec_lt(v_x_1261_, v_y_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT void l_BitVec_usubOverflow_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1260_ = stack[0].m_obj;
lean_object* v_x_1261_ = stack[1].m_obj;
lean_object* v_y_1262_ = stack[2].m_obj;
uint8_t v_res_1264_;
v_res_1264_ = l_BitVec_usubOverflow(v_w_1260_, v_x_1261_, v_y_1262_);
stack->m_num = v_res_1264_;
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___boxed(lean_object* v_w_1265_, lean_object* v_x_1266_, lean_object* v_y_1267_){
_start:
{
uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_res_1268_ = l_BitVec_usubOverflow(v_w_1265_, v_x_1266_, v_y_1267_);
lean_dec(v_y_1267_);
lean_dec(v_x_1266_);
lean_dec(v_w_1265_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
uint8_t l_BitVec_ssubOverflow(lean_object* v_w_1270_, lean_object* v_x_1271_, lean_object* v_y_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1273_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1274_ = lean_unsigned_to_nat(1u);
v___x_1275_ = lean_nat_sub(v_w_1270_, v___x_1274_);
v___x_1276_ = l_Int_pow(v___x_1273_, v___x_1275_);
lean_dec(v___x_1275_);
v___x_1277_ = l_BitVec_toInt(v_w_1270_, v_x_1271_);
v___x_1278_ = l_BitVec_toInt(v_w_1270_, v_y_1272_);
v___x_1279_ = lean_int_sub(v___x_1277_, v___x_1278_);
lean_dec(v___x_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_int_dec_le(v___x_1276_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = lean_int_neg(v___x_1276_);
lean_dec(v___x_1276_);
v___x_1282_ = lean_int_dec_lt(v___x_1279_, v___x_1281_);
lean_dec(v___x_1281_);
lean_dec(v___x_1279_);
return v___x_1282_;
}
else
{
lean_dec(v___x_1279_);
lean_dec(v___x_1276_);
return v___x_1280_;
}
}
}
LEAN_EXPORT void l_BitVec_ssubOverflow_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1270_ = stack[0].m_obj;
lean_object* v_x_1271_ = stack[1].m_obj;
lean_object* v_y_1272_ = stack[2].m_obj;
uint8_t v_res_1283_;
v_res_1283_ = l_BitVec_ssubOverflow(v_w_1270_, v_x_1271_, v_y_1272_);
stack->m_num = v_res_1283_;
}
LEAN_EXPORT lean_object* l_BitVec_ssubOverflow___boxed(lean_object* v_w_1284_, lean_object* v_x_1285_, lean_object* v_y_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_BitVec_ssubOverflow(v_w_1284_, v_x_1285_, v_y_1286_);
lean_dec(v_w_1284_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
uint8_t l_BitVec_negOverflow(lean_object* v_w_1289_, lean_object* v_x_1290_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1291_ = l_BitVec_toInt(v_w_1289_, v_x_1290_);
v___x_1292_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1293_ = lean_unsigned_to_nat(1u);
v___x_1294_ = lean_nat_sub(v_w_1289_, v___x_1293_);
v___x_1295_ = l_Int_pow(v___x_1292_, v___x_1294_);
lean_dec(v___x_1294_);
v___x_1296_ = lean_int_neg(v___x_1295_);
lean_dec(v___x_1295_);
v___x_1297_ = lean_int_dec_eq(v___x_1291_, v___x_1296_);
lean_dec(v___x_1296_);
lean_dec(v___x_1291_);
return v___x_1297_;
}
}
LEAN_EXPORT void l_BitVec_negOverflow_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1289_ = stack[0].m_obj;
lean_object* v_x_1290_ = stack[1].m_obj;
uint8_t v_res_1298_;
v_res_1298_ = l_BitVec_negOverflow(v_w_1289_, v_x_1290_);
stack->m_num = v_res_1298_;
}
LEAN_EXPORT lean_object* l_BitVec_negOverflow___boxed(lean_object* v_w_1299_, lean_object* v_x_1300_){
_start:
{
uint8_t v_res_1301_; lean_object* v_r_1302_; 
v_res_1301_ = l_BitVec_negOverflow(v_w_1299_, v_x_1300_);
lean_dec(v_w_1299_);
v_r_1302_ = lean_box(v_res_1301_);
return v_r_1302_;
}
}
uint8_t l_BitVec_sdivOverflow(lean_object* v_w_1303_, lean_object* v_x_1304_, lean_object* v_y_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1306_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1307_ = lean_unsigned_to_nat(1u);
v___x_1308_ = lean_nat_sub(v_w_1303_, v___x_1307_);
v___x_1309_ = l_Int_pow(v___x_1306_, v___x_1308_);
lean_dec(v___x_1308_);
v___x_1310_ = l_BitVec_toInt(v_w_1303_, v_x_1304_);
v___x_1311_ = l_BitVec_toInt(v_w_1303_, v_y_1305_);
v___x_1312_ = lean_int_ediv(v___x_1310_, v___x_1311_);
lean_dec(v___x_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_int_dec_le(v___x_1309_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = lean_int_neg(v___x_1309_);
lean_dec(v___x_1309_);
v___x_1315_ = lean_int_dec_lt(v___x_1312_, v___x_1314_);
lean_dec(v___x_1314_);
lean_dec(v___x_1312_);
return v___x_1315_;
}
else
{
lean_dec(v___x_1312_);
lean_dec(v___x_1309_);
return v___x_1313_;
}
}
}
LEAN_EXPORT void l_BitVec_sdivOverflow_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1303_ = stack[0].m_obj;
lean_object* v_x_1304_ = stack[1].m_obj;
lean_object* v_y_1305_ = stack[2].m_obj;
uint8_t v_res_1316_;
v_res_1316_ = l_BitVec_sdivOverflow(v_w_1303_, v_x_1304_, v_y_1305_);
stack->m_num = v_res_1316_;
}
LEAN_EXPORT lean_object* l_BitVec_sdivOverflow___boxed(lean_object* v_w_1317_, lean_object* v_x_1318_, lean_object* v_y_1319_){
_start:
{
uint8_t v_res_1320_; lean_object* v_r_1321_; 
v_res_1320_ = l_BitVec_sdivOverflow(v_w_1317_, v_x_1318_, v_y_1319_);
lean_dec(v_w_1317_);
v_r_1321_ = lean_box(v_res_1320_);
return v_r_1321_;
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse(lean_object* v_x_1322_, lean_object* v_x_1323_){
_start:
{
lean_object* v_zero_1324_; uint8_t v_isZero_1325_; 
v_zero_1324_ = lean_unsigned_to_nat(0u);
v_isZero_1325_ = lean_nat_dec_eq(v_x_1322_, v_zero_1324_);
if (v_isZero_1325_ == 1)
{
lean_inc(v_x_1323_);
return v_x_1323_;
}
else
{
lean_object* v_one_1326_; lean_object* v_n_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_one_1326_ = lean_unsigned_to_nat(1u);
v_n_1327_ = lean_nat_sub(v_x_1322_, v_one_1326_);
v___x_1328_ = lean_nat_add(v_n_1327_, v_one_1326_);
v___x_1329_ = l_BitVec_setWidth(v___x_1328_, v_n_1327_, v_x_1323_);
v___x_1330_ = l_BitVec_reverse(v_n_1327_, v___x_1329_);
lean_dec(v___x_1329_);
lean_dec(v_n_1327_);
v___x_1331_ = lean_nat_dec_lt(v_zero_1324_, v___x_1328_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
lean_dec(v___x_1328_);
v___x_1332_ = l_BitVec_concat___redArg(v___x_1330_, v___x_1331_);
lean_dec(v___x_1330_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_nat_sub(v___x_1328_, v_one_1326_);
lean_dec(v___x_1328_);
v___x_1334_ = l_Nat_testBit(v_x_1323_, v___x_1333_);
lean_dec(v___x_1333_);
v___x_1335_ = l_BitVec_concat___redArg(v___x_1330_, v___x_1334_);
lean_dec(v___x_1330_);
return v___x_1335_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse___boxed(lean_object* v_x_1336_, lean_object* v_x_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_BitVec_reverse(v_x_1336_, v_x_1337_);
lean_dec(v_x_1337_);
lean_dec(v_x_1336_);
return v_res_1338_;
}
}
uint8_t l_BitVec_umulOverflow(lean_object* v_w_1339_, lean_object* v_x_1340_, lean_object* v_y_1341_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1342_ = lean_unsigned_to_nat(2u);
v___x_1343_ = lean_nat_pow(v___x_1342_, v_w_1339_);
v___x_1344_ = lean_nat_mul(v_x_1340_, v_y_1341_);
v___x_1345_ = lean_nat_dec_le(v___x_1343_, v___x_1344_);
lean_dec(v___x_1344_);
lean_dec(v___x_1343_);
return v___x_1345_;
}
}
LEAN_EXPORT void l_BitVec_umulOverflow_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1339_ = stack[0].m_obj;
lean_object* v_x_1340_ = stack[1].m_obj;
lean_object* v_y_1341_ = stack[2].m_obj;
uint8_t v_res_1346_;
v_res_1346_ = l_BitVec_umulOverflow(v_w_1339_, v_x_1340_, v_y_1341_);
stack->m_num = v_res_1346_;
}
LEAN_EXPORT lean_object* l_BitVec_umulOverflow___boxed(lean_object* v_w_1347_, lean_object* v_x_1348_, lean_object* v_y_1349_){
_start:
{
uint8_t v_res_1350_; lean_object* v_r_1351_; 
v_res_1350_ = l_BitVec_umulOverflow(v_w_1347_, v_x_1348_, v_y_1349_);
lean_dec(v_y_1349_);
lean_dec(v_x_1348_);
lean_dec(v_w_1347_);
v_r_1351_ = lean_box(v_res_1350_);
return v_r_1351_;
}
}
uint8_t l_BitVec_smulOverflow(lean_object* v_w_1352_, lean_object* v_x_1353_, lean_object* v_y_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1355_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = lean_nat_sub(v_w_1352_, v___x_1356_);
v___x_1358_ = l_Int_pow(v___x_1355_, v___x_1357_);
lean_dec(v___x_1357_);
v___x_1359_ = l_BitVec_toInt(v_w_1352_, v_x_1353_);
v___x_1360_ = l_BitVec_toInt(v_w_1352_, v_y_1354_);
v___x_1361_ = lean_int_mul(v___x_1359_, v___x_1360_);
lean_dec(v___x_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_int_dec_le(v___x_1358_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = lean_int_neg(v___x_1358_);
lean_dec(v___x_1358_);
v___x_1364_ = lean_int_dec_lt(v___x_1361_, v___x_1363_);
lean_dec(v___x_1363_);
lean_dec(v___x_1361_);
return v___x_1364_;
}
else
{
lean_dec(v___x_1361_);
lean_dec(v___x_1358_);
return v___x_1362_;
}
}
}
LEAN_EXPORT void l_BitVec_smulOverflow_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1352_ = stack[0].m_obj;
lean_object* v_x_1353_ = stack[1].m_obj;
lean_object* v_y_1354_ = stack[2].m_obj;
uint8_t v_res_1365_;
v_res_1365_ = l_BitVec_smulOverflow(v_w_1352_, v_x_1353_, v_y_1354_);
stack->m_num = v_res_1365_;
}
LEAN_EXPORT lean_object* l_BitVec_smulOverflow___boxed(lean_object* v_w_1366_, lean_object* v_x_1367_, lean_object* v_y_1368_){
_start:
{
uint8_t v_res_1369_; lean_object* v_r_1370_; 
v_res_1369_ = l_BitVec_smulOverflow(v_w_1366_, v_x_1367_, v_y_1368_);
lean_dec(v_w_1366_);
v_r_1370_ = lean_box(v_res_1369_);
return v_r_1370_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec(lean_object* v_w_1371_, lean_object* v_x_1372_, lean_object* v_n_1373_){
_start:
{
lean_object* v_zero_1374_; uint8_t v_isZero_1375_; 
v_zero_1374_ = lean_unsigned_to_nat(0u);
v_isZero_1375_ = lean_nat_dec_eq(v_n_1373_, v_zero_1374_);
if (v_isZero_1375_ == 1)
{
uint8_t v___x_1376_; 
lean_dec(v_n_1373_);
v___x_1376_ = l_Nat_testBit(v_x_1372_, v_zero_1374_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = l_BitVec_ofNat(v_w_1371_, v_w_1371_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_unsigned_to_nat(1u);
v___x_1379_ = lean_nat_sub(v_w_1371_, v___x_1378_);
v___x_1380_ = l_BitVec_ofNat(v_w_1371_, v___x_1379_);
lean_dec(v___x_1379_);
return v___x_1380_;
}
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = l_Nat_testBit(v_x_1372_, v_n_1373_);
if (v___x_1381_ == 0)
{
lean_object* v_one_1382_; lean_object* v_n_1383_; 
v_one_1382_ = lean_unsigned_to_nat(1u);
v_n_1383_ = lean_nat_sub(v_n_1373_, v_one_1382_);
lean_dec(v_n_1373_);
v_n_1373_ = v_n_1383_;
goto _start;
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1385_ = lean_unsigned_to_nat(1u);
v___x_1386_ = lean_nat_sub(v_w_1371_, v___x_1385_);
v___x_1387_ = lean_nat_sub(v___x_1386_, v_n_1373_);
lean_dec(v_n_1373_);
lean_dec(v___x_1386_);
v___x_1388_ = l_BitVec_ofNat(v_w_1371_, v___x_1387_);
lean_dec(v___x_1387_);
return v___x_1388_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec___boxed(lean_object* v_w_1389_, lean_object* v_x_1390_, lean_object* v_n_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_BitVec_clzAuxRec(v_w_1389_, v_x_1390_, v_n_1391_);
lean_dec(v_x_1390_);
lean_dec(v_w_1389_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clz(lean_object* v_w_1393_, lean_object* v_x_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = lean_nat_sub(v_w_1393_, v___x_1395_);
v___x_1397_ = l_BitVec_clzAuxRec(v_w_1393_, v_x_1394_, v___x_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clz___boxed(lean_object* v_w_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_BitVec_clz(v_w_1398_, v_x_1399_);
lean_dec(v_x_1399_);
lean_dec(v_w_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ctz(lean_object* v_w_1401_, lean_object* v_x_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = l_BitVec_reverse(v_w_1401_, v_x_1402_);
v___x_1404_ = l_BitVec_clz(v_w_1401_, v___x_1403_);
lean_dec(v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ctz___boxed(lean_object* v_w_1405_, lean_object* v_x_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_BitVec_ctz(v_w_1405_, v_x_1406_);
lean_dec(v_x_1406_);
lean_dec(v_w_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg(lean_object* v_x_1408_, lean_object* v_pos_1409_, lean_object* v_acc_1410_){
_start:
{
lean_object* v_zero_1411_; uint8_t v_isZero_1412_; 
v_zero_1411_ = lean_unsigned_to_nat(0u);
v_isZero_1412_ = lean_nat_dec_eq(v_pos_1409_, v_zero_1411_);
if (v_isZero_1412_ == 1)
{
lean_dec(v_pos_1409_);
return v_acc_1410_;
}
else
{
lean_object* v_one_1413_; lean_object* v_n_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_one_1413_ = lean_unsigned_to_nat(1u);
v_n_1414_ = lean_nat_sub(v_pos_1409_, v_one_1413_);
lean_dec(v_pos_1409_);
v___x_1415_ = l_Nat_testBit(v_x_1408_, v_n_1414_);
v___x_1416_ = l_Bool_toNat(v___x_1415_);
v___x_1417_ = lean_nat_add(v_acc_1410_, v___x_1416_);
lean_dec(v___x_1416_);
lean_dec(v_acc_1410_);
v_pos_1409_ = v_n_1414_;
v_acc_1410_ = v___x_1417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg___boxed(lean_object* v_x_1419_, lean_object* v_pos_1420_, lean_object* v_acc_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_BitVec_cpopNatRec___redArg(v_x_1419_, v_pos_1420_, v_acc_1421_);
lean_dec(v_x_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec(lean_object* v_w_1423_, lean_object* v_x_1424_, lean_object* v_pos_1425_, lean_object* v_acc_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_BitVec_cpopNatRec___redArg(v_x_1424_, v_pos_1425_, v_acc_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___boxed(lean_object* v_w_1428_, lean_object* v_x_1429_, lean_object* v_pos_1430_, lean_object* v_acc_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_BitVec_cpopNatRec(v_w_1428_, v_x_1429_, v_pos_1430_, v_acc_1431_);
lean_dec(v_x_1429_);
lean_dec(v_w_1428_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpop(lean_object* v_w_1433_, lean_object* v_x_1434_){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = lean_unsigned_to_nat(0u);
lean_inc(v_w_1433_);
v___x_1436_ = l_BitVec_cpopNatRec___redArg(v_x_1434_, v_w_1433_, v___x_1435_);
v___x_1437_ = l_BitVec_ofNat(v_w_1433_, v___x_1436_);
lean_dec(v___x_1436_);
lean_dec(v_w_1433_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpop___boxed(lean_object* v_w_1438_, lean_object* v_x_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_BitVec_cpop(v_w_1438_, v_x_1439_);
lean_dec(v_x_1439_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg___lam__0(lean_object* v_x_1441_, lean_object* v_y_1442_){
_start:
{
uint8_t v___x_1443_; 
v___x_1443_ = lean_nat_dec_le(v_x_1441_, v_y_1442_);
if (v___x_1443_ == 0)
{
lean_inc(v_y_1442_);
return v_y_1442_;
}
else
{
lean_inc(v_x_1441_);
return v_x_1441_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg___lam__0___boxed(lean_object* v_x_1444_, lean_object* v_y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_BitVec_instMin___redArg___lam__0(v_x_1444_, v_y_1445_);
lean_dec(v_y_1445_);
lean_dec(v_x_1444_);
return v_res_1446_;
}
}
lean_object* l_BitVec_instMin___redArg(){
_start:
{
lean_object* v___f_1449_; 
v___f_1449_ = ((lean_object*)(l_BitVec_instMin___redArg___closed__0));
return v___f_1449_;
}
}
LEAN_EXPORT void l_BitVec_instMin___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1450_;
v_res_1450_ = l_BitVec_instMin___redArg();
stack->m_obj
 = v_res_1450_;
}
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg___boxed(lean_object* v___dummy_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_BitVec_instMin___redArg();
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin(lean_object* v_w_1453_){
_start:
{
lean_object* v___f_1454_; 
v___f_1454_ = ((lean_object*)(l_BitVec_instMin___redArg___closed__0));
return v___f_1454_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___boxed(lean_object* v_w_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_BitVec_instMin(v_w_1455_);
lean_dec(v_w_1455_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg___lam__0(lean_object* v_x_1457_, lean_object* v_y_1458_){
_start:
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_nat_dec_le(v_x_1457_, v_y_1458_);
if (v___x_1459_ == 0)
{
lean_inc(v_x_1457_);
return v_x_1457_;
}
else
{
lean_inc(v_y_1458_);
return v_y_1458_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg___lam__0___boxed(lean_object* v_x_1460_, lean_object* v_y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_BitVec_instMax___redArg___lam__0(v_x_1460_, v_y_1461_);
lean_dec(v_y_1461_);
lean_dec(v_x_1460_);
return v_res_1462_;
}
}
lean_object* l_BitVec_instMax___redArg(){
_start:
{
lean_object* v___f_1465_; 
v___f_1465_ = ((lean_object*)(l_BitVec_instMax___redArg___closed__0));
return v___f_1465_;
}
}
LEAN_EXPORT void l_BitVec_instMax___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1466_;
v_res_1466_ = l_BitVec_instMax___redArg();
stack->m_obj
 = v_res_1466_;
}
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg___boxed(lean_object* v___dummy_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_BitVec_instMax___redArg();
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax(lean_object* v_w_1469_){
_start:
{
lean_object* v___f_1470_; 
v___f_1470_ = ((lean_object*)(l_BitVec_instMax___redArg___closed__0));
return v___f_1470_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___boxed(lean_object* v_w_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_BitVec_instMax(v_w_1471_);
lean_dec(v_w_1471_);
return v_res_1472_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WF(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_BitVec_nil = _init_l_BitVec_nil();
lean_mark_persistent(l_BitVec_nil);
l_BitVec_toHex___boxed__const__1 = _init_l_BitVec_toHex___boxed__const__1();
lean_mark_persistent(l_BitVec_toHex___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_BitVec_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* initialize_Init_WF(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_Meta_Defs(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_BitVec_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
