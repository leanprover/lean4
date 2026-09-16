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
LEAN_EXPORT lean_object* l_BitVec_zero___redArg(){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_unsigned_to_nat(0u);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zero___redArg___boxed(lean_object* v___dummy_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_BitVec_zero___redArg();
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zero(lean_object* v_n_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(0u);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zero___boxed(lean_object* v_n_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_BitVec_zero(v_n_18_);
lean_dec(v_n_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instInhabited___redArg(){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(0u);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instInhabited___redArg___boxed(lean_object* v___dummy_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_BitVec_instInhabited___redArg();
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instInhabited(lean_object* v_n_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_unsigned_to_nat(0u);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instInhabited___boxed(lean_object* v_n_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_BitVec_instInhabited(v_n_26_);
lean_dec(v_n_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_BitVec_allOnes(lean_object* v_n_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_29_ = lean_unsigned_to_nat(2u);
v___x_30_ = lean_nat_pow(v___x_29_, v_n_28_);
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lean_nat_sub(v___x_30_, v___x_31_);
lean_dec(v___x_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_BitVec_allOnes___boxed(lean_object* v_n_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_BitVec_allOnes(v_n_33_);
lean_dec(v_n_33_);
return v_res_34_;
}
}
LEAN_EXPORT uint8_t l_BitVec_getLsb___redArg(lean_object* v_x_35_, lean_object* v_i_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = l_Nat_testBit(v_x_35_, v_i_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb___redArg___boxed(lean_object* v_x_38_, lean_object* v_i_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_BitVec_getLsb___redArg(v_x_38_, v_i_39_);
lean_dec(v_i_39_);
lean_dec(v_x_38_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT uint8_t l_BitVec_getLsb(lean_object* v_w_42_, lean_object* v_x_43_, lean_object* v_i_44_){
_start:
{
uint8_t v___x_45_; 
v___x_45_ = l_Nat_testBit(v_x_43_, v_i_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb___boxed(lean_object* v_w_46_, lean_object* v_x_47_, lean_object* v_i_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_BitVec_getLsb(v_w_46_, v_x_47_, v_i_48_);
lean_dec(v_i_48_);
lean_dec(v_x_47_);
lean_dec(v_w_46_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb_x3f(lean_object* v_w_51_, lean_object* v_x_52_, lean_object* v_i_53_){
_start:
{
uint8_t v___x_54_; 
v___x_54_ = lean_nat_dec_lt(v_i_53_, v_w_51_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
v___x_55_ = lean_box(0);
return v___x_55_;
}
else
{
uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = l_Nat_testBit(v_x_52_, v_i_53_);
v___x_57_ = lean_box(v___x_56_);
v___x_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb_x3f___boxed(lean_object* v_w_59_, lean_object* v_x_60_, lean_object* v_i_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_BitVec_getLsb_x3f(v_w_59_, v_x_60_, v_i_61_);
lean_dec(v_i_61_);
lean_dec(v_x_60_);
lean_dec(v_w_59_);
return v_res_62_;
}
}
LEAN_EXPORT uint8_t l_BitVec_getMsb(lean_object* v_w_63_, lean_object* v_x_64_, lean_object* v_i_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_sub(v_w_63_, v___x_66_);
v___x_68_ = lean_nat_sub(v___x_67_, v_i_65_);
lean_dec(v___x_67_);
v___x_69_ = l_Nat_testBit(v_x_64_, v___x_68_);
lean_dec(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsb___boxed(lean_object* v_w_70_, lean_object* v_x_71_, lean_object* v_i_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_BitVec_getMsb(v_w_70_, v_x_71_, v_i_72_);
lean_dec(v_i_72_);
lean_dec(v_x_71_);
lean_dec(v_w_70_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsb_x3f(lean_object* v_w_75_, lean_object* v_x_76_, lean_object* v_i_77_){
_start:
{
uint8_t v___x_78_; 
v___x_78_ = lean_nat_dec_lt(v_i_77_, v_w_75_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
v___x_79_ = lean_box(0);
return v___x_79_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_sub(v_w_75_, v___x_80_);
v___x_82_ = lean_nat_sub(v___x_81_, v_i_77_);
lean_dec(v___x_81_);
v___x_83_ = l_Nat_testBit(v_x_76_, v___x_82_);
lean_dec(v___x_82_);
v___x_84_ = lean_box(v___x_83_);
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsb_x3f___boxed(lean_object* v_w_86_, lean_object* v_x_87_, lean_object* v_i_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_BitVec_getMsb_x3f(v_w_86_, v_x_87_, v_i_88_);
lean_dec(v_i_88_);
lean_dec(v_x_87_);
lean_dec(v_w_86_);
return v_res_89_;
}
}
LEAN_EXPORT uint8_t l_BitVec_getLsbD___redArg(lean_object* v_x_90_, lean_object* v_i_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = l_Nat_testBit(v_x_90_, v_i_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsbD___redArg___boxed(lean_object* v_x_93_, lean_object* v_i_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_BitVec_getLsbD___redArg(v_x_93_, v_i_94_);
lean_dec(v_i_94_);
lean_dec(v_x_93_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_BitVec_getLsbD(lean_object* v_w_97_, lean_object* v_x_98_, lean_object* v_i_99_){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = l_Nat_testBit(v_x_98_, v_i_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsbD___boxed(lean_object* v_w_101_, lean_object* v_x_102_, lean_object* v_i_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_BitVec_getLsbD(v_w_101_, v_x_102_, v_i_103_);
lean_dec(v_i_103_);
lean_dec(v_x_102_);
lean_dec(v_w_101_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_BitVec_getMsbD(lean_object* v_w_106_, lean_object* v_x_107_, lean_object* v_i_108_){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = lean_nat_dec_lt(v_i_108_, v_w_106_);
if (v___x_109_ == 0)
{
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_sub(v_w_106_, v___x_110_);
v___x_112_ = lean_nat_sub(v___x_111_, v_i_108_);
lean_dec(v___x_111_);
v___x_113_ = l_Nat_testBit(v_x_107_, v___x_112_);
lean_dec(v___x_112_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsbD___boxed(lean_object* v_w_114_, lean_object* v_x_115_, lean_object* v_i_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_BitVec_getMsbD(v_w_114_, v_x_115_, v_i_116_);
lean_dec(v_i_116_);
lean_dec(v_x_115_);
lean_dec(v_w_114_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT uint8_t l_BitVec_msb(lean_object* v_n_119_, lean_object* v_x_120_){
_start:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_nat_dec_lt(v___x_121_, v_n_119_);
if (v___x_122_ == 0)
{
return v___x_122_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_sub(v_n_119_, v___x_123_);
v___x_125_ = l_Nat_testBit(v_x_120_, v___x_124_);
lean_dec(v___x_124_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_msb___boxed(lean_object* v_n_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_BitVec_msb(v_n_126_, v_x_127_);
lean_dec(v_x_127_);
lean_dec(v_n_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instGetElemNatBoolLt___redArg___lam__0(lean_object* v_xs_130_, lean_object* v_i_131_, lean_object* v_h_132_){
_start:
{
uint8_t v___x_133_; 
v___x_133_ = l_Nat_testBit(v_xs_130_, v_i_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___redArg___lam__0___boxed(lean_object* v_xs_134_, lean_object* v_i_135_, lean_object* v_h_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_BitVec_instGetElemNatBoolLt___redArg___lam__0(v_xs_134_, v_i_135_, v_h_136_);
lean_dec(v_i_135_);
lean_dec(v_xs_134_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___redArg(){
_start:
{
lean_object* v___f_141_; 
v___f_141_ = ((lean_object*)(l_BitVec_instGetElemNatBoolLt___redArg___closed__0));
return v___f_141_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___redArg___boxed(lean_object* v___dummy_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_BitVec_instGetElemNatBoolLt___redArg();
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt(lean_object* v_w_144_){
_start:
{
lean_object* v___f_145_; 
v___f_145_ = ((lean_object*)(l_BitVec_instGetElemNatBoolLt___redArg___closed__0));
return v___f_145_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___boxed(lean_object* v_w_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_BitVec_instGetElemNatBoolLt(v_w_146_);
lean_dec(v_w_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00BitVec_toInt_spec__0(lean_object* v_a_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_nat_to_int(v_a_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_BitVec_toInt(lean_object* v_n_150_, lean_object* v_x_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = lean_unsigned_to_nat(2u);
v___x_153_ = lean_nat_mul(v___x_152_, v_x_151_);
v___x_154_ = lean_nat_pow(v___x_152_, v_n_150_);
v___x_155_ = lean_nat_dec_lt(v___x_153_, v___x_154_);
lean_dec(v___x_153_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_nat_to_int(v_x_151_);
v___x_157_ = lean_nat_to_int(v___x_154_);
v___x_158_ = lean_int_sub(v___x_156_, v___x_157_);
lean_dec(v___x_157_);
lean_dec(v___x_156_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; 
lean_dec(v___x_154_);
v___x_159_ = lean_nat_to_int(v_x_151_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_toInt___boxed(lean_object* v_n_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_BitVec_toInt(v_n_160_, v_x_161_);
lean_dec(v_n_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofInt(lean_object* v_n_163_, lean_object* v_i_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_165_ = lean_unsigned_to_nat(2u);
v___x_166_ = lean_nat_pow(v___x_165_, v_n_163_);
v___x_167_ = lean_nat_to_int(v___x_166_);
v___x_168_ = lean_int_emod(v_i_164_, v___x_167_);
lean_dec(v___x_167_);
v___x_169_ = l_Int_toNat(v___x_168_);
lean_dec(v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofInt___boxed(lean_object* v_n_170_, lean_object* v_i_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_BitVec_ofInt(v_n_170_, v_i_171_);
lean_dec(v_i_171_);
lean_dec(v_n_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instIntCast(lean_object* v_w_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_alloc_closure((void*)(l_BitVec_ofInt___boxed), 2, 1);
lean_closure_set(v___x_174_, 0, v_w_173_);
return v___x_174_;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5));
v___x_234_ = l_String_toRawSubstring_x27(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1(lean_object* v_x_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__2));
lean_inc(v_x_248_);
v___x_252_ = l_Lean_Syntax_isOfKind(v_x_248_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_x_248_);
v___x_253_ = lean_box(1);
v___x_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v_a_250_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = l_Lean_Syntax_getArg(v_x_248_, v___x_255_);
v___x_257_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__6));
lean_inc(v___x_256_);
v___x_258_ = l_Lean_Syntax_isOfKind(v___x_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v___x_256_);
lean_dec(v_x_248_);
v___x_259_ = lean_box(1);
v___x_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v_a_250_);
return v___x_260_;
}
else
{
lean_object* v_quotContext_261_; lean_object* v_currMacroScope_262_; lean_object* v_ref_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_quotContext_261_ = lean_ctor_get(v_a_249_, 1);
v_currMacroScope_262_ = lean_ctor_get(v_a_249_, 2);
v_ref_263_ = lean_ctor_get(v_a_249_, 5);
v___x_264_ = lean_unsigned_to_nat(2u);
v___x_265_ = l_Lean_Syntax_getArg(v_x_248_, v___x_264_);
lean_dec(v_x_248_);
v___x_266_ = 0;
v___x_267_ = l_Lean_SourceInfo_fromRef(v_ref_263_, v___x_266_);
v___x_268_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
v___x_269_ = lean_obj_once(&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6, &l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6_once, _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6);
v___x_270_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8));
lean_inc(v_currMacroScope_262_);
lean_inc(v_quotContext_261_);
v___x_271_ = l_Lean_addMacroScope(v_quotContext_261_, v___x_270_, v_currMacroScope_262_);
v___x_272_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10));
lean_inc_n(v___x_267_, 2);
v___x_273_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_273_, 0, v___x_267_);
lean_ctor_set(v___x_273_, 1, v___x_269_);
lean_ctor_set(v___x_273_, 2, v___x_271_);
lean_ctor_set(v___x_273_, 3, v___x_272_);
v___x_274_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12));
v___x_275_ = l_Lean_Syntax_node2(v___x_267_, v___x_274_, v___x_265_, v___x_256_);
v___x_276_ = l_Lean_Syntax_node2(v___x_267_, v___x_268_, v___x_273_, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_a_250_);
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___boxed(lean_object* v_x_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1(v_x_278_, v_a_279_, v_a_280_);
lean_dec_ref(v_a_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat(lean_object* v_x_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
lean_inc(v_x_282_);
v___x_286_ = l_Lean_Syntax_isOfKind(v_x_282_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_x_282_);
v___x_287_ = lean_box(0);
v___x_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v_a_284_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = l_Lean_Syntax_getArg(v_x_282_, v___x_289_);
lean_dec(v_x_282_);
v___x_291_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_290_);
v___x_292_ = l_Lean_Syntax_matchesNull(v___x_290_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_a_284_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = l_Lean_Syntax_getArg(v___x_290_, v___x_289_);
v___x_296_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__6));
lean_inc(v___x_295_);
v___x_297_ = l_Lean_Syntax_isOfKind(v___x_295_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v___x_295_);
lean_dec(v___x_290_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_a_284_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = l_Lean_Syntax_getArg(v___x_290_, v___x_300_);
lean_dec(v___x_290_);
v___x_302_ = 0;
v___x_303_ = l_Lean_SourceInfo_fromRef(v_a_283_, v___x_302_);
v___x_304_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__2));
v___x_305_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__12));
lean_inc(v___x_303_);
v___x_306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_303_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = l_Lean_Syntax_node3(v___x_303_, v___x_304_, v___x_295_, v___x_306_, v___x_301_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_a_284_);
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat___boxed(lean_object* v_x_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_BitVec_unexpandBitVecOfNat(v_x_309_, v_a_310_, v_a_311_);
lean_dec(v_a_310_);
return v_res_312_;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__0));
v___x_339_ = l_String_toRawSubstring_x27(v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1(lean_object* v_x_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l_BitVec_term_____x23_x27_____00__closed__1));
lean_inc(v_x_350_);
v___x_354_ = l_Lean_Syntax_isOfKind(v_x_350_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v_x_350_);
v___x_355_ = lean_box(1);
v___x_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_a_352_);
return v___x_356_;
}
else
{
lean_object* v_quotContext_357_; lean_object* v_currMacroScope_358_; lean_object* v_ref_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_quotContext_357_ = lean_ctor_get(v_a_351_, 1);
v_currMacroScope_358_ = lean_ctor_get(v_a_351_, 2);
v_ref_359_ = lean_ctor_get(v_a_351_, 5);
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = l_Lean_Syntax_getArg(v_x_350_, v___x_360_);
v___x_362_ = lean_unsigned_to_nat(2u);
v___x_363_ = l_Lean_Syntax_getArg(v_x_350_, v___x_362_);
lean_dec(v_x_350_);
v___x_364_ = 0;
v___x_365_ = l_Lean_SourceInfo_fromRef(v_ref_359_, v___x_364_);
v___x_366_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
v___x_367_ = lean_obj_once(&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1, &l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1_once, _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1);
v___x_368_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3));
lean_inc(v_currMacroScope_358_);
lean_inc(v_quotContext_357_);
v___x_369_ = l_Lean_addMacroScope(v_quotContext_357_, v___x_368_, v_currMacroScope_358_);
v___x_370_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5));
lean_inc_n(v___x_365_, 2);
v___x_371_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_371_, 0, v___x_365_);
lean_ctor_set(v___x_371_, 1, v___x_367_);
lean_ctor_set(v___x_371_, 2, v___x_369_);
lean_ctor_set(v___x_371_, 3, v___x_370_);
v___x_372_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12));
v___x_373_ = l_Lean_Syntax_node2(v___x_365_, v___x_372_, v___x_361_, v___x_363_);
v___x_374_ = l_Lean_Syntax_node2(v___x_365_, v___x_366_, v___x_371_, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v_a_352_);
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___boxed(lean_object* v_x_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1(v_x_376_, v_a_377_, v_a_378_);
lean_dec_ref(v_a_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt(lean_object* v_x_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
lean_inc(v_x_380_);
v___x_384_ = l_Lean_Syntax_isOfKind(v_x_380_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v_x_380_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v_a_382_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = l_Lean_Syntax_getArg(v_x_380_, v___x_387_);
lean_dec(v_x_380_);
v___x_389_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_388_);
v___x_390_ = l_Lean_Syntax_matchesNull(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_a_382_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = l_Lean_Syntax_getArg(v___x_388_, v___x_393_);
v___x_395_ = l_Lean_Syntax_getArg(v___x_388_, v___x_387_);
lean_dec(v___x_388_);
v___x_396_ = 0;
v___x_397_ = l_Lean_SourceInfo_fromRef(v_a_381_, v___x_396_);
v___x_398_ = ((lean_object*)(l_BitVec_term_____x23_x27_____00__closed__1));
v___x_399_ = ((lean_object*)(l_BitVec_term_____x23_x27_____00__closed__2));
lean_inc(v___x_397_);
v___x_400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_397_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = l_Lean_Syntax_node3(v___x_397_, v___x_398_, v___x_394_, v___x_400_, v___x_395_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v_a_382_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt___boxed(lean_object* v_x_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_BitVec_unexpandBitVecOfNatLt(v_x_403_, v_a_404_, v_a_405_);
lean_dec(v_a_404_);
return v_res_406_;
}
}
static lean_object* _init_l_BitVec_toHex___boxed__const__1(void){
_start:
{
uint32_t v___x_407_; lean_object* v___x_408_; 
v___x_407_ = 48;
v___x_408_ = lean_box_uint32(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_BitVec_toHex(lean_object* v_n_409_, lean_object* v_x_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_s_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_t_422_; lean_object* v___x_423_; 
v___x_411_ = lean_unsigned_to_nat(16u);
v___x_412_ = l_Nat_toDigits(v___x_411_, v_x_410_);
v_s_413_ = lean_string_mk(v___x_412_);
v___x_414_ = lean_unsigned_to_nat(3u);
v___x_415_ = lean_nat_add(v_n_409_, v___x_414_);
v___x_416_ = lean_unsigned_to_nat(2u);
v___x_417_ = lean_nat_shiftr(v___x_415_, v___x_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_string_length(v_s_413_);
v___x_419_ = lean_nat_sub(v___x_417_, v___x_418_);
lean_dec(v___x_418_);
lean_dec(v___x_417_);
v___x_420_ = l_BitVec_toHex___boxed__const__1;
v___x_421_ = l_List_replicateTR___redArg(v___x_419_, v___x_420_);
v_t_422_ = lean_string_mk(v___x_421_);
v___x_423_ = lean_string_append(v_t_422_, v_s_413_);
lean_dec_ref(v_s_413_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_BitVec_toHex___boxed(lean_object* v_n_424_, lean_object* v_x_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_BitVec_toHex(v_n_424_, v_x_425_);
lean_dec(v_n_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_BitVec_repr(lean_object* v_n_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_434_ = ((lean_object*)(l_BitVec_repr___closed__1));
v___x_435_ = l_BitVec_toHex(v_n_432_, v_a_433_);
v___x_436_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
v___x_437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_434_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = ((lean_object*)(l_BitVec_repr___closed__2));
v___x_439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = l_Nat_reprFast(v_n_432_);
v___x_441_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
v___x_442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_439_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr___lam__0(lean_object* v_n_443_, lean_object* v_a_444_, lean_object* v_x_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_BitVec_repr(v_n_443_, v_a_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr___lam__0___boxed(lean_object* v_n_447_, lean_object* v_a_448_, lean_object* v_x_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_BitVec_instRepr___lam__0(v_n_447_, v_a_448_, v_x_449_);
lean_dec(v_x_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr(lean_object* v_n_451_){
_start:
{
lean_object* v___f_452_; 
v___f_452_ = lean_alloc_closure((void*)(l_BitVec_instRepr___lam__0___boxed), 3, 1);
lean_closure_set(v___f_452_, 0, v_n_451_);
return v___f_452_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instToString___lam__0(lean_object* v_n_453_, lean_object* v_a_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_455_ = l_BitVec_repr(v_n_453_, v_a_454_);
v___x_456_ = l_Std_Format_defWidth;
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = l_Std_Format_pretty(v___x_455_, v___x_456_, v___x_457_, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instToString(lean_object* v_n_459_){
_start:
{
lean_object* v___f_460_; 
v___f_460_ = lean_alloc_closure((void*)(l_BitVec_instToString___lam__0), 2, 1);
lean_closure_set(v___f_460_, 0, v_n_459_);
return v___f_460_;
}
}
LEAN_EXPORT lean_object* l_BitVec_neg(lean_object* v_n_461_, lean_object* v_x_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_463_ = lean_unsigned_to_nat(2u);
v___x_464_ = lean_nat_pow(v___x_463_, v_n_461_);
v___x_465_ = lean_nat_sub(v___x_464_, v_x_462_);
lean_dec(v___x_464_);
v___x_466_ = l_BitVec_ofNat(v_n_461_, v___x_465_);
lean_dec(v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_BitVec_neg___boxed(lean_object* v_n_467_, lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_BitVec_neg(v_n_467_, v_x_468_);
lean_dec(v_x_468_);
lean_dec(v_n_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instNeg(lean_object* v_n_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_alloc_closure((void*)(l_BitVec_neg___boxed), 2, 1);
lean_closure_set(v___x_471_, 0, v_n_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_BitVec_abs(lean_object* v_n_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_nat_dec_lt(v___x_474_, v_n_472_);
if (v___x_475_ == 0)
{
lean_inc(v_x_473_);
return v_x_473_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_sub(v_n_472_, v___x_476_);
v___x_478_ = l_Nat_testBit(v_x_473_, v___x_477_);
lean_dec(v___x_477_);
if (v___x_478_ == 0)
{
lean_inc(v_x_473_);
return v_x_473_;
}
else
{
lean_object* v___x_479_; 
v___x_479_ = l_BitVec_neg(v_n_472_, v_x_473_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_abs___boxed(lean_object* v_n_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_BitVec_abs(v_n_480_, v_x_481_);
lean_dec(v_x_481_);
lean_dec(v_n_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mul(lean_object* v_n_483_, lean_object* v_x_484_, lean_object* v_y_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_nat_mul(v_x_484_, v_y_485_);
v___x_487_ = l_BitVec_ofNat(v_n_483_, v___x_486_);
lean_dec(v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mul___boxed(lean_object* v_n_488_, lean_object* v_x_489_, lean_object* v_y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_BitVec_mul(v_n_488_, v_x_489_, v_y_490_);
lean_dec(v_y_490_);
lean_dec(v_x_489_);
lean_dec(v_n_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMul(lean_object* v_n_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = lean_alloc_closure((void*)(l_BitVec_mul___boxed), 3, 1);
lean_closure_set(v___x_493_, 0, v_n_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_BitVec_pow(lean_object* v_n_494_, lean_object* v_x_495_, lean_object* v_y_496_){
_start:
{
lean_object* v_zero_497_; uint8_t v_isZero_498_; 
v_zero_497_ = lean_unsigned_to_nat(0u);
v_isZero_498_ = lean_nat_dec_eq(v_y_496_, v_zero_497_);
if (v_isZero_498_ == 1)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = l_BitVec_ofNat(v_n_494_, v___x_499_);
return v___x_500_;
}
else
{
lean_object* v_one_501_; lean_object* v_n_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_one_501_ = lean_unsigned_to_nat(1u);
v_n_502_ = lean_nat_sub(v_y_496_, v_one_501_);
v___x_503_ = l_BitVec_pow(v_n_494_, v_x_495_, v_n_502_);
lean_dec(v_n_502_);
v___x_504_ = l_BitVec_mul(v_n_494_, v___x_503_, v_x_495_);
lean_dec(v___x_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_pow___boxed(lean_object* v_n_505_, lean_object* v_x_506_, lean_object* v_y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_BitVec_pow(v_n_505_, v_x_506_, v_y_507_);
lean_dec(v_y_507_);
lean_dec(v_x_506_);
lean_dec(v_n_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat___lam__0(lean_object* v_n_509_, lean_object* v_x_510_, lean_object* v_y_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_BitVec_pow(v_n_509_, v_x_510_, v_y_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat___lam__0___boxed(lean_object* v_n_513_, lean_object* v_x_514_, lean_object* v_y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_BitVec_instPowNat___lam__0(v_n_513_, v_x_514_, v_y_515_);
lean_dec(v_y_515_);
lean_dec(v_x_514_);
lean_dec(v_n_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat(lean_object* v_n_517_){
_start:
{
lean_object* v___f_518_; 
v___f_518_ = lean_alloc_closure((void*)(l_BitVec_instPowNat___lam__0___boxed), 3, 1);
lean_closure_set(v___f_518_, 0, v_n_517_);
return v___f_518_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___redArg(lean_object* v_x_519_, lean_object* v_y_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = lean_nat_div(v_x_519_, v_y_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___redArg___boxed(lean_object* v_x_522_, lean_object* v_y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_BitVec_udiv___redArg(v_x_522_, v_y_523_);
lean_dec(v_y_523_);
lean_dec(v_x_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv(lean_object* v_n_525_, lean_object* v_x_526_, lean_object* v_y_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_nat_div(v_x_526_, v_y_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___boxed(lean_object* v_n_529_, lean_object* v_x_530_, lean_object* v_y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_BitVec_udiv(v_n_529_, v_x_530_, v_y_531_);
lean_dec(v_y_531_);
lean_dec(v_x_530_);
lean_dec(v_n_529_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDiv(lean_object* v_n_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_closure((void*)(l_BitVec_udiv___boxed), 3, 1);
lean_closure_set(v___x_534_, 0, v_n_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___redArg(lean_object* v_x_535_, lean_object* v_y_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_nat_mod(v_x_535_, v_y_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___redArg___boxed(lean_object* v_x_538_, lean_object* v_y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_BitVec_umod___redArg(v_x_538_, v_y_539_);
lean_dec(v_y_539_);
lean_dec(v_x_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod(lean_object* v_n_541_, lean_object* v_x_542_, lean_object* v_y_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = lean_nat_mod(v_x_542_, v_y_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___boxed(lean_object* v_n_545_, lean_object* v_x_546_, lean_object* v_y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_BitVec_umod(v_n_545_, v_x_546_, v_y_547_);
lean_dec(v_y_547_);
lean_dec(v_x_546_);
lean_dec(v_n_545_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMod(lean_object* v_n_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_closure((void*)(l_BitVec_umod___boxed), 3, 1);
lean_closure_set(v___x_550_, 0, v_n_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtUDiv(lean_object* v_n_551_, lean_object* v_x_552_, lean_object* v_y_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = l_BitVec_ofNat(v_n_551_, v___x_554_);
v___x_556_ = lean_nat_dec_eq(v_y_553_, v___x_555_);
lean_dec(v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
v___x_557_ = lean_nat_div(v_x_552_, v_y_553_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; 
v___x_558_ = l_BitVec_allOnes(v_n_551_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtUDiv___boxed(lean_object* v_n_559_, lean_object* v_x_560_, lean_object* v_y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_BitVec_smtUDiv(v_n_559_, v_x_560_, v_y_561_);
lean_dec(v_y_561_);
lean_dec(v_x_560_);
lean_dec(v_n_559_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv(lean_object* v_n_563_, lean_object* v_x_564_, lean_object* v_y_565_){
_start:
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_nat_dec_lt(v___x_581_, v_n_563_);
if (v___x_582_ == 0)
{
goto v___jp_566_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_nat_sub(v_n_563_, v___x_583_);
v___x_585_ = l_Nat_testBit(v_x_564_, v___x_584_);
if (v___x_585_ == 0)
{
lean_dec(v___x_584_);
goto v___jp_566_;
}
else
{
if (v___x_582_ == 0)
{
lean_dec(v___x_584_);
goto v___jp_577_;
}
else
{
uint8_t v___x_586_; 
v___x_586_ = l_Nat_testBit(v_y_565_, v___x_584_);
lean_dec(v___x_584_);
if (v___x_586_ == 0)
{
goto v___jp_577_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = l_BitVec_neg(v_n_563_, v_x_564_);
v___x_588_ = l_BitVec_neg(v_n_563_, v_y_565_);
v___x_589_ = lean_nat_div(v___x_587_, v___x_588_);
lean_dec(v___x_588_);
lean_dec(v___x_587_);
return v___x_589_;
}
}
}
}
v___jp_566_:
{
lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_nat_dec_lt(v___x_567_, v_n_563_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
v___x_569_ = lean_nat_div(v_x_564_, v_y_565_);
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_sub(v_n_563_, v___x_570_);
v___x_572_ = l_Nat_testBit(v_y_565_, v___x_571_);
lean_dec(v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
v___x_573_ = lean_nat_div(v_x_564_, v_y_565_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = l_BitVec_neg(v_n_563_, v_y_565_);
v___x_575_ = lean_nat_div(v_x_564_, v___x_574_);
lean_dec(v___x_574_);
v___x_576_ = l_BitVec_neg(v_n_563_, v___x_575_);
lean_dec(v___x_575_);
return v___x_576_;
}
}
}
v___jp_577_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = l_BitVec_neg(v_n_563_, v_x_564_);
v___x_579_ = lean_nat_div(v___x_578_, v_y_565_);
lean_dec(v___x_578_);
v___x_580_ = l_BitVec_neg(v_n_563_, v___x_579_);
lean_dec(v___x_579_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv___boxed(lean_object* v_n_590_, lean_object* v_x_591_, lean_object* v_y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_BitVec_sdiv(v_n_590_, v_x_591_, v_y_592_);
lean_dec(v_y_592_);
lean_dec(v_x_591_);
lean_dec(v_n_590_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv(lean_object* v_n_594_, lean_object* v_x_595_, lean_object* v_y_596_){
_start:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_nat_dec_lt(v___x_612_, v_n_594_);
if (v___x_613_ == 0)
{
goto v___jp_597_;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_nat_sub(v_n_594_, v___x_614_);
v___x_616_ = l_Nat_testBit(v_x_595_, v___x_615_);
if (v___x_616_ == 0)
{
lean_dec(v___x_615_);
goto v___jp_597_;
}
else
{
if (v___x_613_ == 0)
{
lean_dec(v___x_615_);
goto v___jp_608_;
}
else
{
uint8_t v___x_617_; 
v___x_617_ = l_Nat_testBit(v_y_596_, v___x_615_);
lean_dec(v___x_615_);
if (v___x_617_ == 0)
{
goto v___jp_608_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = l_BitVec_neg(v_n_594_, v_x_595_);
v___x_619_ = l_BitVec_neg(v_n_594_, v_y_596_);
v___x_620_ = l_BitVec_smtUDiv(v_n_594_, v___x_618_, v___x_619_);
lean_dec(v___x_619_);
lean_dec(v___x_618_);
return v___x_620_;
}
}
}
}
v___jp_597_:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = lean_nat_dec_lt(v___x_598_, v_n_594_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = l_BitVec_smtUDiv(v_n_594_, v_x_595_, v_y_596_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_nat_sub(v_n_594_, v___x_601_);
v___x_603_ = l_Nat_testBit(v_y_596_, v___x_602_);
lean_dec(v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = l_BitVec_smtUDiv(v_n_594_, v_x_595_, v_y_596_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = l_BitVec_neg(v_n_594_, v_y_596_);
v___x_606_ = l_BitVec_smtUDiv(v_n_594_, v_x_595_, v___x_605_);
lean_dec(v___x_605_);
v___x_607_ = l_BitVec_neg(v_n_594_, v___x_606_);
lean_dec(v___x_606_);
return v___x_607_;
}
}
}
v___jp_608_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = l_BitVec_neg(v_n_594_, v_x_595_);
v___x_610_ = l_BitVec_smtUDiv(v_n_594_, v___x_609_, v_y_596_);
lean_dec(v___x_609_);
v___x_611_ = l_BitVec_neg(v_n_594_, v___x_610_);
lean_dec(v___x_610_);
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv___boxed(lean_object* v_n_621_, lean_object* v_x_622_, lean_object* v_y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_BitVec_smtSDiv(v_n_621_, v_x_622_, v_y_623_);
lean_dec(v_y_623_);
lean_dec(v_x_622_);
lean_dec(v_n_621_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_BitVec_srem(lean_object* v_n_625_, lean_object* v_x_626_, lean_object* v_y_627_){
_start:
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_nat_dec_lt(v___x_642_, v_n_625_);
if (v___x_643_ == 0)
{
goto v___jp_628_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_sub(v_n_625_, v___x_644_);
v___x_646_ = l_Nat_testBit(v_x_626_, v___x_645_);
if (v___x_646_ == 0)
{
lean_dec(v___x_645_);
goto v___jp_628_;
}
else
{
if (v___x_643_ == 0)
{
lean_dec(v___x_645_);
goto v___jp_638_;
}
else
{
uint8_t v___x_647_; 
v___x_647_ = l_Nat_testBit(v_y_627_, v___x_645_);
lean_dec(v___x_645_);
if (v___x_647_ == 0)
{
goto v___jp_638_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = l_BitVec_neg(v_n_625_, v_x_626_);
v___x_649_ = l_BitVec_neg(v_n_625_, v_y_627_);
v___x_650_ = lean_nat_mod(v___x_648_, v___x_649_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
v___x_651_ = l_BitVec_neg(v_n_625_, v___x_650_);
lean_dec(v___x_650_);
return v___x_651_;
}
}
}
}
v___jp_628_:
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_nat_dec_lt(v___x_629_, v_n_625_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
v___x_631_ = lean_nat_mod(v_x_626_, v_y_627_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_sub(v_n_625_, v___x_632_);
v___x_634_ = l_Nat_testBit(v_y_627_, v___x_633_);
lean_dec(v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = lean_nat_mod(v_x_626_, v_y_627_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = l_BitVec_neg(v_n_625_, v_y_627_);
v___x_637_ = lean_nat_mod(v_x_626_, v___x_636_);
lean_dec(v___x_636_);
return v___x_637_;
}
}
}
v___jp_638_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = l_BitVec_neg(v_n_625_, v_x_626_);
v___x_640_ = lean_nat_mod(v___x_639_, v_y_627_);
lean_dec(v___x_639_);
v___x_641_ = l_BitVec_neg(v_n_625_, v___x_640_);
lean_dec(v___x_640_);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_srem___boxed(lean_object* v_n_652_, lean_object* v_x_653_, lean_object* v_y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_BitVec_srem(v_n_652_, v_x_653_, v_y_654_);
lean_dec(v_y_654_);
lean_dec(v_x_653_);
lean_dec(v_n_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smod(lean_object* v_m_656_, lean_object* v_x_657_, lean_object* v_y_658_){
_start:
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_nat_dec_lt(v___x_677_, v_m_656_);
if (v___x_678_ == 0)
{
goto v___jp_659_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_sub(v_m_656_, v___x_679_);
v___x_681_ = l_Nat_testBit(v_x_657_, v___x_680_);
if (v___x_681_ == 0)
{
lean_dec(v___x_680_);
goto v___jp_659_;
}
else
{
if (v___x_678_ == 0)
{
lean_dec(v___x_680_);
goto v___jp_671_;
}
else
{
uint8_t v___x_682_; 
v___x_682_ = l_Nat_testBit(v_y_658_, v___x_680_);
lean_dec(v___x_680_);
if (v___x_682_ == 0)
{
goto v___jp_671_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = l_BitVec_neg(v_m_656_, v_x_657_);
v___x_684_ = l_BitVec_neg(v_m_656_, v_y_658_);
v___x_685_ = lean_nat_mod(v___x_683_, v___x_684_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
v___x_686_ = l_BitVec_neg(v_m_656_, v___x_685_);
lean_dec(v___x_685_);
return v___x_686_;
}
}
}
}
v___jp_659_:
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_nat_dec_lt(v___x_660_, v_m_656_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = lean_nat_mod(v_x_657_, v_y_658_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_sub(v_m_656_, v___x_663_);
v___x_665_ = l_Nat_testBit(v_y_658_, v___x_664_);
lean_dec(v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
v___x_666_ = lean_nat_mod(v_x_657_, v_y_658_);
return v___x_666_;
}
else
{
lean_object* v___x_667_; lean_object* v_u_668_; uint8_t v___x_669_; 
v___x_667_ = l_BitVec_neg(v_m_656_, v_y_658_);
v_u_668_ = lean_nat_mod(v_x_657_, v___x_667_);
lean_dec(v___x_667_);
v___x_669_ = lean_nat_dec_eq(v_u_668_, v___x_660_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = l_BitVec_add(v_m_656_, v_u_668_, v_y_658_);
lean_dec(v_u_668_);
return v___x_670_;
}
else
{
return v_u_668_;
}
}
}
}
v___jp_671_:
{
lean_object* v___x_672_; lean_object* v_u_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_672_ = l_BitVec_neg(v_m_656_, v_x_657_);
v_u_673_ = lean_nat_mod(v___x_672_, v_y_658_);
lean_dec(v___x_672_);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_nat_dec_eq(v_u_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = l_BitVec_sub(v_m_656_, v_y_658_, v_u_673_);
lean_dec(v_u_673_);
return v___x_676_;
}
else
{
return v_u_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smod___boxed(lean_object* v_m_687_, lean_object* v_x_688_, lean_object* v_y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_BitVec_smod(v_m_687_, v_x_688_, v_y_689_);
lean_dec(v_y_689_);
lean_dec(v_x_688_);
lean_dec(v_m_687_);
return v_res_690_;
}
}
static lean_object* _init_l_BitVec_ofBool___closed__0(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = l_BitVec_ofNat(v___x_692_, v___x_691_);
return v___x_693_;
}
}
static lean_object* _init_l_BitVec_ofBool___closed__1(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = l_BitVec_ofNat(v___x_694_, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBool(uint8_t v_b_696_){
_start:
{
if (v_b_696_ == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_obj_once(&l_BitVec_ofBool___closed__0, &l_BitVec_ofBool___closed__0_once, _init_l_BitVec_ofBool___closed__0);
return v___x_697_;
}
else
{
lean_object* v___x_698_; 
v___x_698_ = lean_obj_once(&l_BitVec_ofBool___closed__1, &l_BitVec_ofBool___closed__1_once, _init_l_BitVec_ofBool___closed__1);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBool___boxed(lean_object* v_b_699_){
_start:
{
uint8_t v_b_boxed_700_; lean_object* v_res_701_; 
v_b_boxed_700_ = lean_unbox(v_b_699_);
v_res_701_ = l_BitVec_ofBool(v_b_boxed_700_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_BitVec_fill(lean_object* v_w_702_, uint8_t v_b_703_){
_start:
{
if (v_b_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = l_BitVec_ofNat(v_w_702_, v___x_704_);
return v___x_705_;
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = l_BitVec_ofNat(v_w_702_, v___x_706_);
v___x_708_ = l_BitVec_neg(v_w_702_, v___x_707_);
lean_dec(v___x_707_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_fill___boxed(lean_object* v_w_709_, lean_object* v_b_710_){
_start:
{
uint8_t v_b_boxed_711_; lean_object* v_res_712_; 
v_b_boxed_711_ = lean_unbox(v_b_710_);
v_res_712_ = l_BitVec_fill(v_w_709_, v_b_boxed_711_);
lean_dec(v_w_709_);
return v_res_712_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ult___redArg(lean_object* v_x_713_, lean_object* v_y_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_nat_dec_lt(v_x_713_, v_y_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult___redArg___boxed(lean_object* v_x_716_, lean_object* v_y_717_){
_start:
{
uint8_t v_res_718_; lean_object* v_r_719_; 
v_res_718_ = l_BitVec_ult___redArg(v_x_716_, v_y_717_);
lean_dec(v_y_717_);
lean_dec(v_x_716_);
v_r_719_ = lean_box(v_res_718_);
return v_r_719_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ult(lean_object* v_n_720_, lean_object* v_x_721_, lean_object* v_y_722_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = lean_nat_dec_lt(v_x_721_, v_y_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult___boxed(lean_object* v_n_724_, lean_object* v_x_725_, lean_object* v_y_726_){
_start:
{
uint8_t v_res_727_; lean_object* v_r_728_; 
v_res_727_ = l_BitVec_ult(v_n_724_, v_x_725_, v_y_726_);
lean_dec(v_y_726_);
lean_dec(v_x_725_);
lean_dec(v_n_724_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ule___redArg(lean_object* v_x_729_, lean_object* v_y_730_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_nat_dec_le(v_x_729_, v_y_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule___redArg___boxed(lean_object* v_x_732_, lean_object* v_y_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_BitVec_ule___redArg(v_x_732_, v_y_733_);
lean_dec(v_y_733_);
lean_dec(v_x_732_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ule(lean_object* v_n_736_, lean_object* v_x_737_, lean_object* v_y_738_){
_start:
{
uint8_t v___x_739_; 
v___x_739_ = lean_nat_dec_le(v_x_737_, v_y_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule___boxed(lean_object* v_n_740_, lean_object* v_x_741_, lean_object* v_y_742_){
_start:
{
uint8_t v_res_743_; lean_object* v_r_744_; 
v_res_743_ = l_BitVec_ule(v_n_740_, v_x_741_, v_y_742_);
lean_dec(v_y_742_);
lean_dec(v_x_741_);
lean_dec(v_n_740_);
v_r_744_ = lean_box(v_res_743_);
return v_r_744_;
}
}
LEAN_EXPORT uint8_t l_BitVec_slt(lean_object* v_n_745_, lean_object* v_x_746_, lean_object* v_y_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = l_BitVec_toInt(v_n_745_, v_x_746_);
v___x_749_ = l_BitVec_toInt(v_n_745_, v_y_747_);
v___x_750_ = lean_int_dec_lt(v___x_748_, v___x_749_);
lean_dec(v___x_749_);
lean_dec(v___x_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_BitVec_slt___boxed(lean_object* v_n_751_, lean_object* v_x_752_, lean_object* v_y_753_){
_start:
{
uint8_t v_res_754_; lean_object* v_r_755_; 
v_res_754_ = l_BitVec_slt(v_n_751_, v_x_752_, v_y_753_);
lean_dec(v_n_751_);
v_r_755_ = lean_box(v_res_754_);
return v_r_755_;
}
}
LEAN_EXPORT uint8_t l_BitVec_sle(lean_object* v_n_756_, lean_object* v_x_757_, lean_object* v_y_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_759_ = l_BitVec_toInt(v_n_756_, v_x_757_);
v___x_760_ = l_BitVec_toInt(v_n_756_, v_y_758_);
v___x_761_ = lean_int_dec_le(v___x_759_, v___x_760_);
lean_dec(v___x_760_);
lean_dec(v___x_759_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sle___boxed(lean_object* v_n_762_, lean_object* v_x_763_, lean_object* v_y_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_BitVec_sle(v_n_762_, v_x_763_, v_y_764_);
lean_dec(v_n_762_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___redArg(lean_object* v_x_767_){
_start:
{
lean_inc(v_x_767_);
return v_x_767_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___redArg___boxed(lean_object* v_x_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_BitVec_cast___redArg(v_x_768_);
lean_dec(v_x_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast(lean_object* v_n_770_, lean_object* v_m_771_, lean_object* v_eq_772_, lean_object* v_x_773_){
_start:
{
lean_inc(v_x_773_);
return v_x_773_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___boxed(lean_object* v_n_774_, lean_object* v_m_775_, lean_object* v_eq_776_, lean_object* v_x_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_BitVec_cast(v_n_774_, v_m_775_, v_eq_776_, v_x_777_);
lean_dec(v_x_777_);
lean_dec(v_m_775_);
lean_dec(v_n_774_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___redArg(lean_object* v_start_779_, lean_object* v_len_780_, lean_object* v_x_781_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_nat_shiftr(v_x_781_, v_start_779_);
v___x_783_ = l_BitVec_ofNat(v_len_780_, v___x_782_);
lean_dec(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___redArg___boxed(lean_object* v_start_784_, lean_object* v_len_785_, lean_object* v_x_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_BitVec_extractLsb_x27___redArg(v_start_784_, v_len_785_, v_x_786_);
lean_dec(v_x_786_);
lean_dec(v_len_785_);
lean_dec(v_start_784_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27(lean_object* v_n_788_, lean_object* v_start_789_, lean_object* v_len_790_, lean_object* v_x_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_BitVec_extractLsb_x27___redArg(v_start_789_, v_len_790_, v_x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___boxed(lean_object* v_n_793_, lean_object* v_start_794_, lean_object* v_len_795_, lean_object* v_x_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_BitVec_extractLsb_x27(v_n_793_, v_start_794_, v_len_795_, v_x_796_);
lean_dec(v_x_796_);
lean_dec(v_len_795_);
lean_dec(v_start_794_);
lean_dec(v_n_793_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___redArg(lean_object* v_hi_798_, lean_object* v_lo_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_801_ = lean_nat_sub(v_hi_798_, v_lo_799_);
v___x_802_ = lean_unsigned_to_nat(1u);
v___x_803_ = lean_nat_add(v___x_801_, v___x_802_);
lean_dec(v___x_801_);
v___x_804_ = l_BitVec_extractLsb_x27___redArg(v_lo_799_, v___x_803_, v_x_800_);
lean_dec(v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___redArg___boxed(lean_object* v_hi_805_, lean_object* v_lo_806_, lean_object* v_x_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_BitVec_extractLsb___redArg(v_hi_805_, v_lo_806_, v_x_807_);
lean_dec(v_x_807_);
lean_dec(v_lo_806_);
lean_dec(v_hi_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb(lean_object* v_n_809_, lean_object* v_hi_810_, lean_object* v_lo_811_, lean_object* v_x_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_BitVec_extractLsb___redArg(v_hi_810_, v_lo_811_, v_x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___boxed(lean_object* v_n_814_, lean_object* v_hi_815_, lean_object* v_lo_816_, lean_object* v_x_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_BitVec_extractLsb(v_n_814_, v_hi_815_, v_lo_816_, v_x_817_);
lean_dec(v_x_817_);
lean_dec(v_lo_816_);
lean_dec(v_hi_815_);
lean_dec(v_n_814_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___redArg(lean_object* v_x_819_){
_start:
{
lean_inc(v_x_819_);
return v_x_819_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___redArg___boxed(lean_object* v_x_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_BitVec_setWidth_x27___redArg(v_x_820_);
lean_dec(v_x_820_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27(lean_object* v_n_822_, lean_object* v_w_823_, lean_object* v_le_824_, lean_object* v_x_825_){
_start:
{
lean_inc(v_x_825_);
return v_x_825_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___boxed(lean_object* v_n_826_, lean_object* v_w_827_, lean_object* v_le_828_, lean_object* v_x_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_BitVec_setWidth_x27(v_n_826_, v_w_827_, v_le_828_, v_x_829_);
lean_dec(v_x_829_);
lean_dec(v_w_827_);
lean_dec(v_n_826_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___redArg(lean_object* v_msbs_831_, lean_object* v_m_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = lean_nat_shiftl(v_msbs_831_, v_m_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___redArg___boxed(lean_object* v_msbs_834_, lean_object* v_m_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_BitVec_shiftLeftZeroExtend___redArg(v_msbs_834_, v_m_835_);
lean_dec(v_m_835_);
lean_dec(v_msbs_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend(lean_object* v_w_837_, lean_object* v_msbs_838_, lean_object* v_m_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_nat_shiftl(v_msbs_838_, v_m_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___boxed(lean_object* v_w_841_, lean_object* v_msbs_842_, lean_object* v_m_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_BitVec_shiftLeftZeroExtend(v_w_841_, v_msbs_842_, v_m_843_);
lean_dec(v_m_843_);
lean_dec(v_msbs_842_);
lean_dec(v_w_841_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth(lean_object* v_w_845_, lean_object* v_v_846_, lean_object* v_x_847_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = lean_nat_dec_le(v_w_845_, v_v_846_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
v___x_849_ = l_BitVec_ofNat(v_v_846_, v_x_847_);
return v___x_849_;
}
else
{
lean_inc(v_x_847_);
return v_x_847_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth___boxed(lean_object* v_w_850_, lean_object* v_v_851_, lean_object* v_x_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_BitVec_setWidth(v_w_850_, v_v_851_, v_x_852_);
lean_dec(v_x_852_);
lean_dec(v_v_851_);
lean_dec(v_w_850_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zeroExtend(lean_object* v_w_854_, lean_object* v_v_855_, lean_object* v_x_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_BitVec_setWidth(v_w_854_, v_v_855_, v_x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zeroExtend___boxed(lean_object* v_w_858_, lean_object* v_v_859_, lean_object* v_x_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_BitVec_zeroExtend(v_w_858_, v_v_859_, v_x_860_);
lean_dec(v_x_860_);
lean_dec(v_v_859_);
lean_dec(v_w_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_BitVec_truncate(lean_object* v_w_862_, lean_object* v_v_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_BitVec_setWidth(v_w_862_, v_v_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_BitVec_truncate___boxed(lean_object* v_w_866_, lean_object* v_v_867_, lean_object* v_x_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_BitVec_truncate(v_w_866_, v_v_867_, v_x_868_);
lean_dec(v_x_868_);
lean_dec(v_v_867_);
lean_dec(v_w_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_BitVec_signExtend(lean_object* v_w_870_, lean_object* v_v_871_, lean_object* v_x_872_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = l_BitVec_toInt(v_w_870_, v_x_872_);
v___x_874_ = l_BitVec_ofInt(v_v_871_, v___x_873_);
lean_dec(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_BitVec_signExtend___boxed(lean_object* v_w_875_, lean_object* v_v_876_, lean_object* v_x_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_BitVec_signExtend(v_w_875_, v_v_876_, v_x_877_);
lean_dec(v_v_876_);
lean_dec(v_w_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___redArg(lean_object* v_x_879_, lean_object* v_y_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = lean_nat_land(v_x_879_, v_y_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___redArg___boxed(lean_object* v_x_882_, lean_object* v_y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_BitVec_and___redArg(v_x_882_, v_y_883_);
lean_dec(v_y_883_);
lean_dec(v_x_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and(lean_object* v_n_885_, lean_object* v_x_886_, lean_object* v_y_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_nat_land(v_x_886_, v_y_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___boxed(lean_object* v_n_889_, lean_object* v_x_890_, lean_object* v_y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_BitVec_and(v_n_889_, v_x_890_, v_y_891_);
lean_dec(v_y_891_);
lean_dec(v_x_890_);
lean_dec(v_n_889_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instAndOp(lean_object* v_w_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lean_alloc_closure((void*)(l_BitVec_and___boxed), 3, 1);
lean_closure_set(v___x_894_, 0, v_w_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___redArg(lean_object* v_x_895_, lean_object* v_y_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = lean_nat_lor(v_x_895_, v_y_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___redArg___boxed(lean_object* v_x_898_, lean_object* v_y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_BitVec_or___redArg(v_x_898_, v_y_899_);
lean_dec(v_y_899_);
lean_dec(v_x_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or(lean_object* v_n_901_, lean_object* v_x_902_, lean_object* v_y_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_nat_lor(v_x_902_, v_y_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___boxed(lean_object* v_n_905_, lean_object* v_x_906_, lean_object* v_y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_BitVec_or(v_n_905_, v_x_906_, v_y_907_);
lean_dec(v_y_907_);
lean_dec(v_x_906_);
lean_dec(v_n_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instOrOp(lean_object* v_w_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = lean_alloc_closure((void*)(l_BitVec_or___boxed), 3, 1);
lean_closure_set(v___x_910_, 0, v_w_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___redArg(lean_object* v_x_911_, lean_object* v_y_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = lean_nat_lxor(v_x_911_, v_y_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___redArg___boxed(lean_object* v_x_914_, lean_object* v_y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_BitVec_xor___redArg(v_x_914_, v_y_915_);
lean_dec(v_y_915_);
lean_dec(v_x_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor(lean_object* v_n_917_, lean_object* v_x_918_, lean_object* v_y_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = lean_nat_lxor(v_x_918_, v_y_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___boxed(lean_object* v_n_921_, lean_object* v_x_922_, lean_object* v_y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_BitVec_xor(v_n_921_, v_x_922_, v_y_923_);
lean_dec(v_y_923_);
lean_dec(v_x_922_);
lean_dec(v_n_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instXorOp(lean_object* v_w_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = lean_alloc_closure((void*)(l_BitVec_xor___boxed), 3, 1);
lean_closure_set(v___x_926_, 0, v_w_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_BitVec_not(lean_object* v_n_927_, lean_object* v_x_928_){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = l_BitVec_allOnes(v_n_927_);
v___x_930_ = lean_nat_lxor(v___x_929_, v_x_928_);
lean_dec(v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_BitVec_not___boxed(lean_object* v_n_931_, lean_object* v_x_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_BitVec_not(v_n_931_, v_x_932_);
lean_dec(v_x_932_);
lean_dec(v_n_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instComplement(lean_object* v_w_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_closure((void*)(l_BitVec_not___boxed), 2, 1);
lean_closure_set(v___x_935_, 0, v_w_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeft(lean_object* v_n_936_, lean_object* v_x_937_, lean_object* v_s_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_nat_shiftl(v_x_937_, v_s_938_);
v___x_940_ = l_BitVec_ofNat(v_n_936_, v___x_939_);
lean_dec(v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeft___boxed(lean_object* v_n_941_, lean_object* v_x_942_, lean_object* v_s_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_BitVec_shiftLeft(v_n_941_, v_x_942_, v_s_943_);
lean_dec(v_s_943_);
lean_dec(v_x_942_);
lean_dec(v_n_941_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeftNat(lean_object* v_w_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_closure((void*)(l_BitVec_shiftLeft___boxed), 3, 1);
lean_closure_set(v___x_946_, 0, v_w_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___redArg(lean_object* v_x_947_, lean_object* v_s_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = lean_nat_shiftr(v_x_947_, v_s_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___redArg___boxed(lean_object* v_x_950_, lean_object* v_s_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_BitVec_ushiftRight___redArg(v_x_950_, v_s_951_);
lean_dec(v_s_951_);
lean_dec(v_x_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight(lean_object* v_n_953_, lean_object* v_x_954_, lean_object* v_s_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = lean_nat_shiftr(v_x_954_, v_s_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___boxed(lean_object* v_n_957_, lean_object* v_x_958_, lean_object* v_s_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_BitVec_ushiftRight(v_n_957_, v_x_958_, v_s_959_);
lean_dec(v_s_959_);
lean_dec(v_x_958_);
lean_dec(v_n_957_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRightNat(lean_object* v_w_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_closure((void*)(l_BitVec_ushiftRight___boxed), 3, 1);
lean_closure_set(v___x_962_, 0, v_w_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight(lean_object* v_n_963_, lean_object* v_x_964_, lean_object* v_s_965_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = l_BitVec_toInt(v_n_963_, v_x_964_);
v___x_967_ = l_Int_shiftRight(v___x_966_, v_s_965_);
lean_dec(v___x_966_);
v___x_968_ = l_BitVec_ofInt(v_n_963_, v___x_967_);
lean_dec(v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight___boxed(lean_object* v_n_969_, lean_object* v_x_970_, lean_object* v_s_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_BitVec_sshiftRight(v_n_969_, v_x_970_, v_s_971_);
lean_dec(v_s_971_);
lean_dec(v_n_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg___lam__0(lean_object* v_m_973_, lean_object* v_x_974_, lean_object* v_y_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_BitVec_shiftLeft(v_m_973_, v_x_974_, v_y_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg___lam__0___boxed(lean_object* v_m_977_, lean_object* v_x_978_, lean_object* v_y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_BitVec_instHShiftLeft___redArg___lam__0(v_m_977_, v_x_978_, v_y_979_);
lean_dec(v_y_979_);
lean_dec(v_x_978_);
lean_dec(v_m_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg(lean_object* v_m_981_){
_start:
{
lean_object* v___f_982_; 
v___f_982_ = lean_alloc_closure((void*)(l_BitVec_instHShiftLeft___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_982_, 0, v_m_981_);
return v___f_982_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft(lean_object* v_m_983_, lean_object* v_n_984_){
_start:
{
lean_object* v___f_985_; 
v___f_985_ = lean_alloc_closure((void*)(l_BitVec_instHShiftLeft___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_985_, 0, v_m_983_);
return v___f_985_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___boxed(lean_object* v_m_986_, lean_object* v_n_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_BitVec_instHShiftLeft(v_m_986_, v_n_987_);
lean_dec(v_n_987_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___redArg(){
_start:
{
lean_object* v___f_991_; 
v___f_991_ = ((lean_object*)(l_BitVec_instHShiftRight___redArg___closed__0));
return v___f_991_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___redArg___boxed(lean_object* v___dummy_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_BitVec_instHShiftRight___redArg();
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight(lean_object* v_m_994_, lean_object* v_n_995_){
_start:
{
lean_object* v___f_996_; 
v___f_996_ = ((lean_object*)(l_BitVec_instHShiftRight___redArg___closed__0));
return v___f_996_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___boxed(lean_object* v_m_997_, lean_object* v_n_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_BitVec_instHShiftRight(v_m_997_, v_n_998_);
lean_dec(v_n_998_);
lean_dec(v_m_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg(lean_object* v_n_1000_, lean_object* v_a_1001_, lean_object* v_s_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_BitVec_sshiftRight(v_n_1000_, v_a_1001_, v_s_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg___boxed(lean_object* v_n_1004_, lean_object* v_a_1005_, lean_object* v_s_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_BitVec_sshiftRight_x27___redArg(v_n_1004_, v_a_1005_, v_s_1006_);
lean_dec(v_s_1006_);
lean_dec(v_n_1004_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27(lean_object* v_n_1008_, lean_object* v_m_1009_, lean_object* v_a_1010_, lean_object* v_s_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_BitVec_sshiftRight(v_n_1008_, v_a_1010_, v_s_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___boxed(lean_object* v_n_1013_, lean_object* v_m_1014_, lean_object* v_a_1015_, lean_object* v_s_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_BitVec_sshiftRight_x27(v_n_1013_, v_m_1014_, v_a_1015_, v_s_1016_);
lean_dec(v_s_1016_);
lean_dec(v_m_1014_);
lean_dec(v_n_1013_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux(lean_object* v_w_1018_, lean_object* v_x_1019_, lean_object* v_n_1020_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1021_ = l_BitVec_shiftLeft(v_w_1018_, v_x_1019_, v_n_1020_);
v___x_1022_ = lean_nat_sub(v_w_1018_, v_n_1020_);
v___x_1023_ = lean_nat_shiftr(v_x_1019_, v___x_1022_);
lean_dec(v___x_1022_);
v___x_1024_ = lean_nat_lor(v___x_1021_, v___x_1023_);
lean_dec(v___x_1023_);
lean_dec(v___x_1021_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux___boxed(lean_object* v_w_1025_, lean_object* v_x_1026_, lean_object* v_n_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_BitVec_rotateLeftAux(v_w_1025_, v_x_1026_, v_n_1027_);
lean_dec(v_n_1027_);
lean_dec(v_x_1026_);
lean_dec(v_w_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft(lean_object* v_w_1029_, lean_object* v_x_1030_, lean_object* v_n_1031_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_nat_mod(v_n_1031_, v_w_1029_);
v___x_1033_ = l_BitVec_rotateLeftAux(v_w_1029_, v_x_1030_, v___x_1032_);
lean_dec(v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft___boxed(lean_object* v_w_1034_, lean_object* v_x_1035_, lean_object* v_n_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_BitVec_rotateLeft(v_w_1034_, v_x_1035_, v_n_1036_);
lean_dec(v_n_1036_);
lean_dec(v_x_1035_);
lean_dec(v_w_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux(lean_object* v_w_1038_, lean_object* v_x_1039_, lean_object* v_n_1040_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1041_ = lean_nat_shiftr(v_x_1039_, v_n_1040_);
v___x_1042_ = lean_nat_sub(v_w_1038_, v_n_1040_);
v___x_1043_ = l_BitVec_shiftLeft(v_w_1038_, v_x_1039_, v___x_1042_);
lean_dec(v___x_1042_);
v___x_1044_ = lean_nat_lor(v___x_1041_, v___x_1043_);
lean_dec(v___x_1043_);
lean_dec(v___x_1041_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux___boxed(lean_object* v_w_1045_, lean_object* v_x_1046_, lean_object* v_n_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_BitVec_rotateRightAux(v_w_1045_, v_x_1046_, v_n_1047_);
lean_dec(v_n_1047_);
lean_dec(v_x_1046_);
lean_dec(v_w_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight(lean_object* v_w_1049_, lean_object* v_x_1050_, lean_object* v_n_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_nat_mod(v_n_1051_, v_w_1049_);
v___x_1053_ = l_BitVec_rotateRightAux(v_w_1049_, v_x_1050_, v___x_1052_);
lean_dec(v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight___boxed(lean_object* v_w_1054_, lean_object* v_x_1055_, lean_object* v_n_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_BitVec_rotateRight(v_w_1054_, v_x_1055_, v_n_1056_);
lean_dec(v_n_1056_);
lean_dec(v_x_1055_);
lean_dec(v_w_1054_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___redArg(lean_object* v_m_1058_, lean_object* v_msbs_1059_, lean_object* v_lsbs_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_nat_shiftl(v_msbs_1059_, v_m_1058_);
v___x_1062_ = lean_nat_lor(v___x_1061_, v_lsbs_1060_);
lean_dec(v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___redArg___boxed(lean_object* v_m_1063_, lean_object* v_msbs_1064_, lean_object* v_lsbs_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_BitVec_append___redArg(v_m_1063_, v_msbs_1064_, v_lsbs_1065_);
lean_dec(v_lsbs_1065_);
lean_dec(v_msbs_1064_);
lean_dec(v_m_1063_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append(lean_object* v_n_1067_, lean_object* v_m_1068_, lean_object* v_msbs_1069_, lean_object* v_lsbs_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_BitVec_append___redArg(v_m_1068_, v_msbs_1069_, v_lsbs_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___boxed(lean_object* v_n_1072_, lean_object* v_m_1073_, lean_object* v_msbs_1074_, lean_object* v_lsbs_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_BitVec_append(v_n_1072_, v_m_1073_, v_msbs_1074_, v_lsbs_1075_);
lean_dec(v_lsbs_1075_);
lean_dec(v_msbs_1074_);
lean_dec(v_m_1073_);
lean_dec(v_n_1072_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat(lean_object* v_w_1077_, lean_object* v_v_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_closure((void*)(l_BitVec_append___boxed), 4, 2);
lean_closure_set(v___x_1079_, 0, v_w_1077_);
lean_closure_set(v___x_1079_, 1, v_v_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate(lean_object* v_w_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
lean_object* v_zero_1083_; uint8_t v_isZero_1084_; 
v_zero_1083_ = lean_unsigned_to_nat(0u);
v_isZero_1084_ = lean_nat_dec_eq(v_x_1081_, v_zero_1083_);
if (v_isZero_1084_ == 1)
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1085_;
}
else
{
lean_object* v_one_1086_; lean_object* v_n_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_one_1086_ = lean_unsigned_to_nat(1u);
v_n_1087_ = lean_nat_sub(v_x_1081_, v_one_1086_);
v___x_1088_ = lean_nat_mul(v_w_1080_, v_n_1087_);
v___x_1089_ = l_BitVec_replicate(v_w_1080_, v_n_1087_, v_x_1082_);
lean_dec(v_n_1087_);
v___x_1090_ = l_BitVec_append___redArg(v___x_1088_, v_x_1082_, v___x_1089_);
lean_dec(v___x_1089_);
lean_dec(v___x_1088_);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate___boxed(lean_object* v_w_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_BitVec_replicate(v_w_1091_, v_x_1092_, v_x_1093_);
lean_dec(v_x_1093_);
lean_dec(v_x_1092_);
lean_dec(v_w_1091_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___redArg(lean_object* v_msbs_1095_, uint8_t v_lsb_1096_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = lean_unsigned_to_nat(1u);
v___x_1098_ = l_BitVec_ofBool(v_lsb_1096_);
v___x_1099_ = l_BitVec_append___redArg(v___x_1097_, v_msbs_1095_, v___x_1098_);
lean_dec(v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___redArg___boxed(lean_object* v_msbs_1100_, lean_object* v_lsb_1101_){
_start:
{
uint8_t v_lsb_boxed_1102_; lean_object* v_res_1103_; 
v_lsb_boxed_1102_ = lean_unbox(v_lsb_1101_);
v_res_1103_ = l_BitVec_concat___redArg(v_msbs_1100_, v_lsb_boxed_1102_);
lean_dec(v_msbs_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat(lean_object* v_n_1104_, lean_object* v_msbs_1105_, uint8_t v_lsb_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_BitVec_concat___redArg(v_msbs_1105_, v_lsb_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___boxed(lean_object* v_n_1108_, lean_object* v_msbs_1109_, lean_object* v_lsb_1110_){
_start:
{
uint8_t v_lsb_boxed_1111_; lean_object* v_res_1112_; 
v_lsb_boxed_1111_ = lean_unbox(v_lsb_1110_);
v_res_1112_ = l_BitVec_concat(v_n_1108_, v_msbs_1109_, v_lsb_boxed_1111_);
lean_dec(v_msbs_1109_);
lean_dec(v_n_1108_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat(lean_object* v_n_1113_, lean_object* v_x_1114_, uint8_t v_b_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_nat_add(v_n_1113_, v___x_1116_);
v___x_1118_ = l_BitVec_concat___redArg(v_x_1114_, v_b_1115_);
v___x_1119_ = l_BitVec_setWidth(v___x_1117_, v_n_1113_, v___x_1118_);
lean_dec(v___x_1118_);
lean_dec(v___x_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat___boxed(lean_object* v_n_1120_, lean_object* v_x_1121_, lean_object* v_b_1122_){
_start:
{
uint8_t v_b_boxed_1123_; lean_object* v_res_1124_; 
v_b_boxed_1123_ = lean_unbox(v_b_1122_);
v_res_1124_ = l_BitVec_shiftConcat(v_n_1120_, v_x_1121_, v_b_boxed_1123_);
lean_dec(v_x_1121_);
lean_dec(v_n_1120_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cons(lean_object* v_n_1125_, uint8_t v_msb_1126_, lean_object* v_lsbs_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = l_BitVec_ofBool(v_msb_1126_);
v___x_1129_ = l_BitVec_append___redArg(v_n_1125_, v___x_1128_, v_lsbs_1127_);
lean_dec(v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cons___boxed(lean_object* v_n_1130_, lean_object* v_msb_1131_, lean_object* v_lsbs_1132_){
_start:
{
uint8_t v_msb_boxed_1133_; lean_object* v_res_1134_; 
v_msb_boxed_1133_ = lean_unbox(v_msb_1131_);
v_res_1134_ = l_BitVec_cons(v_n_1130_, v_msb_boxed_1133_, v_lsbs_1132_);
lean_dec(v_lsbs_1132_);
lean_dec(v_n_1130_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow(lean_object* v_w_1135_, lean_object* v_i_1136_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = l_BitVec_ofNat(v_w_1135_, v___x_1137_);
v___x_1139_ = l_BitVec_shiftLeft(v_w_1135_, v___x_1138_, v_i_1136_);
lean_dec(v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow___boxed(lean_object* v_w_1140_, lean_object* v_i_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_BitVec_twoPow(v_w_1140_, v_i_1141_);
lean_dec(v_i_1141_);
lean_dec(v_w_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMin(lean_object* v_w_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_nat_sub(v_w_1143_, v___x_1144_);
v___x_1146_ = l_BitVec_twoPow(v_w_1143_, v___x_1145_);
lean_dec(v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMin___boxed(lean_object* v_w_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_BitVec_intMin(v_w_1147_);
lean_dec(v_w_1147_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMax(lean_object* v_w_1149_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = lean_nat_sub(v_w_1149_, v___x_1150_);
v___x_1152_ = l_BitVec_twoPow(v_w_1149_, v___x_1151_);
lean_dec(v___x_1151_);
v___x_1153_ = l_BitVec_ofNat(v_w_1149_, v___x_1150_);
v___x_1154_ = l_BitVec_sub(v_w_1149_, v___x_1152_, v___x_1153_);
lean_dec(v___x_1153_);
lean_dec(v___x_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMax___boxed(lean_object* v_w_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_BitVec_intMax(v_w_1155_);
lean_dec(v_w_1155_);
return v_res_1156_;
}
}
LEAN_EXPORT uint64_t l_BitVec_hash(lean_object* v_n_1157_, lean_object* v_bv_1158_){
_start:
{
lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = lean_unsigned_to_nat(64u);
v___x_1160_ = lean_nat_dec_le(v_n_1157_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint64_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint64_t v___x_1165_; uint64_t v___x_1166_; 
v___x_1161_ = lean_uint64_of_nat(v_bv_1158_);
v___x_1162_ = lean_nat_sub(v_n_1157_, v___x_1159_);
v___x_1163_ = lean_nat_shiftr(v_bv_1158_, v___x_1159_);
v___x_1164_ = l_BitVec_setWidth(v_n_1157_, v___x_1162_, v___x_1163_);
lean_dec(v___x_1163_);
v___x_1165_ = l_BitVec_hash(v___x_1162_, v___x_1164_);
lean_dec(v___x_1164_);
lean_dec(v___x_1162_);
v___x_1166_ = lean_uint64_mix_hash(v___x_1161_, v___x_1165_);
return v___x_1166_;
}
else
{
uint64_t v___x_1167_; 
v___x_1167_ = lean_uint64_of_nat(v_bv_1158_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_hash___boxed(lean_object* v_n_1168_, lean_object* v_bv_1169_){
_start:
{
uint64_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_BitVec_hash(v_n_1168_, v_bv_1169_);
lean_dec(v_bv_1169_);
lean_dec(v_n_1168_);
v_r_1171_ = lean_box_uint64(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHashable(lean_object* v_n_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_alloc_closure((void*)(l_BitVec_hash___boxed), 2, 1);
lean_closure_set(v___x_1173_, 0, v_n_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE(lean_object* v_x_1174_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 0)
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1175_;
}
else
{
lean_object* v_head_1176_; lean_object* v_tail_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; 
v_head_1176_ = lean_ctor_get(v_x_1174_, 0);
v_tail_1177_ = lean_ctor_get(v_x_1174_, 1);
v___x_1178_ = l_List_lengthTR___redArg(v_tail_1177_);
v___x_1179_ = l_BitVec_ofBoolListBE(v_tail_1177_);
v___x_1180_ = lean_unbox(v_head_1176_);
v___x_1181_ = l_BitVec_cons(v___x_1178_, v___x_1180_, v___x_1179_);
lean_dec(v___x_1179_);
lean_dec(v___x_1178_);
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE___boxed(lean_object* v_x_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_BitVec_ofBoolListBE(v_x_1182_);
lean_dec(v_x_1182_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE(lean_object* v_x_1184_){
_start:
{
if (lean_obj_tag(v_x_1184_) == 0)
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1185_;
}
else
{
lean_object* v_head_1186_; lean_object* v_tail_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; 
v_head_1186_ = lean_ctor_get(v_x_1184_, 0);
v_tail_1187_ = lean_ctor_get(v_x_1184_, 1);
v___x_1188_ = l_BitVec_ofBoolListLE(v_tail_1187_);
v___x_1189_ = lean_unbox(v_head_1186_);
v___x_1190_ = l_BitVec_concat___redArg(v___x_1188_, v___x_1189_);
lean_dec(v___x_1188_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE___boxed(lean_object* v_x_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_BitVec_ofBoolListLE(v_x_1191_);
lean_dec(v_x_1191_);
return v_res_1192_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uaddOverflow(lean_object* v_w_1193_, lean_object* v_x_1194_, lean_object* v_y_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1196_ = lean_unsigned_to_nat(2u);
v___x_1197_ = lean_nat_pow(v___x_1196_, v_w_1193_);
v___x_1198_ = lean_nat_add(v_x_1194_, v_y_1195_);
v___x_1199_ = lean_nat_dec_le(v___x_1197_, v___x_1198_);
lean_dec(v___x_1198_);
lean_dec(v___x_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_BitVec_uaddOverflow___boxed(lean_object* v_w_1200_, lean_object* v_x_1201_, lean_object* v_y_1202_){
_start:
{
uint8_t v_res_1203_; lean_object* v_r_1204_; 
v_res_1203_ = l_BitVec_uaddOverflow(v_w_1200_, v_x_1201_, v_y_1202_);
lean_dec(v_y_1202_);
lean_dec(v_x_1201_);
lean_dec(v_w_1200_);
v_r_1204_ = lean_box(v_res_1203_);
return v_r_1204_;
}
}
static lean_object* _init_l_BitVec_saddOverflow___closed__0(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_unsigned_to_nat(2u);
v___x_1206_ = lean_nat_to_int(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT uint8_t l_BitVec_saddOverflow(lean_object* v_w_1207_, lean_object* v_x_1208_, lean_object* v_y_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1210_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_nat_sub(v_w_1207_, v___x_1211_);
v___x_1213_ = l_Int_pow(v___x_1210_, v___x_1212_);
lean_dec(v___x_1212_);
v___x_1214_ = l_BitVec_toInt(v_w_1207_, v_x_1208_);
v___x_1215_ = l_BitVec_toInt(v_w_1207_, v_y_1209_);
v___x_1216_ = lean_int_add(v___x_1214_, v___x_1215_);
lean_dec(v___x_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_int_dec_le(v___x_1213_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = lean_int_neg(v___x_1213_);
lean_dec(v___x_1213_);
v___x_1219_ = lean_int_dec_lt(v___x_1216_, v___x_1218_);
lean_dec(v___x_1218_);
lean_dec(v___x_1216_);
return v___x_1219_;
}
else
{
lean_dec(v___x_1216_);
lean_dec(v___x_1213_);
return v___x_1217_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_saddOverflow___boxed(lean_object* v_w_1220_, lean_object* v_x_1221_, lean_object* v_y_1222_){
_start:
{
uint8_t v_res_1223_; lean_object* v_r_1224_; 
v_res_1223_ = l_BitVec_saddOverflow(v_w_1220_, v_x_1221_, v_y_1222_);
lean_dec(v_w_1220_);
v_r_1224_ = lean_box(v_res_1223_);
return v_r_1224_;
}
}
LEAN_EXPORT uint8_t l_BitVec_usubOverflow___redArg(lean_object* v_x_1225_, lean_object* v_y_1226_){
_start:
{
uint8_t v___x_1227_; 
v___x_1227_ = lean_nat_dec_lt(v_x_1225_, v_y_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___redArg___boxed(lean_object* v_x_1228_, lean_object* v_y_1229_){
_start:
{
uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_res_1230_ = l_BitVec_usubOverflow___redArg(v_x_1228_, v_y_1229_);
lean_dec(v_y_1229_);
lean_dec(v_x_1228_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
LEAN_EXPORT uint8_t l_BitVec_usubOverflow(lean_object* v_w_1232_, lean_object* v_x_1233_, lean_object* v_y_1234_){
_start:
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_nat_dec_lt(v_x_1233_, v_y_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___boxed(lean_object* v_w_1236_, lean_object* v_x_1237_, lean_object* v_y_1238_){
_start:
{
uint8_t v_res_1239_; lean_object* v_r_1240_; 
v_res_1239_ = l_BitVec_usubOverflow(v_w_1236_, v_x_1237_, v_y_1238_);
lean_dec(v_y_1238_);
lean_dec(v_x_1237_);
lean_dec(v_w_1236_);
v_r_1240_ = lean_box(v_res_1239_);
return v_r_1240_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ssubOverflow(lean_object* v_w_1241_, lean_object* v_x_1242_, lean_object* v_y_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1244_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1245_ = lean_unsigned_to_nat(1u);
v___x_1246_ = lean_nat_sub(v_w_1241_, v___x_1245_);
v___x_1247_ = l_Int_pow(v___x_1244_, v___x_1246_);
lean_dec(v___x_1246_);
v___x_1248_ = l_BitVec_toInt(v_w_1241_, v_x_1242_);
v___x_1249_ = l_BitVec_toInt(v_w_1241_, v_y_1243_);
v___x_1250_ = lean_int_sub(v___x_1248_, v___x_1249_);
lean_dec(v___x_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_int_dec_le(v___x_1247_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = lean_int_neg(v___x_1247_);
lean_dec(v___x_1247_);
v___x_1253_ = lean_int_dec_lt(v___x_1250_, v___x_1252_);
lean_dec(v___x_1252_);
lean_dec(v___x_1250_);
return v___x_1253_;
}
else
{
lean_dec(v___x_1250_);
lean_dec(v___x_1247_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ssubOverflow___boxed(lean_object* v_w_1254_, lean_object* v_x_1255_, lean_object* v_y_1256_){
_start:
{
uint8_t v_res_1257_; lean_object* v_r_1258_; 
v_res_1257_ = l_BitVec_ssubOverflow(v_w_1254_, v_x_1255_, v_y_1256_);
lean_dec(v_w_1254_);
v_r_1258_ = lean_box(v_res_1257_);
return v_r_1258_;
}
}
LEAN_EXPORT uint8_t l_BitVec_negOverflow(lean_object* v_w_1259_, lean_object* v_x_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1261_ = l_BitVec_toInt(v_w_1259_, v_x_1260_);
v___x_1262_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_nat_sub(v_w_1259_, v___x_1263_);
v___x_1265_ = l_Int_pow(v___x_1262_, v___x_1264_);
lean_dec(v___x_1264_);
v___x_1266_ = lean_int_neg(v___x_1265_);
lean_dec(v___x_1265_);
v___x_1267_ = lean_int_dec_eq(v___x_1261_, v___x_1266_);
lean_dec(v___x_1266_);
lean_dec(v___x_1261_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_BitVec_negOverflow___boxed(lean_object* v_w_1268_, lean_object* v_x_1269_){
_start:
{
uint8_t v_res_1270_; lean_object* v_r_1271_; 
v_res_1270_ = l_BitVec_negOverflow(v_w_1268_, v_x_1269_);
lean_dec(v_w_1268_);
v_r_1271_ = lean_box(v_res_1270_);
return v_r_1271_;
}
}
LEAN_EXPORT uint8_t l_BitVec_sdivOverflow(lean_object* v_w_1272_, lean_object* v_x_1273_, lean_object* v_y_1274_){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1275_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1276_ = lean_unsigned_to_nat(1u);
v___x_1277_ = lean_nat_sub(v_w_1272_, v___x_1276_);
v___x_1278_ = l_Int_pow(v___x_1275_, v___x_1277_);
lean_dec(v___x_1277_);
v___x_1279_ = l_BitVec_toInt(v_w_1272_, v_x_1273_);
v___x_1280_ = l_BitVec_toInt(v_w_1272_, v_y_1274_);
v___x_1281_ = lean_int_ediv(v___x_1279_, v___x_1280_);
lean_dec(v___x_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_int_dec_le(v___x_1278_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = lean_int_neg(v___x_1278_);
lean_dec(v___x_1278_);
v___x_1284_ = lean_int_dec_lt(v___x_1281_, v___x_1283_);
lean_dec(v___x_1283_);
lean_dec(v___x_1281_);
return v___x_1284_;
}
else
{
lean_dec(v___x_1281_);
lean_dec(v___x_1278_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sdivOverflow___boxed(lean_object* v_w_1285_, lean_object* v_x_1286_, lean_object* v_y_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_BitVec_sdivOverflow(v_w_1285_, v_x_1286_, v_y_1287_);
lean_dec(v_w_1285_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse(lean_object* v_x_1290_, lean_object* v_x_1291_){
_start:
{
lean_object* v_zero_1292_; uint8_t v_isZero_1293_; 
v_zero_1292_ = lean_unsigned_to_nat(0u);
v_isZero_1293_ = lean_nat_dec_eq(v_x_1290_, v_zero_1292_);
if (v_isZero_1293_ == 1)
{
lean_inc(v_x_1291_);
return v_x_1291_;
}
else
{
lean_object* v_one_1294_; lean_object* v_n_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_one_1294_ = lean_unsigned_to_nat(1u);
v_n_1295_ = lean_nat_sub(v_x_1290_, v_one_1294_);
v___x_1296_ = lean_nat_add(v_n_1295_, v_one_1294_);
v___x_1297_ = l_BitVec_setWidth(v___x_1296_, v_n_1295_, v_x_1291_);
v___x_1298_ = l_BitVec_reverse(v_n_1295_, v___x_1297_);
lean_dec(v___x_1297_);
lean_dec(v_n_1295_);
v___x_1299_ = lean_nat_dec_lt(v_zero_1292_, v___x_1296_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
lean_dec(v___x_1296_);
v___x_1300_ = l_BitVec_concat___redArg(v___x_1298_, v___x_1299_);
lean_dec(v___x_1298_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_nat_sub(v___x_1296_, v_one_1294_);
lean_dec(v___x_1296_);
v___x_1302_ = l_Nat_testBit(v_x_1291_, v___x_1301_);
lean_dec(v___x_1301_);
v___x_1303_ = l_BitVec_concat___redArg(v___x_1298_, v___x_1302_);
lean_dec(v___x_1298_);
return v___x_1303_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse___boxed(lean_object* v_x_1304_, lean_object* v_x_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_BitVec_reverse(v_x_1304_, v_x_1305_);
lean_dec(v_x_1305_);
lean_dec(v_x_1304_);
return v_res_1306_;
}
}
LEAN_EXPORT uint8_t l_BitVec_umulOverflow(lean_object* v_w_1307_, lean_object* v_x_1308_, lean_object* v_y_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1310_ = lean_unsigned_to_nat(2u);
v___x_1311_ = lean_nat_pow(v___x_1310_, v_w_1307_);
v___x_1312_ = lean_nat_mul(v_x_1308_, v_y_1309_);
v___x_1313_ = lean_nat_dec_le(v___x_1311_, v___x_1312_);
lean_dec(v___x_1312_);
lean_dec(v___x_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umulOverflow___boxed(lean_object* v_w_1314_, lean_object* v_x_1315_, lean_object* v_y_1316_){
_start:
{
uint8_t v_res_1317_; lean_object* v_r_1318_; 
v_res_1317_ = l_BitVec_umulOverflow(v_w_1314_, v_x_1315_, v_y_1316_);
lean_dec(v_y_1316_);
lean_dec(v_x_1315_);
lean_dec(v_w_1314_);
v_r_1318_ = lean_box(v_res_1317_);
return v_r_1318_;
}
}
LEAN_EXPORT uint8_t l_BitVec_smulOverflow(lean_object* v_w_1319_, lean_object* v_x_1320_, lean_object* v_y_1321_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1322_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = lean_nat_sub(v_w_1319_, v___x_1323_);
v___x_1325_ = l_Int_pow(v___x_1322_, v___x_1324_);
lean_dec(v___x_1324_);
v___x_1326_ = l_BitVec_toInt(v_w_1319_, v_x_1320_);
v___x_1327_ = l_BitVec_toInt(v_w_1319_, v_y_1321_);
v___x_1328_ = lean_int_mul(v___x_1326_, v___x_1327_);
lean_dec(v___x_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_int_dec_le(v___x_1325_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = lean_int_neg(v___x_1325_);
lean_dec(v___x_1325_);
v___x_1331_ = lean_int_dec_lt(v___x_1328_, v___x_1330_);
lean_dec(v___x_1330_);
lean_dec(v___x_1328_);
return v___x_1331_;
}
else
{
lean_dec(v___x_1328_);
lean_dec(v___x_1325_);
return v___x_1329_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smulOverflow___boxed(lean_object* v_w_1332_, lean_object* v_x_1333_, lean_object* v_y_1334_){
_start:
{
uint8_t v_res_1335_; lean_object* v_r_1336_; 
v_res_1335_ = l_BitVec_smulOverflow(v_w_1332_, v_x_1333_, v_y_1334_);
lean_dec(v_w_1332_);
v_r_1336_ = lean_box(v_res_1335_);
return v_r_1336_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec(lean_object* v_w_1337_, lean_object* v_x_1338_, lean_object* v_n_1339_){
_start:
{
lean_object* v_zero_1340_; uint8_t v_isZero_1341_; 
v_zero_1340_ = lean_unsigned_to_nat(0u);
v_isZero_1341_ = lean_nat_dec_eq(v_n_1339_, v_zero_1340_);
if (v_isZero_1341_ == 1)
{
uint8_t v___x_1342_; 
lean_dec(v_n_1339_);
v___x_1342_ = l_Nat_testBit(v_x_1338_, v_zero_1340_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = l_BitVec_ofNat(v_w_1337_, v_w_1337_);
return v___x_1343_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = lean_nat_sub(v_w_1337_, v___x_1344_);
v___x_1346_ = l_BitVec_ofNat(v_w_1337_, v___x_1345_);
lean_dec(v___x_1345_);
return v___x_1346_;
}
}
else
{
uint8_t v___x_1347_; 
v___x_1347_ = l_Nat_testBit(v_x_1338_, v_n_1339_);
if (v___x_1347_ == 0)
{
lean_object* v_one_1348_; lean_object* v_n_1349_; 
v_one_1348_ = lean_unsigned_to_nat(1u);
v_n_1349_ = lean_nat_sub(v_n_1339_, v_one_1348_);
lean_dec(v_n_1339_);
v_n_1339_ = v_n_1349_;
goto _start;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1351_ = lean_unsigned_to_nat(1u);
v___x_1352_ = lean_nat_sub(v_w_1337_, v___x_1351_);
v___x_1353_ = lean_nat_sub(v___x_1352_, v_n_1339_);
lean_dec(v_n_1339_);
lean_dec(v___x_1352_);
v___x_1354_ = l_BitVec_ofNat(v_w_1337_, v___x_1353_);
lean_dec(v___x_1353_);
return v___x_1354_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec___boxed(lean_object* v_w_1355_, lean_object* v_x_1356_, lean_object* v_n_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_BitVec_clzAuxRec(v_w_1355_, v_x_1356_, v_n_1357_);
lean_dec(v_x_1356_);
lean_dec(v_w_1355_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clz(lean_object* v_w_1359_, lean_object* v_x_1360_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = lean_unsigned_to_nat(1u);
v___x_1362_ = lean_nat_sub(v_w_1359_, v___x_1361_);
v___x_1363_ = l_BitVec_clzAuxRec(v_w_1359_, v_x_1360_, v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clz___boxed(lean_object* v_w_1364_, lean_object* v_x_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_BitVec_clz(v_w_1364_, v_x_1365_);
lean_dec(v_x_1365_);
lean_dec(v_w_1364_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ctz(lean_object* v_w_1367_, lean_object* v_x_1368_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = l_BitVec_reverse(v_w_1367_, v_x_1368_);
v___x_1370_ = l_BitVec_clz(v_w_1367_, v___x_1369_);
lean_dec(v___x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ctz___boxed(lean_object* v_w_1371_, lean_object* v_x_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_BitVec_ctz(v_w_1371_, v_x_1372_);
lean_dec(v_x_1372_);
lean_dec(v_w_1371_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg(lean_object* v_x_1374_, lean_object* v_pos_1375_, lean_object* v_acc_1376_){
_start:
{
lean_object* v_zero_1377_; uint8_t v_isZero_1378_; 
v_zero_1377_ = lean_unsigned_to_nat(0u);
v_isZero_1378_ = lean_nat_dec_eq(v_pos_1375_, v_zero_1377_);
if (v_isZero_1378_ == 1)
{
lean_dec(v_pos_1375_);
return v_acc_1376_;
}
else
{
lean_object* v_one_1379_; lean_object* v_n_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_one_1379_ = lean_unsigned_to_nat(1u);
v_n_1380_ = lean_nat_sub(v_pos_1375_, v_one_1379_);
lean_dec(v_pos_1375_);
v___x_1381_ = l_Nat_testBit(v_x_1374_, v_n_1380_);
v___x_1382_ = l_Bool_toNat(v___x_1381_);
v___x_1383_ = lean_nat_add(v_acc_1376_, v___x_1382_);
lean_dec(v___x_1382_);
lean_dec(v_acc_1376_);
v_pos_1375_ = v_n_1380_;
v_acc_1376_ = v___x_1383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg___boxed(lean_object* v_x_1385_, lean_object* v_pos_1386_, lean_object* v_acc_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_BitVec_cpopNatRec___redArg(v_x_1385_, v_pos_1386_, v_acc_1387_);
lean_dec(v_x_1385_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec(lean_object* v_w_1389_, lean_object* v_x_1390_, lean_object* v_pos_1391_, lean_object* v_acc_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_BitVec_cpopNatRec___redArg(v_x_1390_, v_pos_1391_, v_acc_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___boxed(lean_object* v_w_1394_, lean_object* v_x_1395_, lean_object* v_pos_1396_, lean_object* v_acc_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_BitVec_cpopNatRec(v_w_1394_, v_x_1395_, v_pos_1396_, v_acc_1397_);
lean_dec(v_x_1395_);
lean_dec(v_w_1394_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpop(lean_object* v_w_1399_, lean_object* v_x_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = lean_unsigned_to_nat(0u);
lean_inc(v_w_1399_);
v___x_1402_ = l_BitVec_cpopNatRec___redArg(v_x_1400_, v_w_1399_, v___x_1401_);
v___x_1403_ = l_BitVec_ofNat(v_w_1399_, v___x_1402_);
lean_dec(v___x_1402_);
lean_dec(v_w_1399_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpop___boxed(lean_object* v_w_1404_, lean_object* v_x_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_BitVec_cpop(v_w_1404_, v_x_1405_);
lean_dec(v_x_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg___lam__0(lean_object* v_x_1407_, lean_object* v_y_1408_){
_start:
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_nat_dec_le(v_x_1407_, v_y_1408_);
if (v___x_1409_ == 0)
{
lean_inc(v_y_1408_);
return v_y_1408_;
}
else
{
lean_inc(v_x_1407_);
return v_x_1407_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg___lam__0___boxed(lean_object* v_x_1410_, lean_object* v_y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_BitVec_instMin___redArg___lam__0(v_x_1410_, v_y_1411_);
lean_dec(v_y_1411_);
lean_dec(v_x_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg(){
_start:
{
lean_object* v___f_1415_; 
v___f_1415_ = ((lean_object*)(l_BitVec_instMin___redArg___closed__0));
return v___f_1415_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg___boxed(lean_object* v___dummy_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_BitVec_instMin___redArg();
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin(lean_object* v_w_1418_){
_start:
{
lean_object* v___f_1419_; 
v___f_1419_ = ((lean_object*)(l_BitVec_instMin___redArg___closed__0));
return v___f_1419_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___boxed(lean_object* v_w_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_BitVec_instMin(v_w_1420_);
lean_dec(v_w_1420_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg___lam__0(lean_object* v_x_1422_, lean_object* v_y_1423_){
_start:
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_nat_dec_le(v_x_1422_, v_y_1423_);
if (v___x_1424_ == 0)
{
lean_inc(v_x_1422_);
return v_x_1422_;
}
else
{
lean_inc(v_y_1423_);
return v_y_1423_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg___lam__0___boxed(lean_object* v_x_1425_, lean_object* v_y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_BitVec_instMax___redArg___lam__0(v_x_1425_, v_y_1426_);
lean_dec(v_y_1426_);
lean_dec(v_x_1425_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg(){
_start:
{
lean_object* v___f_1430_; 
v___f_1430_ = ((lean_object*)(l_BitVec_instMax___redArg___closed__0));
return v___f_1430_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg___boxed(lean_object* v___dummy_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_BitVec_instMax___redArg();
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax(lean_object* v_w_1433_){
_start:
{
lean_object* v___f_1434_; 
v___f_1434_ = ((lean_object*)(l_BitVec_instMax___redArg___closed__0));
return v___f_1434_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___boxed(lean_object* v_w_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_BitVec_instMax(v_w_1435_);
lean_dec(v_w_1435_);
return v_res_1436_;
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
