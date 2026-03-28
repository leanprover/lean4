// Lean compiler output
// Module: Init.Data.BitVec.Basic
// Imports: public import Init.Data.Int.Bitwise.Basic public import Init.Data.Bool public import Init.Data.Int.DivMod.Basic public import Init.WF import Init.Data.Nat.Bitwise.Lemmas import Init.Data.Nat.Lemmas import Init.Data.Nat.Linear import Init.Meta.Defs import Init.Omega import Init.WFTactics
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
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_sub(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_shiftRight___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_BitVec_zero(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_zero___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_BitVec_instGetElemNatBoolLt___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_BitVec_instGetElemNatBoolLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_BitVec_instGetElemNatBoolLt___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instGetElemNatBoolLt___closed__0 = (const lean_object*)&l_BitVec_instGetElemNatBoolLt___closed__0_value;
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
static const lean_closure_object l_BitVec_instHShiftRight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instHShiftRight___closed__0 = (const lean_object*)&l_BitVec_instHShiftRight___closed__0_value;
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
LEAN_EXPORT lean_object* l_BitVec_zero(lean_object* v_n_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_unsigned_to_nat(0u);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zero___boxed(lean_object* v_n_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_BitVec_zero(v_n_14_);
lean_dec(v_n_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instInhabited(lean_object* v_n_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(0u);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instInhabited___boxed(lean_object* v_n_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_BitVec_instInhabited(v_n_18_);
lean_dec(v_n_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_BitVec_allOnes(lean_object* v_n_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_21_ = lean_unsigned_to_nat(2u);
v___x_22_ = lean_nat_pow(v___x_21_, v_n_20_);
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_sub(v___x_22_, v___x_23_);
lean_dec(v___x_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_BitVec_allOnes___boxed(lean_object* v_n_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_BitVec_allOnes(v_n_25_);
lean_dec(v_n_25_);
return v_res_26_;
}
}
LEAN_EXPORT uint8_t l_BitVec_getLsb___redArg(lean_object* v_x_27_, lean_object* v_i_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = l_Nat_testBit(v_x_27_, v_i_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb___redArg___boxed(lean_object* v_x_30_, lean_object* v_i_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_BitVec_getLsb___redArg(v_x_30_, v_i_31_);
lean_dec(v_i_31_);
lean_dec(v_x_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_BitVec_getLsb(lean_object* v_w_34_, lean_object* v_x_35_, lean_object* v_i_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = l_Nat_testBit(v_x_35_, v_i_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb___boxed(lean_object* v_w_38_, lean_object* v_x_39_, lean_object* v_i_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_BitVec_getLsb(v_w_38_, v_x_39_, v_i_40_);
lean_dec(v_i_40_);
lean_dec(v_x_39_);
lean_dec(v_w_38_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb_x3f(lean_object* v_w_43_, lean_object* v_x_44_, lean_object* v_i_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = lean_nat_dec_lt(v_i_45_, v_w_43_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; 
v___x_47_ = lean_box(0);
return v___x_47_;
}
else
{
uint8_t v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = l_Nat_testBit(v_x_44_, v_i_45_);
v___x_49_ = lean_box(v___x_48_);
v___x_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsb_x3f___boxed(lean_object* v_w_51_, lean_object* v_x_52_, lean_object* v_i_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_BitVec_getLsb_x3f(v_w_51_, v_x_52_, v_i_53_);
lean_dec(v_i_53_);
lean_dec(v_x_52_);
lean_dec(v_w_51_);
return v_res_54_;
}
}
LEAN_EXPORT uint8_t l_BitVec_getMsb(lean_object* v_w_55_, lean_object* v_x_56_, lean_object* v_i_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_nat_sub(v_w_55_, v___x_58_);
v___x_60_ = lean_nat_sub(v___x_59_, v_i_57_);
lean_dec(v___x_59_);
v___x_61_ = l_Nat_testBit(v_x_56_, v___x_60_);
lean_dec(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsb___boxed(lean_object* v_w_62_, lean_object* v_x_63_, lean_object* v_i_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_BitVec_getMsb(v_w_62_, v_x_63_, v_i_64_);
lean_dec(v_i_64_);
lean_dec(v_x_63_);
lean_dec(v_w_62_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsb_x3f(lean_object* v_w_67_, lean_object* v_x_68_, lean_object* v_i_69_){
_start:
{
uint8_t v___x_70_; 
v___x_70_ = lean_nat_dec_lt(v_i_69_, v_w_67_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
v___x_71_ = lean_box(0);
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_sub(v_w_67_, v___x_72_);
v___x_74_ = lean_nat_sub(v___x_73_, v_i_69_);
lean_dec(v___x_73_);
v___x_75_ = l_Nat_testBit(v_x_68_, v___x_74_);
lean_dec(v___x_74_);
v___x_76_ = lean_box(v___x_75_);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsb_x3f___boxed(lean_object* v_w_78_, lean_object* v_x_79_, lean_object* v_i_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_BitVec_getMsb_x3f(v_w_78_, v_x_79_, v_i_80_);
lean_dec(v_i_80_);
lean_dec(v_x_79_);
lean_dec(v_w_78_);
return v_res_81_;
}
}
LEAN_EXPORT uint8_t l_BitVec_getLsbD___redArg(lean_object* v_x_82_, lean_object* v_i_83_){
_start:
{
uint8_t v___x_84_; 
v___x_84_ = l_Nat_testBit(v_x_82_, v_i_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsbD___redArg___boxed(lean_object* v_x_85_, lean_object* v_i_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_BitVec_getLsbD___redArg(v_x_85_, v_i_86_);
lean_dec(v_i_86_);
lean_dec(v_x_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_BitVec_getLsbD(lean_object* v_w_89_, lean_object* v_x_90_, lean_object* v_i_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = l_Nat_testBit(v_x_90_, v_i_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_BitVec_getLsbD___boxed(lean_object* v_w_93_, lean_object* v_x_94_, lean_object* v_i_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_BitVec_getLsbD(v_w_93_, v_x_94_, v_i_95_);
lean_dec(v_i_95_);
lean_dec(v_x_94_);
lean_dec(v_w_93_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT uint8_t l_BitVec_getMsbD(lean_object* v_w_98_, lean_object* v_x_99_, lean_object* v_i_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_nat_dec_lt(v_i_100_, v_w_98_);
if (v___x_101_ == 0)
{
return v___x_101_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_sub(v_w_98_, v___x_102_);
v___x_104_ = lean_nat_sub(v___x_103_, v_i_100_);
lean_dec(v___x_103_);
v___x_105_ = l_Nat_testBit(v_x_99_, v___x_104_);
lean_dec(v___x_104_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_getMsbD___boxed(lean_object* v_w_106_, lean_object* v_x_107_, lean_object* v_i_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_BitVec_getMsbD(v_w_106_, v_x_107_, v_i_108_);
lean_dec(v_i_108_);
lean_dec(v_x_107_);
lean_dec(v_w_106_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_BitVec_msb(lean_object* v_n_111_, lean_object* v_x_112_){
_start:
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_nat_dec_lt(v___x_113_, v_n_111_);
if (v___x_114_ == 0)
{
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_sub(v_n_111_, v___x_115_);
v___x_117_ = l_Nat_testBit(v_x_112_, v___x_116_);
lean_dec(v___x_116_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_msb___boxed(lean_object* v_n_118_, lean_object* v_x_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_BitVec_msb(v_n_118_, v_x_119_);
lean_dec(v_x_119_);
lean_dec(v_n_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l_BitVec_instGetElemNatBoolLt___lam__0(lean_object* v_xs_122_, lean_object* v_i_123_, lean_object* v_h_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = l_Nat_testBit(v_xs_122_, v_i_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___lam__0___boxed(lean_object* v_xs_126_, lean_object* v_i_127_, lean_object* v_h_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_BitVec_instGetElemNatBoolLt___lam__0(v_xs_126_, v_i_127_, v_h_128_);
lean_dec(v_i_127_);
lean_dec(v_xs_126_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt(lean_object* v_w_132_){
_start:
{
lean_object* v___f_133_; 
v___f_133_ = ((lean_object*)(l_BitVec_instGetElemNatBoolLt___closed__0));
return v___f_133_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instGetElemNatBoolLt___boxed(lean_object* v_w_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_BitVec_instGetElemNatBoolLt(v_w_134_);
lean_dec(v_w_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00BitVec_toInt_spec__0(lean_object* v_a_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_nat_to_int(v_a_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_BitVec_toInt(lean_object* v_n_138_, lean_object* v_x_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_140_ = lean_unsigned_to_nat(2u);
v___x_141_ = lean_nat_mul(v___x_140_, v_x_139_);
v___x_142_ = lean_nat_pow(v___x_140_, v_n_138_);
v___x_143_ = lean_nat_dec_lt(v___x_141_, v___x_142_);
lean_dec(v___x_141_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_nat_to_int(v_x_139_);
v___x_145_ = lean_nat_to_int(v___x_142_);
v___x_146_ = lean_int_sub(v___x_144_, v___x_145_);
lean_dec(v___x_145_);
lean_dec(v___x_144_);
return v___x_146_;
}
else
{
lean_object* v___x_147_; 
lean_dec(v___x_142_);
v___x_147_ = lean_nat_to_int(v_x_139_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_toInt___boxed(lean_object* v_n_148_, lean_object* v_x_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_BitVec_toInt(v_n_148_, v_x_149_);
lean_dec(v_n_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofInt(lean_object* v_n_151_, lean_object* v_i_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = lean_unsigned_to_nat(2u);
v___x_154_ = lean_nat_pow(v___x_153_, v_n_151_);
v___x_155_ = lean_nat_to_int(v___x_154_);
v___x_156_ = lean_int_emod(v_i_152_, v___x_155_);
lean_dec(v___x_155_);
v___x_157_ = l_Int_toNat(v___x_156_);
lean_dec(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofInt___boxed(lean_object* v_n_158_, lean_object* v_i_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_BitVec_ofInt(v_n_158_, v_i_159_);
lean_dec(v_i_159_);
lean_dec(v_n_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instIntCast(lean_object* v_w_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_alloc_closure((void*)(l_BitVec_ofInt___boxed), 2, 1);
lean_closure_set(v___x_162_, 0, v_w_161_);
return v___x_162_;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__5));
v___x_222_ = l_String_toRawSubstring_x27(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1(lean_object* v_x_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__2));
lean_inc(v_x_236_);
v___x_240_ = l_Lean_Syntax_isOfKind(v_x_236_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec(v_x_236_);
v___x_241_ = lean_box(1);
v___x_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v_a_238_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = l_Lean_Syntax_getArg(v_x_236_, v___x_243_);
v___x_245_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__6));
lean_inc(v___x_244_);
v___x_246_ = l_Lean_Syntax_isOfKind(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v___x_244_);
lean_dec(v_x_236_);
v___x_247_ = lean_box(1);
v___x_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_a_238_);
return v___x_248_;
}
else
{
lean_object* v_quotContext_249_; lean_object* v_currMacroScope_250_; lean_object* v_ref_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_quotContext_249_ = lean_ctor_get(v_a_237_, 1);
v_currMacroScope_250_ = lean_ctor_get(v_a_237_, 2);
v_ref_251_ = lean_ctor_get(v_a_237_, 5);
v___x_252_ = lean_unsigned_to_nat(2u);
v___x_253_ = l_Lean_Syntax_getArg(v_x_236_, v___x_252_);
lean_dec(v_x_236_);
v___x_254_ = 0;
v___x_255_ = l_Lean_SourceInfo_fromRef(v_ref_251_, v___x_254_);
v___x_256_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
v___x_257_ = lean_obj_once(&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6, &l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6_once, _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6);
v___x_258_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8));
lean_inc(v_currMacroScope_250_);
lean_inc(v_quotContext_249_);
v___x_259_ = l_Lean_addMacroScope(v_quotContext_249_, v___x_258_, v_currMacroScope_250_);
v___x_260_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10));
lean_inc_n(v___x_255_, 2);
v___x_261_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_261_, 0, v___x_255_);
lean_ctor_set(v___x_261_, 1, v___x_257_);
lean_ctor_set(v___x_261_, 2, v___x_259_);
lean_ctor_set(v___x_261_, 3, v___x_260_);
v___x_262_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12));
v___x_263_ = l_Lean_Syntax_node2(v___x_255_, v___x_262_, v___x_253_, v___x_244_);
v___x_264_ = l_Lean_Syntax_node2(v___x_255_, v___x_256_, v___x_261_, v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_a_238_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___boxed(lean_object* v_x_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1(v_x_266_, v_a_267_, v_a_268_);
lean_dec_ref(v_a_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat(lean_object* v_x_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
lean_inc(v_x_270_);
v___x_274_ = l_Lean_Syntax_isOfKind(v_x_270_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec(v_x_270_);
v___x_275_ = lean_box(0);
v___x_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v_a_272_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = l_Lean_Syntax_getArg(v_x_270_, v___x_277_);
lean_dec(v_x_270_);
v___x_279_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_278_);
v___x_280_ = l_Lean_Syntax_matchesNull(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v_a_272_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_283_ = l_Lean_Syntax_getArg(v___x_278_, v___x_277_);
v___x_284_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__6));
lean_inc(v___x_283_);
v___x_285_ = l_Lean_Syntax_isOfKind(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v___x_283_);
lean_dec(v___x_278_);
v___x_286_ = lean_box(0);
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v_a_272_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l_Lean_Syntax_getArg(v___x_278_, v___x_288_);
lean_dec(v___x_278_);
v___x_290_ = 0;
v___x_291_ = l_Lean_SourceInfo_fromRef(v_a_271_, v___x_290_);
v___x_292_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__2));
v___x_293_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__12));
lean_inc(v___x_291_);
v___x_294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_291_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = l_Lean_Syntax_node3(v___x_291_, v___x_292_, v___x_283_, v___x_294_, v___x_289_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v_a_272_);
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat___boxed(lean_object* v_x_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_BitVec_unexpandBitVecOfNat(v_x_297_, v_a_298_, v_a_299_);
lean_dec(v_a_298_);
return v_res_300_;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__0));
v___x_327_ = l_String_toRawSubstring_x27(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1(lean_object* v_x_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l_BitVec_term_____x23_x27_____00__closed__1));
lean_inc(v_x_338_);
v___x_342_ = l_Lean_Syntax_isOfKind(v_x_338_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v_x_338_);
v___x_343_ = lean_box(1);
v___x_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v_a_340_);
return v___x_344_;
}
else
{
lean_object* v_quotContext_345_; lean_object* v_currMacroScope_346_; lean_object* v_ref_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_quotContext_345_ = lean_ctor_get(v_a_339_, 1);
v_currMacroScope_346_ = lean_ctor_get(v_a_339_, 2);
v_ref_347_ = lean_ctor_get(v_a_339_, 5);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = l_Lean_Syntax_getArg(v_x_338_, v___x_348_);
v___x_350_ = lean_unsigned_to_nat(2u);
v___x_351_ = l_Lean_Syntax_getArg(v_x_338_, v___x_350_);
lean_dec(v_x_338_);
v___x_352_ = 0;
v___x_353_ = l_Lean_SourceInfo_fromRef(v_ref_347_, v___x_352_);
v___x_354_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
v___x_355_ = lean_obj_once(&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1, &l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1_once, _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1);
v___x_356_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3));
lean_inc(v_currMacroScope_346_);
lean_inc(v_quotContext_345_);
v___x_357_ = l_Lean_addMacroScope(v_quotContext_345_, v___x_356_, v_currMacroScope_346_);
v___x_358_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5));
lean_inc_n(v___x_353_, 2);
v___x_359_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_359_, 0, v___x_353_);
lean_ctor_set(v___x_359_, 1, v___x_355_);
lean_ctor_set(v___x_359_, 2, v___x_357_);
lean_ctor_set(v___x_359_, 3, v___x_358_);
v___x_360_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12));
v___x_361_ = l_Lean_Syntax_node2(v___x_353_, v___x_360_, v___x_349_, v___x_351_);
v___x_362_ = l_Lean_Syntax_node2(v___x_353_, v___x_354_, v___x_359_, v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v_a_340_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___boxed(lean_object* v_x_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1(v_x_364_, v_a_365_, v_a_366_);
lean_dec_ref(v_a_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt(lean_object* v_x_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
lean_inc(v_x_368_);
v___x_372_ = l_Lean_Syntax_isOfKind(v_x_368_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v_x_368_);
v___x_373_ = lean_box(0);
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v_a_370_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = l_Lean_Syntax_getArg(v_x_368_, v___x_375_);
lean_dec(v_x_368_);
v___x_377_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_376_);
v___x_378_ = l_Lean_Syntax_matchesNull(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v_a_370_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = l_Lean_Syntax_getArg(v___x_376_, v___x_381_);
v___x_383_ = l_Lean_Syntax_getArg(v___x_376_, v___x_375_);
lean_dec(v___x_376_);
v___x_384_ = 0;
v___x_385_ = l_Lean_SourceInfo_fromRef(v_a_369_, v___x_384_);
v___x_386_ = ((lean_object*)(l_BitVec_term_____x23_x27_____00__closed__1));
v___x_387_ = ((lean_object*)(l_BitVec_term_____x23_x27_____00__closed__2));
lean_inc(v___x_385_);
v___x_388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_385_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_Syntax_node3(v___x_385_, v___x_386_, v___x_382_, v___x_388_, v___x_383_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v_a_370_);
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt___boxed(lean_object* v_x_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_BitVec_unexpandBitVecOfNatLt(v_x_391_, v_a_392_, v_a_393_);
lean_dec(v_a_392_);
return v_res_394_;
}
}
static lean_object* _init_l_BitVec_toHex___boxed__const__1(void){
_start:
{
uint32_t v___x_395_; lean_object* v___x_396_; 
v___x_395_ = 48;
v___x_396_ = lean_box_uint32(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_BitVec_toHex(lean_object* v_n_397_, lean_object* v_x_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_s_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_t_410_; lean_object* v___x_411_; 
v___x_399_ = lean_unsigned_to_nat(16u);
v___x_400_ = l_Nat_toDigits(v___x_399_, v_x_398_);
v_s_401_ = lean_string_mk(v___x_400_);
v___x_402_ = lean_unsigned_to_nat(3u);
v___x_403_ = lean_nat_add(v_n_397_, v___x_402_);
v___x_404_ = lean_unsigned_to_nat(2u);
v___x_405_ = lean_nat_shiftr(v___x_403_, v___x_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_string_length(v_s_401_);
v___x_407_ = lean_nat_sub(v___x_405_, v___x_406_);
lean_dec(v___x_406_);
lean_dec(v___x_405_);
v___x_408_ = l_BitVec_toHex___boxed__const__1;
v___x_409_ = l_List_replicateTR___redArg(v___x_407_, v___x_408_);
v_t_410_ = lean_string_mk(v___x_409_);
v___x_411_ = lean_string_append(v_t_410_, v_s_401_);
lean_dec_ref(v_s_401_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_BitVec_toHex___boxed(lean_object* v_n_412_, lean_object* v_x_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_BitVec_toHex(v_n_412_, v_x_413_);
lean_dec(v_n_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_BitVec_repr(lean_object* v_n_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_422_ = ((lean_object*)(l_BitVec_repr___closed__1));
v___x_423_ = l_BitVec_toHex(v_n_420_, v_a_421_);
v___x_424_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
v___x_425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_422_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = ((lean_object*)(l_BitVec_repr___closed__2));
v___x_427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Nat_reprFast(v_n_420_);
v___x_429_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
v___x_430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_427_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr___lam__0(lean_object* v_n_431_, lean_object* v_a_432_, lean_object* v_x_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_BitVec_repr(v_n_431_, v_a_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr___lam__0___boxed(lean_object* v_n_435_, lean_object* v_a_436_, lean_object* v_x_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_BitVec_instRepr___lam__0(v_n_435_, v_a_436_, v_x_437_);
lean_dec(v_x_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr(lean_object* v_n_439_){
_start:
{
lean_object* v___f_440_; 
v___f_440_ = lean_alloc_closure((void*)(l_BitVec_instRepr___lam__0___boxed), 3, 1);
lean_closure_set(v___f_440_, 0, v_n_439_);
return v___f_440_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instToString___lam__0(lean_object* v_n_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_443_ = l_BitVec_repr(v_n_441_, v_a_442_);
v___x_444_ = l_Std_Format_defWidth;
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = l_Std_Format_pretty(v___x_443_, v___x_444_, v___x_445_, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instToString(lean_object* v_n_447_){
_start:
{
lean_object* v___f_448_; 
v___f_448_ = lean_alloc_closure((void*)(l_BitVec_instToString___lam__0), 2, 1);
lean_closure_set(v___f_448_, 0, v_n_447_);
return v___f_448_;
}
}
LEAN_EXPORT lean_object* l_BitVec_neg(lean_object* v_n_449_, lean_object* v_x_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_451_ = lean_unsigned_to_nat(2u);
v___x_452_ = lean_nat_pow(v___x_451_, v_n_449_);
v___x_453_ = lean_nat_sub(v___x_452_, v_x_450_);
lean_dec(v___x_452_);
v___x_454_ = l_BitVec_ofNat(v_n_449_, v___x_453_);
lean_dec(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_BitVec_neg___boxed(lean_object* v_n_455_, lean_object* v_x_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_BitVec_neg(v_n_455_, v_x_456_);
lean_dec(v_x_456_);
lean_dec(v_n_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instNeg(lean_object* v_n_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_closure((void*)(l_BitVec_neg___boxed), 2, 1);
lean_closure_set(v___x_459_, 0, v_n_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_BitVec_abs(lean_object* v_n_460_, lean_object* v_x_461_){
_start:
{
uint8_t v___y_463_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_nat_dec_lt(v___x_465_, v_n_460_);
if (v___x_466_ == 0)
{
v___y_463_ = v___x_466_;
goto v___jp_462_;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_nat_sub(v_n_460_, v___x_467_);
v___x_469_ = l_Nat_testBit(v_x_461_, v___x_468_);
lean_dec(v___x_468_);
v___y_463_ = v___x_469_;
goto v___jp_462_;
}
v___jp_462_:
{
if (v___y_463_ == 0)
{
lean_inc(v_x_461_);
return v_x_461_;
}
else
{
lean_object* v___x_464_; 
v___x_464_ = l_BitVec_neg(v_n_460_, v_x_461_);
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_abs___boxed(lean_object* v_n_470_, lean_object* v_x_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_BitVec_abs(v_n_470_, v_x_471_);
lean_dec(v_x_471_);
lean_dec(v_n_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mul(lean_object* v_n_473_, lean_object* v_x_474_, lean_object* v_y_475_){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_nat_mul(v_x_474_, v_y_475_);
v___x_477_ = l_BitVec_ofNat(v_n_473_, v___x_476_);
lean_dec(v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mul___boxed(lean_object* v_n_478_, lean_object* v_x_479_, lean_object* v_y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_BitVec_mul(v_n_478_, v_x_479_, v_y_480_);
lean_dec(v_y_480_);
lean_dec(v_x_479_);
lean_dec(v_n_478_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMul(lean_object* v_n_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lean_alloc_closure((void*)(l_BitVec_mul___boxed), 3, 1);
lean_closure_set(v___x_483_, 0, v_n_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_BitVec_pow(lean_object* v_n_484_, lean_object* v_x_485_, lean_object* v_y_486_){
_start:
{
lean_object* v_zero_487_; uint8_t v_isZero_488_; 
v_zero_487_ = lean_unsigned_to_nat(0u);
v_isZero_488_ = lean_nat_dec_eq(v_y_486_, v_zero_487_);
if (v_isZero_488_ == 1)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = l_BitVec_ofNat(v_n_484_, v___x_489_);
return v___x_490_;
}
else
{
lean_object* v_one_491_; lean_object* v_n_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_one_491_ = lean_unsigned_to_nat(1u);
v_n_492_ = lean_nat_sub(v_y_486_, v_one_491_);
v___x_493_ = l_BitVec_pow(v_n_484_, v_x_485_, v_n_492_);
lean_dec(v_n_492_);
v___x_494_ = l_BitVec_mul(v_n_484_, v___x_493_, v_x_485_);
lean_dec(v___x_493_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_pow___boxed(lean_object* v_n_495_, lean_object* v_x_496_, lean_object* v_y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_BitVec_pow(v_n_495_, v_x_496_, v_y_497_);
lean_dec(v_y_497_);
lean_dec(v_x_496_);
lean_dec(v_n_495_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat___lam__0(lean_object* v_n_499_, lean_object* v_x_500_, lean_object* v_y_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_BitVec_pow(v_n_499_, v_x_500_, v_y_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat___lam__0___boxed(lean_object* v_n_503_, lean_object* v_x_504_, lean_object* v_y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_BitVec_instPowNat___lam__0(v_n_503_, v_x_504_, v_y_505_);
lean_dec(v_y_505_);
lean_dec(v_x_504_);
lean_dec(v_n_503_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat(lean_object* v_n_507_){
_start:
{
lean_object* v___f_508_; 
v___f_508_ = lean_alloc_closure((void*)(l_BitVec_instPowNat___lam__0___boxed), 3, 1);
lean_closure_set(v___f_508_, 0, v_n_507_);
return v___f_508_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___redArg(lean_object* v_x_509_, lean_object* v_y_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = lean_nat_div(v_x_509_, v_y_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___redArg___boxed(lean_object* v_x_512_, lean_object* v_y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_BitVec_udiv___redArg(v_x_512_, v_y_513_);
lean_dec(v_y_513_);
lean_dec(v_x_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv(lean_object* v_n_515_, lean_object* v_x_516_, lean_object* v_y_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = lean_nat_div(v_x_516_, v_y_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___boxed(lean_object* v_n_519_, lean_object* v_x_520_, lean_object* v_y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_BitVec_udiv(v_n_519_, v_x_520_, v_y_521_);
lean_dec(v_y_521_);
lean_dec(v_x_520_);
lean_dec(v_n_519_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDiv(lean_object* v_n_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = lean_alloc_closure((void*)(l_BitVec_udiv___boxed), 3, 1);
lean_closure_set(v___x_524_, 0, v_n_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___redArg(lean_object* v_x_525_, lean_object* v_y_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_nat_mod(v_x_525_, v_y_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___redArg___boxed(lean_object* v_x_528_, lean_object* v_y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_BitVec_umod___redArg(v_x_528_, v_y_529_);
lean_dec(v_y_529_);
lean_dec(v_x_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod(lean_object* v_n_531_, lean_object* v_x_532_, lean_object* v_y_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_nat_mod(v_x_532_, v_y_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___boxed(lean_object* v_n_535_, lean_object* v_x_536_, lean_object* v_y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_BitVec_umod(v_n_535_, v_x_536_, v_y_537_);
lean_dec(v_y_537_);
lean_dec(v_x_536_);
lean_dec(v_n_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMod(lean_object* v_n_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = lean_alloc_closure((void*)(l_BitVec_umod___boxed), 3, 1);
lean_closure_set(v___x_540_, 0, v_n_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtUDiv(lean_object* v_n_541_, lean_object* v_x_542_, lean_object* v_y_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = l_BitVec_ofNat(v_n_541_, v___x_544_);
v___x_546_ = lean_nat_dec_eq(v_y_543_, v___x_545_);
lean_dec(v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
v___x_547_ = lean_nat_div(v_x_542_, v_y_543_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = l_BitVec_allOnes(v_n_541_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtUDiv___boxed(lean_object* v_n_549_, lean_object* v_x_550_, lean_object* v_y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_BitVec_smtUDiv(v_n_549_, v_x_550_, v_y_551_);
lean_dec(v_y_551_);
lean_dec(v_x_550_);
lean_dec(v_n_549_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv(lean_object* v_n_553_, lean_object* v_x_554_, lean_object* v_y_555_){
_start:
{
uint8_t v___y_557_; uint8_t v___y_563_; uint8_t v___y_571_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_nat_dec_lt(v___x_582_, v_n_553_);
if (v___x_583_ == 0)
{
v___y_571_ = v___x_583_;
goto v___jp_570_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = lean_nat_sub(v_n_553_, v___x_584_);
v___x_586_ = l_Nat_testBit(v_x_554_, v___x_585_);
lean_dec(v___x_585_);
v___y_571_ = v___x_586_;
goto v___jp_570_;
}
v___jp_556_:
{
if (v___y_557_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = lean_nat_div(v_x_554_, v_y_555_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = l_BitVec_neg(v_n_553_, v_y_555_);
v___x_560_ = lean_nat_div(v_x_554_, v___x_559_);
lean_dec(v___x_559_);
v___x_561_ = l_BitVec_neg(v_n_553_, v___x_560_);
lean_dec(v___x_560_);
return v___x_561_;
}
}
v___jp_562_:
{
if (v___y_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = l_BitVec_neg(v_n_553_, v_x_554_);
v___x_565_ = lean_nat_div(v___x_564_, v_y_555_);
lean_dec(v___x_564_);
v___x_566_ = l_BitVec_neg(v_n_553_, v___x_565_);
lean_dec(v___x_565_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = l_BitVec_neg(v_n_553_, v_x_554_);
v___x_568_ = l_BitVec_neg(v_n_553_, v_y_555_);
v___x_569_ = lean_nat_div(v___x_567_, v___x_568_);
lean_dec(v___x_568_);
lean_dec(v___x_567_);
return v___x_569_;
}
}
v___jp_570_:
{
if (v___y_571_ == 0)
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_nat_dec_lt(v___x_572_, v_n_553_);
if (v___x_573_ == 0)
{
v___y_557_ = v___x_573_;
goto v___jp_556_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_nat_sub(v_n_553_, v___x_574_);
v___x_576_ = l_Nat_testBit(v_y_555_, v___x_575_);
lean_dec(v___x_575_);
v___y_557_ = v___x_576_;
goto v___jp_556_;
}
}
else
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_nat_dec_lt(v___x_577_, v_n_553_);
if (v___x_578_ == 0)
{
v___y_563_ = v___x_578_;
goto v___jp_562_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_sub(v_n_553_, v___x_579_);
v___x_581_ = l_Nat_testBit(v_y_555_, v___x_580_);
lean_dec(v___x_580_);
v___y_563_ = v___x_581_;
goto v___jp_562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv___boxed(lean_object* v_n_587_, lean_object* v_x_588_, lean_object* v_y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_BitVec_sdiv(v_n_587_, v_x_588_, v_y_589_);
lean_dec(v_y_589_);
lean_dec(v_x_588_);
lean_dec(v_n_587_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv(lean_object* v_n_591_, lean_object* v_x_592_, lean_object* v_y_593_){
_start:
{
uint8_t v___y_595_; uint8_t v___y_601_; uint8_t v___y_609_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_nat_dec_lt(v___x_620_, v_n_591_);
if (v___x_621_ == 0)
{
v___y_609_ = v___x_621_;
goto v___jp_608_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = lean_nat_sub(v_n_591_, v___x_622_);
v___x_624_ = l_Nat_testBit(v_x_592_, v___x_623_);
lean_dec(v___x_623_);
v___y_609_ = v___x_624_;
goto v___jp_608_;
}
v___jp_594_:
{
if (v___y_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = l_BitVec_smtUDiv(v_n_591_, v_x_592_, v_y_593_);
return v___x_596_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = l_BitVec_neg(v_n_591_, v_y_593_);
v___x_598_ = l_BitVec_smtUDiv(v_n_591_, v_x_592_, v___x_597_);
lean_dec(v___x_597_);
v___x_599_ = l_BitVec_neg(v_n_591_, v___x_598_);
lean_dec(v___x_598_);
return v___x_599_;
}
}
v___jp_600_:
{
if (v___y_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = l_BitVec_neg(v_n_591_, v_x_592_);
v___x_603_ = l_BitVec_smtUDiv(v_n_591_, v___x_602_, v_y_593_);
lean_dec(v___x_602_);
v___x_604_ = l_BitVec_neg(v_n_591_, v___x_603_);
lean_dec(v___x_603_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = l_BitVec_neg(v_n_591_, v_x_592_);
v___x_606_ = l_BitVec_neg(v_n_591_, v_y_593_);
v___x_607_ = l_BitVec_smtUDiv(v_n_591_, v___x_605_, v___x_606_);
lean_dec(v___x_606_);
lean_dec(v___x_605_);
return v___x_607_;
}
}
v___jp_608_:
{
if (v___y_609_ == 0)
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_nat_dec_lt(v___x_610_, v_n_591_);
if (v___x_611_ == 0)
{
v___y_595_ = v___x_611_;
goto v___jp_594_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_nat_sub(v_n_591_, v___x_612_);
v___x_614_ = l_Nat_testBit(v_y_593_, v___x_613_);
lean_dec(v___x_613_);
v___y_595_ = v___x_614_;
goto v___jp_594_;
}
}
else
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_nat_dec_lt(v___x_615_, v_n_591_);
if (v___x_616_ == 0)
{
v___y_601_ = v___x_616_;
goto v___jp_600_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_nat_sub(v_n_591_, v___x_617_);
v___x_619_ = l_Nat_testBit(v_y_593_, v___x_618_);
lean_dec(v___x_618_);
v___y_601_ = v___x_619_;
goto v___jp_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv___boxed(lean_object* v_n_625_, lean_object* v_x_626_, lean_object* v_y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_BitVec_smtSDiv(v_n_625_, v_x_626_, v_y_627_);
lean_dec(v_y_627_);
lean_dec(v_x_626_);
lean_dec(v_n_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_BitVec_srem(lean_object* v_n_629_, lean_object* v_x_630_, lean_object* v_y_631_){
_start:
{
uint8_t v___y_633_; uint8_t v___y_638_; uint8_t v___y_647_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_nat_dec_lt(v___x_658_, v_n_629_);
if (v___x_659_ == 0)
{
v___y_647_ = v___x_659_;
goto v___jp_646_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_sub(v_n_629_, v___x_660_);
v___x_662_ = l_Nat_testBit(v_x_630_, v___x_661_);
lean_dec(v___x_661_);
v___y_647_ = v___x_662_;
goto v___jp_646_;
}
v___jp_632_:
{
if (v___y_633_ == 0)
{
lean_object* v___x_634_; 
v___x_634_ = lean_nat_mod(v_x_630_, v_y_631_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = l_BitVec_neg(v_n_629_, v_y_631_);
v___x_636_ = lean_nat_mod(v_x_630_, v___x_635_);
lean_dec(v___x_635_);
return v___x_636_;
}
}
v___jp_637_:
{
if (v___y_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = l_BitVec_neg(v_n_629_, v_x_630_);
v___x_640_ = lean_nat_mod(v___x_639_, v_y_631_);
lean_dec(v___x_639_);
v___x_641_ = l_BitVec_neg(v_n_629_, v___x_640_);
lean_dec(v___x_640_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = l_BitVec_neg(v_n_629_, v_x_630_);
v___x_643_ = l_BitVec_neg(v_n_629_, v_y_631_);
v___x_644_ = lean_nat_mod(v___x_642_, v___x_643_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
v___x_645_ = l_BitVec_neg(v_n_629_, v___x_644_);
lean_dec(v___x_644_);
return v___x_645_;
}
}
v___jp_646_:
{
if (v___y_647_ == 0)
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_nat_dec_lt(v___x_648_, v_n_629_);
if (v___x_649_ == 0)
{
v___y_633_ = v___x_649_;
goto v___jp_632_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_650_ = lean_unsigned_to_nat(1u);
v___x_651_ = lean_nat_sub(v_n_629_, v___x_650_);
v___x_652_ = l_Nat_testBit(v_y_631_, v___x_651_);
lean_dec(v___x_651_);
v___y_633_ = v___x_652_;
goto v___jp_632_;
}
}
else
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_nat_dec_lt(v___x_653_, v_n_629_);
if (v___x_654_ == 0)
{
v___y_638_ = v___x_654_;
goto v___jp_637_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_unsigned_to_nat(1u);
v___x_656_ = lean_nat_sub(v_n_629_, v___x_655_);
v___x_657_ = l_Nat_testBit(v_y_631_, v___x_656_);
lean_dec(v___x_656_);
v___y_638_ = v___x_657_;
goto v___jp_637_;
}
}
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
uint8_t v___y_671_; uint8_t v___y_679_; uint8_t v___y_690_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_nat_dec_lt(v___x_701_, v_m_667_);
if (v___x_702_ == 0)
{
v___y_690_ = v___x_702_;
goto v___jp_689_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_sub(v_m_667_, v___x_703_);
v___x_705_ = l_Nat_testBit(v_x_668_, v___x_704_);
lean_dec(v___x_704_);
v___y_690_ = v___x_705_;
goto v___jp_689_;
}
v___jp_670_:
{
if (v___y_671_ == 0)
{
lean_object* v___x_672_; 
v___x_672_ = lean_nat_mod(v_x_668_, v_y_669_);
return v___x_672_;
}
else
{
lean_object* v___x_673_; lean_object* v_u_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_673_ = l_BitVec_neg(v_m_667_, v_y_669_);
v_u_674_ = lean_nat_mod(v_x_668_, v___x_673_);
lean_dec(v___x_673_);
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_nat_dec_eq(v_u_674_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
v___x_677_ = l_BitVec_add(v_m_667_, v_u_674_, v_y_669_);
lean_dec(v_u_674_);
return v___x_677_;
}
else
{
return v_u_674_;
}
}
}
v___jp_678_:
{
if (v___y_679_ == 0)
{
lean_object* v___x_680_; lean_object* v_u_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_680_ = l_BitVec_neg(v_m_667_, v_x_668_);
v_u_681_ = lean_nat_mod(v___x_680_, v_y_669_);
lean_dec(v___x_680_);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_nat_dec_eq(v_u_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
v___x_684_ = l_BitVec_sub(v_m_667_, v_y_669_, v_u_681_);
lean_dec(v_u_681_);
return v___x_684_;
}
else
{
return v_u_681_;
}
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = l_BitVec_neg(v_m_667_, v_x_668_);
v___x_686_ = l_BitVec_neg(v_m_667_, v_y_669_);
v___x_687_ = lean_nat_mod(v___x_685_, v___x_686_);
lean_dec(v___x_686_);
lean_dec(v___x_685_);
v___x_688_ = l_BitVec_neg(v_m_667_, v___x_687_);
lean_dec(v___x_687_);
return v___x_688_;
}
}
v___jp_689_:
{
if (v___y_690_ == 0)
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_nat_dec_lt(v___x_691_, v_m_667_);
if (v___x_692_ == 0)
{
v___y_671_ = v___x_692_;
goto v___jp_670_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_nat_sub(v_m_667_, v___x_693_);
v___x_695_ = l_Nat_testBit(v_y_669_, v___x_694_);
lean_dec(v___x_694_);
v___y_671_ = v___x_695_;
goto v___jp_670_;
}
}
else
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_nat_dec_lt(v___x_696_, v_m_667_);
if (v___x_697_ == 0)
{
v___y_679_ = v___x_697_;
goto v___jp_678_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_698_ = lean_unsigned_to_nat(1u);
v___x_699_ = lean_nat_sub(v_m_667_, v___x_698_);
v___x_700_ = l_Nat_testBit(v_y_669_, v___x_699_);
lean_dec(v___x_699_);
v___y_679_ = v___x_700_;
goto v___jp_678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smod___boxed(lean_object* v_m_706_, lean_object* v_x_707_, lean_object* v_y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_BitVec_smod(v_m_706_, v_x_707_, v_y_708_);
lean_dec(v_y_708_);
lean_dec(v_x_707_);
lean_dec(v_m_706_);
return v_res_709_;
}
}
static lean_object* _init_l_BitVec_ofBool___closed__0(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = l_BitVec_ofNat(v___x_711_, v___x_710_);
return v___x_712_;
}
}
static lean_object* _init_l_BitVec_ofBool___closed__1(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = l_BitVec_ofNat(v___x_713_, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBool(uint8_t v_b_715_){
_start:
{
if (v_b_715_ == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_obj_once(&l_BitVec_ofBool___closed__0, &l_BitVec_ofBool___closed__0_once, _init_l_BitVec_ofBool___closed__0);
return v___x_716_;
}
else
{
lean_object* v___x_717_; 
v___x_717_ = lean_obj_once(&l_BitVec_ofBool___closed__1, &l_BitVec_ofBool___closed__1_once, _init_l_BitVec_ofBool___closed__1);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBool___boxed(lean_object* v_b_718_){
_start:
{
uint8_t v_b_boxed_719_; lean_object* v_res_720_; 
v_b_boxed_719_ = lean_unbox(v_b_718_);
v_res_720_ = l_BitVec_ofBool(v_b_boxed_719_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_BitVec_fill(lean_object* v_w_721_, uint8_t v_b_722_){
_start:
{
if (v_b_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = l_BitVec_ofNat(v_w_721_, v___x_723_);
return v___x_724_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = l_BitVec_ofNat(v_w_721_, v___x_725_);
v___x_727_ = l_BitVec_neg(v_w_721_, v___x_726_);
lean_dec(v___x_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_fill___boxed(lean_object* v_w_728_, lean_object* v_b_729_){
_start:
{
uint8_t v_b_boxed_730_; lean_object* v_res_731_; 
v_b_boxed_730_ = lean_unbox(v_b_729_);
v_res_731_ = l_BitVec_fill(v_w_728_, v_b_boxed_730_);
lean_dec(v_w_728_);
return v_res_731_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ult___redArg(lean_object* v_x_732_, lean_object* v_y_733_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = lean_nat_dec_lt(v_x_732_, v_y_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult___redArg___boxed(lean_object* v_x_735_, lean_object* v_y_736_){
_start:
{
uint8_t v_res_737_; lean_object* v_r_738_; 
v_res_737_ = l_BitVec_ult___redArg(v_x_735_, v_y_736_);
lean_dec(v_y_736_);
lean_dec(v_x_735_);
v_r_738_ = lean_box(v_res_737_);
return v_r_738_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ult(lean_object* v_n_739_, lean_object* v_x_740_, lean_object* v_y_741_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = lean_nat_dec_lt(v_x_740_, v_y_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult___boxed(lean_object* v_n_743_, lean_object* v_x_744_, lean_object* v_y_745_){
_start:
{
uint8_t v_res_746_; lean_object* v_r_747_; 
v_res_746_ = l_BitVec_ult(v_n_743_, v_x_744_, v_y_745_);
lean_dec(v_y_745_);
lean_dec(v_x_744_);
lean_dec(v_n_743_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ule___redArg(lean_object* v_x_748_, lean_object* v_y_749_){
_start:
{
uint8_t v___x_750_; 
v___x_750_ = lean_nat_dec_le(v_x_748_, v_y_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule___redArg___boxed(lean_object* v_x_751_, lean_object* v_y_752_){
_start:
{
uint8_t v_res_753_; lean_object* v_r_754_; 
v_res_753_ = l_BitVec_ule___redArg(v_x_751_, v_y_752_);
lean_dec(v_y_752_);
lean_dec(v_x_751_);
v_r_754_ = lean_box(v_res_753_);
return v_r_754_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ule(lean_object* v_n_755_, lean_object* v_x_756_, lean_object* v_y_757_){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = lean_nat_dec_le(v_x_756_, v_y_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule___boxed(lean_object* v_n_759_, lean_object* v_x_760_, lean_object* v_y_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l_BitVec_ule(v_n_759_, v_x_760_, v_y_761_);
lean_dec(v_y_761_);
lean_dec(v_x_760_);
lean_dec(v_n_759_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT uint8_t l_BitVec_slt(lean_object* v_n_764_, lean_object* v_x_765_, lean_object* v_y_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_767_ = l_BitVec_toInt(v_n_764_, v_x_765_);
v___x_768_ = l_BitVec_toInt(v_n_764_, v_y_766_);
v___x_769_ = lean_int_dec_lt(v___x_767_, v___x_768_);
lean_dec(v___x_768_);
lean_dec(v___x_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_BitVec_slt___boxed(lean_object* v_n_770_, lean_object* v_x_771_, lean_object* v_y_772_){
_start:
{
uint8_t v_res_773_; lean_object* v_r_774_; 
v_res_773_ = l_BitVec_slt(v_n_770_, v_x_771_, v_y_772_);
lean_dec(v_n_770_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
LEAN_EXPORT uint8_t l_BitVec_sle(lean_object* v_n_775_, lean_object* v_x_776_, lean_object* v_y_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = l_BitVec_toInt(v_n_775_, v_x_776_);
v___x_779_ = l_BitVec_toInt(v_n_775_, v_y_777_);
v___x_780_ = lean_int_dec_le(v___x_778_, v___x_779_);
lean_dec(v___x_779_);
lean_dec(v___x_778_);
return v___x_780_;
}
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
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight(lean_object* v_m_1009_, lean_object* v_n_1010_){
_start:
{
lean_object* v___f_1011_; 
v___f_1011_ = ((lean_object*)(l_BitVec_instHShiftRight___closed__0));
return v___f_1011_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___boxed(lean_object* v_m_1012_, lean_object* v_n_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_BitVec_instHShiftRight(v_m_1012_, v_n_1013_);
lean_dec(v_n_1013_);
lean_dec(v_m_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg(lean_object* v_n_1015_, lean_object* v_a_1016_, lean_object* v_s_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_BitVec_sshiftRight(v_n_1015_, v_a_1016_, v_s_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg___boxed(lean_object* v_n_1019_, lean_object* v_a_1020_, lean_object* v_s_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_BitVec_sshiftRight_x27___redArg(v_n_1019_, v_a_1020_, v_s_1021_);
lean_dec(v_s_1021_);
lean_dec(v_n_1019_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27(lean_object* v_n_1023_, lean_object* v_m_1024_, lean_object* v_a_1025_, lean_object* v_s_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_BitVec_sshiftRight(v_n_1023_, v_a_1025_, v_s_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___boxed(lean_object* v_n_1028_, lean_object* v_m_1029_, lean_object* v_a_1030_, lean_object* v_s_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_BitVec_sshiftRight_x27(v_n_1028_, v_m_1029_, v_a_1030_, v_s_1031_);
lean_dec(v_s_1031_);
lean_dec(v_m_1029_);
lean_dec(v_n_1028_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux(lean_object* v_w_1033_, lean_object* v_x_1034_, lean_object* v_n_1035_){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1036_ = l_BitVec_shiftLeft(v_w_1033_, v_x_1034_, v_n_1035_);
v___x_1037_ = lean_nat_sub(v_w_1033_, v_n_1035_);
v___x_1038_ = lean_nat_shiftr(v_x_1034_, v___x_1037_);
lean_dec(v___x_1037_);
v___x_1039_ = lean_nat_lor(v___x_1036_, v___x_1038_);
lean_dec(v___x_1038_);
lean_dec(v___x_1036_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux___boxed(lean_object* v_w_1040_, lean_object* v_x_1041_, lean_object* v_n_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_BitVec_rotateLeftAux(v_w_1040_, v_x_1041_, v_n_1042_);
lean_dec(v_n_1042_);
lean_dec(v_x_1041_);
lean_dec(v_w_1040_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft(lean_object* v_w_1044_, lean_object* v_x_1045_, lean_object* v_n_1046_){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_nat_mod(v_n_1046_, v_w_1044_);
v___x_1048_ = l_BitVec_rotateLeftAux(v_w_1044_, v_x_1045_, v___x_1047_);
lean_dec(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft___boxed(lean_object* v_w_1049_, lean_object* v_x_1050_, lean_object* v_n_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_BitVec_rotateLeft(v_w_1049_, v_x_1050_, v_n_1051_);
lean_dec(v_n_1051_);
lean_dec(v_x_1050_);
lean_dec(v_w_1049_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux(lean_object* v_w_1053_, lean_object* v_x_1054_, lean_object* v_n_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1056_ = lean_nat_shiftr(v_x_1054_, v_n_1055_);
v___x_1057_ = lean_nat_sub(v_w_1053_, v_n_1055_);
v___x_1058_ = l_BitVec_shiftLeft(v_w_1053_, v_x_1054_, v___x_1057_);
lean_dec(v___x_1057_);
v___x_1059_ = lean_nat_lor(v___x_1056_, v___x_1058_);
lean_dec(v___x_1058_);
lean_dec(v___x_1056_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux___boxed(lean_object* v_w_1060_, lean_object* v_x_1061_, lean_object* v_n_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_BitVec_rotateRightAux(v_w_1060_, v_x_1061_, v_n_1062_);
lean_dec(v_n_1062_);
lean_dec(v_x_1061_);
lean_dec(v_w_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight(lean_object* v_w_1064_, lean_object* v_x_1065_, lean_object* v_n_1066_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_nat_mod(v_n_1066_, v_w_1064_);
v___x_1068_ = l_BitVec_rotateRightAux(v_w_1064_, v_x_1065_, v___x_1067_);
lean_dec(v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight___boxed(lean_object* v_w_1069_, lean_object* v_x_1070_, lean_object* v_n_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_BitVec_rotateRight(v_w_1069_, v_x_1070_, v_n_1071_);
lean_dec(v_n_1071_);
lean_dec(v_x_1070_);
lean_dec(v_w_1069_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___redArg(lean_object* v_m_1073_, lean_object* v_msbs_1074_, lean_object* v_lsbs_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_nat_shiftl(v_msbs_1074_, v_m_1073_);
v___x_1077_ = lean_nat_lor(v___x_1076_, v_lsbs_1075_);
lean_dec(v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___redArg___boxed(lean_object* v_m_1078_, lean_object* v_msbs_1079_, lean_object* v_lsbs_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_BitVec_append___redArg(v_m_1078_, v_msbs_1079_, v_lsbs_1080_);
lean_dec(v_lsbs_1080_);
lean_dec(v_msbs_1079_);
lean_dec(v_m_1078_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append(lean_object* v_n_1082_, lean_object* v_m_1083_, lean_object* v_msbs_1084_, lean_object* v_lsbs_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_BitVec_append___redArg(v_m_1083_, v_msbs_1084_, v_lsbs_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___boxed(lean_object* v_n_1087_, lean_object* v_m_1088_, lean_object* v_msbs_1089_, lean_object* v_lsbs_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_BitVec_append(v_n_1087_, v_m_1088_, v_msbs_1089_, v_lsbs_1090_);
lean_dec(v_lsbs_1090_);
lean_dec(v_msbs_1089_);
lean_dec(v_m_1088_);
lean_dec(v_n_1087_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat(lean_object* v_w_1092_, lean_object* v_v_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_alloc_closure((void*)(l_BitVec_append___boxed), 4, 2);
lean_closure_set(v___x_1094_, 0, v_w_1092_);
lean_closure_set(v___x_1094_, 1, v_v_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate(lean_object* v_w_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
lean_object* v_zero_1098_; uint8_t v_isZero_1099_; 
v_zero_1098_ = lean_unsigned_to_nat(0u);
v_isZero_1099_ = lean_nat_dec_eq(v_x_1096_, v_zero_1098_);
if (v_isZero_1099_ == 1)
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1100_;
}
else
{
lean_object* v_one_1101_; lean_object* v_n_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_one_1101_ = lean_unsigned_to_nat(1u);
v_n_1102_ = lean_nat_sub(v_x_1096_, v_one_1101_);
v___x_1103_ = lean_nat_mul(v_w_1095_, v_n_1102_);
v___x_1104_ = l_BitVec_replicate(v_w_1095_, v_n_1102_, v_x_1097_);
lean_dec(v_n_1102_);
v___x_1105_ = l_BitVec_append___redArg(v___x_1103_, v_x_1097_, v___x_1104_);
lean_dec(v___x_1104_);
lean_dec(v___x_1103_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate___boxed(lean_object* v_w_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_BitVec_replicate(v_w_1106_, v_x_1107_, v_x_1108_);
lean_dec(v_x_1108_);
lean_dec(v_x_1107_);
lean_dec(v_w_1106_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___redArg(lean_object* v_msbs_1110_, uint8_t v_lsb_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = l_BitVec_ofBool(v_lsb_1111_);
v___x_1114_ = l_BitVec_append___redArg(v___x_1112_, v_msbs_1110_, v___x_1113_);
lean_dec(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___redArg___boxed(lean_object* v_msbs_1115_, lean_object* v_lsb_1116_){
_start:
{
uint8_t v_lsb_boxed_1117_; lean_object* v_res_1118_; 
v_lsb_boxed_1117_ = lean_unbox(v_lsb_1116_);
v_res_1118_ = l_BitVec_concat___redArg(v_msbs_1115_, v_lsb_boxed_1117_);
lean_dec(v_msbs_1115_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat(lean_object* v_n_1119_, lean_object* v_msbs_1120_, uint8_t v_lsb_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_BitVec_concat___redArg(v_msbs_1120_, v_lsb_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___boxed(lean_object* v_n_1123_, lean_object* v_msbs_1124_, lean_object* v_lsb_1125_){
_start:
{
uint8_t v_lsb_boxed_1126_; lean_object* v_res_1127_; 
v_lsb_boxed_1126_ = lean_unbox(v_lsb_1125_);
v_res_1127_ = l_BitVec_concat(v_n_1123_, v_msbs_1124_, v_lsb_boxed_1126_);
lean_dec(v_msbs_1124_);
lean_dec(v_n_1123_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat(lean_object* v_n_1128_, lean_object* v_x_1129_, uint8_t v_b_1130_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_nat_add(v_n_1128_, v___x_1131_);
v___x_1133_ = l_BitVec_concat___redArg(v_x_1129_, v_b_1130_);
v___x_1134_ = l_BitVec_setWidth(v___x_1132_, v_n_1128_, v___x_1133_);
lean_dec(v___x_1133_);
lean_dec(v___x_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat___boxed(lean_object* v_n_1135_, lean_object* v_x_1136_, lean_object* v_b_1137_){
_start:
{
uint8_t v_b_boxed_1138_; lean_object* v_res_1139_; 
v_b_boxed_1138_ = lean_unbox(v_b_1137_);
v_res_1139_ = l_BitVec_shiftConcat(v_n_1135_, v_x_1136_, v_b_boxed_1138_);
lean_dec(v_x_1136_);
lean_dec(v_n_1135_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cons(lean_object* v_n_1140_, uint8_t v_msb_1141_, lean_object* v_lsbs_1142_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = l_BitVec_ofBool(v_msb_1141_);
v___x_1144_ = l_BitVec_append___redArg(v_n_1140_, v___x_1143_, v_lsbs_1142_);
lean_dec(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cons___boxed(lean_object* v_n_1145_, lean_object* v_msb_1146_, lean_object* v_lsbs_1147_){
_start:
{
uint8_t v_msb_boxed_1148_; lean_object* v_res_1149_; 
v_msb_boxed_1148_ = lean_unbox(v_msb_1146_);
v_res_1149_ = l_BitVec_cons(v_n_1145_, v_msb_boxed_1148_, v_lsbs_1147_);
lean_dec(v_lsbs_1147_);
lean_dec(v_n_1145_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow(lean_object* v_w_1150_, lean_object* v_i_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = l_BitVec_ofNat(v_w_1150_, v___x_1152_);
v___x_1154_ = l_BitVec_shiftLeft(v_w_1150_, v___x_1153_, v_i_1151_);
lean_dec(v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow___boxed(lean_object* v_w_1155_, lean_object* v_i_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_BitVec_twoPow(v_w_1155_, v_i_1156_);
lean_dec(v_i_1156_);
lean_dec(v_w_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMin(lean_object* v_w_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = lean_unsigned_to_nat(1u);
v___x_1160_ = lean_nat_sub(v_w_1158_, v___x_1159_);
v___x_1161_ = l_BitVec_twoPow(v_w_1158_, v___x_1160_);
lean_dec(v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMin___boxed(lean_object* v_w_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_BitVec_intMin(v_w_1162_);
lean_dec(v_w_1162_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMax(lean_object* v_w_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1165_ = lean_unsigned_to_nat(1u);
v___x_1166_ = lean_nat_sub(v_w_1164_, v___x_1165_);
v___x_1167_ = l_BitVec_twoPow(v_w_1164_, v___x_1166_);
lean_dec(v___x_1166_);
v___x_1168_ = l_BitVec_ofNat(v_w_1164_, v___x_1165_);
v___x_1169_ = l_BitVec_sub(v_w_1164_, v___x_1167_, v___x_1168_);
lean_dec(v___x_1168_);
lean_dec(v___x_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMax___boxed(lean_object* v_w_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_BitVec_intMax(v_w_1170_);
lean_dec(v_w_1170_);
return v_res_1171_;
}
}
LEAN_EXPORT uint64_t l_BitVec_hash(lean_object* v_n_1172_, lean_object* v_bv_1173_){
_start:
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = lean_unsigned_to_nat(64u);
v___x_1175_ = lean_nat_dec_le(v_n_1172_, v___x_1174_);
if (v___x_1175_ == 0)
{
uint64_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; 
v___x_1176_ = lean_uint64_of_nat(v_bv_1173_);
v___x_1177_ = lean_nat_sub(v_n_1172_, v___x_1174_);
v___x_1178_ = lean_nat_shiftr(v_bv_1173_, v___x_1174_);
v___x_1179_ = l_BitVec_setWidth(v_n_1172_, v___x_1177_, v___x_1178_);
lean_dec(v___x_1178_);
v___x_1180_ = l_BitVec_hash(v___x_1177_, v___x_1179_);
lean_dec(v___x_1179_);
lean_dec(v___x_1177_);
v___x_1181_ = lean_uint64_mix_hash(v___x_1176_, v___x_1180_);
return v___x_1181_;
}
else
{
uint64_t v___x_1182_; 
v___x_1182_ = lean_uint64_of_nat(v_bv_1173_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_hash___boxed(lean_object* v_n_1183_, lean_object* v_bv_1184_){
_start:
{
uint64_t v_res_1185_; lean_object* v_r_1186_; 
v_res_1185_ = l_BitVec_hash(v_n_1183_, v_bv_1184_);
lean_dec(v_bv_1184_);
lean_dec(v_n_1183_);
v_r_1186_ = lean_box_uint64(v_res_1185_);
return v_r_1186_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHashable(lean_object* v_n_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_alloc_closure((void*)(l_BitVec_hash___boxed), 2, 1);
lean_closure_set(v___x_1188_, 0, v_n_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE(lean_object* v_x_1189_){
_start:
{
if (lean_obj_tag(v_x_1189_) == 0)
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1190_;
}
else
{
lean_object* v_head_1191_; lean_object* v_tail_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; 
v_head_1191_ = lean_ctor_get(v_x_1189_, 0);
v_tail_1192_ = lean_ctor_get(v_x_1189_, 1);
v___x_1193_ = l_List_lengthTR___redArg(v_tail_1192_);
v___x_1194_ = l_BitVec_ofBoolListBE(v_tail_1192_);
v___x_1195_ = lean_unbox(v_head_1191_);
v___x_1196_ = l_BitVec_cons(v___x_1193_, v___x_1195_, v___x_1194_);
lean_dec(v___x_1194_);
lean_dec(v___x_1193_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE___boxed(lean_object* v_x_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_BitVec_ofBoolListBE(v_x_1197_);
lean_dec(v_x_1197_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE(lean_object* v_x_1199_){
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
lean_object* v_head_1201_; lean_object* v_tail_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; lean_object* v___x_1205_; 
v_head_1201_ = lean_ctor_get(v_x_1199_, 0);
v_tail_1202_ = lean_ctor_get(v_x_1199_, 1);
v___x_1203_ = l_BitVec_ofBoolListLE(v_tail_1202_);
v___x_1204_ = lean_unbox(v_head_1201_);
v___x_1205_ = l_BitVec_concat___redArg(v___x_1203_, v___x_1204_);
lean_dec(v___x_1203_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE___boxed(lean_object* v_x_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_BitVec_ofBoolListLE(v_x_1206_);
lean_dec(v_x_1206_);
return v_res_1207_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uaddOverflow(lean_object* v_w_1208_, lean_object* v_x_1209_, lean_object* v_y_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1211_ = lean_unsigned_to_nat(2u);
v___x_1212_ = lean_nat_pow(v___x_1211_, v_w_1208_);
v___x_1213_ = lean_nat_add(v_x_1209_, v_y_1210_);
v___x_1214_ = lean_nat_dec_le(v___x_1212_, v___x_1213_);
lean_dec(v___x_1213_);
lean_dec(v___x_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_BitVec_uaddOverflow___boxed(lean_object* v_w_1215_, lean_object* v_x_1216_, lean_object* v_y_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = l_BitVec_uaddOverflow(v_w_1215_, v_x_1216_, v_y_1217_);
lean_dec(v_y_1217_);
lean_dec(v_x_1216_);
lean_dec(v_w_1215_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
static lean_object* _init_l_BitVec_saddOverflow___closed__0(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_unsigned_to_nat(2u);
v___x_1221_ = lean_nat_to_int(v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT uint8_t l_BitVec_saddOverflow(lean_object* v_w_1222_, lean_object* v_x_1223_, lean_object* v_y_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1225_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_sub(v_w_1222_, v___x_1226_);
v___x_1228_ = l_Int_pow(v___x_1225_, v___x_1227_);
lean_dec(v___x_1227_);
v___x_1229_ = l_BitVec_toInt(v_w_1222_, v_x_1223_);
v___x_1230_ = l_BitVec_toInt(v_w_1222_, v_y_1224_);
v___x_1231_ = lean_int_add(v___x_1229_, v___x_1230_);
lean_dec(v___x_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_int_dec_le(v___x_1228_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_int_neg(v___x_1228_);
lean_dec(v___x_1228_);
v___x_1234_ = lean_int_dec_lt(v___x_1231_, v___x_1233_);
lean_dec(v___x_1233_);
lean_dec(v___x_1231_);
return v___x_1234_;
}
else
{
lean_dec(v___x_1231_);
lean_dec(v___x_1228_);
return v___x_1232_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_saddOverflow___boxed(lean_object* v_w_1235_, lean_object* v_x_1236_, lean_object* v_y_1237_){
_start:
{
uint8_t v_res_1238_; lean_object* v_r_1239_; 
v_res_1238_ = l_BitVec_saddOverflow(v_w_1235_, v_x_1236_, v_y_1237_);
lean_dec(v_w_1235_);
v_r_1239_ = lean_box(v_res_1238_);
return v_r_1239_;
}
}
LEAN_EXPORT uint8_t l_BitVec_usubOverflow___redArg(lean_object* v_x_1240_, lean_object* v_y_1241_){
_start:
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_nat_dec_lt(v_x_1240_, v_y_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___redArg___boxed(lean_object* v_x_1243_, lean_object* v_y_1244_){
_start:
{
uint8_t v_res_1245_; lean_object* v_r_1246_; 
v_res_1245_ = l_BitVec_usubOverflow___redArg(v_x_1243_, v_y_1244_);
lean_dec(v_y_1244_);
lean_dec(v_x_1243_);
v_r_1246_ = lean_box(v_res_1245_);
return v_r_1246_;
}
}
LEAN_EXPORT uint8_t l_BitVec_usubOverflow(lean_object* v_w_1247_, lean_object* v_x_1248_, lean_object* v_y_1249_){
_start:
{
uint8_t v___x_1250_; 
v___x_1250_ = lean_nat_dec_lt(v_x_1248_, v_y_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___boxed(lean_object* v_w_1251_, lean_object* v_x_1252_, lean_object* v_y_1253_){
_start:
{
uint8_t v_res_1254_; lean_object* v_r_1255_; 
v_res_1254_ = l_BitVec_usubOverflow(v_w_1251_, v_x_1252_, v_y_1253_);
lean_dec(v_y_1253_);
lean_dec(v_x_1252_);
lean_dec(v_w_1251_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ssubOverflow(lean_object* v_w_1256_, lean_object* v_x_1257_, lean_object* v_y_1258_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1259_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_sub(v_w_1256_, v___x_1260_);
v___x_1262_ = l_Int_pow(v___x_1259_, v___x_1261_);
lean_dec(v___x_1261_);
v___x_1263_ = l_BitVec_toInt(v_w_1256_, v_x_1257_);
v___x_1264_ = l_BitVec_toInt(v_w_1256_, v_y_1258_);
v___x_1265_ = lean_int_sub(v___x_1263_, v___x_1264_);
lean_dec(v___x_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_int_dec_le(v___x_1262_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1267_ = lean_int_neg(v___x_1262_);
lean_dec(v___x_1262_);
v___x_1268_ = lean_int_dec_lt(v___x_1265_, v___x_1267_);
lean_dec(v___x_1267_);
lean_dec(v___x_1265_);
return v___x_1268_;
}
else
{
lean_dec(v___x_1265_);
lean_dec(v___x_1262_);
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ssubOverflow___boxed(lean_object* v_w_1269_, lean_object* v_x_1270_, lean_object* v_y_1271_){
_start:
{
uint8_t v_res_1272_; lean_object* v_r_1273_; 
v_res_1272_ = l_BitVec_ssubOverflow(v_w_1269_, v_x_1270_, v_y_1271_);
lean_dec(v_w_1269_);
v_r_1273_ = lean_box(v_res_1272_);
return v_r_1273_;
}
}
LEAN_EXPORT uint8_t l_BitVec_negOverflow(lean_object* v_w_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1276_ = l_BitVec_toInt(v_w_1274_, v_x_1275_);
v___x_1277_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1278_ = lean_unsigned_to_nat(1u);
v___x_1279_ = lean_nat_sub(v_w_1274_, v___x_1278_);
v___x_1280_ = l_Int_pow(v___x_1277_, v___x_1279_);
lean_dec(v___x_1279_);
v___x_1281_ = lean_int_neg(v___x_1280_);
lean_dec(v___x_1280_);
v___x_1282_ = lean_int_dec_eq(v___x_1276_, v___x_1281_);
lean_dec(v___x_1281_);
lean_dec(v___x_1276_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_BitVec_negOverflow___boxed(lean_object* v_w_1283_, lean_object* v_x_1284_){
_start:
{
uint8_t v_res_1285_; lean_object* v_r_1286_; 
v_res_1285_ = l_BitVec_negOverflow(v_w_1283_, v_x_1284_);
lean_dec(v_w_1283_);
v_r_1286_ = lean_box(v_res_1285_);
return v_r_1286_;
}
}
LEAN_EXPORT uint8_t l_BitVec_sdivOverflow(lean_object* v_w_1287_, lean_object* v_x_1288_, lean_object* v_y_1289_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1290_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_nat_sub(v_w_1287_, v___x_1291_);
v___x_1293_ = l_Int_pow(v___x_1290_, v___x_1292_);
lean_dec(v___x_1292_);
v___x_1294_ = l_BitVec_toInt(v_w_1287_, v_x_1288_);
v___x_1295_ = l_BitVec_toInt(v_w_1287_, v_y_1289_);
v___x_1296_ = lean_int_ediv(v___x_1294_, v___x_1295_);
lean_dec(v___x_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_int_dec_le(v___x_1293_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = lean_int_neg(v___x_1293_);
lean_dec(v___x_1293_);
v___x_1299_ = lean_int_dec_lt(v___x_1296_, v___x_1298_);
lean_dec(v___x_1298_);
lean_dec(v___x_1296_);
return v___x_1299_;
}
else
{
lean_dec(v___x_1296_);
lean_dec(v___x_1293_);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sdivOverflow___boxed(lean_object* v_w_1300_, lean_object* v_x_1301_, lean_object* v_y_1302_){
_start:
{
uint8_t v_res_1303_; lean_object* v_r_1304_; 
v_res_1303_ = l_BitVec_sdivOverflow(v_w_1300_, v_x_1301_, v_y_1302_);
lean_dec(v_w_1300_);
v_r_1304_ = lean_box(v_res_1303_);
return v_r_1304_;
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse(lean_object* v_x_1305_, lean_object* v_x_1306_){
_start:
{
lean_object* v_zero_1307_; uint8_t v_isZero_1308_; 
v_zero_1307_ = lean_unsigned_to_nat(0u);
v_isZero_1308_ = lean_nat_dec_eq(v_x_1305_, v_zero_1307_);
if (v_isZero_1308_ == 1)
{
lean_inc(v_x_1306_);
return v_x_1306_;
}
else
{
lean_object* v_one_1309_; lean_object* v_n_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_one_1309_ = lean_unsigned_to_nat(1u);
v_n_1310_ = lean_nat_sub(v_x_1305_, v_one_1309_);
v___x_1311_ = lean_nat_add(v_n_1310_, v_one_1309_);
v___x_1312_ = l_BitVec_setWidth(v___x_1311_, v_n_1310_, v_x_1306_);
v___x_1313_ = l_BitVec_reverse(v_n_1310_, v___x_1312_);
lean_dec(v___x_1312_);
lean_dec(v_n_1310_);
v___x_1314_ = lean_nat_dec_lt(v_zero_1307_, v___x_1311_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_dec(v___x_1311_);
v___x_1315_ = l_BitVec_concat___redArg(v___x_1313_, v___x_1314_);
lean_dec(v___x_1313_);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; uint8_t v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_nat_sub(v___x_1311_, v_one_1309_);
lean_dec(v___x_1311_);
v___x_1317_ = l_Nat_testBit(v_x_1306_, v___x_1316_);
lean_dec(v___x_1316_);
v___x_1318_ = l_BitVec_concat___redArg(v___x_1313_, v___x_1317_);
lean_dec(v___x_1313_);
return v___x_1318_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse___boxed(lean_object* v_x_1319_, lean_object* v_x_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_BitVec_reverse(v_x_1319_, v_x_1320_);
lean_dec(v_x_1320_);
lean_dec(v_x_1319_);
return v_res_1321_;
}
}
LEAN_EXPORT uint8_t l_BitVec_umulOverflow(lean_object* v_w_1322_, lean_object* v_x_1323_, lean_object* v_y_1324_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1325_ = lean_unsigned_to_nat(2u);
v___x_1326_ = lean_nat_pow(v___x_1325_, v_w_1322_);
v___x_1327_ = lean_nat_mul(v_x_1323_, v_y_1324_);
v___x_1328_ = lean_nat_dec_le(v___x_1326_, v___x_1327_);
lean_dec(v___x_1327_);
lean_dec(v___x_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umulOverflow___boxed(lean_object* v_w_1329_, lean_object* v_x_1330_, lean_object* v_y_1331_){
_start:
{
uint8_t v_res_1332_; lean_object* v_r_1333_; 
v_res_1332_ = l_BitVec_umulOverflow(v_w_1329_, v_x_1330_, v_y_1331_);
lean_dec(v_y_1331_);
lean_dec(v_x_1330_);
lean_dec(v_w_1329_);
v_r_1333_ = lean_box(v_res_1332_);
return v_r_1333_;
}
}
LEAN_EXPORT uint8_t l_BitVec_smulOverflow(lean_object* v_w_1334_, lean_object* v_x_1335_, lean_object* v_y_1336_){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1337_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1338_ = lean_unsigned_to_nat(1u);
v___x_1339_ = lean_nat_sub(v_w_1334_, v___x_1338_);
v___x_1340_ = l_Int_pow(v___x_1337_, v___x_1339_);
lean_dec(v___x_1339_);
v___x_1341_ = l_BitVec_toInt(v_w_1334_, v_x_1335_);
v___x_1342_ = l_BitVec_toInt(v_w_1334_, v_y_1336_);
v___x_1343_ = lean_int_mul(v___x_1341_, v___x_1342_);
lean_dec(v___x_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_int_dec_le(v___x_1340_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1345_ = lean_int_neg(v___x_1340_);
lean_dec(v___x_1340_);
v___x_1346_ = lean_int_dec_lt(v___x_1343_, v___x_1345_);
lean_dec(v___x_1345_);
lean_dec(v___x_1343_);
return v___x_1346_;
}
else
{
lean_dec(v___x_1343_);
lean_dec(v___x_1340_);
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smulOverflow___boxed(lean_object* v_w_1347_, lean_object* v_x_1348_, lean_object* v_y_1349_){
_start:
{
uint8_t v_res_1350_; lean_object* v_r_1351_; 
v_res_1350_ = l_BitVec_smulOverflow(v_w_1347_, v_x_1348_, v_y_1349_);
lean_dec(v_w_1347_);
v_r_1351_ = lean_box(v_res_1350_);
return v_r_1351_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec(lean_object* v_w_1352_, lean_object* v_x_1353_, lean_object* v_n_1354_){
_start:
{
lean_object* v_zero_1355_; uint8_t v_isZero_1356_; 
v_zero_1355_ = lean_unsigned_to_nat(0u);
v_isZero_1356_ = lean_nat_dec_eq(v_n_1354_, v_zero_1355_);
if (v_isZero_1356_ == 1)
{
uint8_t v___x_1357_; 
lean_dec(v_n_1354_);
v___x_1357_ = l_Nat_testBit(v_x_1353_, v_zero_1355_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
v___x_1358_ = l_BitVec_ofNat(v_w_1352_, v_w_1352_);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = lean_unsigned_to_nat(1u);
v___x_1360_ = lean_nat_sub(v_w_1352_, v___x_1359_);
v___x_1361_ = l_BitVec_ofNat(v_w_1352_, v___x_1360_);
lean_dec(v___x_1360_);
return v___x_1361_;
}
}
else
{
uint8_t v___x_1362_; 
v___x_1362_ = l_Nat_testBit(v_x_1353_, v_n_1354_);
if (v___x_1362_ == 0)
{
lean_object* v_one_1363_; lean_object* v_n_1364_; 
v_one_1363_ = lean_unsigned_to_nat(1u);
v_n_1364_ = lean_nat_sub(v_n_1354_, v_one_1363_);
lean_dec(v_n_1354_);
v_n_1354_ = v_n_1364_;
goto _start;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1366_ = lean_unsigned_to_nat(1u);
v___x_1367_ = lean_nat_sub(v_w_1352_, v___x_1366_);
v___x_1368_ = lean_nat_sub(v___x_1367_, v_n_1354_);
lean_dec(v_n_1354_);
lean_dec(v___x_1367_);
v___x_1369_ = l_BitVec_ofNat(v_w_1352_, v___x_1368_);
lean_dec(v___x_1368_);
return v___x_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec___boxed(lean_object* v_w_1370_, lean_object* v_x_1371_, lean_object* v_n_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_BitVec_clzAuxRec(v_w_1370_, v_x_1371_, v_n_1372_);
lean_dec(v_x_1371_);
lean_dec(v_w_1370_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clz(lean_object* v_w_1374_, lean_object* v_x_1375_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = lean_nat_sub(v_w_1374_, v___x_1376_);
v___x_1378_ = l_BitVec_clzAuxRec(v_w_1374_, v_x_1375_, v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clz___boxed(lean_object* v_w_1379_, lean_object* v_x_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_BitVec_clz(v_w_1379_, v_x_1380_);
lean_dec(v_x_1380_);
lean_dec(v_w_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ctz(lean_object* v_w_1382_, lean_object* v_x_1383_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = l_BitVec_reverse(v_w_1382_, v_x_1383_);
v___x_1385_ = l_BitVec_clz(v_w_1382_, v___x_1384_);
lean_dec(v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ctz___boxed(lean_object* v_w_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_BitVec_ctz(v_w_1386_, v_x_1387_);
lean_dec(v_x_1387_);
lean_dec(v_w_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg(lean_object* v_x_1389_, lean_object* v_pos_1390_, lean_object* v_acc_1391_){
_start:
{
lean_object* v_zero_1392_; uint8_t v_isZero_1393_; 
v_zero_1392_ = lean_unsigned_to_nat(0u);
v_isZero_1393_ = lean_nat_dec_eq(v_pos_1390_, v_zero_1392_);
if (v_isZero_1393_ == 1)
{
lean_dec(v_pos_1390_);
return v_acc_1391_;
}
else
{
lean_object* v_one_1394_; lean_object* v_n_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v_one_1394_ = lean_unsigned_to_nat(1u);
v_n_1395_ = lean_nat_sub(v_pos_1390_, v_one_1394_);
lean_dec(v_pos_1390_);
v___x_1396_ = l_Nat_testBit(v_x_1389_, v_n_1395_);
v___x_1397_ = l_Bool_toNat(v___x_1396_);
v___x_1398_ = lean_nat_add(v_acc_1391_, v___x_1397_);
lean_dec(v___x_1397_);
lean_dec(v_acc_1391_);
v_pos_1390_ = v_n_1395_;
v_acc_1391_ = v___x_1398_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg___boxed(lean_object* v_x_1400_, lean_object* v_pos_1401_, lean_object* v_acc_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_BitVec_cpopNatRec___redArg(v_x_1400_, v_pos_1401_, v_acc_1402_);
lean_dec(v_x_1400_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec(lean_object* v_w_1404_, lean_object* v_x_1405_, lean_object* v_pos_1406_, lean_object* v_acc_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_BitVec_cpopNatRec___redArg(v_x_1405_, v_pos_1406_, v_acc_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___boxed(lean_object* v_w_1409_, lean_object* v_x_1410_, lean_object* v_pos_1411_, lean_object* v_acc_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_BitVec_cpopNatRec(v_w_1409_, v_x_1410_, v_pos_1411_, v_acc_1412_);
lean_dec(v_x_1410_);
lean_dec(v_w_1409_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpop(lean_object* v_w_1414_, lean_object* v_x_1415_){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = lean_unsigned_to_nat(0u);
lean_inc(v_w_1414_);
v___x_1417_ = l_BitVec_cpopNatRec___redArg(v_x_1415_, v_w_1414_, v___x_1416_);
v___x_1418_ = l_BitVec_ofNat(v_w_1414_, v___x_1417_);
lean_dec(v___x_1417_);
lean_dec(v_w_1414_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpop___boxed(lean_object* v_w_1419_, lean_object* v_x_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_BitVec_cpop(v_w_1419_, v_x_1420_);
lean_dec(v_x_1420_);
return v_res_1421_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WF(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Linear(builtin);
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
