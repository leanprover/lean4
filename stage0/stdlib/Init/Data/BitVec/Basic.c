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
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_237_);
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
lean_dec_ref(v_a_237_);
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
lean_inc(v_quotContext_249_);
v_currMacroScope_250_ = lean_ctor_get(v_a_237_, 2);
lean_inc(v_currMacroScope_250_);
v_ref_251_ = lean_ctor_get(v_a_237_, 5);
lean_inc(v_ref_251_);
lean_dec_ref(v_a_237_);
v___x_252_ = lean_unsigned_to_nat(2u);
v___x_253_ = l_Lean_Syntax_getArg(v_x_236_, v___x_252_);
lean_dec(v_x_236_);
v___x_254_ = 0;
v___x_255_ = l_Lean_SourceInfo_fromRef(v_ref_251_, v___x_254_);
lean_dec(v_ref_251_);
v___x_256_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
v___x_257_ = lean_obj_once(&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6, &l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6_once, _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__6);
v___x_258_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__8));
v___x_259_ = l_Lean_addMacroScope(v_quotContext_249_, v___x_258_, v_currMacroScope_250_);
v___x_260_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__10));
lean_inc(v___x_255_);
v___x_261_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_261_, 0, v___x_255_);
lean_ctor_set(v___x_261_, 1, v___x_257_);
lean_ctor_set(v___x_261_, 2, v___x_259_);
lean_ctor_set(v___x_261_, 3, v___x_260_);
v___x_262_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12));
lean_inc(v___x_255_);
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
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat(lean_object* v_x_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
lean_inc(v_x_266_);
v___x_270_ = l_Lean_Syntax_isOfKind(v_x_266_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v_x_266_);
v___x_271_ = lean_box(0);
v___x_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v_a_268_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = l_Lean_Syntax_getArg(v_x_266_, v___x_273_);
lean_dec(v_x_266_);
v___x_275_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_274_);
v___x_276_ = l_Lean_Syntax_matchesNull(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_a_268_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_279_ = l_Lean_Syntax_getArg(v___x_274_, v___x_273_);
v___x_280_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__6));
lean_inc(v___x_279_);
v___x_281_ = l_Lean_Syntax_isOfKind(v___x_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v___x_279_);
lean_dec(v___x_274_);
v___x_282_ = lean_box(0);
v___x_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_a_268_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = l_Lean_Syntax_getArg(v___x_274_, v___x_284_);
lean_dec(v___x_274_);
v___x_286_ = 0;
v___x_287_ = l_Lean_SourceInfo_fromRef(v_a_267_, v___x_286_);
v___x_288_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__2));
v___x_289_ = ((lean_object*)(l_BitVec_term_____x23_____00__closed__12));
lean_inc(v___x_287_);
v___x_290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_287_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = l_Lean_Syntax_node3(v___x_287_, v___x_288_, v___x_279_, v___x_290_, v___x_285_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_a_268_);
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNat___boxed(lean_object* v_x_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_BitVec_unexpandBitVecOfNat(v_x_293_, v_a_294_, v_a_295_);
lean_dec(v_a_294_);
return v_res_296_;
}
}
static lean_object* _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__0));
v___x_323_ = l_String_toRawSubstring_x27(v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1(lean_object* v_x_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = ((lean_object*)(l_BitVec_term_____x23_x27_____00__closed__1));
lean_inc(v_x_334_);
v___x_338_ = l_Lean_Syntax_isOfKind(v_x_334_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec_ref(v_a_335_);
lean_dec(v_x_334_);
v___x_339_ = lean_box(1);
v___x_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_a_336_);
return v___x_340_;
}
else
{
lean_object* v_quotContext_341_; lean_object* v_currMacroScope_342_; lean_object* v_ref_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_quotContext_341_ = lean_ctor_get(v_a_335_, 1);
lean_inc(v_quotContext_341_);
v_currMacroScope_342_ = lean_ctor_get(v_a_335_, 2);
lean_inc(v_currMacroScope_342_);
v_ref_343_ = lean_ctor_get(v_a_335_, 5);
lean_inc(v_ref_343_);
lean_dec_ref(v_a_335_);
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = l_Lean_Syntax_getArg(v_x_334_, v___x_344_);
v___x_346_ = lean_unsigned_to_nat(2u);
v___x_347_ = l_Lean_Syntax_getArg(v_x_334_, v___x_346_);
lean_dec(v_x_334_);
v___x_348_ = 0;
v___x_349_ = l_Lean_SourceInfo_fromRef(v_ref_343_, v___x_348_);
lean_dec(v_ref_343_);
v___x_350_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
v___x_351_ = lean_obj_once(&l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1, &l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1_once, _init_l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__1);
v___x_352_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__3));
v___x_353_ = l_Lean_addMacroScope(v_quotContext_341_, v___x_352_, v_currMacroScope_342_);
v___x_354_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23_x27______1___closed__5));
lean_inc(v___x_349_);
v___x_355_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_355_, 0, v___x_349_);
lean_ctor_set(v___x_355_, 1, v___x_351_);
lean_ctor_set(v___x_355_, 2, v___x_353_);
lean_ctor_set(v___x_355_, 3, v___x_354_);
v___x_356_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__12));
lean_inc(v___x_349_);
v___x_357_ = l_Lean_Syntax_node2(v___x_349_, v___x_356_, v___x_345_, v___x_347_);
v___x_358_ = l_Lean_Syntax_node2(v___x_349_, v___x_350_, v___x_355_, v___x_357_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v_a_336_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt(lean_object* v_x_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = ((lean_object*)(l_BitVec___aux__Init__Data__BitVec__Basic______macroRules__BitVec__term_____x23______1___closed__4));
lean_inc(v_x_360_);
v___x_364_ = l_Lean_Syntax_isOfKind(v_x_360_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec(v_x_360_);
v___x_365_ = lean_box(0);
v___x_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_a_362_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = l_Lean_Syntax_getArg(v_x_360_, v___x_367_);
lean_dec(v_x_360_);
v___x_369_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_368_);
v___x_370_ = l_Lean_Syntax_matchesNull(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v___x_372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_a_362_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = l_Lean_Syntax_getArg(v___x_368_, v___x_373_);
v___x_375_ = l_Lean_Syntax_getArg(v___x_368_, v___x_367_);
lean_dec(v___x_368_);
v___x_376_ = 0;
v___x_377_ = l_Lean_SourceInfo_fromRef(v_a_361_, v___x_376_);
v___x_378_ = ((lean_object*)(l_BitVec_term_____x23_x27_____00__closed__1));
v___x_379_ = ((lean_object*)(l_BitVec_term_____x23_x27_____00__closed__2));
lean_inc(v___x_377_);
v___x_380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_377_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = l_Lean_Syntax_node3(v___x_377_, v___x_378_, v___x_374_, v___x_380_, v___x_375_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v_a_362_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_unexpandBitVecOfNatLt___boxed(lean_object* v_x_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_BitVec_unexpandBitVecOfNatLt(v_x_383_, v_a_384_, v_a_385_);
lean_dec(v_a_384_);
return v_res_386_;
}
}
static lean_object* _init_l_BitVec_toHex___boxed__const__1(void){
_start:
{
uint32_t v___x_387_; lean_object* v___x_388_; 
v___x_387_ = 48;
v___x_388_ = lean_box_uint32(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_BitVec_toHex(lean_object* v_n_389_, lean_object* v_x_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_s_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_t_402_; lean_object* v___x_403_; 
v___x_391_ = lean_unsigned_to_nat(16u);
v___x_392_ = l_Nat_toDigits(v___x_391_, v_x_390_);
v_s_393_ = lean_string_mk(v___x_392_);
v___x_394_ = lean_unsigned_to_nat(3u);
v___x_395_ = lean_nat_add(v_n_389_, v___x_394_);
v___x_396_ = lean_unsigned_to_nat(2u);
v___x_397_ = lean_nat_shiftr(v___x_395_, v___x_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_string_length(v_s_393_);
v___x_399_ = lean_nat_sub(v___x_397_, v___x_398_);
lean_dec(v___x_398_);
lean_dec(v___x_397_);
v___x_400_ = l_BitVec_toHex___boxed__const__1;
v___x_401_ = l_List_replicateTR___redArg(v___x_399_, v___x_400_);
v_t_402_ = lean_string_mk(v___x_401_);
v___x_403_ = lean_string_append(v_t_402_, v_s_393_);
lean_dec_ref(v_s_393_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_BitVec_toHex___boxed(lean_object* v_n_404_, lean_object* v_x_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_BitVec_toHex(v_n_404_, v_x_405_);
lean_dec(v_n_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_BitVec_repr(lean_object* v_n_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_414_ = ((lean_object*)(l_BitVec_repr___closed__1));
v___x_415_ = l_BitVec_toHex(v_n_412_, v_a_413_);
v___x_416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
v___x_417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_414_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = ((lean_object*)(l_BitVec_repr___closed__2));
v___x_419_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = l_Nat_reprFast(v_n_412_);
v___x_421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
v___x_422_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_419_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr___lam__0(lean_object* v_n_423_, lean_object* v_a_424_, lean_object* v_x_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_BitVec_repr(v_n_423_, v_a_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr___lam__0___boxed(lean_object* v_n_427_, lean_object* v_a_428_, lean_object* v_x_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_BitVec_instRepr___lam__0(v_n_427_, v_a_428_, v_x_429_);
lean_dec(v_x_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRepr(lean_object* v_n_431_){
_start:
{
lean_object* v___f_432_; 
v___f_432_ = lean_alloc_closure((void*)(l_BitVec_instRepr___lam__0___boxed), 3, 1);
lean_closure_set(v___f_432_, 0, v_n_431_);
return v___f_432_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instToString___lam__0(lean_object* v_n_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_435_ = l_BitVec_repr(v_n_433_, v_a_434_);
v___x_436_ = l_Std_Format_defWidth;
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = l_Std_Format_pretty(v___x_435_, v___x_436_, v___x_437_, v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instToString(lean_object* v_n_439_){
_start:
{
lean_object* v___f_440_; 
v___f_440_ = lean_alloc_closure((void*)(l_BitVec_instToString___lam__0), 2, 1);
lean_closure_set(v___f_440_, 0, v_n_439_);
return v___f_440_;
}
}
LEAN_EXPORT lean_object* l_BitVec_neg(lean_object* v_n_441_, lean_object* v_x_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_443_ = lean_unsigned_to_nat(2u);
v___x_444_ = lean_nat_pow(v___x_443_, v_n_441_);
v___x_445_ = lean_nat_sub(v___x_444_, v_x_442_);
lean_dec(v___x_444_);
v___x_446_ = l_BitVec_ofNat(v_n_441_, v___x_445_);
lean_dec(v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_BitVec_neg___boxed(lean_object* v_n_447_, lean_object* v_x_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_BitVec_neg(v_n_447_, v_x_448_);
lean_dec(v_x_448_);
lean_dec(v_n_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instNeg(lean_object* v_n_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = lean_alloc_closure((void*)(l_BitVec_neg___boxed), 2, 1);
lean_closure_set(v___x_451_, 0, v_n_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_BitVec_abs(lean_object* v_n_452_, lean_object* v_x_453_){
_start:
{
uint8_t v___y_455_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_nat_dec_lt(v___x_457_, v_n_452_);
if (v___x_458_ == 0)
{
v___y_455_ = v___x_458_;
goto v___jp_454_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_sub(v_n_452_, v___x_459_);
v___x_461_ = l_Nat_testBit(v_x_453_, v___x_460_);
lean_dec(v___x_460_);
v___y_455_ = v___x_461_;
goto v___jp_454_;
}
v___jp_454_:
{
if (v___y_455_ == 0)
{
lean_inc(v_x_453_);
return v_x_453_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = l_BitVec_neg(v_n_452_, v_x_453_);
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_abs___boxed(lean_object* v_n_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_BitVec_abs(v_n_462_, v_x_463_);
lean_dec(v_x_463_);
lean_dec(v_n_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mul(lean_object* v_n_465_, lean_object* v_x_466_, lean_object* v_y_467_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_nat_mul(v_x_466_, v_y_467_);
v___x_469_ = l_BitVec_ofNat(v_n_465_, v___x_468_);
lean_dec(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mul___boxed(lean_object* v_n_470_, lean_object* v_x_471_, lean_object* v_y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_BitVec_mul(v_n_470_, v_x_471_, v_y_472_);
lean_dec(v_y_472_);
lean_dec(v_x_471_);
lean_dec(v_n_470_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMul(lean_object* v_n_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_closure((void*)(l_BitVec_mul___boxed), 3, 1);
lean_closure_set(v___x_475_, 0, v_n_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_BitVec_pow(lean_object* v_n_476_, lean_object* v_x_477_, lean_object* v_y_478_){
_start:
{
lean_object* v_zero_479_; uint8_t v_isZero_480_; 
v_zero_479_ = lean_unsigned_to_nat(0u);
v_isZero_480_ = lean_nat_dec_eq(v_y_478_, v_zero_479_);
if (v_isZero_480_ == 1)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = l_BitVec_ofNat(v_n_476_, v___x_481_);
return v___x_482_;
}
else
{
lean_object* v_one_483_; lean_object* v_n_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_one_483_ = lean_unsigned_to_nat(1u);
v_n_484_ = lean_nat_sub(v_y_478_, v_one_483_);
v___x_485_ = l_BitVec_pow(v_n_476_, v_x_477_, v_n_484_);
lean_dec(v_n_484_);
v___x_486_ = l_BitVec_mul(v_n_476_, v___x_485_, v_x_477_);
lean_dec(v___x_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_pow___boxed(lean_object* v_n_487_, lean_object* v_x_488_, lean_object* v_y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_BitVec_pow(v_n_487_, v_x_488_, v_y_489_);
lean_dec(v_y_489_);
lean_dec(v_x_488_);
lean_dec(v_n_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat___lam__0(lean_object* v_n_491_, lean_object* v_x_492_, lean_object* v_y_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_BitVec_pow(v_n_491_, v_x_492_, v_y_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat___lam__0___boxed(lean_object* v_n_495_, lean_object* v_x_496_, lean_object* v_y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_BitVec_instPowNat___lam__0(v_n_495_, v_x_496_, v_y_497_);
lean_dec(v_y_497_);
lean_dec(v_x_496_);
lean_dec(v_n_495_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat(lean_object* v_n_499_){
_start:
{
lean_object* v___f_500_; 
v___f_500_ = lean_alloc_closure((void*)(l_BitVec_instPowNat___lam__0___boxed), 3, 1);
lean_closure_set(v___f_500_, 0, v_n_499_);
return v___f_500_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___redArg(lean_object* v_x_501_, lean_object* v_y_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_nat_div(v_x_501_, v_y_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___redArg___boxed(lean_object* v_x_504_, lean_object* v_y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_BitVec_udiv___redArg(v_x_504_, v_y_505_);
lean_dec(v_y_505_);
lean_dec(v_x_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv(lean_object* v_n_507_, lean_object* v_x_508_, lean_object* v_y_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_nat_div(v_x_508_, v_y_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___boxed(lean_object* v_n_511_, lean_object* v_x_512_, lean_object* v_y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_BitVec_udiv(v_n_511_, v_x_512_, v_y_513_);
lean_dec(v_y_513_);
lean_dec(v_x_512_);
lean_dec(v_n_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDiv(lean_object* v_n_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_closure((void*)(l_BitVec_udiv___boxed), 3, 1);
lean_closure_set(v___x_516_, 0, v_n_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___redArg(lean_object* v_x_517_, lean_object* v_y_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = lean_nat_mod(v_x_517_, v_y_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___redArg___boxed(lean_object* v_x_520_, lean_object* v_y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_BitVec_umod___redArg(v_x_520_, v_y_521_);
lean_dec(v_y_521_);
lean_dec(v_x_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod(lean_object* v_n_523_, lean_object* v_x_524_, lean_object* v_y_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_nat_mod(v_x_524_, v_y_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___boxed(lean_object* v_n_527_, lean_object* v_x_528_, lean_object* v_y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_BitVec_umod(v_n_527_, v_x_528_, v_y_529_);
lean_dec(v_y_529_);
lean_dec(v_x_528_);
lean_dec(v_n_527_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMod(lean_object* v_n_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_closure((void*)(l_BitVec_umod___boxed), 3, 1);
lean_closure_set(v___x_532_, 0, v_n_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtUDiv(lean_object* v_n_533_, lean_object* v_x_534_, lean_object* v_y_535_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = l_BitVec_ofNat(v_n_533_, v___x_536_);
v___x_538_ = lean_nat_dec_eq(v_y_535_, v___x_537_);
lean_dec(v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
v___x_539_ = lean_nat_div(v_x_534_, v_y_535_);
return v___x_539_;
}
else
{
lean_object* v___x_540_; 
v___x_540_ = l_BitVec_allOnes(v_n_533_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtUDiv___boxed(lean_object* v_n_541_, lean_object* v_x_542_, lean_object* v_y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_BitVec_smtUDiv(v_n_541_, v_x_542_, v_y_543_);
lean_dec(v_y_543_);
lean_dec(v_x_542_);
lean_dec(v_n_541_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv(lean_object* v_n_545_, lean_object* v_x_546_, lean_object* v_y_547_){
_start:
{
uint8_t v___y_549_; uint8_t v___y_555_; uint8_t v___y_563_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_nat_dec_lt(v___x_574_, v_n_545_);
if (v___x_575_ == 0)
{
v___y_563_ = v___x_575_;
goto v___jp_562_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_sub(v_n_545_, v___x_576_);
v___x_578_ = l_Nat_testBit(v_x_546_, v___x_577_);
lean_dec(v___x_577_);
v___y_563_ = v___x_578_;
goto v___jp_562_;
}
v___jp_548_:
{
if (v___y_549_ == 0)
{
lean_object* v___x_550_; 
v___x_550_ = lean_nat_div(v_x_546_, v_y_547_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = l_BitVec_neg(v_n_545_, v_y_547_);
v___x_552_ = lean_nat_div(v_x_546_, v___x_551_);
lean_dec(v___x_551_);
v___x_553_ = l_BitVec_neg(v_n_545_, v___x_552_);
lean_dec(v___x_552_);
return v___x_553_;
}
}
v___jp_554_:
{
if (v___y_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = l_BitVec_neg(v_n_545_, v_x_546_);
v___x_557_ = lean_nat_div(v___x_556_, v_y_547_);
lean_dec(v___x_556_);
v___x_558_ = l_BitVec_neg(v_n_545_, v___x_557_);
lean_dec(v___x_557_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = l_BitVec_neg(v_n_545_, v_x_546_);
v___x_560_ = l_BitVec_neg(v_n_545_, v_y_547_);
v___x_561_ = lean_nat_div(v___x_559_, v___x_560_);
lean_dec(v___x_560_);
lean_dec(v___x_559_);
return v___x_561_;
}
}
v___jp_562_:
{
if (v___y_563_ == 0)
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_nat_dec_lt(v___x_564_, v_n_545_);
if (v___x_565_ == 0)
{
v___y_549_ = v___x_565_;
goto v___jp_548_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_nat_sub(v_n_545_, v___x_566_);
v___x_568_ = l_Nat_testBit(v_y_547_, v___x_567_);
lean_dec(v___x_567_);
v___y_549_ = v___x_568_;
goto v___jp_548_;
}
}
else
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_nat_dec_lt(v___x_569_, v_n_545_);
if (v___x_570_ == 0)
{
v___y_555_ = v___x_570_;
goto v___jp_554_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_nat_sub(v_n_545_, v___x_571_);
v___x_573_ = l_Nat_testBit(v_y_547_, v___x_572_);
lean_dec(v___x_572_);
v___y_555_ = v___x_573_;
goto v___jp_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv___boxed(lean_object* v_n_579_, lean_object* v_x_580_, lean_object* v_y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_BitVec_sdiv(v_n_579_, v_x_580_, v_y_581_);
lean_dec(v_y_581_);
lean_dec(v_x_580_);
lean_dec(v_n_579_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv(lean_object* v_n_583_, lean_object* v_x_584_, lean_object* v_y_585_){
_start:
{
uint8_t v___y_587_; uint8_t v___y_593_; uint8_t v___y_601_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_nat_dec_lt(v___x_612_, v_n_583_);
if (v___x_613_ == 0)
{
v___y_601_ = v___x_613_;
goto v___jp_600_;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_nat_sub(v_n_583_, v___x_614_);
v___x_616_ = l_Nat_testBit(v_x_584_, v___x_615_);
lean_dec(v___x_615_);
v___y_601_ = v___x_616_;
goto v___jp_600_;
}
v___jp_586_:
{
if (v___y_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = l_BitVec_smtUDiv(v_n_583_, v_x_584_, v_y_585_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = l_BitVec_neg(v_n_583_, v_y_585_);
v___x_590_ = l_BitVec_smtUDiv(v_n_583_, v_x_584_, v___x_589_);
lean_dec(v___x_589_);
v___x_591_ = l_BitVec_neg(v_n_583_, v___x_590_);
lean_dec(v___x_590_);
return v___x_591_;
}
}
v___jp_592_:
{
if (v___y_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = l_BitVec_neg(v_n_583_, v_x_584_);
v___x_595_ = l_BitVec_smtUDiv(v_n_583_, v___x_594_, v_y_585_);
lean_dec(v___x_594_);
v___x_596_ = l_BitVec_neg(v_n_583_, v___x_595_);
lean_dec(v___x_595_);
return v___x_596_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = l_BitVec_neg(v_n_583_, v_x_584_);
v___x_598_ = l_BitVec_neg(v_n_583_, v_y_585_);
v___x_599_ = l_BitVec_smtUDiv(v_n_583_, v___x_597_, v___x_598_);
lean_dec(v___x_598_);
lean_dec(v___x_597_);
return v___x_599_;
}
}
v___jp_600_:
{
if (v___y_601_ == 0)
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = lean_nat_dec_lt(v___x_602_, v_n_583_);
if (v___x_603_ == 0)
{
v___y_587_ = v___x_603_;
goto v___jp_586_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_sub(v_n_583_, v___x_604_);
v___x_606_ = l_Nat_testBit(v_y_585_, v___x_605_);
lean_dec(v___x_605_);
v___y_587_ = v___x_606_;
goto v___jp_586_;
}
}
else
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_nat_dec_lt(v___x_607_, v_n_583_);
if (v___x_608_ == 0)
{
v___y_593_ = v___x_608_;
goto v___jp_592_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_sub(v_n_583_, v___x_609_);
v___x_611_ = l_Nat_testBit(v_y_585_, v___x_610_);
lean_dec(v___x_610_);
v___y_593_ = v___x_611_;
goto v___jp_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv___boxed(lean_object* v_n_617_, lean_object* v_x_618_, lean_object* v_y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_BitVec_smtSDiv(v_n_617_, v_x_618_, v_y_619_);
lean_dec(v_y_619_);
lean_dec(v_x_618_);
lean_dec(v_n_617_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_BitVec_srem(lean_object* v_n_621_, lean_object* v_x_622_, lean_object* v_y_623_){
_start:
{
uint8_t v___y_625_; uint8_t v___y_630_; uint8_t v___y_639_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_nat_dec_lt(v___x_650_, v_n_621_);
if (v___x_651_ == 0)
{
v___y_639_ = v___x_651_;
goto v___jp_638_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_nat_sub(v_n_621_, v___x_652_);
v___x_654_ = l_Nat_testBit(v_x_622_, v___x_653_);
lean_dec(v___x_653_);
v___y_639_ = v___x_654_;
goto v___jp_638_;
}
v___jp_624_:
{
if (v___y_625_ == 0)
{
lean_object* v___x_626_; 
v___x_626_ = lean_nat_mod(v_x_622_, v_y_623_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = l_BitVec_neg(v_n_621_, v_y_623_);
v___x_628_ = lean_nat_mod(v_x_622_, v___x_627_);
lean_dec(v___x_627_);
return v___x_628_;
}
}
v___jp_629_:
{
if (v___y_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = l_BitVec_neg(v_n_621_, v_x_622_);
v___x_632_ = lean_nat_mod(v___x_631_, v_y_623_);
lean_dec(v___x_631_);
v___x_633_ = l_BitVec_neg(v_n_621_, v___x_632_);
lean_dec(v___x_632_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_634_ = l_BitVec_neg(v_n_621_, v_x_622_);
v___x_635_ = l_BitVec_neg(v_n_621_, v_y_623_);
v___x_636_ = lean_nat_mod(v___x_634_, v___x_635_);
lean_dec(v___x_635_);
lean_dec(v___x_634_);
v___x_637_ = l_BitVec_neg(v_n_621_, v___x_636_);
lean_dec(v___x_636_);
return v___x_637_;
}
}
v___jp_638_:
{
if (v___y_639_ == 0)
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_nat_dec_lt(v___x_640_, v_n_621_);
if (v___x_641_ == 0)
{
v___y_625_ = v___x_641_;
goto v___jp_624_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_sub(v_n_621_, v___x_642_);
v___x_644_ = l_Nat_testBit(v_y_623_, v___x_643_);
lean_dec(v___x_643_);
v___y_625_ = v___x_644_;
goto v___jp_624_;
}
}
else
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_nat_dec_lt(v___x_645_, v_n_621_);
if (v___x_646_ == 0)
{
v___y_630_ = v___x_646_;
goto v___jp_629_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_nat_sub(v_n_621_, v___x_647_);
v___x_649_ = l_Nat_testBit(v_y_623_, v___x_648_);
lean_dec(v___x_648_);
v___y_630_ = v___x_649_;
goto v___jp_629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_srem___boxed(lean_object* v_n_655_, lean_object* v_x_656_, lean_object* v_y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_BitVec_srem(v_n_655_, v_x_656_, v_y_657_);
lean_dec(v_y_657_);
lean_dec(v_x_656_);
lean_dec(v_n_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smod(lean_object* v_m_659_, lean_object* v_x_660_, lean_object* v_y_661_){
_start:
{
uint8_t v___y_663_; uint8_t v___y_671_; uint8_t v___y_682_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_nat_dec_lt(v___x_693_, v_m_659_);
if (v___x_694_ == 0)
{
v___y_682_ = v___x_694_;
goto v___jp_681_;
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_nat_sub(v_m_659_, v___x_695_);
v___x_697_ = l_Nat_testBit(v_x_660_, v___x_696_);
lean_dec(v___x_696_);
v___y_682_ = v___x_697_;
goto v___jp_681_;
}
v___jp_662_:
{
if (v___y_663_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = lean_nat_mod(v_x_660_, v_y_661_);
return v___x_664_;
}
else
{
lean_object* v___x_665_; lean_object* v_u_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_665_ = l_BitVec_neg(v_m_659_, v_y_661_);
v_u_666_ = lean_nat_mod(v_x_660_, v___x_665_);
lean_dec(v___x_665_);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_nat_dec_eq(v_u_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
v___x_669_ = l_BitVec_add(v_m_659_, v_u_666_, v_y_661_);
lean_dec(v_u_666_);
return v___x_669_;
}
else
{
return v_u_666_;
}
}
}
v___jp_670_:
{
if (v___y_671_ == 0)
{
lean_object* v___x_672_; lean_object* v_u_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_672_ = l_BitVec_neg(v_m_659_, v_x_660_);
v_u_673_ = lean_nat_mod(v___x_672_, v_y_661_);
lean_dec(v___x_672_);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_nat_dec_eq(v_u_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = l_BitVec_sub(v_m_659_, v_y_661_, v_u_673_);
lean_dec(v_u_673_);
return v___x_676_;
}
else
{
return v_u_673_;
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_677_ = l_BitVec_neg(v_m_659_, v_x_660_);
v___x_678_ = l_BitVec_neg(v_m_659_, v_y_661_);
v___x_679_ = lean_nat_mod(v___x_677_, v___x_678_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
v___x_680_ = l_BitVec_neg(v_m_659_, v___x_679_);
lean_dec(v___x_679_);
return v___x_680_;
}
}
v___jp_681_:
{
if (v___y_682_ == 0)
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_nat_dec_lt(v___x_683_, v_m_659_);
if (v___x_684_ == 0)
{
v___y_663_ = v___x_684_;
goto v___jp_662_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_sub(v_m_659_, v___x_685_);
v___x_687_ = l_Nat_testBit(v_y_661_, v___x_686_);
lean_dec(v___x_686_);
v___y_663_ = v___x_687_;
goto v___jp_662_;
}
}
else
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_nat_dec_lt(v___x_688_, v_m_659_);
if (v___x_689_ == 0)
{
v___y_671_ = v___x_689_;
goto v___jp_670_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_sub(v_m_659_, v___x_690_);
v___x_692_ = l_Nat_testBit(v_y_661_, v___x_691_);
lean_dec(v___x_691_);
v___y_671_ = v___x_692_;
goto v___jp_670_;
}
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
LEAN_EXPORT lean_object* l_BitVec_ofBool(uint8_t v_b_707_){
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
LEAN_EXPORT lean_object* l_BitVec_ofBool___boxed(lean_object* v_b_710_){
_start:
{
uint8_t v_b_boxed_711_; lean_object* v_res_712_; 
v_b_boxed_711_ = lean_unbox(v_b_710_);
v_res_712_ = l_BitVec_ofBool(v_b_boxed_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_BitVec_fill(lean_object* v_w_713_, uint8_t v_b_714_){
_start:
{
if (v_b_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = l_BitVec_ofNat(v_w_713_, v___x_715_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = l_BitVec_ofNat(v_w_713_, v___x_717_);
v___x_719_ = l_BitVec_neg(v_w_713_, v___x_718_);
lean_dec(v___x_718_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_fill___boxed(lean_object* v_w_720_, lean_object* v_b_721_){
_start:
{
uint8_t v_b_boxed_722_; lean_object* v_res_723_; 
v_b_boxed_722_ = lean_unbox(v_b_721_);
v_res_723_ = l_BitVec_fill(v_w_720_, v_b_boxed_722_);
lean_dec(v_w_720_);
return v_res_723_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ult___redArg(lean_object* v_x_724_, lean_object* v_y_725_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = lean_nat_dec_lt(v_x_724_, v_y_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult___redArg___boxed(lean_object* v_x_727_, lean_object* v_y_728_){
_start:
{
uint8_t v_res_729_; lean_object* v_r_730_; 
v_res_729_ = l_BitVec_ult___redArg(v_x_727_, v_y_728_);
lean_dec(v_y_728_);
lean_dec(v_x_727_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ult(lean_object* v_n_731_, lean_object* v_x_732_, lean_object* v_y_733_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = lean_nat_dec_lt(v_x_732_, v_y_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult___boxed(lean_object* v_n_735_, lean_object* v_x_736_, lean_object* v_y_737_){
_start:
{
uint8_t v_res_738_; lean_object* v_r_739_; 
v_res_738_ = l_BitVec_ult(v_n_735_, v_x_736_, v_y_737_);
lean_dec(v_y_737_);
lean_dec(v_x_736_);
lean_dec(v_n_735_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ule___redArg(lean_object* v_x_740_, lean_object* v_y_741_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = lean_nat_dec_le(v_x_740_, v_y_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule___redArg___boxed(lean_object* v_x_743_, lean_object* v_y_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_BitVec_ule___redArg(v_x_743_, v_y_744_);
lean_dec(v_y_744_);
lean_dec(v_x_743_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ule(lean_object* v_n_747_, lean_object* v_x_748_, lean_object* v_y_749_){
_start:
{
uint8_t v___x_750_; 
v___x_750_ = lean_nat_dec_le(v_x_748_, v_y_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule___boxed(lean_object* v_n_751_, lean_object* v_x_752_, lean_object* v_y_753_){
_start:
{
uint8_t v_res_754_; lean_object* v_r_755_; 
v_res_754_ = l_BitVec_ule(v_n_751_, v_x_752_, v_y_753_);
lean_dec(v_y_753_);
lean_dec(v_x_752_);
lean_dec(v_n_751_);
v_r_755_ = lean_box(v_res_754_);
return v_r_755_;
}
}
LEAN_EXPORT uint8_t l_BitVec_slt(lean_object* v_n_756_, lean_object* v_x_757_, lean_object* v_y_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_759_ = l_BitVec_toInt(v_n_756_, v_x_757_);
v___x_760_ = l_BitVec_toInt(v_n_756_, v_y_758_);
v___x_761_ = lean_int_dec_lt(v___x_759_, v___x_760_);
lean_dec(v___x_760_);
lean_dec(v___x_759_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_BitVec_slt___boxed(lean_object* v_n_762_, lean_object* v_x_763_, lean_object* v_y_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_BitVec_slt(v_n_762_, v_x_763_, v_y_764_);
lean_dec(v_n_762_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT uint8_t l_BitVec_sle(lean_object* v_n_767_, lean_object* v_x_768_, lean_object* v_y_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_770_ = l_BitVec_toInt(v_n_767_, v_x_768_);
v___x_771_ = l_BitVec_toInt(v_n_767_, v_y_769_);
v___x_772_ = lean_int_dec_le(v___x_770_, v___x_771_);
lean_dec(v___x_771_);
lean_dec(v___x_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sle___boxed(lean_object* v_n_773_, lean_object* v_x_774_, lean_object* v_y_775_){
_start:
{
uint8_t v_res_776_; lean_object* v_r_777_; 
v_res_776_ = l_BitVec_sle(v_n_773_, v_x_774_, v_y_775_);
lean_dec(v_n_773_);
v_r_777_ = lean_box(v_res_776_);
return v_r_777_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___redArg(lean_object* v_x_778_){
_start:
{
lean_inc(v_x_778_);
return v_x_778_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___redArg___boxed(lean_object* v_x_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_BitVec_cast___redArg(v_x_779_);
lean_dec(v_x_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast(lean_object* v_n_781_, lean_object* v_m_782_, lean_object* v_eq_783_, lean_object* v_x_784_){
_start:
{
lean_inc(v_x_784_);
return v_x_784_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___boxed(lean_object* v_n_785_, lean_object* v_m_786_, lean_object* v_eq_787_, lean_object* v_x_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_BitVec_cast(v_n_785_, v_m_786_, v_eq_787_, v_x_788_);
lean_dec(v_x_788_);
lean_dec(v_m_786_);
lean_dec(v_n_785_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___redArg(lean_object* v_start_790_, lean_object* v_len_791_, lean_object* v_x_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_nat_shiftr(v_x_792_, v_start_790_);
v___x_794_ = l_BitVec_ofNat(v_len_791_, v___x_793_);
lean_dec(v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___redArg___boxed(lean_object* v_start_795_, lean_object* v_len_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_BitVec_extractLsb_x27___redArg(v_start_795_, v_len_796_, v_x_797_);
lean_dec(v_x_797_);
lean_dec(v_len_796_);
lean_dec(v_start_795_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27(lean_object* v_n_799_, lean_object* v_start_800_, lean_object* v_len_801_, lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_BitVec_extractLsb_x27___redArg(v_start_800_, v_len_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___boxed(lean_object* v_n_804_, lean_object* v_start_805_, lean_object* v_len_806_, lean_object* v_x_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_BitVec_extractLsb_x27(v_n_804_, v_start_805_, v_len_806_, v_x_807_);
lean_dec(v_x_807_);
lean_dec(v_len_806_);
lean_dec(v_start_805_);
lean_dec(v_n_804_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___redArg(lean_object* v_hi_809_, lean_object* v_lo_810_, lean_object* v_x_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_812_ = lean_nat_sub(v_hi_809_, v_lo_810_);
v___x_813_ = lean_unsigned_to_nat(1u);
v___x_814_ = lean_nat_add(v___x_812_, v___x_813_);
lean_dec(v___x_812_);
v___x_815_ = l_BitVec_extractLsb_x27___redArg(v_lo_810_, v___x_814_, v_x_811_);
lean_dec(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___redArg___boxed(lean_object* v_hi_816_, lean_object* v_lo_817_, lean_object* v_x_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_BitVec_extractLsb___redArg(v_hi_816_, v_lo_817_, v_x_818_);
lean_dec(v_x_818_);
lean_dec(v_lo_817_);
lean_dec(v_hi_816_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb(lean_object* v_n_820_, lean_object* v_hi_821_, lean_object* v_lo_822_, lean_object* v_x_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_BitVec_extractLsb___redArg(v_hi_821_, v_lo_822_, v_x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___boxed(lean_object* v_n_825_, lean_object* v_hi_826_, lean_object* v_lo_827_, lean_object* v_x_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_BitVec_extractLsb(v_n_825_, v_hi_826_, v_lo_827_, v_x_828_);
lean_dec(v_x_828_);
lean_dec(v_lo_827_);
lean_dec(v_hi_826_);
lean_dec(v_n_825_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___redArg(lean_object* v_x_830_){
_start:
{
lean_inc(v_x_830_);
return v_x_830_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___redArg___boxed(lean_object* v_x_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_BitVec_setWidth_x27___redArg(v_x_831_);
lean_dec(v_x_831_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27(lean_object* v_n_833_, lean_object* v_w_834_, lean_object* v_le_835_, lean_object* v_x_836_){
_start:
{
lean_inc(v_x_836_);
return v_x_836_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___boxed(lean_object* v_n_837_, lean_object* v_w_838_, lean_object* v_le_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_BitVec_setWidth_x27(v_n_837_, v_w_838_, v_le_839_, v_x_840_);
lean_dec(v_x_840_);
lean_dec(v_w_838_);
lean_dec(v_n_837_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___redArg(lean_object* v_msbs_842_, lean_object* v_m_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = lean_nat_shiftl(v_msbs_842_, v_m_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___redArg___boxed(lean_object* v_msbs_845_, lean_object* v_m_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_BitVec_shiftLeftZeroExtend___redArg(v_msbs_845_, v_m_846_);
lean_dec(v_m_846_);
lean_dec(v_msbs_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend(lean_object* v_w_848_, lean_object* v_msbs_849_, lean_object* v_m_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = lean_nat_shiftl(v_msbs_849_, v_m_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___boxed(lean_object* v_w_852_, lean_object* v_msbs_853_, lean_object* v_m_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_BitVec_shiftLeftZeroExtend(v_w_852_, v_msbs_853_, v_m_854_);
lean_dec(v_m_854_);
lean_dec(v_msbs_853_);
lean_dec(v_w_852_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth(lean_object* v_w_856_, lean_object* v_v_857_, lean_object* v_x_858_){
_start:
{
uint8_t v___x_859_; 
v___x_859_ = lean_nat_dec_le(v_w_856_, v_v_857_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
v___x_860_ = l_BitVec_ofNat(v_v_857_, v_x_858_);
return v___x_860_;
}
else
{
lean_inc(v_x_858_);
return v_x_858_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth___boxed(lean_object* v_w_861_, lean_object* v_v_862_, lean_object* v_x_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_BitVec_setWidth(v_w_861_, v_v_862_, v_x_863_);
lean_dec(v_x_863_);
lean_dec(v_v_862_);
lean_dec(v_w_861_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zeroExtend(lean_object* v_w_865_, lean_object* v_v_866_, lean_object* v_x_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_BitVec_setWidth(v_w_865_, v_v_866_, v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zeroExtend___boxed(lean_object* v_w_869_, lean_object* v_v_870_, lean_object* v_x_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_BitVec_zeroExtend(v_w_869_, v_v_870_, v_x_871_);
lean_dec(v_x_871_);
lean_dec(v_v_870_);
lean_dec(v_w_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_BitVec_truncate(lean_object* v_w_873_, lean_object* v_v_874_, lean_object* v_x_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_BitVec_setWidth(v_w_873_, v_v_874_, v_x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_BitVec_truncate___boxed(lean_object* v_w_877_, lean_object* v_v_878_, lean_object* v_x_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_BitVec_truncate(v_w_877_, v_v_878_, v_x_879_);
lean_dec(v_x_879_);
lean_dec(v_v_878_);
lean_dec(v_w_877_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_BitVec_signExtend(lean_object* v_w_881_, lean_object* v_v_882_, lean_object* v_x_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = l_BitVec_toInt(v_w_881_, v_x_883_);
v___x_885_ = l_BitVec_ofInt(v_v_882_, v___x_884_);
lean_dec(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_BitVec_signExtend___boxed(lean_object* v_w_886_, lean_object* v_v_887_, lean_object* v_x_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_BitVec_signExtend(v_w_886_, v_v_887_, v_x_888_);
lean_dec(v_v_887_);
lean_dec(v_w_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___redArg(lean_object* v_x_890_, lean_object* v_y_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_nat_land(v_x_890_, v_y_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___redArg___boxed(lean_object* v_x_893_, lean_object* v_y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_BitVec_and___redArg(v_x_893_, v_y_894_);
lean_dec(v_y_894_);
lean_dec(v_x_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and(lean_object* v_n_896_, lean_object* v_x_897_, lean_object* v_y_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = lean_nat_land(v_x_897_, v_y_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___boxed(lean_object* v_n_900_, lean_object* v_x_901_, lean_object* v_y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_BitVec_and(v_n_900_, v_x_901_, v_y_902_);
lean_dec(v_y_902_);
lean_dec(v_x_901_);
lean_dec(v_n_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instAndOp(lean_object* v_w_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = lean_alloc_closure((void*)(l_BitVec_and___boxed), 3, 1);
lean_closure_set(v___x_905_, 0, v_w_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___redArg(lean_object* v_x_906_, lean_object* v_y_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_nat_lor(v_x_906_, v_y_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___redArg___boxed(lean_object* v_x_909_, lean_object* v_y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_BitVec_or___redArg(v_x_909_, v_y_910_);
lean_dec(v_y_910_);
lean_dec(v_x_909_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or(lean_object* v_n_912_, lean_object* v_x_913_, lean_object* v_y_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lean_nat_lor(v_x_913_, v_y_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___boxed(lean_object* v_n_916_, lean_object* v_x_917_, lean_object* v_y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_BitVec_or(v_n_916_, v_x_917_, v_y_918_);
lean_dec(v_y_918_);
lean_dec(v_x_917_);
lean_dec(v_n_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instOrOp(lean_object* v_w_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = lean_alloc_closure((void*)(l_BitVec_or___boxed), 3, 1);
lean_closure_set(v___x_921_, 0, v_w_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___redArg(lean_object* v_x_922_, lean_object* v_y_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_nat_lxor(v_x_922_, v_y_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___redArg___boxed(lean_object* v_x_925_, lean_object* v_y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_BitVec_xor___redArg(v_x_925_, v_y_926_);
lean_dec(v_y_926_);
lean_dec(v_x_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor(lean_object* v_n_928_, lean_object* v_x_929_, lean_object* v_y_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = lean_nat_lxor(v_x_929_, v_y_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___boxed(lean_object* v_n_932_, lean_object* v_x_933_, lean_object* v_y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_BitVec_xor(v_n_932_, v_x_933_, v_y_934_);
lean_dec(v_y_934_);
lean_dec(v_x_933_);
lean_dec(v_n_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instXorOp(lean_object* v_w_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_closure((void*)(l_BitVec_xor___boxed), 3, 1);
lean_closure_set(v___x_937_, 0, v_w_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_BitVec_not(lean_object* v_n_938_, lean_object* v_x_939_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = l_BitVec_allOnes(v_n_938_);
v___x_941_ = lean_nat_lxor(v___x_940_, v_x_939_);
lean_dec(v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_BitVec_not___boxed(lean_object* v_n_942_, lean_object* v_x_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_BitVec_not(v_n_942_, v_x_943_);
lean_dec(v_x_943_);
lean_dec(v_n_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instComplement(lean_object* v_w_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_closure((void*)(l_BitVec_not___boxed), 2, 1);
lean_closure_set(v___x_946_, 0, v_w_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeft(lean_object* v_n_947_, lean_object* v_x_948_, lean_object* v_s_949_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_nat_shiftl(v_x_948_, v_s_949_);
v___x_951_ = l_BitVec_ofNat(v_n_947_, v___x_950_);
lean_dec(v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeft___boxed(lean_object* v_n_952_, lean_object* v_x_953_, lean_object* v_s_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_BitVec_shiftLeft(v_n_952_, v_x_953_, v_s_954_);
lean_dec(v_s_954_);
lean_dec(v_x_953_);
lean_dec(v_n_952_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeftNat(lean_object* v_w_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_closure((void*)(l_BitVec_shiftLeft___boxed), 3, 1);
lean_closure_set(v___x_957_, 0, v_w_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___redArg(lean_object* v_x_958_, lean_object* v_s_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = lean_nat_shiftr(v_x_958_, v_s_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___redArg___boxed(lean_object* v_x_961_, lean_object* v_s_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_BitVec_ushiftRight___redArg(v_x_961_, v_s_962_);
lean_dec(v_s_962_);
lean_dec(v_x_961_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight(lean_object* v_n_964_, lean_object* v_x_965_, lean_object* v_s_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = lean_nat_shiftr(v_x_965_, v_s_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___boxed(lean_object* v_n_968_, lean_object* v_x_969_, lean_object* v_s_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_BitVec_ushiftRight(v_n_968_, v_x_969_, v_s_970_);
lean_dec(v_s_970_);
lean_dec(v_x_969_);
lean_dec(v_n_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRightNat(lean_object* v_w_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_closure((void*)(l_BitVec_ushiftRight___boxed), 3, 1);
lean_closure_set(v___x_973_, 0, v_w_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight(lean_object* v_n_974_, lean_object* v_x_975_, lean_object* v_s_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = l_BitVec_toInt(v_n_974_, v_x_975_);
v___x_978_ = l_Int_shiftRight(v___x_977_, v_s_976_);
lean_dec(v___x_977_);
v___x_979_ = l_BitVec_ofInt(v_n_974_, v___x_978_);
lean_dec(v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight___boxed(lean_object* v_n_980_, lean_object* v_x_981_, lean_object* v_s_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_BitVec_sshiftRight(v_n_980_, v_x_981_, v_s_982_);
lean_dec(v_s_982_);
lean_dec(v_n_980_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg___lam__0(lean_object* v_m_984_, lean_object* v_x_985_, lean_object* v_y_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_BitVec_shiftLeft(v_m_984_, v_x_985_, v_y_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg___lam__0___boxed(lean_object* v_m_988_, lean_object* v_x_989_, lean_object* v_y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_BitVec_instHShiftLeft___redArg___lam__0(v_m_988_, v_x_989_, v_y_990_);
lean_dec(v_y_990_);
lean_dec(v_x_989_);
lean_dec(v_m_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg(lean_object* v_m_992_){
_start:
{
lean_object* v___f_993_; 
v___f_993_ = lean_alloc_closure((void*)(l_BitVec_instHShiftLeft___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_993_, 0, v_m_992_);
return v___f_993_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft(lean_object* v_m_994_, lean_object* v_n_995_){
_start:
{
lean_object* v___f_996_; 
v___f_996_ = lean_alloc_closure((void*)(l_BitVec_instHShiftLeft___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_996_, 0, v_m_994_);
return v___f_996_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___boxed(lean_object* v_m_997_, lean_object* v_n_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_BitVec_instHShiftLeft(v_m_997_, v_n_998_);
lean_dec(v_n_998_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight(lean_object* v_m_1001_, lean_object* v_n_1002_){
_start:
{
lean_object* v___f_1003_; 
v___f_1003_ = ((lean_object*)(l_BitVec_instHShiftRight___closed__0));
return v___f_1003_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___boxed(lean_object* v_m_1004_, lean_object* v_n_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_BitVec_instHShiftRight(v_m_1004_, v_n_1005_);
lean_dec(v_n_1005_);
lean_dec(v_m_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg(lean_object* v_n_1007_, lean_object* v_a_1008_, lean_object* v_s_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_BitVec_sshiftRight(v_n_1007_, v_a_1008_, v_s_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg___boxed(lean_object* v_n_1011_, lean_object* v_a_1012_, lean_object* v_s_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_BitVec_sshiftRight_x27___redArg(v_n_1011_, v_a_1012_, v_s_1013_);
lean_dec(v_s_1013_);
lean_dec(v_n_1011_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27(lean_object* v_n_1015_, lean_object* v_m_1016_, lean_object* v_a_1017_, lean_object* v_s_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_BitVec_sshiftRight(v_n_1015_, v_a_1017_, v_s_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___boxed(lean_object* v_n_1020_, lean_object* v_m_1021_, lean_object* v_a_1022_, lean_object* v_s_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_BitVec_sshiftRight_x27(v_n_1020_, v_m_1021_, v_a_1022_, v_s_1023_);
lean_dec(v_s_1023_);
lean_dec(v_m_1021_);
lean_dec(v_n_1020_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux(lean_object* v_w_1025_, lean_object* v_x_1026_, lean_object* v_n_1027_){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = l_BitVec_shiftLeft(v_w_1025_, v_x_1026_, v_n_1027_);
v___x_1029_ = lean_nat_sub(v_w_1025_, v_n_1027_);
v___x_1030_ = lean_nat_shiftr(v_x_1026_, v___x_1029_);
lean_dec(v___x_1029_);
v___x_1031_ = lean_nat_lor(v___x_1028_, v___x_1030_);
lean_dec(v___x_1030_);
lean_dec(v___x_1028_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux___boxed(lean_object* v_w_1032_, lean_object* v_x_1033_, lean_object* v_n_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_BitVec_rotateLeftAux(v_w_1032_, v_x_1033_, v_n_1034_);
lean_dec(v_n_1034_);
lean_dec(v_x_1033_);
lean_dec(v_w_1032_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft(lean_object* v_w_1036_, lean_object* v_x_1037_, lean_object* v_n_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_nat_mod(v_n_1038_, v_w_1036_);
v___x_1040_ = l_BitVec_rotateLeftAux(v_w_1036_, v_x_1037_, v___x_1039_);
lean_dec(v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft___boxed(lean_object* v_w_1041_, lean_object* v_x_1042_, lean_object* v_n_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_BitVec_rotateLeft(v_w_1041_, v_x_1042_, v_n_1043_);
lean_dec(v_n_1043_);
lean_dec(v_x_1042_);
lean_dec(v_w_1041_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux(lean_object* v_w_1045_, lean_object* v_x_1046_, lean_object* v_n_1047_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1048_ = lean_nat_shiftr(v_x_1046_, v_n_1047_);
v___x_1049_ = lean_nat_sub(v_w_1045_, v_n_1047_);
v___x_1050_ = l_BitVec_shiftLeft(v_w_1045_, v_x_1046_, v___x_1049_);
lean_dec(v___x_1049_);
v___x_1051_ = lean_nat_lor(v___x_1048_, v___x_1050_);
lean_dec(v___x_1050_);
lean_dec(v___x_1048_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux___boxed(lean_object* v_w_1052_, lean_object* v_x_1053_, lean_object* v_n_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_BitVec_rotateRightAux(v_w_1052_, v_x_1053_, v_n_1054_);
lean_dec(v_n_1054_);
lean_dec(v_x_1053_);
lean_dec(v_w_1052_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight(lean_object* v_w_1056_, lean_object* v_x_1057_, lean_object* v_n_1058_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_nat_mod(v_n_1058_, v_w_1056_);
v___x_1060_ = l_BitVec_rotateRightAux(v_w_1056_, v_x_1057_, v___x_1059_);
lean_dec(v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight___boxed(lean_object* v_w_1061_, lean_object* v_x_1062_, lean_object* v_n_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_BitVec_rotateRight(v_w_1061_, v_x_1062_, v_n_1063_);
lean_dec(v_n_1063_);
lean_dec(v_x_1062_);
lean_dec(v_w_1061_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___redArg(lean_object* v_m_1065_, lean_object* v_msbs_1066_, lean_object* v_lsbs_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_nat_shiftl(v_msbs_1066_, v_m_1065_);
v___x_1069_ = lean_nat_lor(v___x_1068_, v_lsbs_1067_);
lean_dec(v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___redArg___boxed(lean_object* v_m_1070_, lean_object* v_msbs_1071_, lean_object* v_lsbs_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_BitVec_append___redArg(v_m_1070_, v_msbs_1071_, v_lsbs_1072_);
lean_dec(v_lsbs_1072_);
lean_dec(v_msbs_1071_);
lean_dec(v_m_1070_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append(lean_object* v_n_1074_, lean_object* v_m_1075_, lean_object* v_msbs_1076_, lean_object* v_lsbs_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_BitVec_append___redArg(v_m_1075_, v_msbs_1076_, v_lsbs_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___boxed(lean_object* v_n_1079_, lean_object* v_m_1080_, lean_object* v_msbs_1081_, lean_object* v_lsbs_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_BitVec_append(v_n_1079_, v_m_1080_, v_msbs_1081_, v_lsbs_1082_);
lean_dec(v_lsbs_1082_);
lean_dec(v_msbs_1081_);
lean_dec(v_m_1080_);
lean_dec(v_n_1079_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat(lean_object* v_w_1084_, lean_object* v_v_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_closure((void*)(l_BitVec_append___boxed), 4, 2);
lean_closure_set(v___x_1086_, 0, v_w_1084_);
lean_closure_set(v___x_1086_, 1, v_v_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate(lean_object* v_w_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v_zero_1090_; uint8_t v_isZero_1091_; 
v_zero_1090_ = lean_unsigned_to_nat(0u);
v_isZero_1091_ = lean_nat_dec_eq(v_x_1088_, v_zero_1090_);
if (v_isZero_1091_ == 1)
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1092_;
}
else
{
lean_object* v_one_1093_; lean_object* v_n_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_one_1093_ = lean_unsigned_to_nat(1u);
v_n_1094_ = lean_nat_sub(v_x_1088_, v_one_1093_);
v___x_1095_ = lean_nat_mul(v_w_1087_, v_n_1094_);
v___x_1096_ = l_BitVec_replicate(v_w_1087_, v_n_1094_, v_x_1089_);
lean_dec(v_n_1094_);
v___x_1097_ = l_BitVec_append___redArg(v___x_1095_, v_x_1089_, v___x_1096_);
lean_dec(v___x_1096_);
lean_dec(v___x_1095_);
return v___x_1097_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate___boxed(lean_object* v_w_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_BitVec_replicate(v_w_1098_, v_x_1099_, v_x_1100_);
lean_dec(v_x_1100_);
lean_dec(v_x_1099_);
lean_dec(v_w_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___redArg(lean_object* v_msbs_1102_, uint8_t v_lsb_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = l_BitVec_ofBool(v_lsb_1103_);
v___x_1106_ = l_BitVec_append___redArg(v___x_1104_, v_msbs_1102_, v___x_1105_);
lean_dec(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___redArg___boxed(lean_object* v_msbs_1107_, lean_object* v_lsb_1108_){
_start:
{
uint8_t v_lsb_boxed_1109_; lean_object* v_res_1110_; 
v_lsb_boxed_1109_ = lean_unbox(v_lsb_1108_);
v_res_1110_ = l_BitVec_concat___redArg(v_msbs_1107_, v_lsb_boxed_1109_);
lean_dec(v_msbs_1107_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat(lean_object* v_n_1111_, lean_object* v_msbs_1112_, uint8_t v_lsb_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_BitVec_concat___redArg(v_msbs_1112_, v_lsb_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___boxed(lean_object* v_n_1115_, lean_object* v_msbs_1116_, lean_object* v_lsb_1117_){
_start:
{
uint8_t v_lsb_boxed_1118_; lean_object* v_res_1119_; 
v_lsb_boxed_1118_ = lean_unbox(v_lsb_1117_);
v_res_1119_ = l_BitVec_concat(v_n_1115_, v_msbs_1116_, v_lsb_boxed_1118_);
lean_dec(v_msbs_1116_);
lean_dec(v_n_1115_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat(lean_object* v_n_1120_, lean_object* v_x_1121_, uint8_t v_b_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = lean_nat_add(v_n_1120_, v___x_1123_);
v___x_1125_ = l_BitVec_concat___redArg(v_x_1121_, v_b_1122_);
v___x_1126_ = l_BitVec_setWidth(v___x_1124_, v_n_1120_, v___x_1125_);
lean_dec(v___x_1125_);
lean_dec(v___x_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat___boxed(lean_object* v_n_1127_, lean_object* v_x_1128_, lean_object* v_b_1129_){
_start:
{
uint8_t v_b_boxed_1130_; lean_object* v_res_1131_; 
v_b_boxed_1130_ = lean_unbox(v_b_1129_);
v_res_1131_ = l_BitVec_shiftConcat(v_n_1127_, v_x_1128_, v_b_boxed_1130_);
lean_dec(v_x_1128_);
lean_dec(v_n_1127_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cons(lean_object* v_n_1132_, uint8_t v_msb_1133_, lean_object* v_lsbs_1134_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = l_BitVec_ofBool(v_msb_1133_);
v___x_1136_ = l_BitVec_append___redArg(v_n_1132_, v___x_1135_, v_lsbs_1134_);
lean_dec(v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cons___boxed(lean_object* v_n_1137_, lean_object* v_msb_1138_, lean_object* v_lsbs_1139_){
_start:
{
uint8_t v_msb_boxed_1140_; lean_object* v_res_1141_; 
v_msb_boxed_1140_ = lean_unbox(v_msb_1138_);
v_res_1141_ = l_BitVec_cons(v_n_1137_, v_msb_boxed_1140_, v_lsbs_1139_);
lean_dec(v_lsbs_1139_);
lean_dec(v_n_1137_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow(lean_object* v_w_1142_, lean_object* v_i_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = l_BitVec_ofNat(v_w_1142_, v___x_1144_);
v___x_1146_ = l_BitVec_shiftLeft(v_w_1142_, v___x_1145_, v_i_1143_);
lean_dec(v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow___boxed(lean_object* v_w_1147_, lean_object* v_i_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_BitVec_twoPow(v_w_1147_, v_i_1148_);
lean_dec(v_i_1148_);
lean_dec(v_w_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMin(lean_object* v_w_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_sub(v_w_1150_, v___x_1151_);
v___x_1153_ = l_BitVec_twoPow(v_w_1150_, v___x_1152_);
lean_dec(v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMin___boxed(lean_object* v_w_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_BitVec_intMin(v_w_1154_);
lean_dec(v_w_1154_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMax(lean_object* v_w_1156_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1157_ = lean_unsigned_to_nat(1u);
v___x_1158_ = lean_nat_sub(v_w_1156_, v___x_1157_);
v___x_1159_ = l_BitVec_twoPow(v_w_1156_, v___x_1158_);
lean_dec(v___x_1158_);
v___x_1160_ = l_BitVec_ofNat(v_w_1156_, v___x_1157_);
v___x_1161_ = l_BitVec_sub(v_w_1156_, v___x_1159_, v___x_1160_);
lean_dec(v___x_1160_);
lean_dec(v___x_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMax___boxed(lean_object* v_w_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_BitVec_intMax(v_w_1162_);
lean_dec(v_w_1162_);
return v_res_1163_;
}
}
LEAN_EXPORT uint64_t l_BitVec_hash(lean_object* v_n_1164_, lean_object* v_bv_1165_){
_start:
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_unsigned_to_nat(64u);
v___x_1167_ = lean_nat_dec_le(v_n_1164_, v___x_1166_);
if (v___x_1167_ == 0)
{
uint64_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint64_t v___x_1172_; uint64_t v___x_1173_; 
v___x_1168_ = lean_uint64_of_nat(v_bv_1165_);
v___x_1169_ = lean_nat_sub(v_n_1164_, v___x_1166_);
v___x_1170_ = lean_nat_shiftr(v_bv_1165_, v___x_1166_);
v___x_1171_ = l_BitVec_setWidth(v_n_1164_, v___x_1169_, v___x_1170_);
lean_dec(v___x_1170_);
v___x_1172_ = l_BitVec_hash(v___x_1169_, v___x_1171_);
lean_dec(v___x_1171_);
lean_dec(v___x_1169_);
v___x_1173_ = lean_uint64_mix_hash(v___x_1168_, v___x_1172_);
return v___x_1173_;
}
else
{
uint64_t v___x_1174_; 
v___x_1174_ = lean_uint64_of_nat(v_bv_1165_);
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_hash___boxed(lean_object* v_n_1175_, lean_object* v_bv_1176_){
_start:
{
uint64_t v_res_1177_; lean_object* v_r_1178_; 
v_res_1177_ = l_BitVec_hash(v_n_1175_, v_bv_1176_);
lean_dec(v_bv_1176_);
lean_dec(v_n_1175_);
v_r_1178_ = lean_box_uint64(v_res_1177_);
return v_r_1178_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHashable(lean_object* v_n_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_alloc_closure((void*)(l_BitVec_hash___boxed), 2, 1);
lean_closure_set(v___x_1180_, 0, v_n_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE(lean_object* v_x_1181_){
_start:
{
if (lean_obj_tag(v_x_1181_) == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1182_;
}
else
{
lean_object* v_head_1183_; lean_object* v_tail_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; 
v_head_1183_ = lean_ctor_get(v_x_1181_, 0);
v_tail_1184_ = lean_ctor_get(v_x_1181_, 1);
v___x_1185_ = l_List_lengthTR___redArg(v_tail_1184_);
v___x_1186_ = l_BitVec_ofBoolListBE(v_tail_1184_);
v___x_1187_ = lean_unbox(v_head_1183_);
v___x_1188_ = l_BitVec_cons(v___x_1185_, v___x_1187_, v___x_1186_);
lean_dec(v___x_1186_);
lean_dec(v___x_1185_);
return v___x_1188_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE___boxed(lean_object* v_x_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_BitVec_ofBoolListBE(v_x_1189_);
lean_dec(v_x_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE(lean_object* v_x_1191_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 0)
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1192_;
}
else
{
lean_object* v_head_1193_; lean_object* v_tail_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; lean_object* v___x_1197_; 
v_head_1193_ = lean_ctor_get(v_x_1191_, 0);
v_tail_1194_ = lean_ctor_get(v_x_1191_, 1);
v___x_1195_ = l_BitVec_ofBoolListLE(v_tail_1194_);
v___x_1196_ = lean_unbox(v_head_1193_);
v___x_1197_ = l_BitVec_concat___redArg(v___x_1195_, v___x_1196_);
lean_dec(v___x_1195_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE___boxed(lean_object* v_x_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_BitVec_ofBoolListLE(v_x_1198_);
lean_dec(v_x_1198_);
return v_res_1199_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uaddOverflow(lean_object* v_w_1200_, lean_object* v_x_1201_, lean_object* v_y_1202_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1203_ = lean_unsigned_to_nat(2u);
v___x_1204_ = lean_nat_pow(v___x_1203_, v_w_1200_);
v___x_1205_ = lean_nat_add(v_x_1201_, v_y_1202_);
v___x_1206_ = lean_nat_dec_le(v___x_1204_, v___x_1205_);
lean_dec(v___x_1205_);
lean_dec(v___x_1204_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_BitVec_uaddOverflow___boxed(lean_object* v_w_1207_, lean_object* v_x_1208_, lean_object* v_y_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_BitVec_uaddOverflow(v_w_1207_, v_x_1208_, v_y_1209_);
lean_dec(v_y_1209_);
lean_dec(v_x_1208_);
lean_dec(v_w_1207_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
static lean_object* _init_l_BitVec_saddOverflow___closed__0(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_unsigned_to_nat(2u);
v___x_1213_ = lean_nat_to_int(v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT uint8_t l_BitVec_saddOverflow(lean_object* v_w_1214_, lean_object* v_x_1215_, lean_object* v_y_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1217_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1218_ = lean_unsigned_to_nat(1u);
v___x_1219_ = lean_nat_sub(v_w_1214_, v___x_1218_);
v___x_1220_ = l_Int_pow(v___x_1217_, v___x_1219_);
lean_dec(v___x_1219_);
v___x_1221_ = l_BitVec_toInt(v_w_1214_, v_x_1215_);
v___x_1222_ = l_BitVec_toInt(v_w_1214_, v_y_1216_);
v___x_1223_ = lean_int_add(v___x_1221_, v___x_1222_);
lean_dec(v___x_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_int_dec_le(v___x_1220_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = lean_int_neg(v___x_1220_);
lean_dec(v___x_1220_);
v___x_1226_ = lean_int_dec_lt(v___x_1223_, v___x_1225_);
lean_dec(v___x_1225_);
lean_dec(v___x_1223_);
return v___x_1226_;
}
else
{
lean_dec(v___x_1223_);
lean_dec(v___x_1220_);
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_saddOverflow___boxed(lean_object* v_w_1227_, lean_object* v_x_1228_, lean_object* v_y_1229_){
_start:
{
uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_res_1230_ = l_BitVec_saddOverflow(v_w_1227_, v_x_1228_, v_y_1229_);
lean_dec(v_w_1227_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
LEAN_EXPORT uint8_t l_BitVec_usubOverflow___redArg(lean_object* v_x_1232_, lean_object* v_y_1233_){
_start:
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_nat_dec_lt(v_x_1232_, v_y_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___redArg___boxed(lean_object* v_x_1235_, lean_object* v_y_1236_){
_start:
{
uint8_t v_res_1237_; lean_object* v_r_1238_; 
v_res_1237_ = l_BitVec_usubOverflow___redArg(v_x_1235_, v_y_1236_);
lean_dec(v_y_1236_);
lean_dec(v_x_1235_);
v_r_1238_ = lean_box(v_res_1237_);
return v_r_1238_;
}
}
LEAN_EXPORT uint8_t l_BitVec_usubOverflow(lean_object* v_w_1239_, lean_object* v_x_1240_, lean_object* v_y_1241_){
_start:
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_nat_dec_lt(v_x_1240_, v_y_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___boxed(lean_object* v_w_1243_, lean_object* v_x_1244_, lean_object* v_y_1245_){
_start:
{
uint8_t v_res_1246_; lean_object* v_r_1247_; 
v_res_1246_ = l_BitVec_usubOverflow(v_w_1243_, v_x_1244_, v_y_1245_);
lean_dec(v_y_1245_);
lean_dec(v_x_1244_);
lean_dec(v_w_1243_);
v_r_1247_ = lean_box(v_res_1246_);
return v_r_1247_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ssubOverflow(lean_object* v_w_1248_, lean_object* v_x_1249_, lean_object* v_y_1250_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1251_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_nat_sub(v_w_1248_, v___x_1252_);
v___x_1254_ = l_Int_pow(v___x_1251_, v___x_1253_);
lean_dec(v___x_1253_);
v___x_1255_ = l_BitVec_toInt(v_w_1248_, v_x_1249_);
v___x_1256_ = l_BitVec_toInt(v_w_1248_, v_y_1250_);
v___x_1257_ = lean_int_sub(v___x_1255_, v___x_1256_);
lean_dec(v___x_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_int_dec_le(v___x_1254_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = lean_int_neg(v___x_1254_);
lean_dec(v___x_1254_);
v___x_1260_ = lean_int_dec_lt(v___x_1257_, v___x_1259_);
lean_dec(v___x_1259_);
lean_dec(v___x_1257_);
return v___x_1260_;
}
else
{
lean_dec(v___x_1257_);
lean_dec(v___x_1254_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ssubOverflow___boxed(lean_object* v_w_1261_, lean_object* v_x_1262_, lean_object* v_y_1263_){
_start:
{
uint8_t v_res_1264_; lean_object* v_r_1265_; 
v_res_1264_ = l_BitVec_ssubOverflow(v_w_1261_, v_x_1262_, v_y_1263_);
lean_dec(v_w_1261_);
v_r_1265_ = lean_box(v_res_1264_);
return v_r_1265_;
}
}
LEAN_EXPORT uint8_t l_BitVec_negOverflow(lean_object* v_w_1266_, lean_object* v_x_1267_){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1268_ = l_BitVec_toInt(v_w_1266_, v_x_1267_);
v___x_1269_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_nat_sub(v_w_1266_, v___x_1270_);
v___x_1272_ = l_Int_pow(v___x_1269_, v___x_1271_);
lean_dec(v___x_1271_);
v___x_1273_ = lean_int_neg(v___x_1272_);
lean_dec(v___x_1272_);
v___x_1274_ = lean_int_dec_eq(v___x_1268_, v___x_1273_);
lean_dec(v___x_1273_);
lean_dec(v___x_1268_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_BitVec_negOverflow___boxed(lean_object* v_w_1275_, lean_object* v_x_1276_){
_start:
{
uint8_t v_res_1277_; lean_object* v_r_1278_; 
v_res_1277_ = l_BitVec_negOverflow(v_w_1275_, v_x_1276_);
lean_dec(v_w_1275_);
v_r_1278_ = lean_box(v_res_1277_);
return v_r_1278_;
}
}
LEAN_EXPORT uint8_t l_BitVec_sdivOverflow(lean_object* v_w_1279_, lean_object* v_x_1280_, lean_object* v_y_1281_){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1282_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1283_ = lean_unsigned_to_nat(1u);
v___x_1284_ = lean_nat_sub(v_w_1279_, v___x_1283_);
v___x_1285_ = l_Int_pow(v___x_1282_, v___x_1284_);
lean_dec(v___x_1284_);
v___x_1286_ = l_BitVec_toInt(v_w_1279_, v_x_1280_);
v___x_1287_ = l_BitVec_toInt(v_w_1279_, v_y_1281_);
v___x_1288_ = lean_int_ediv(v___x_1286_, v___x_1287_);
lean_dec(v___x_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_int_dec_le(v___x_1285_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = lean_int_neg(v___x_1285_);
lean_dec(v___x_1285_);
v___x_1291_ = lean_int_dec_lt(v___x_1288_, v___x_1290_);
lean_dec(v___x_1290_);
lean_dec(v___x_1288_);
return v___x_1291_;
}
else
{
lean_dec(v___x_1288_);
lean_dec(v___x_1285_);
return v___x_1289_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sdivOverflow___boxed(lean_object* v_w_1292_, lean_object* v_x_1293_, lean_object* v_y_1294_){
_start:
{
uint8_t v_res_1295_; lean_object* v_r_1296_; 
v_res_1295_ = l_BitVec_sdivOverflow(v_w_1292_, v_x_1293_, v_y_1294_);
lean_dec(v_w_1292_);
v_r_1296_ = lean_box(v_res_1295_);
return v_r_1296_;
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse(lean_object* v_x_1297_, lean_object* v_x_1298_){
_start:
{
lean_object* v_zero_1299_; uint8_t v_isZero_1300_; 
v_zero_1299_ = lean_unsigned_to_nat(0u);
v_isZero_1300_ = lean_nat_dec_eq(v_x_1297_, v_zero_1299_);
if (v_isZero_1300_ == 1)
{
lean_inc(v_x_1298_);
return v_x_1298_;
}
else
{
lean_object* v_one_1301_; lean_object* v_n_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_one_1301_ = lean_unsigned_to_nat(1u);
v_n_1302_ = lean_nat_sub(v_x_1297_, v_one_1301_);
v___x_1303_ = lean_nat_add(v_n_1302_, v_one_1301_);
v___x_1304_ = l_BitVec_setWidth(v___x_1303_, v_n_1302_, v_x_1298_);
v___x_1305_ = l_BitVec_reverse(v_n_1302_, v___x_1304_);
lean_dec(v___x_1304_);
lean_dec(v_n_1302_);
v___x_1306_ = lean_nat_dec_lt(v_zero_1299_, v___x_1303_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; 
lean_dec(v___x_1303_);
v___x_1307_ = l_BitVec_concat___redArg(v___x_1305_, v___x_1306_);
lean_dec(v___x_1305_);
return v___x_1307_;
}
else
{
lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = lean_nat_sub(v___x_1303_, v_one_1301_);
lean_dec(v___x_1303_);
v___x_1309_ = l_Nat_testBit(v_x_1298_, v___x_1308_);
lean_dec(v___x_1308_);
v___x_1310_ = l_BitVec_concat___redArg(v___x_1305_, v___x_1309_);
lean_dec(v___x_1305_);
return v___x_1310_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse___boxed(lean_object* v_x_1311_, lean_object* v_x_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_BitVec_reverse(v_x_1311_, v_x_1312_);
lean_dec(v_x_1312_);
lean_dec(v_x_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT uint8_t l_BitVec_umulOverflow(lean_object* v_w_1314_, lean_object* v_x_1315_, lean_object* v_y_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1317_ = lean_unsigned_to_nat(2u);
v___x_1318_ = lean_nat_pow(v___x_1317_, v_w_1314_);
v___x_1319_ = lean_nat_mul(v_x_1315_, v_y_1316_);
v___x_1320_ = lean_nat_dec_le(v___x_1318_, v___x_1319_);
lean_dec(v___x_1319_);
lean_dec(v___x_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umulOverflow___boxed(lean_object* v_w_1321_, lean_object* v_x_1322_, lean_object* v_y_1323_){
_start:
{
uint8_t v_res_1324_; lean_object* v_r_1325_; 
v_res_1324_ = l_BitVec_umulOverflow(v_w_1321_, v_x_1322_, v_y_1323_);
lean_dec(v_y_1323_);
lean_dec(v_x_1322_);
lean_dec(v_w_1321_);
v_r_1325_ = lean_box(v_res_1324_);
return v_r_1325_;
}
}
LEAN_EXPORT uint8_t l_BitVec_smulOverflow(lean_object* v_w_1326_, lean_object* v_x_1327_, lean_object* v_y_1328_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1329_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1330_ = lean_unsigned_to_nat(1u);
v___x_1331_ = lean_nat_sub(v_w_1326_, v___x_1330_);
v___x_1332_ = l_Int_pow(v___x_1329_, v___x_1331_);
lean_dec(v___x_1331_);
v___x_1333_ = l_BitVec_toInt(v_w_1326_, v_x_1327_);
v___x_1334_ = l_BitVec_toInt(v_w_1326_, v_y_1328_);
v___x_1335_ = lean_int_mul(v___x_1333_, v___x_1334_);
lean_dec(v___x_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_int_dec_le(v___x_1332_, v___x_1335_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1337_ = lean_int_neg(v___x_1332_);
lean_dec(v___x_1332_);
v___x_1338_ = lean_int_dec_lt(v___x_1335_, v___x_1337_);
lean_dec(v___x_1337_);
lean_dec(v___x_1335_);
return v___x_1338_;
}
else
{
lean_dec(v___x_1335_);
lean_dec(v___x_1332_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smulOverflow___boxed(lean_object* v_w_1339_, lean_object* v_x_1340_, lean_object* v_y_1341_){
_start:
{
uint8_t v_res_1342_; lean_object* v_r_1343_; 
v_res_1342_ = l_BitVec_smulOverflow(v_w_1339_, v_x_1340_, v_y_1341_);
lean_dec(v_w_1339_);
v_r_1343_ = lean_box(v_res_1342_);
return v_r_1343_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec(lean_object* v_w_1344_, lean_object* v_x_1345_, lean_object* v_n_1346_){
_start:
{
lean_object* v_zero_1347_; uint8_t v_isZero_1348_; 
v_zero_1347_ = lean_unsigned_to_nat(0u);
v_isZero_1348_ = lean_nat_dec_eq(v_n_1346_, v_zero_1347_);
if (v_isZero_1348_ == 1)
{
uint8_t v___x_1349_; 
lean_dec(v_n_1346_);
v___x_1349_ = l_Nat_testBit(v_x_1345_, v_zero_1347_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
v___x_1350_ = l_BitVec_ofNat(v_w_1344_, v_w_1344_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = lean_unsigned_to_nat(1u);
v___x_1352_ = lean_nat_sub(v_w_1344_, v___x_1351_);
v___x_1353_ = l_BitVec_ofNat(v_w_1344_, v___x_1352_);
lean_dec(v___x_1352_);
return v___x_1353_;
}
}
else
{
uint8_t v___x_1354_; 
v___x_1354_ = l_Nat_testBit(v_x_1345_, v_n_1346_);
if (v___x_1354_ == 0)
{
lean_object* v_one_1355_; lean_object* v_n_1356_; 
v_one_1355_ = lean_unsigned_to_nat(1u);
v_n_1356_ = lean_nat_sub(v_n_1346_, v_one_1355_);
lean_dec(v_n_1346_);
v_n_1346_ = v_n_1356_;
goto _start;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1358_ = lean_unsigned_to_nat(1u);
v___x_1359_ = lean_nat_sub(v_w_1344_, v___x_1358_);
v___x_1360_ = lean_nat_sub(v___x_1359_, v_n_1346_);
lean_dec(v_n_1346_);
lean_dec(v___x_1359_);
v___x_1361_ = l_BitVec_ofNat(v_w_1344_, v___x_1360_);
lean_dec(v___x_1360_);
return v___x_1361_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec___boxed(lean_object* v_w_1362_, lean_object* v_x_1363_, lean_object* v_n_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_BitVec_clzAuxRec(v_w_1362_, v_x_1363_, v_n_1364_);
lean_dec(v_x_1363_);
lean_dec(v_w_1362_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clz(lean_object* v_w_1366_, lean_object* v_x_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_nat_sub(v_w_1366_, v___x_1368_);
v___x_1370_ = l_BitVec_clzAuxRec(v_w_1366_, v_x_1367_, v___x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clz___boxed(lean_object* v_w_1371_, lean_object* v_x_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_BitVec_clz(v_w_1371_, v_x_1372_);
lean_dec(v_x_1372_);
lean_dec(v_w_1371_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ctz(lean_object* v_w_1374_, lean_object* v_x_1375_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = l_BitVec_reverse(v_w_1374_, v_x_1375_);
v___x_1377_ = l_BitVec_clz(v_w_1374_, v___x_1376_);
lean_dec(v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ctz___boxed(lean_object* v_w_1378_, lean_object* v_x_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_BitVec_ctz(v_w_1378_, v_x_1379_);
lean_dec(v_x_1379_);
lean_dec(v_w_1378_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg(lean_object* v_x_1381_, lean_object* v_pos_1382_, lean_object* v_acc_1383_){
_start:
{
lean_object* v_zero_1384_; uint8_t v_isZero_1385_; 
v_zero_1384_ = lean_unsigned_to_nat(0u);
v_isZero_1385_ = lean_nat_dec_eq(v_pos_1382_, v_zero_1384_);
if (v_isZero_1385_ == 1)
{
lean_dec(v_pos_1382_);
return v_acc_1383_;
}
else
{
lean_object* v_one_1386_; lean_object* v_n_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_one_1386_ = lean_unsigned_to_nat(1u);
v_n_1387_ = lean_nat_sub(v_pos_1382_, v_one_1386_);
lean_dec(v_pos_1382_);
v___x_1388_ = l_Nat_testBit(v_x_1381_, v_n_1387_);
v___x_1389_ = l_Bool_toNat(v___x_1388_);
v___x_1390_ = lean_nat_add(v_acc_1383_, v___x_1389_);
lean_dec(v___x_1389_);
lean_dec(v_acc_1383_);
v_pos_1382_ = v_n_1387_;
v_acc_1383_ = v___x_1390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg___boxed(lean_object* v_x_1392_, lean_object* v_pos_1393_, lean_object* v_acc_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_BitVec_cpopNatRec___redArg(v_x_1392_, v_pos_1393_, v_acc_1394_);
lean_dec(v_x_1392_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec(lean_object* v_w_1396_, lean_object* v_x_1397_, lean_object* v_pos_1398_, lean_object* v_acc_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_BitVec_cpopNatRec___redArg(v_x_1397_, v_pos_1398_, v_acc_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___boxed(lean_object* v_w_1401_, lean_object* v_x_1402_, lean_object* v_pos_1403_, lean_object* v_acc_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_BitVec_cpopNatRec(v_w_1401_, v_x_1402_, v_pos_1403_, v_acc_1404_);
lean_dec(v_x_1402_);
lean_dec(v_w_1401_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpop(lean_object* v_w_1406_, lean_object* v_x_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
lean_inc(v_w_1406_);
v___x_1409_ = l_BitVec_cpopNatRec___redArg(v_x_1407_, v_w_1406_, v___x_1408_);
v___x_1410_ = l_BitVec_ofNat(v_w_1406_, v___x_1409_);
lean_dec(v___x_1409_);
lean_dec(v_w_1406_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpop___boxed(lean_object* v_w_1411_, lean_object* v_x_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_BitVec_cpop(v_w_1411_, v_x_1412_);
lean_dec(v_x_1412_);
return v_res_1413_;
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
