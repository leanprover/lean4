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
LEAN_EXPORT lean_object* l_BitVec_instMin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_BitVec_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_BitVec_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instMin___closed__0 = (const lean_object*)&l_BitVec_instMin___closed__0_value;
LEAN_EXPORT lean_object* l_BitVec_instMin(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_BitVec_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_BitVec_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instMax___closed__0 = (const lean_object*)&l_BitVec_instMax___closed__0_value;
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
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_nat_dec_lt(v___x_462_, v_n_460_);
if (v___x_463_ == 0)
{
lean_inc(v_x_461_);
return v_x_461_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_464_ = lean_unsigned_to_nat(1u);
v___x_465_ = lean_nat_sub(v_n_460_, v___x_464_);
v___x_466_ = l_Nat_testBit(v_x_461_, v___x_465_);
lean_dec(v___x_465_);
if (v___x_466_ == 0)
{
lean_inc(v_x_461_);
return v_x_461_;
}
else
{
lean_object* v___x_467_; 
v___x_467_ = l_BitVec_neg(v_n_460_, v_x_461_);
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_abs___boxed(lean_object* v_n_468_, lean_object* v_x_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_BitVec_abs(v_n_468_, v_x_469_);
lean_dec(v_x_469_);
lean_dec(v_n_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mul(lean_object* v_n_471_, lean_object* v_x_472_, lean_object* v_y_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_nat_mul(v_x_472_, v_y_473_);
v___x_475_ = l_BitVec_ofNat(v_n_471_, v___x_474_);
lean_dec(v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mul___boxed(lean_object* v_n_476_, lean_object* v_x_477_, lean_object* v_y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_BitVec_mul(v_n_476_, v_x_477_, v_y_478_);
lean_dec(v_y_478_);
lean_dec(v_x_477_);
lean_dec(v_n_476_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMul(lean_object* v_n_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = lean_alloc_closure((void*)(l_BitVec_mul___boxed), 3, 1);
lean_closure_set(v___x_481_, 0, v_n_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_BitVec_pow(lean_object* v_n_482_, lean_object* v_x_483_, lean_object* v_y_484_){
_start:
{
lean_object* v_zero_485_; uint8_t v_isZero_486_; 
v_zero_485_ = lean_unsigned_to_nat(0u);
v_isZero_486_ = lean_nat_dec_eq(v_y_484_, v_zero_485_);
if (v_isZero_486_ == 1)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = l_BitVec_ofNat(v_n_482_, v___x_487_);
return v___x_488_;
}
else
{
lean_object* v_one_489_; lean_object* v_n_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_one_489_ = lean_unsigned_to_nat(1u);
v_n_490_ = lean_nat_sub(v_y_484_, v_one_489_);
v___x_491_ = l_BitVec_pow(v_n_482_, v_x_483_, v_n_490_);
lean_dec(v_n_490_);
v___x_492_ = l_BitVec_mul(v_n_482_, v___x_491_, v_x_483_);
lean_dec(v___x_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_pow___boxed(lean_object* v_n_493_, lean_object* v_x_494_, lean_object* v_y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_BitVec_pow(v_n_493_, v_x_494_, v_y_495_);
lean_dec(v_y_495_);
lean_dec(v_x_494_);
lean_dec(v_n_493_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat___lam__0(lean_object* v_n_497_, lean_object* v_x_498_, lean_object* v_y_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_BitVec_pow(v_n_497_, v_x_498_, v_y_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat___lam__0___boxed(lean_object* v_n_501_, lean_object* v_x_502_, lean_object* v_y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_BitVec_instPowNat___lam__0(v_n_501_, v_x_502_, v_y_503_);
lean_dec(v_y_503_);
lean_dec(v_x_502_);
lean_dec(v_n_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instPowNat(lean_object* v_n_505_){
_start:
{
lean_object* v___f_506_; 
v___f_506_ = lean_alloc_closure((void*)(l_BitVec_instPowNat___lam__0___boxed), 3, 1);
lean_closure_set(v___f_506_, 0, v_n_505_);
return v___f_506_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___redArg(lean_object* v_x_507_, lean_object* v_y_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_nat_div(v_x_507_, v_y_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___redArg___boxed(lean_object* v_x_510_, lean_object* v_y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_BitVec_udiv___redArg(v_x_510_, v_y_511_);
lean_dec(v_y_511_);
lean_dec(v_x_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv(lean_object* v_n_513_, lean_object* v_x_514_, lean_object* v_y_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = lean_nat_div(v_x_514_, v_y_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_BitVec_udiv___boxed(lean_object* v_n_517_, lean_object* v_x_518_, lean_object* v_y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_BitVec_udiv(v_n_517_, v_x_518_, v_y_519_);
lean_dec(v_y_519_);
lean_dec(v_x_518_);
lean_dec(v_n_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instDiv(lean_object* v_n_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_alloc_closure((void*)(l_BitVec_udiv___boxed), 3, 1);
lean_closure_set(v___x_522_, 0, v_n_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___redArg(lean_object* v_x_523_, lean_object* v_y_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_nat_mod(v_x_523_, v_y_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___redArg___boxed(lean_object* v_x_526_, lean_object* v_y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_BitVec_umod___redArg(v_x_526_, v_y_527_);
lean_dec(v_y_527_);
lean_dec(v_x_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod(lean_object* v_n_529_, lean_object* v_x_530_, lean_object* v_y_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_nat_mod(v_x_530_, v_y_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umod___boxed(lean_object* v_n_533_, lean_object* v_x_534_, lean_object* v_y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_BitVec_umod(v_n_533_, v_x_534_, v_y_535_);
lean_dec(v_y_535_);
lean_dec(v_x_534_);
lean_dec(v_n_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMod(lean_object* v_n_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = lean_alloc_closure((void*)(l_BitVec_umod___boxed), 3, 1);
lean_closure_set(v___x_538_, 0, v_n_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtUDiv(lean_object* v_n_539_, lean_object* v_x_540_, lean_object* v_y_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = l_BitVec_ofNat(v_n_539_, v___x_542_);
v___x_544_ = lean_nat_dec_eq(v_y_541_, v___x_543_);
lean_dec(v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; 
v___x_545_ = lean_nat_div(v_x_540_, v_y_541_);
return v___x_545_;
}
else
{
lean_object* v___x_546_; 
v___x_546_ = l_BitVec_allOnes(v_n_539_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtUDiv___boxed(lean_object* v_n_547_, lean_object* v_x_548_, lean_object* v_y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_BitVec_smtUDiv(v_n_547_, v_x_548_, v_y_549_);
lean_dec(v_y_549_);
lean_dec(v_x_548_);
lean_dec(v_n_547_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv(lean_object* v_n_551_, lean_object* v_x_552_, lean_object* v_y_553_){
_start:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_nat_dec_lt(v___x_569_, v_n_551_);
if (v___x_570_ == 0)
{
goto v___jp_554_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_nat_sub(v_n_551_, v___x_571_);
v___x_573_ = l_Nat_testBit(v_x_552_, v___x_572_);
if (v___x_573_ == 0)
{
lean_dec(v___x_572_);
goto v___jp_554_;
}
else
{
if (v___x_570_ == 0)
{
lean_dec(v___x_572_);
goto v___jp_565_;
}
else
{
uint8_t v___x_574_; 
v___x_574_ = l_Nat_testBit(v_y_553_, v___x_572_);
lean_dec(v___x_572_);
if (v___x_574_ == 0)
{
goto v___jp_565_;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = l_BitVec_neg(v_n_551_, v_x_552_);
v___x_576_ = l_BitVec_neg(v_n_551_, v_y_553_);
v___x_577_ = lean_nat_div(v___x_575_, v___x_576_);
lean_dec(v___x_576_);
lean_dec(v___x_575_);
return v___x_577_;
}
}
}
}
v___jp_554_:
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_nat_dec_lt(v___x_555_, v_n_551_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
v___x_557_ = lean_nat_div(v_x_552_, v_y_553_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_nat_sub(v_n_551_, v___x_558_);
v___x_560_ = l_Nat_testBit(v_y_553_, v___x_559_);
lean_dec(v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_nat_div(v_x_552_, v_y_553_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = l_BitVec_neg(v_n_551_, v_y_553_);
v___x_563_ = lean_nat_div(v_x_552_, v___x_562_);
lean_dec(v___x_562_);
v___x_564_ = l_BitVec_neg(v_n_551_, v___x_563_);
lean_dec(v___x_563_);
return v___x_564_;
}
}
}
v___jp_565_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = l_BitVec_neg(v_n_551_, v_x_552_);
v___x_567_ = lean_nat_div(v___x_566_, v_y_553_);
lean_dec(v___x_566_);
v___x_568_ = l_BitVec_neg(v_n_551_, v___x_567_);
lean_dec(v___x_567_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv___boxed(lean_object* v_n_578_, lean_object* v_x_579_, lean_object* v_y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_BitVec_sdiv(v_n_578_, v_x_579_, v_y_580_);
lean_dec(v_y_580_);
lean_dec(v_x_579_);
lean_dec(v_n_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv(lean_object* v_n_582_, lean_object* v_x_583_, lean_object* v_y_584_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_nat_dec_lt(v___x_600_, v_n_582_);
if (v___x_601_ == 0)
{
goto v___jp_585_;
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_sub(v_n_582_, v___x_602_);
v___x_604_ = l_Nat_testBit(v_x_583_, v___x_603_);
if (v___x_604_ == 0)
{
lean_dec(v___x_603_);
goto v___jp_585_;
}
else
{
if (v___x_601_ == 0)
{
lean_dec(v___x_603_);
goto v___jp_596_;
}
else
{
uint8_t v___x_605_; 
v___x_605_ = l_Nat_testBit(v_y_584_, v___x_603_);
lean_dec(v___x_603_);
if (v___x_605_ == 0)
{
goto v___jp_596_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = l_BitVec_neg(v_n_582_, v_x_583_);
v___x_607_ = l_BitVec_neg(v_n_582_, v_y_584_);
v___x_608_ = l_BitVec_smtUDiv(v_n_582_, v___x_606_, v___x_607_);
lean_dec(v___x_607_);
lean_dec(v___x_606_);
return v___x_608_;
}
}
}
}
v___jp_585_:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_nat_dec_lt(v___x_586_, v_n_582_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = l_BitVec_smtUDiv(v_n_582_, v_x_583_, v_y_584_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_sub(v_n_582_, v___x_589_);
v___x_591_ = l_Nat_testBit(v_y_584_, v___x_590_);
lean_dec(v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = l_BitVec_smtUDiv(v_n_582_, v_x_583_, v_y_584_);
return v___x_592_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = l_BitVec_neg(v_n_582_, v_y_584_);
v___x_594_ = l_BitVec_smtUDiv(v_n_582_, v_x_583_, v___x_593_);
lean_dec(v___x_593_);
v___x_595_ = l_BitVec_neg(v_n_582_, v___x_594_);
lean_dec(v___x_594_);
return v___x_595_;
}
}
}
v___jp_596_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = l_BitVec_neg(v_n_582_, v_x_583_);
v___x_598_ = l_BitVec_smtUDiv(v_n_582_, v___x_597_, v_y_584_);
lean_dec(v___x_597_);
v___x_599_ = l_BitVec_neg(v_n_582_, v___x_598_);
lean_dec(v___x_598_);
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv___boxed(lean_object* v_n_609_, lean_object* v_x_610_, lean_object* v_y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_BitVec_smtSDiv(v_n_609_, v_x_610_, v_y_611_);
lean_dec(v_y_611_);
lean_dec(v_x_610_);
lean_dec(v_n_609_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_BitVec_srem(lean_object* v_n_613_, lean_object* v_x_614_, lean_object* v_y_615_){
_start:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_nat_dec_lt(v___x_630_, v_n_613_);
if (v___x_631_ == 0)
{
goto v___jp_616_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_sub(v_n_613_, v___x_632_);
v___x_634_ = l_Nat_testBit(v_x_614_, v___x_633_);
if (v___x_634_ == 0)
{
lean_dec(v___x_633_);
goto v___jp_616_;
}
else
{
if (v___x_631_ == 0)
{
lean_dec(v___x_633_);
goto v___jp_626_;
}
else
{
uint8_t v___x_635_; 
v___x_635_ = l_Nat_testBit(v_y_615_, v___x_633_);
lean_dec(v___x_633_);
if (v___x_635_ == 0)
{
goto v___jp_626_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_636_ = l_BitVec_neg(v_n_613_, v_x_614_);
v___x_637_ = l_BitVec_neg(v_n_613_, v_y_615_);
v___x_638_ = lean_nat_mod(v___x_636_, v___x_637_);
lean_dec(v___x_637_);
lean_dec(v___x_636_);
v___x_639_ = l_BitVec_neg(v_n_613_, v___x_638_);
lean_dec(v___x_638_);
return v___x_639_;
}
}
}
}
v___jp_616_:
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = lean_nat_dec_lt(v___x_617_, v_n_613_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
v___x_619_ = lean_nat_mod(v_x_614_, v_y_615_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_sub(v_n_613_, v___x_620_);
v___x_622_ = l_Nat_testBit(v_y_615_, v___x_621_);
lean_dec(v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
v___x_623_ = lean_nat_mod(v_x_614_, v_y_615_);
return v___x_623_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = l_BitVec_neg(v_n_613_, v_y_615_);
v___x_625_ = lean_nat_mod(v_x_614_, v___x_624_);
lean_dec(v___x_624_);
return v___x_625_;
}
}
}
v___jp_626_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = l_BitVec_neg(v_n_613_, v_x_614_);
v___x_628_ = lean_nat_mod(v___x_627_, v_y_615_);
lean_dec(v___x_627_);
v___x_629_ = l_BitVec_neg(v_n_613_, v___x_628_);
lean_dec(v___x_628_);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_srem___boxed(lean_object* v_n_640_, lean_object* v_x_641_, lean_object* v_y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_BitVec_srem(v_n_640_, v_x_641_, v_y_642_);
lean_dec(v_y_642_);
lean_dec(v_x_641_);
lean_dec(v_n_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smod(lean_object* v_m_644_, lean_object* v_x_645_, lean_object* v_y_646_){
_start:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_nat_dec_lt(v___x_665_, v_m_644_);
if (v___x_666_ == 0)
{
goto v___jp_647_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_nat_sub(v_m_644_, v___x_667_);
v___x_669_ = l_Nat_testBit(v_x_645_, v___x_668_);
if (v___x_669_ == 0)
{
lean_dec(v___x_668_);
goto v___jp_647_;
}
else
{
if (v___x_666_ == 0)
{
lean_dec(v___x_668_);
goto v___jp_659_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = l_Nat_testBit(v_y_646_, v___x_668_);
lean_dec(v___x_668_);
if (v___x_670_ == 0)
{
goto v___jp_659_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_671_ = l_BitVec_neg(v_m_644_, v_x_645_);
v___x_672_ = l_BitVec_neg(v_m_644_, v_y_646_);
v___x_673_ = lean_nat_mod(v___x_671_, v___x_672_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
v___x_674_ = l_BitVec_neg(v_m_644_, v___x_673_);
lean_dec(v___x_673_);
return v___x_674_;
}
}
}
}
v___jp_647_:
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_nat_dec_lt(v___x_648_, v_m_644_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
v___x_650_ = lean_nat_mod(v_x_645_, v_y_646_);
return v___x_650_;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_nat_sub(v_m_644_, v___x_651_);
v___x_653_ = l_Nat_testBit(v_y_646_, v___x_652_);
lean_dec(v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
v___x_654_ = lean_nat_mod(v_x_645_, v_y_646_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; lean_object* v_u_656_; uint8_t v___x_657_; 
v___x_655_ = l_BitVec_neg(v_m_644_, v_y_646_);
v_u_656_ = lean_nat_mod(v_x_645_, v___x_655_);
lean_dec(v___x_655_);
v___x_657_ = lean_nat_dec_eq(v_u_656_, v___x_648_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
v___x_658_ = l_BitVec_add(v_m_644_, v_u_656_, v_y_646_);
lean_dec(v_u_656_);
return v___x_658_;
}
else
{
return v_u_656_;
}
}
}
}
v___jp_659_:
{
lean_object* v___x_660_; lean_object* v_u_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_660_ = l_BitVec_neg(v_m_644_, v_x_645_);
v_u_661_ = lean_nat_mod(v___x_660_, v_y_646_);
lean_dec(v___x_660_);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_nat_dec_eq(v_u_661_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = l_BitVec_sub(v_m_644_, v_y_646_, v_u_661_);
lean_dec(v_u_661_);
return v___x_664_;
}
else
{
return v_u_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smod___boxed(lean_object* v_m_675_, lean_object* v_x_676_, lean_object* v_y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_BitVec_smod(v_m_675_, v_x_676_, v_y_677_);
lean_dec(v_y_677_);
lean_dec(v_x_676_);
lean_dec(v_m_675_);
return v_res_678_;
}
}
static lean_object* _init_l_BitVec_ofBool___closed__0(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = l_BitVec_ofNat(v___x_680_, v___x_679_);
return v___x_681_;
}
}
static lean_object* _init_l_BitVec_ofBool___closed__1(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = l_BitVec_ofNat(v___x_682_, v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBool(uint8_t v_b_684_){
_start:
{
if (v_b_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_obj_once(&l_BitVec_ofBool___closed__0, &l_BitVec_ofBool___closed__0_once, _init_l_BitVec_ofBool___closed__0);
return v___x_685_;
}
else
{
lean_object* v___x_686_; 
v___x_686_ = lean_obj_once(&l_BitVec_ofBool___closed__1, &l_BitVec_ofBool___closed__1_once, _init_l_BitVec_ofBool___closed__1);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBool___boxed(lean_object* v_b_687_){
_start:
{
uint8_t v_b_boxed_688_; lean_object* v_res_689_; 
v_b_boxed_688_ = lean_unbox(v_b_687_);
v_res_689_ = l_BitVec_ofBool(v_b_boxed_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_BitVec_fill(lean_object* v_w_690_, uint8_t v_b_691_){
_start:
{
if (v_b_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = l_BitVec_ofNat(v_w_690_, v___x_692_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = l_BitVec_ofNat(v_w_690_, v___x_694_);
v___x_696_ = l_BitVec_neg(v_w_690_, v___x_695_);
lean_dec(v___x_695_);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_fill___boxed(lean_object* v_w_697_, lean_object* v_b_698_){
_start:
{
uint8_t v_b_boxed_699_; lean_object* v_res_700_; 
v_b_boxed_699_ = lean_unbox(v_b_698_);
v_res_700_ = l_BitVec_fill(v_w_697_, v_b_boxed_699_);
lean_dec(v_w_697_);
return v_res_700_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ult___redArg(lean_object* v_x_701_, lean_object* v_y_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = lean_nat_dec_lt(v_x_701_, v_y_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult___redArg___boxed(lean_object* v_x_704_, lean_object* v_y_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l_BitVec_ult___redArg(v_x_704_, v_y_705_);
lean_dec(v_y_705_);
lean_dec(v_x_704_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ult(lean_object* v_n_708_, lean_object* v_x_709_, lean_object* v_y_710_){
_start:
{
uint8_t v___x_711_; 
v___x_711_ = lean_nat_dec_lt(v_x_709_, v_y_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult___boxed(lean_object* v_n_712_, lean_object* v_x_713_, lean_object* v_y_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_BitVec_ult(v_n_712_, v_x_713_, v_y_714_);
lean_dec(v_y_714_);
lean_dec(v_x_713_);
lean_dec(v_n_712_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ule___redArg(lean_object* v_x_717_, lean_object* v_y_718_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = lean_nat_dec_le(v_x_717_, v_y_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule___redArg___boxed(lean_object* v_x_720_, lean_object* v_y_721_){
_start:
{
uint8_t v_res_722_; lean_object* v_r_723_; 
v_res_722_ = l_BitVec_ule___redArg(v_x_720_, v_y_721_);
lean_dec(v_y_721_);
lean_dec(v_x_720_);
v_r_723_ = lean_box(v_res_722_);
return v_r_723_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ule(lean_object* v_n_724_, lean_object* v_x_725_, lean_object* v_y_726_){
_start:
{
uint8_t v___x_727_; 
v___x_727_ = lean_nat_dec_le(v_x_725_, v_y_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule___boxed(lean_object* v_n_728_, lean_object* v_x_729_, lean_object* v_y_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l_BitVec_ule(v_n_728_, v_x_729_, v_y_730_);
lean_dec(v_y_730_);
lean_dec(v_x_729_);
lean_dec(v_n_728_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
LEAN_EXPORT uint8_t l_BitVec_slt(lean_object* v_n_733_, lean_object* v_x_734_, lean_object* v_y_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_736_ = l_BitVec_toInt(v_n_733_, v_x_734_);
v___x_737_ = l_BitVec_toInt(v_n_733_, v_y_735_);
v___x_738_ = lean_int_dec_lt(v___x_736_, v___x_737_);
lean_dec(v___x_737_);
lean_dec(v___x_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_BitVec_slt___boxed(lean_object* v_n_739_, lean_object* v_x_740_, lean_object* v_y_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l_BitVec_slt(v_n_739_, v_x_740_, v_y_741_);
lean_dec(v_n_739_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
LEAN_EXPORT uint8_t l_BitVec_sle(lean_object* v_n_744_, lean_object* v_x_745_, lean_object* v_y_746_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_747_ = l_BitVec_toInt(v_n_744_, v_x_745_);
v___x_748_ = l_BitVec_toInt(v_n_744_, v_y_746_);
v___x_749_ = lean_int_dec_le(v___x_747_, v___x_748_);
lean_dec(v___x_748_);
lean_dec(v___x_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sle___boxed(lean_object* v_n_750_, lean_object* v_x_751_, lean_object* v_y_752_){
_start:
{
uint8_t v_res_753_; lean_object* v_r_754_; 
v_res_753_ = l_BitVec_sle(v_n_750_, v_x_751_, v_y_752_);
lean_dec(v_n_750_);
v_r_754_ = lean_box(v_res_753_);
return v_r_754_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___redArg(lean_object* v_x_755_){
_start:
{
lean_inc(v_x_755_);
return v_x_755_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___redArg___boxed(lean_object* v_x_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_BitVec_cast___redArg(v_x_756_);
lean_dec(v_x_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast(lean_object* v_n_758_, lean_object* v_m_759_, lean_object* v_eq_760_, lean_object* v_x_761_){
_start:
{
lean_inc(v_x_761_);
return v_x_761_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___boxed(lean_object* v_n_762_, lean_object* v_m_763_, lean_object* v_eq_764_, lean_object* v_x_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_BitVec_cast(v_n_762_, v_m_763_, v_eq_764_, v_x_765_);
lean_dec(v_x_765_);
lean_dec(v_m_763_);
lean_dec(v_n_762_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___redArg(lean_object* v_start_767_, lean_object* v_len_768_, lean_object* v_x_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_nat_shiftr(v_x_769_, v_start_767_);
v___x_771_ = l_BitVec_ofNat(v_len_768_, v___x_770_);
lean_dec(v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___redArg___boxed(lean_object* v_start_772_, lean_object* v_len_773_, lean_object* v_x_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_BitVec_extractLsb_x27___redArg(v_start_772_, v_len_773_, v_x_774_);
lean_dec(v_x_774_);
lean_dec(v_len_773_);
lean_dec(v_start_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27(lean_object* v_n_776_, lean_object* v_start_777_, lean_object* v_len_778_, lean_object* v_x_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_BitVec_extractLsb_x27___redArg(v_start_777_, v_len_778_, v_x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___boxed(lean_object* v_n_781_, lean_object* v_start_782_, lean_object* v_len_783_, lean_object* v_x_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_BitVec_extractLsb_x27(v_n_781_, v_start_782_, v_len_783_, v_x_784_);
lean_dec(v_x_784_);
lean_dec(v_len_783_);
lean_dec(v_start_782_);
lean_dec(v_n_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___redArg(lean_object* v_hi_786_, lean_object* v_lo_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_789_ = lean_nat_sub(v_hi_786_, v_lo_787_);
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_nat_add(v___x_789_, v___x_790_);
lean_dec(v___x_789_);
v___x_792_ = l_BitVec_extractLsb_x27___redArg(v_lo_787_, v___x_791_, v_x_788_);
lean_dec(v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___redArg___boxed(lean_object* v_hi_793_, lean_object* v_lo_794_, lean_object* v_x_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_BitVec_extractLsb___redArg(v_hi_793_, v_lo_794_, v_x_795_);
lean_dec(v_x_795_);
lean_dec(v_lo_794_);
lean_dec(v_hi_793_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb(lean_object* v_n_797_, lean_object* v_hi_798_, lean_object* v_lo_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_BitVec_extractLsb___redArg(v_hi_798_, v_lo_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___boxed(lean_object* v_n_802_, lean_object* v_hi_803_, lean_object* v_lo_804_, lean_object* v_x_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_BitVec_extractLsb(v_n_802_, v_hi_803_, v_lo_804_, v_x_805_);
lean_dec(v_x_805_);
lean_dec(v_lo_804_);
lean_dec(v_hi_803_);
lean_dec(v_n_802_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___redArg(lean_object* v_x_807_){
_start:
{
lean_inc(v_x_807_);
return v_x_807_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___redArg___boxed(lean_object* v_x_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_BitVec_setWidth_x27___redArg(v_x_808_);
lean_dec(v_x_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27(lean_object* v_n_810_, lean_object* v_w_811_, lean_object* v_le_812_, lean_object* v_x_813_){
_start:
{
lean_inc(v_x_813_);
return v_x_813_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___boxed(lean_object* v_n_814_, lean_object* v_w_815_, lean_object* v_le_816_, lean_object* v_x_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_BitVec_setWidth_x27(v_n_814_, v_w_815_, v_le_816_, v_x_817_);
lean_dec(v_x_817_);
lean_dec(v_w_815_);
lean_dec(v_n_814_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___redArg(lean_object* v_msbs_819_, lean_object* v_m_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = lean_nat_shiftl(v_msbs_819_, v_m_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___redArg___boxed(lean_object* v_msbs_822_, lean_object* v_m_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_BitVec_shiftLeftZeroExtend___redArg(v_msbs_822_, v_m_823_);
lean_dec(v_m_823_);
lean_dec(v_msbs_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend(lean_object* v_w_825_, lean_object* v_msbs_826_, lean_object* v_m_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = lean_nat_shiftl(v_msbs_826_, v_m_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___boxed(lean_object* v_w_829_, lean_object* v_msbs_830_, lean_object* v_m_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_BitVec_shiftLeftZeroExtend(v_w_829_, v_msbs_830_, v_m_831_);
lean_dec(v_m_831_);
lean_dec(v_msbs_830_);
lean_dec(v_w_829_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth(lean_object* v_w_833_, lean_object* v_v_834_, lean_object* v_x_835_){
_start:
{
uint8_t v___x_836_; 
v___x_836_ = lean_nat_dec_le(v_w_833_, v_v_834_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; 
v___x_837_ = l_BitVec_ofNat(v_v_834_, v_x_835_);
return v___x_837_;
}
else
{
lean_inc(v_x_835_);
return v_x_835_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth___boxed(lean_object* v_w_838_, lean_object* v_v_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_BitVec_setWidth(v_w_838_, v_v_839_, v_x_840_);
lean_dec(v_x_840_);
lean_dec(v_v_839_);
lean_dec(v_w_838_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zeroExtend(lean_object* v_w_842_, lean_object* v_v_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_BitVec_setWidth(v_w_842_, v_v_843_, v_x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zeroExtend___boxed(lean_object* v_w_846_, lean_object* v_v_847_, lean_object* v_x_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_BitVec_zeroExtend(v_w_846_, v_v_847_, v_x_848_);
lean_dec(v_x_848_);
lean_dec(v_v_847_);
lean_dec(v_w_846_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_BitVec_truncate(lean_object* v_w_850_, lean_object* v_v_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_BitVec_setWidth(v_w_850_, v_v_851_, v_x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_BitVec_truncate___boxed(lean_object* v_w_854_, lean_object* v_v_855_, lean_object* v_x_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_BitVec_truncate(v_w_854_, v_v_855_, v_x_856_);
lean_dec(v_x_856_);
lean_dec(v_v_855_);
lean_dec(v_w_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_BitVec_signExtend(lean_object* v_w_858_, lean_object* v_v_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = l_BitVec_toInt(v_w_858_, v_x_860_);
v___x_862_ = l_BitVec_ofInt(v_v_859_, v___x_861_);
lean_dec(v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_BitVec_signExtend___boxed(lean_object* v_w_863_, lean_object* v_v_864_, lean_object* v_x_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_BitVec_signExtend(v_w_863_, v_v_864_, v_x_865_);
lean_dec(v_v_864_);
lean_dec(v_w_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___redArg(lean_object* v_x_867_, lean_object* v_y_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = lean_nat_land(v_x_867_, v_y_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___redArg___boxed(lean_object* v_x_870_, lean_object* v_y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_BitVec_and___redArg(v_x_870_, v_y_871_);
lean_dec(v_y_871_);
lean_dec(v_x_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and(lean_object* v_n_873_, lean_object* v_x_874_, lean_object* v_y_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = lean_nat_land(v_x_874_, v_y_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___boxed(lean_object* v_n_877_, lean_object* v_x_878_, lean_object* v_y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_BitVec_and(v_n_877_, v_x_878_, v_y_879_);
lean_dec(v_y_879_);
lean_dec(v_x_878_);
lean_dec(v_n_877_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instAndOp(lean_object* v_w_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = lean_alloc_closure((void*)(l_BitVec_and___boxed), 3, 1);
lean_closure_set(v___x_882_, 0, v_w_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___redArg(lean_object* v_x_883_, lean_object* v_y_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = lean_nat_lor(v_x_883_, v_y_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___redArg___boxed(lean_object* v_x_886_, lean_object* v_y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_BitVec_or___redArg(v_x_886_, v_y_887_);
lean_dec(v_y_887_);
lean_dec(v_x_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or(lean_object* v_n_889_, lean_object* v_x_890_, lean_object* v_y_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_nat_lor(v_x_890_, v_y_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___boxed(lean_object* v_n_893_, lean_object* v_x_894_, lean_object* v_y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_BitVec_or(v_n_893_, v_x_894_, v_y_895_);
lean_dec(v_y_895_);
lean_dec(v_x_894_);
lean_dec(v_n_893_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instOrOp(lean_object* v_w_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = lean_alloc_closure((void*)(l_BitVec_or___boxed), 3, 1);
lean_closure_set(v___x_898_, 0, v_w_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___redArg(lean_object* v_x_899_, lean_object* v_y_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_nat_lxor(v_x_899_, v_y_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___redArg___boxed(lean_object* v_x_902_, lean_object* v_y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_BitVec_xor___redArg(v_x_902_, v_y_903_);
lean_dec(v_y_903_);
lean_dec(v_x_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor(lean_object* v_n_905_, lean_object* v_x_906_, lean_object* v_y_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_nat_lxor(v_x_906_, v_y_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___boxed(lean_object* v_n_909_, lean_object* v_x_910_, lean_object* v_y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_BitVec_xor(v_n_909_, v_x_910_, v_y_911_);
lean_dec(v_y_911_);
lean_dec(v_x_910_);
lean_dec(v_n_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instXorOp(lean_object* v_w_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_closure((void*)(l_BitVec_xor___boxed), 3, 1);
lean_closure_set(v___x_914_, 0, v_w_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_BitVec_not(lean_object* v_n_915_, lean_object* v_x_916_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = l_BitVec_allOnes(v_n_915_);
v___x_918_ = lean_nat_lxor(v___x_917_, v_x_916_);
lean_dec(v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_BitVec_not___boxed(lean_object* v_n_919_, lean_object* v_x_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_BitVec_not(v_n_919_, v_x_920_);
lean_dec(v_x_920_);
lean_dec(v_n_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instComplement(lean_object* v_w_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_closure((void*)(l_BitVec_not___boxed), 2, 1);
lean_closure_set(v___x_923_, 0, v_w_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeft(lean_object* v_n_924_, lean_object* v_x_925_, lean_object* v_s_926_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_nat_shiftl(v_x_925_, v_s_926_);
v___x_928_ = l_BitVec_ofNat(v_n_924_, v___x_927_);
lean_dec(v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeft___boxed(lean_object* v_n_929_, lean_object* v_x_930_, lean_object* v_s_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_BitVec_shiftLeft(v_n_929_, v_x_930_, v_s_931_);
lean_dec(v_s_931_);
lean_dec(v_x_930_);
lean_dec(v_n_929_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeftNat(lean_object* v_w_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_closure((void*)(l_BitVec_shiftLeft___boxed), 3, 1);
lean_closure_set(v___x_934_, 0, v_w_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___redArg(lean_object* v_x_935_, lean_object* v_s_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = lean_nat_shiftr(v_x_935_, v_s_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___redArg___boxed(lean_object* v_x_938_, lean_object* v_s_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_BitVec_ushiftRight___redArg(v_x_938_, v_s_939_);
lean_dec(v_s_939_);
lean_dec(v_x_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight(lean_object* v_n_941_, lean_object* v_x_942_, lean_object* v_s_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = lean_nat_shiftr(v_x_942_, v_s_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___boxed(lean_object* v_n_945_, lean_object* v_x_946_, lean_object* v_s_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_BitVec_ushiftRight(v_n_945_, v_x_946_, v_s_947_);
lean_dec(v_s_947_);
lean_dec(v_x_946_);
lean_dec(v_n_945_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRightNat(lean_object* v_w_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_closure((void*)(l_BitVec_ushiftRight___boxed), 3, 1);
lean_closure_set(v___x_950_, 0, v_w_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight(lean_object* v_n_951_, lean_object* v_x_952_, lean_object* v_s_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = l_BitVec_toInt(v_n_951_, v_x_952_);
v___x_955_ = l_Int_shiftRight(v___x_954_, v_s_953_);
lean_dec(v___x_954_);
v___x_956_ = l_BitVec_ofInt(v_n_951_, v___x_955_);
lean_dec(v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight___boxed(lean_object* v_n_957_, lean_object* v_x_958_, lean_object* v_s_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_BitVec_sshiftRight(v_n_957_, v_x_958_, v_s_959_);
lean_dec(v_s_959_);
lean_dec(v_n_957_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg___lam__0(lean_object* v_m_961_, lean_object* v_x_962_, lean_object* v_y_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_BitVec_shiftLeft(v_m_961_, v_x_962_, v_y_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg___lam__0___boxed(lean_object* v_m_965_, lean_object* v_x_966_, lean_object* v_y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_BitVec_instHShiftLeft___redArg___lam__0(v_m_965_, v_x_966_, v_y_967_);
lean_dec(v_y_967_);
lean_dec(v_x_966_);
lean_dec(v_m_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg(lean_object* v_m_969_){
_start:
{
lean_object* v___f_970_; 
v___f_970_ = lean_alloc_closure((void*)(l_BitVec_instHShiftLeft___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_970_, 0, v_m_969_);
return v___f_970_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft(lean_object* v_m_971_, lean_object* v_n_972_){
_start:
{
lean_object* v___f_973_; 
v___f_973_ = lean_alloc_closure((void*)(l_BitVec_instHShiftLeft___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_973_, 0, v_m_971_);
return v___f_973_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___boxed(lean_object* v_m_974_, lean_object* v_n_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_BitVec_instHShiftLeft(v_m_974_, v_n_975_);
lean_dec(v_n_975_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight(lean_object* v_m_978_, lean_object* v_n_979_){
_start:
{
lean_object* v___f_980_; 
v___f_980_ = ((lean_object*)(l_BitVec_instHShiftRight___closed__0));
return v___f_980_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___boxed(lean_object* v_m_981_, lean_object* v_n_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_BitVec_instHShiftRight(v_m_981_, v_n_982_);
lean_dec(v_n_982_);
lean_dec(v_m_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg(lean_object* v_n_984_, lean_object* v_a_985_, lean_object* v_s_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_BitVec_sshiftRight(v_n_984_, v_a_985_, v_s_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg___boxed(lean_object* v_n_988_, lean_object* v_a_989_, lean_object* v_s_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_BitVec_sshiftRight_x27___redArg(v_n_988_, v_a_989_, v_s_990_);
lean_dec(v_s_990_);
lean_dec(v_n_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27(lean_object* v_n_992_, lean_object* v_m_993_, lean_object* v_a_994_, lean_object* v_s_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_BitVec_sshiftRight(v_n_992_, v_a_994_, v_s_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___boxed(lean_object* v_n_997_, lean_object* v_m_998_, lean_object* v_a_999_, lean_object* v_s_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_BitVec_sshiftRight_x27(v_n_997_, v_m_998_, v_a_999_, v_s_1000_);
lean_dec(v_s_1000_);
lean_dec(v_m_998_);
lean_dec(v_n_997_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux(lean_object* v_w_1002_, lean_object* v_x_1003_, lean_object* v_n_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1005_ = l_BitVec_shiftLeft(v_w_1002_, v_x_1003_, v_n_1004_);
v___x_1006_ = lean_nat_sub(v_w_1002_, v_n_1004_);
v___x_1007_ = lean_nat_shiftr(v_x_1003_, v___x_1006_);
lean_dec(v___x_1006_);
v___x_1008_ = lean_nat_lor(v___x_1005_, v___x_1007_);
lean_dec(v___x_1007_);
lean_dec(v___x_1005_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux___boxed(lean_object* v_w_1009_, lean_object* v_x_1010_, lean_object* v_n_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_BitVec_rotateLeftAux(v_w_1009_, v_x_1010_, v_n_1011_);
lean_dec(v_n_1011_);
lean_dec(v_x_1010_);
lean_dec(v_w_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft(lean_object* v_w_1013_, lean_object* v_x_1014_, lean_object* v_n_1015_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_nat_mod(v_n_1015_, v_w_1013_);
v___x_1017_ = l_BitVec_rotateLeftAux(v_w_1013_, v_x_1014_, v___x_1016_);
lean_dec(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft___boxed(lean_object* v_w_1018_, lean_object* v_x_1019_, lean_object* v_n_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_BitVec_rotateLeft(v_w_1018_, v_x_1019_, v_n_1020_);
lean_dec(v_n_1020_);
lean_dec(v_x_1019_);
lean_dec(v_w_1018_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux(lean_object* v_w_1022_, lean_object* v_x_1023_, lean_object* v_n_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1025_ = lean_nat_shiftr(v_x_1023_, v_n_1024_);
v___x_1026_ = lean_nat_sub(v_w_1022_, v_n_1024_);
v___x_1027_ = l_BitVec_shiftLeft(v_w_1022_, v_x_1023_, v___x_1026_);
lean_dec(v___x_1026_);
v___x_1028_ = lean_nat_lor(v___x_1025_, v___x_1027_);
lean_dec(v___x_1027_);
lean_dec(v___x_1025_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux___boxed(lean_object* v_w_1029_, lean_object* v_x_1030_, lean_object* v_n_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_BitVec_rotateRightAux(v_w_1029_, v_x_1030_, v_n_1031_);
lean_dec(v_n_1031_);
lean_dec(v_x_1030_);
lean_dec(v_w_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight(lean_object* v_w_1033_, lean_object* v_x_1034_, lean_object* v_n_1035_){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_nat_mod(v_n_1035_, v_w_1033_);
v___x_1037_ = l_BitVec_rotateRightAux(v_w_1033_, v_x_1034_, v___x_1036_);
lean_dec(v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight___boxed(lean_object* v_w_1038_, lean_object* v_x_1039_, lean_object* v_n_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_BitVec_rotateRight(v_w_1038_, v_x_1039_, v_n_1040_);
lean_dec(v_n_1040_);
lean_dec(v_x_1039_);
lean_dec(v_w_1038_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___redArg(lean_object* v_m_1042_, lean_object* v_msbs_1043_, lean_object* v_lsbs_1044_){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_nat_shiftl(v_msbs_1043_, v_m_1042_);
v___x_1046_ = lean_nat_lor(v___x_1045_, v_lsbs_1044_);
lean_dec(v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___redArg___boxed(lean_object* v_m_1047_, lean_object* v_msbs_1048_, lean_object* v_lsbs_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_BitVec_append___redArg(v_m_1047_, v_msbs_1048_, v_lsbs_1049_);
lean_dec(v_lsbs_1049_);
lean_dec(v_msbs_1048_);
lean_dec(v_m_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append(lean_object* v_n_1051_, lean_object* v_m_1052_, lean_object* v_msbs_1053_, lean_object* v_lsbs_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_BitVec_append___redArg(v_m_1052_, v_msbs_1053_, v_lsbs_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___boxed(lean_object* v_n_1056_, lean_object* v_m_1057_, lean_object* v_msbs_1058_, lean_object* v_lsbs_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_BitVec_append(v_n_1056_, v_m_1057_, v_msbs_1058_, v_lsbs_1059_);
lean_dec(v_lsbs_1059_);
lean_dec(v_msbs_1058_);
lean_dec(v_m_1057_);
lean_dec(v_n_1056_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat(lean_object* v_w_1061_, lean_object* v_v_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_closure((void*)(l_BitVec_append___boxed), 4, 2);
lean_closure_set(v___x_1063_, 0, v_w_1061_);
lean_closure_set(v___x_1063_, 1, v_v_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate(lean_object* v_w_1064_, lean_object* v_x_1065_, lean_object* v_x_1066_){
_start:
{
lean_object* v_zero_1067_; uint8_t v_isZero_1068_; 
v_zero_1067_ = lean_unsigned_to_nat(0u);
v_isZero_1068_ = lean_nat_dec_eq(v_x_1065_, v_zero_1067_);
if (v_isZero_1068_ == 1)
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1069_;
}
else
{
lean_object* v_one_1070_; lean_object* v_n_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_one_1070_ = lean_unsigned_to_nat(1u);
v_n_1071_ = lean_nat_sub(v_x_1065_, v_one_1070_);
v___x_1072_ = lean_nat_mul(v_w_1064_, v_n_1071_);
v___x_1073_ = l_BitVec_replicate(v_w_1064_, v_n_1071_, v_x_1066_);
lean_dec(v_n_1071_);
v___x_1074_ = l_BitVec_append___redArg(v___x_1072_, v_x_1066_, v___x_1073_);
lean_dec(v___x_1073_);
lean_dec(v___x_1072_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate___boxed(lean_object* v_w_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_BitVec_replicate(v_w_1075_, v_x_1076_, v_x_1077_);
lean_dec(v_x_1077_);
lean_dec(v_x_1076_);
lean_dec(v_w_1075_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___redArg(lean_object* v_msbs_1079_, uint8_t v_lsb_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = lean_unsigned_to_nat(1u);
v___x_1082_ = l_BitVec_ofBool(v_lsb_1080_);
v___x_1083_ = l_BitVec_append___redArg(v___x_1081_, v_msbs_1079_, v___x_1082_);
lean_dec(v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___redArg___boxed(lean_object* v_msbs_1084_, lean_object* v_lsb_1085_){
_start:
{
uint8_t v_lsb_boxed_1086_; lean_object* v_res_1087_; 
v_lsb_boxed_1086_ = lean_unbox(v_lsb_1085_);
v_res_1087_ = l_BitVec_concat___redArg(v_msbs_1084_, v_lsb_boxed_1086_);
lean_dec(v_msbs_1084_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat(lean_object* v_n_1088_, lean_object* v_msbs_1089_, uint8_t v_lsb_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_BitVec_concat___redArg(v_msbs_1089_, v_lsb_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___boxed(lean_object* v_n_1092_, lean_object* v_msbs_1093_, lean_object* v_lsb_1094_){
_start:
{
uint8_t v_lsb_boxed_1095_; lean_object* v_res_1096_; 
v_lsb_boxed_1095_ = lean_unbox(v_lsb_1094_);
v_res_1096_ = l_BitVec_concat(v_n_1092_, v_msbs_1093_, v_lsb_boxed_1095_);
lean_dec(v_msbs_1093_);
lean_dec(v_n_1092_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat(lean_object* v_n_1097_, lean_object* v_x_1098_, uint8_t v_b_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1100_ = lean_unsigned_to_nat(1u);
v___x_1101_ = lean_nat_add(v_n_1097_, v___x_1100_);
v___x_1102_ = l_BitVec_concat___redArg(v_x_1098_, v_b_1099_);
v___x_1103_ = l_BitVec_setWidth(v___x_1101_, v_n_1097_, v___x_1102_);
lean_dec(v___x_1102_);
lean_dec(v___x_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat___boxed(lean_object* v_n_1104_, lean_object* v_x_1105_, lean_object* v_b_1106_){
_start:
{
uint8_t v_b_boxed_1107_; lean_object* v_res_1108_; 
v_b_boxed_1107_ = lean_unbox(v_b_1106_);
v_res_1108_ = l_BitVec_shiftConcat(v_n_1104_, v_x_1105_, v_b_boxed_1107_);
lean_dec(v_x_1105_);
lean_dec(v_n_1104_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cons(lean_object* v_n_1109_, uint8_t v_msb_1110_, lean_object* v_lsbs_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = l_BitVec_ofBool(v_msb_1110_);
v___x_1113_ = l_BitVec_append___redArg(v_n_1109_, v___x_1112_, v_lsbs_1111_);
lean_dec(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cons___boxed(lean_object* v_n_1114_, lean_object* v_msb_1115_, lean_object* v_lsbs_1116_){
_start:
{
uint8_t v_msb_boxed_1117_; lean_object* v_res_1118_; 
v_msb_boxed_1117_ = lean_unbox(v_msb_1115_);
v_res_1118_ = l_BitVec_cons(v_n_1114_, v_msb_boxed_1117_, v_lsbs_1116_);
lean_dec(v_lsbs_1116_);
lean_dec(v_n_1114_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow(lean_object* v_w_1119_, lean_object* v_i_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = l_BitVec_ofNat(v_w_1119_, v___x_1121_);
v___x_1123_ = l_BitVec_shiftLeft(v_w_1119_, v___x_1122_, v_i_1120_);
lean_dec(v___x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow___boxed(lean_object* v_w_1124_, lean_object* v_i_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_BitVec_twoPow(v_w_1124_, v_i_1125_);
lean_dec(v_i_1125_);
lean_dec(v_w_1124_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMin(lean_object* v_w_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_unsigned_to_nat(1u);
v___x_1129_ = lean_nat_sub(v_w_1127_, v___x_1128_);
v___x_1130_ = l_BitVec_twoPow(v_w_1127_, v___x_1129_);
lean_dec(v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMin___boxed(lean_object* v_w_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_BitVec_intMin(v_w_1131_);
lean_dec(v_w_1131_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMax(lean_object* v_w_1133_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1134_ = lean_unsigned_to_nat(1u);
v___x_1135_ = lean_nat_sub(v_w_1133_, v___x_1134_);
v___x_1136_ = l_BitVec_twoPow(v_w_1133_, v___x_1135_);
lean_dec(v___x_1135_);
v___x_1137_ = l_BitVec_ofNat(v_w_1133_, v___x_1134_);
v___x_1138_ = l_BitVec_sub(v_w_1133_, v___x_1136_, v___x_1137_);
lean_dec(v___x_1137_);
lean_dec(v___x_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMax___boxed(lean_object* v_w_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_BitVec_intMax(v_w_1139_);
lean_dec(v_w_1139_);
return v_res_1140_;
}
}
LEAN_EXPORT uint64_t l_BitVec_hash(lean_object* v_n_1141_, lean_object* v_bv_1142_){
_start:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = lean_unsigned_to_nat(64u);
v___x_1144_ = lean_nat_dec_le(v_n_1141_, v___x_1143_);
if (v___x_1144_ == 0)
{
uint64_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint64_t v___x_1149_; uint64_t v___x_1150_; 
v___x_1145_ = lean_uint64_of_nat(v_bv_1142_);
v___x_1146_ = lean_nat_sub(v_n_1141_, v___x_1143_);
v___x_1147_ = lean_nat_shiftr(v_bv_1142_, v___x_1143_);
v___x_1148_ = l_BitVec_setWidth(v_n_1141_, v___x_1146_, v___x_1147_);
lean_dec(v___x_1147_);
v___x_1149_ = l_BitVec_hash(v___x_1146_, v___x_1148_);
lean_dec(v___x_1148_);
lean_dec(v___x_1146_);
v___x_1150_ = lean_uint64_mix_hash(v___x_1145_, v___x_1149_);
return v___x_1150_;
}
else
{
uint64_t v___x_1151_; 
v___x_1151_ = lean_uint64_of_nat(v_bv_1142_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_hash___boxed(lean_object* v_n_1152_, lean_object* v_bv_1153_){
_start:
{
uint64_t v_res_1154_; lean_object* v_r_1155_; 
v_res_1154_ = l_BitVec_hash(v_n_1152_, v_bv_1153_);
lean_dec(v_bv_1153_);
lean_dec(v_n_1152_);
v_r_1155_ = lean_box_uint64(v_res_1154_);
return v_r_1155_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHashable(lean_object* v_n_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_closure((void*)(l_BitVec_hash___boxed), 2, 1);
lean_closure_set(v___x_1157_, 0, v_n_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE(lean_object* v_x_1158_){
_start:
{
if (lean_obj_tag(v_x_1158_) == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1159_;
}
else
{
lean_object* v_head_1160_; lean_object* v_tail_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; 
v_head_1160_ = lean_ctor_get(v_x_1158_, 0);
v_tail_1161_ = lean_ctor_get(v_x_1158_, 1);
v___x_1162_ = l_List_lengthTR___redArg(v_tail_1161_);
v___x_1163_ = l_BitVec_ofBoolListBE(v_tail_1161_);
v___x_1164_ = lean_unbox(v_head_1160_);
v___x_1165_ = l_BitVec_cons(v___x_1162_, v___x_1164_, v___x_1163_);
lean_dec(v___x_1163_);
lean_dec(v___x_1162_);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE___boxed(lean_object* v_x_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_BitVec_ofBoolListBE(v_x_1166_);
lean_dec(v_x_1166_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE(lean_object* v_x_1168_){
_start:
{
if (lean_obj_tag(v_x_1168_) == 0)
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1169_;
}
else
{
lean_object* v_head_1170_; lean_object* v_tail_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; 
v_head_1170_ = lean_ctor_get(v_x_1168_, 0);
v_tail_1171_ = lean_ctor_get(v_x_1168_, 1);
v___x_1172_ = l_BitVec_ofBoolListLE(v_tail_1171_);
v___x_1173_ = lean_unbox(v_head_1170_);
v___x_1174_ = l_BitVec_concat___redArg(v___x_1172_, v___x_1173_);
lean_dec(v___x_1172_);
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE___boxed(lean_object* v_x_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_BitVec_ofBoolListLE(v_x_1175_);
lean_dec(v_x_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uaddOverflow(lean_object* v_w_1177_, lean_object* v_x_1178_, lean_object* v_y_1179_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1180_ = lean_unsigned_to_nat(2u);
v___x_1181_ = lean_nat_pow(v___x_1180_, v_w_1177_);
v___x_1182_ = lean_nat_add(v_x_1178_, v_y_1179_);
v___x_1183_ = lean_nat_dec_le(v___x_1181_, v___x_1182_);
lean_dec(v___x_1182_);
lean_dec(v___x_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_BitVec_uaddOverflow___boxed(lean_object* v_w_1184_, lean_object* v_x_1185_, lean_object* v_y_1186_){
_start:
{
uint8_t v_res_1187_; lean_object* v_r_1188_; 
v_res_1187_ = l_BitVec_uaddOverflow(v_w_1184_, v_x_1185_, v_y_1186_);
lean_dec(v_y_1186_);
lean_dec(v_x_1185_);
lean_dec(v_w_1184_);
v_r_1188_ = lean_box(v_res_1187_);
return v_r_1188_;
}
}
static lean_object* _init_l_BitVec_saddOverflow___closed__0(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_unsigned_to_nat(2u);
v___x_1190_ = lean_nat_to_int(v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT uint8_t l_BitVec_saddOverflow(lean_object* v_w_1191_, lean_object* v_x_1192_, lean_object* v_y_1193_){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1194_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1195_ = lean_unsigned_to_nat(1u);
v___x_1196_ = lean_nat_sub(v_w_1191_, v___x_1195_);
v___x_1197_ = l_Int_pow(v___x_1194_, v___x_1196_);
lean_dec(v___x_1196_);
v___x_1198_ = l_BitVec_toInt(v_w_1191_, v_x_1192_);
v___x_1199_ = l_BitVec_toInt(v_w_1191_, v_y_1193_);
v___x_1200_ = lean_int_add(v___x_1198_, v___x_1199_);
lean_dec(v___x_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_int_dec_le(v___x_1197_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = lean_int_neg(v___x_1197_);
lean_dec(v___x_1197_);
v___x_1203_ = lean_int_dec_lt(v___x_1200_, v___x_1202_);
lean_dec(v___x_1202_);
lean_dec(v___x_1200_);
return v___x_1203_;
}
else
{
lean_dec(v___x_1200_);
lean_dec(v___x_1197_);
return v___x_1201_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_saddOverflow___boxed(lean_object* v_w_1204_, lean_object* v_x_1205_, lean_object* v_y_1206_){
_start:
{
uint8_t v_res_1207_; lean_object* v_r_1208_; 
v_res_1207_ = l_BitVec_saddOverflow(v_w_1204_, v_x_1205_, v_y_1206_);
lean_dec(v_w_1204_);
v_r_1208_ = lean_box(v_res_1207_);
return v_r_1208_;
}
}
LEAN_EXPORT uint8_t l_BitVec_usubOverflow___redArg(lean_object* v_x_1209_, lean_object* v_y_1210_){
_start:
{
uint8_t v___x_1211_; 
v___x_1211_ = lean_nat_dec_lt(v_x_1209_, v_y_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___redArg___boxed(lean_object* v_x_1212_, lean_object* v_y_1213_){
_start:
{
uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_res_1214_ = l_BitVec_usubOverflow___redArg(v_x_1212_, v_y_1213_);
lean_dec(v_y_1213_);
lean_dec(v_x_1212_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT uint8_t l_BitVec_usubOverflow(lean_object* v_w_1216_, lean_object* v_x_1217_, lean_object* v_y_1218_){
_start:
{
uint8_t v___x_1219_; 
v___x_1219_ = lean_nat_dec_lt(v_x_1217_, v_y_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___boxed(lean_object* v_w_1220_, lean_object* v_x_1221_, lean_object* v_y_1222_){
_start:
{
uint8_t v_res_1223_; lean_object* v_r_1224_; 
v_res_1223_ = l_BitVec_usubOverflow(v_w_1220_, v_x_1221_, v_y_1222_);
lean_dec(v_y_1222_);
lean_dec(v_x_1221_);
lean_dec(v_w_1220_);
v_r_1224_ = lean_box(v_res_1223_);
return v_r_1224_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ssubOverflow(lean_object* v_w_1225_, lean_object* v_x_1226_, lean_object* v_y_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1228_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1229_ = lean_unsigned_to_nat(1u);
v___x_1230_ = lean_nat_sub(v_w_1225_, v___x_1229_);
v___x_1231_ = l_Int_pow(v___x_1228_, v___x_1230_);
lean_dec(v___x_1230_);
v___x_1232_ = l_BitVec_toInt(v_w_1225_, v_x_1226_);
v___x_1233_ = l_BitVec_toInt(v_w_1225_, v_y_1227_);
v___x_1234_ = lean_int_sub(v___x_1232_, v___x_1233_);
lean_dec(v___x_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_int_dec_le(v___x_1231_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = lean_int_neg(v___x_1231_);
lean_dec(v___x_1231_);
v___x_1237_ = lean_int_dec_lt(v___x_1234_, v___x_1236_);
lean_dec(v___x_1236_);
lean_dec(v___x_1234_);
return v___x_1237_;
}
else
{
lean_dec(v___x_1234_);
lean_dec(v___x_1231_);
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ssubOverflow___boxed(lean_object* v_w_1238_, lean_object* v_x_1239_, lean_object* v_y_1240_){
_start:
{
uint8_t v_res_1241_; lean_object* v_r_1242_; 
v_res_1241_ = l_BitVec_ssubOverflow(v_w_1238_, v_x_1239_, v_y_1240_);
lean_dec(v_w_1238_);
v_r_1242_ = lean_box(v_res_1241_);
return v_r_1242_;
}
}
LEAN_EXPORT uint8_t l_BitVec_negOverflow(lean_object* v_w_1243_, lean_object* v_x_1244_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1245_ = l_BitVec_toInt(v_w_1243_, v_x_1244_);
v___x_1246_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_nat_sub(v_w_1243_, v___x_1247_);
v___x_1249_ = l_Int_pow(v___x_1246_, v___x_1248_);
lean_dec(v___x_1248_);
v___x_1250_ = lean_int_neg(v___x_1249_);
lean_dec(v___x_1249_);
v___x_1251_ = lean_int_dec_eq(v___x_1245_, v___x_1250_);
lean_dec(v___x_1250_);
lean_dec(v___x_1245_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_BitVec_negOverflow___boxed(lean_object* v_w_1252_, lean_object* v_x_1253_){
_start:
{
uint8_t v_res_1254_; lean_object* v_r_1255_; 
v_res_1254_ = l_BitVec_negOverflow(v_w_1252_, v_x_1253_);
lean_dec(v_w_1252_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT uint8_t l_BitVec_sdivOverflow(lean_object* v_w_1256_, lean_object* v_x_1257_, lean_object* v_y_1258_){
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
v___x_1265_ = lean_int_ediv(v___x_1263_, v___x_1264_);
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
LEAN_EXPORT lean_object* l_BitVec_sdivOverflow___boxed(lean_object* v_w_1269_, lean_object* v_x_1270_, lean_object* v_y_1271_){
_start:
{
uint8_t v_res_1272_; lean_object* v_r_1273_; 
v_res_1272_ = l_BitVec_sdivOverflow(v_w_1269_, v_x_1270_, v_y_1271_);
lean_dec(v_w_1269_);
v_r_1273_ = lean_box(v_res_1272_);
return v_r_1273_;
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse(lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v_zero_1276_; uint8_t v_isZero_1277_; 
v_zero_1276_ = lean_unsigned_to_nat(0u);
v_isZero_1277_ = lean_nat_dec_eq(v_x_1274_, v_zero_1276_);
if (v_isZero_1277_ == 1)
{
lean_inc(v_x_1275_);
return v_x_1275_;
}
else
{
lean_object* v_one_1278_; lean_object* v_n_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v_one_1278_ = lean_unsigned_to_nat(1u);
v_n_1279_ = lean_nat_sub(v_x_1274_, v_one_1278_);
v___x_1280_ = lean_nat_add(v_n_1279_, v_one_1278_);
v___x_1281_ = l_BitVec_setWidth(v___x_1280_, v_n_1279_, v_x_1275_);
v___x_1282_ = l_BitVec_reverse(v_n_1279_, v___x_1281_);
lean_dec(v___x_1281_);
lean_dec(v_n_1279_);
v___x_1283_ = lean_nat_dec_lt(v_zero_1276_, v___x_1280_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
lean_dec(v___x_1280_);
v___x_1284_ = l_BitVec_concat___redArg(v___x_1282_, v___x_1283_);
lean_dec(v___x_1282_);
return v___x_1284_;
}
else
{
lean_object* v___x_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = lean_nat_sub(v___x_1280_, v_one_1278_);
lean_dec(v___x_1280_);
v___x_1286_ = l_Nat_testBit(v_x_1275_, v___x_1285_);
lean_dec(v___x_1285_);
v___x_1287_ = l_BitVec_concat___redArg(v___x_1282_, v___x_1286_);
lean_dec(v___x_1282_);
return v___x_1287_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse___boxed(lean_object* v_x_1288_, lean_object* v_x_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_BitVec_reverse(v_x_1288_, v_x_1289_);
lean_dec(v_x_1289_);
lean_dec(v_x_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT uint8_t l_BitVec_umulOverflow(lean_object* v_w_1291_, lean_object* v_x_1292_, lean_object* v_y_1293_){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1294_ = lean_unsigned_to_nat(2u);
v___x_1295_ = lean_nat_pow(v___x_1294_, v_w_1291_);
v___x_1296_ = lean_nat_mul(v_x_1292_, v_y_1293_);
v___x_1297_ = lean_nat_dec_le(v___x_1295_, v___x_1296_);
lean_dec(v___x_1296_);
lean_dec(v___x_1295_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umulOverflow___boxed(lean_object* v_w_1298_, lean_object* v_x_1299_, lean_object* v_y_1300_){
_start:
{
uint8_t v_res_1301_; lean_object* v_r_1302_; 
v_res_1301_ = l_BitVec_umulOverflow(v_w_1298_, v_x_1299_, v_y_1300_);
lean_dec(v_y_1300_);
lean_dec(v_x_1299_);
lean_dec(v_w_1298_);
v_r_1302_ = lean_box(v_res_1301_);
return v_r_1302_;
}
}
LEAN_EXPORT uint8_t l_BitVec_smulOverflow(lean_object* v_w_1303_, lean_object* v_x_1304_, lean_object* v_y_1305_){
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
v___x_1312_ = lean_int_mul(v___x_1310_, v___x_1311_);
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
LEAN_EXPORT lean_object* l_BitVec_smulOverflow___boxed(lean_object* v_w_1316_, lean_object* v_x_1317_, lean_object* v_y_1318_){
_start:
{
uint8_t v_res_1319_; lean_object* v_r_1320_; 
v_res_1319_ = l_BitVec_smulOverflow(v_w_1316_, v_x_1317_, v_y_1318_);
lean_dec(v_w_1316_);
v_r_1320_ = lean_box(v_res_1319_);
return v_r_1320_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec(lean_object* v_w_1321_, lean_object* v_x_1322_, lean_object* v_n_1323_){
_start:
{
lean_object* v_zero_1324_; uint8_t v_isZero_1325_; 
v_zero_1324_ = lean_unsigned_to_nat(0u);
v_isZero_1325_ = lean_nat_dec_eq(v_n_1323_, v_zero_1324_);
if (v_isZero_1325_ == 1)
{
uint8_t v___x_1326_; 
lean_dec(v_n_1323_);
v___x_1326_ = l_Nat_testBit(v_x_1322_, v_zero_1324_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = l_BitVec_ofNat(v_w_1321_, v_w_1321_);
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_sub(v_w_1321_, v___x_1328_);
v___x_1330_ = l_BitVec_ofNat(v_w_1321_, v___x_1329_);
lean_dec(v___x_1329_);
return v___x_1330_;
}
}
else
{
uint8_t v___x_1331_; 
v___x_1331_ = l_Nat_testBit(v_x_1322_, v_n_1323_);
if (v___x_1331_ == 0)
{
lean_object* v_one_1332_; lean_object* v_n_1333_; 
v_one_1332_ = lean_unsigned_to_nat(1u);
v_n_1333_ = lean_nat_sub(v_n_1323_, v_one_1332_);
lean_dec(v_n_1323_);
v_n_1323_ = v_n_1333_;
goto _start;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1335_ = lean_unsigned_to_nat(1u);
v___x_1336_ = lean_nat_sub(v_w_1321_, v___x_1335_);
v___x_1337_ = lean_nat_sub(v___x_1336_, v_n_1323_);
lean_dec(v_n_1323_);
lean_dec(v___x_1336_);
v___x_1338_ = l_BitVec_ofNat(v_w_1321_, v___x_1337_);
lean_dec(v___x_1337_);
return v___x_1338_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec___boxed(lean_object* v_w_1339_, lean_object* v_x_1340_, lean_object* v_n_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_BitVec_clzAuxRec(v_w_1339_, v_x_1340_, v_n_1341_);
lean_dec(v_x_1340_);
lean_dec(v_w_1339_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clz(lean_object* v_w_1343_, lean_object* v_x_1344_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = lean_unsigned_to_nat(1u);
v___x_1346_ = lean_nat_sub(v_w_1343_, v___x_1345_);
v___x_1347_ = l_BitVec_clzAuxRec(v_w_1343_, v_x_1344_, v___x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clz___boxed(lean_object* v_w_1348_, lean_object* v_x_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_BitVec_clz(v_w_1348_, v_x_1349_);
lean_dec(v_x_1349_);
lean_dec(v_w_1348_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ctz(lean_object* v_w_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = l_BitVec_reverse(v_w_1351_, v_x_1352_);
v___x_1354_ = l_BitVec_clz(v_w_1351_, v___x_1353_);
lean_dec(v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ctz___boxed(lean_object* v_w_1355_, lean_object* v_x_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_BitVec_ctz(v_w_1355_, v_x_1356_);
lean_dec(v_x_1356_);
lean_dec(v_w_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg(lean_object* v_x_1358_, lean_object* v_pos_1359_, lean_object* v_acc_1360_){
_start:
{
lean_object* v_zero_1361_; uint8_t v_isZero_1362_; 
v_zero_1361_ = lean_unsigned_to_nat(0u);
v_isZero_1362_ = lean_nat_dec_eq(v_pos_1359_, v_zero_1361_);
if (v_isZero_1362_ == 1)
{
lean_dec(v_pos_1359_);
return v_acc_1360_;
}
else
{
lean_object* v_one_1363_; lean_object* v_n_1364_; uint8_t v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_one_1363_ = lean_unsigned_to_nat(1u);
v_n_1364_ = lean_nat_sub(v_pos_1359_, v_one_1363_);
lean_dec(v_pos_1359_);
v___x_1365_ = l_Nat_testBit(v_x_1358_, v_n_1364_);
v___x_1366_ = l_Bool_toNat(v___x_1365_);
v___x_1367_ = lean_nat_add(v_acc_1360_, v___x_1366_);
lean_dec(v___x_1366_);
lean_dec(v_acc_1360_);
v_pos_1359_ = v_n_1364_;
v_acc_1360_ = v___x_1367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg___boxed(lean_object* v_x_1369_, lean_object* v_pos_1370_, lean_object* v_acc_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_BitVec_cpopNatRec___redArg(v_x_1369_, v_pos_1370_, v_acc_1371_);
lean_dec(v_x_1369_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec(lean_object* v_w_1373_, lean_object* v_x_1374_, lean_object* v_pos_1375_, lean_object* v_acc_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_BitVec_cpopNatRec___redArg(v_x_1374_, v_pos_1375_, v_acc_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___boxed(lean_object* v_w_1378_, lean_object* v_x_1379_, lean_object* v_pos_1380_, lean_object* v_acc_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_BitVec_cpopNatRec(v_w_1378_, v_x_1379_, v_pos_1380_, v_acc_1381_);
lean_dec(v_x_1379_);
lean_dec(v_w_1378_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpop(lean_object* v_w_1383_, lean_object* v_x_1384_){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = lean_unsigned_to_nat(0u);
lean_inc(v_w_1383_);
v___x_1386_ = l_BitVec_cpopNatRec___redArg(v_x_1384_, v_w_1383_, v___x_1385_);
v___x_1387_ = l_BitVec_ofNat(v_w_1383_, v___x_1386_);
lean_dec(v___x_1386_);
lean_dec(v_w_1383_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpop___boxed(lean_object* v_w_1388_, lean_object* v_x_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_BitVec_cpop(v_w_1388_, v_x_1389_);
lean_dec(v_x_1389_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___lam__0(lean_object* v_x_1391_, lean_object* v_y_1392_){
_start:
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_nat_dec_le(v_x_1391_, v_y_1392_);
if (v___x_1393_ == 0)
{
lean_inc(v_y_1392_);
return v_y_1392_;
}
else
{
lean_inc(v_x_1391_);
return v_x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___lam__0___boxed(lean_object* v_x_1394_, lean_object* v_y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_BitVec_instMin___lam__0(v_x_1394_, v_y_1395_);
lean_dec(v_y_1395_);
lean_dec(v_x_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin(lean_object* v_w_1398_){
_start:
{
lean_object* v___f_1399_; 
v___f_1399_ = ((lean_object*)(l_BitVec_instMin___closed__0));
return v___f_1399_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___boxed(lean_object* v_w_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_BitVec_instMin(v_w_1400_);
lean_dec(v_w_1400_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___lam__0(lean_object* v_x_1402_, lean_object* v_y_1403_){
_start:
{
uint8_t v___x_1404_; 
v___x_1404_ = lean_nat_dec_le(v_x_1402_, v_y_1403_);
if (v___x_1404_ == 0)
{
lean_inc(v_x_1402_);
return v_x_1402_;
}
else
{
lean_inc(v_y_1403_);
return v_y_1403_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___lam__0___boxed(lean_object* v_x_1405_, lean_object* v_y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_BitVec_instMax___lam__0(v_x_1405_, v_y_1406_);
lean_dec(v_y_1406_);
lean_dec(v_x_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax(lean_object* v_w_1409_){
_start:
{
lean_object* v___f_1410_; 
v___f_1410_ = ((lean_object*)(l_BitVec_instMax___closed__0));
return v___f_1410_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___boxed(lean_object* v_w_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_BitVec_instMax(v_w_1411_);
lean_dec(v_w_1411_);
return v_res_1412_;
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
