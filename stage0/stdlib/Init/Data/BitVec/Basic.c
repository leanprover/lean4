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
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_nat_dec_lt(v___x_577_, v_n_563_);
if (v___x_578_ == 0)
{
goto v___jp_566_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_sub(v_n_563_, v___x_579_);
v___x_581_ = l_Nat_testBit(v_x_564_, v___x_580_);
if (v___x_581_ == 0)
{
lean_dec(v___x_580_);
goto v___jp_566_;
}
else
{
uint8_t v___x_582_; 
v___x_582_ = l_Nat_testBit(v_y_565_, v___x_580_);
lean_dec(v___x_580_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = l_BitVec_neg(v_n_563_, v_x_564_);
v___x_584_ = lean_nat_div(v___x_583_, v_y_565_);
lean_dec(v___x_583_);
v___x_585_ = l_BitVec_neg(v_n_563_, v___x_584_);
lean_dec(v___x_584_);
return v___x_585_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = l_BitVec_neg(v_n_563_, v_x_564_);
v___x_587_ = l_BitVec_neg(v_n_563_, v_y_565_);
v___x_588_ = lean_nat_div(v___x_586_, v___x_587_);
lean_dec(v___x_587_);
lean_dec(v___x_586_);
return v___x_588_;
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
}
}
LEAN_EXPORT lean_object* l_BitVec_sdiv___boxed(lean_object* v_n_589_, lean_object* v_x_590_, lean_object* v_y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_BitVec_sdiv(v_n_589_, v_x_590_, v_y_591_);
lean_dec(v_y_591_);
lean_dec(v_x_590_);
lean_dec(v_n_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv(lean_object* v_n_593_, lean_object* v_x_594_, lean_object* v_y_595_){
_start:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_nat_dec_lt(v___x_607_, v_n_593_);
if (v___x_608_ == 0)
{
goto v___jp_596_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_sub(v_n_593_, v___x_609_);
v___x_611_ = l_Nat_testBit(v_x_594_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec(v___x_610_);
goto v___jp_596_;
}
else
{
uint8_t v___x_612_; 
v___x_612_ = l_Nat_testBit(v_y_595_, v___x_610_);
lean_dec(v___x_610_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = l_BitVec_neg(v_n_593_, v_x_594_);
v___x_614_ = l_BitVec_smtUDiv(v_n_593_, v___x_613_, v_y_595_);
lean_dec(v___x_613_);
v___x_615_ = l_BitVec_neg(v_n_593_, v___x_614_);
lean_dec(v___x_614_);
return v___x_615_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = l_BitVec_neg(v_n_593_, v_x_594_);
v___x_617_ = l_BitVec_neg(v_n_593_, v_y_595_);
v___x_618_ = l_BitVec_smtUDiv(v_n_593_, v___x_616_, v___x_617_);
lean_dec(v___x_617_);
lean_dec(v___x_616_);
return v___x_618_;
}
}
}
v___jp_596_:
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_nat_dec_lt(v___x_597_, v_n_593_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
v___x_599_ = l_BitVec_smtUDiv(v_n_593_, v_x_594_, v_y_595_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_sub(v_n_593_, v___x_600_);
v___x_602_ = l_Nat_testBit(v_y_595_, v___x_601_);
lean_dec(v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; 
v___x_603_ = l_BitVec_smtUDiv(v_n_593_, v_x_594_, v_y_595_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = l_BitVec_neg(v_n_593_, v_y_595_);
v___x_605_ = l_BitVec_smtUDiv(v_n_593_, v_x_594_, v___x_604_);
lean_dec(v___x_604_);
v___x_606_ = l_BitVec_neg(v_n_593_, v___x_605_);
lean_dec(v___x_605_);
return v___x_606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smtSDiv___boxed(lean_object* v_n_619_, lean_object* v_x_620_, lean_object* v_y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_BitVec_smtSDiv(v_n_619_, v_x_620_, v_y_621_);
lean_dec(v_y_621_);
lean_dec(v_x_620_);
lean_dec(v_n_619_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_BitVec_srem(lean_object* v_n_623_, lean_object* v_x_624_, lean_object* v_y_625_){
_start:
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_nat_dec_lt(v___x_636_, v_n_623_);
if (v___x_637_ == 0)
{
goto v___jp_626_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_sub(v_n_623_, v___x_638_);
v___x_640_ = l_Nat_testBit(v_x_624_, v___x_639_);
if (v___x_640_ == 0)
{
lean_dec(v___x_639_);
goto v___jp_626_;
}
else
{
uint8_t v___x_641_; 
v___x_641_ = l_Nat_testBit(v_y_625_, v___x_639_);
lean_dec(v___x_639_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = l_BitVec_neg(v_n_623_, v_x_624_);
v___x_643_ = lean_nat_mod(v___x_642_, v_y_625_);
lean_dec(v___x_642_);
v___x_644_ = l_BitVec_neg(v_n_623_, v___x_643_);
lean_dec(v___x_643_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_645_ = l_BitVec_neg(v_n_623_, v_x_624_);
v___x_646_ = l_BitVec_neg(v_n_623_, v_y_625_);
v___x_647_ = lean_nat_mod(v___x_645_, v___x_646_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
v___x_648_ = l_BitVec_neg(v_n_623_, v___x_647_);
lean_dec(v___x_647_);
return v___x_648_;
}
}
}
v___jp_626_:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_nat_dec_lt(v___x_627_, v_n_623_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_nat_mod(v_x_624_, v_y_625_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_sub(v_n_623_, v___x_630_);
v___x_632_ = l_Nat_testBit(v_y_625_, v___x_631_);
lean_dec(v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
v___x_633_ = lean_nat_mod(v_x_624_, v_y_625_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = l_BitVec_neg(v_n_623_, v_y_625_);
v___x_635_ = lean_nat_mod(v_x_624_, v___x_634_);
lean_dec(v___x_634_);
return v___x_635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_srem___boxed(lean_object* v_n_649_, lean_object* v_x_650_, lean_object* v_y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_BitVec_srem(v_n_649_, v_x_650_, v_y_651_);
lean_dec(v_y_651_);
lean_dec(v_x_650_);
lean_dec(v_n_649_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_BitVec_smod(lean_object* v_m_653_, lean_object* v_x_654_, lean_object* v_y_655_){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_nat_dec_lt(v___x_668_, v_m_653_);
if (v___x_669_ == 0)
{
goto v___jp_656_;
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_sub(v_m_653_, v___x_670_);
v___x_672_ = l_Nat_testBit(v_x_654_, v___x_671_);
if (v___x_672_ == 0)
{
lean_dec(v___x_671_);
goto v___jp_656_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = l_Nat_testBit(v_y_655_, v___x_671_);
lean_dec(v___x_671_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v_u_675_; uint8_t v___x_676_; 
v___x_674_ = l_BitVec_neg(v_m_653_, v_x_654_);
v_u_675_ = lean_nat_mod(v___x_674_, v_y_655_);
lean_dec(v___x_674_);
v___x_676_ = lean_nat_dec_eq(v_u_675_, v___x_668_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
v___x_677_ = l_BitVec_sub(v_m_653_, v_y_655_, v_u_675_);
lean_dec(v_u_675_);
return v___x_677_;
}
else
{
return v_u_675_;
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_678_ = l_BitVec_neg(v_m_653_, v_x_654_);
v___x_679_ = l_BitVec_neg(v_m_653_, v_y_655_);
v___x_680_ = lean_nat_mod(v___x_678_, v___x_679_);
lean_dec(v___x_679_);
lean_dec(v___x_678_);
v___x_681_ = l_BitVec_neg(v_m_653_, v___x_680_);
lean_dec(v___x_680_);
return v___x_681_;
}
}
}
v___jp_656_:
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_nat_dec_lt(v___x_657_, v_m_653_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
v___x_659_ = lean_nat_mod(v_x_654_, v_y_655_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_nat_sub(v_m_653_, v___x_660_);
v___x_662_ = l_Nat_testBit(v_y_655_, v___x_661_);
lean_dec(v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
v___x_663_ = lean_nat_mod(v_x_654_, v_y_655_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v_u_665_; uint8_t v___x_666_; 
v___x_664_ = l_BitVec_neg(v_m_653_, v_y_655_);
v_u_665_ = lean_nat_mod(v_x_654_, v___x_664_);
lean_dec(v___x_664_);
v___x_666_ = lean_nat_dec_eq(v_u_665_, v___x_657_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
v___x_667_ = l_BitVec_add(v_m_653_, v_u_665_, v_y_655_);
lean_dec(v_u_665_);
return v___x_667_;
}
else
{
return v_u_665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smod___boxed(lean_object* v_m_682_, lean_object* v_x_683_, lean_object* v_y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_BitVec_smod(v_m_682_, v_x_683_, v_y_684_);
lean_dec(v_y_684_);
lean_dec(v_x_683_);
lean_dec(v_m_682_);
return v_res_685_;
}
}
static lean_object* _init_l_BitVec_ofBool___closed__0(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = l_BitVec_ofNat(v___x_687_, v___x_686_);
return v___x_688_;
}
}
static lean_object* _init_l_BitVec_ofBool___closed__1(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = l_BitVec_ofNat(v___x_689_, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBool(uint8_t v_b_691_){
_start:
{
if (v_b_691_ == 0)
{
lean_object* v___x_692_; 
v___x_692_ = lean_obj_once(&l_BitVec_ofBool___closed__0, &l_BitVec_ofBool___closed__0_once, _init_l_BitVec_ofBool___closed__0);
return v___x_692_;
}
else
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_once(&l_BitVec_ofBool___closed__1, &l_BitVec_ofBool___closed__1_once, _init_l_BitVec_ofBool___closed__1);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBool___boxed(lean_object* v_b_694_){
_start:
{
uint8_t v_b_boxed_695_; lean_object* v_res_696_; 
v_b_boxed_695_ = lean_unbox(v_b_694_);
v_res_696_ = l_BitVec_ofBool(v_b_boxed_695_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_BitVec_fill(lean_object* v_w_697_, uint8_t v_b_698_){
_start:
{
if (v_b_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = l_BitVec_ofNat(v_w_697_, v___x_699_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = l_BitVec_ofNat(v_w_697_, v___x_701_);
v___x_703_ = l_BitVec_neg(v_w_697_, v___x_702_);
lean_dec(v___x_702_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_fill___boxed(lean_object* v_w_704_, lean_object* v_b_705_){
_start:
{
uint8_t v_b_boxed_706_; lean_object* v_res_707_; 
v_b_boxed_706_ = lean_unbox(v_b_705_);
v_res_707_ = l_BitVec_fill(v_w_704_, v_b_boxed_706_);
lean_dec(v_w_704_);
return v_res_707_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ult___redArg(lean_object* v_x_708_, lean_object* v_y_709_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = lean_nat_dec_lt(v_x_708_, v_y_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult___redArg___boxed(lean_object* v_x_711_, lean_object* v_y_712_){
_start:
{
uint8_t v_res_713_; lean_object* v_r_714_; 
v_res_713_ = l_BitVec_ult___redArg(v_x_711_, v_y_712_);
lean_dec(v_y_712_);
lean_dec(v_x_711_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ult(lean_object* v_n_715_, lean_object* v_x_716_, lean_object* v_y_717_){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = lean_nat_dec_lt(v_x_716_, v_y_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ult___boxed(lean_object* v_n_719_, lean_object* v_x_720_, lean_object* v_y_721_){
_start:
{
uint8_t v_res_722_; lean_object* v_r_723_; 
v_res_722_ = l_BitVec_ult(v_n_719_, v_x_720_, v_y_721_);
lean_dec(v_y_721_);
lean_dec(v_x_720_);
lean_dec(v_n_719_);
v_r_723_ = lean_box(v_res_722_);
return v_r_723_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ule___redArg(lean_object* v_x_724_, lean_object* v_y_725_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = lean_nat_dec_le(v_x_724_, v_y_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule___redArg___boxed(lean_object* v_x_727_, lean_object* v_y_728_){
_start:
{
uint8_t v_res_729_; lean_object* v_r_730_; 
v_res_729_ = l_BitVec_ule___redArg(v_x_727_, v_y_728_);
lean_dec(v_y_728_);
lean_dec(v_x_727_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ule(lean_object* v_n_731_, lean_object* v_x_732_, lean_object* v_y_733_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = lean_nat_dec_le(v_x_732_, v_y_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ule___boxed(lean_object* v_n_735_, lean_object* v_x_736_, lean_object* v_y_737_){
_start:
{
uint8_t v_res_738_; lean_object* v_r_739_; 
v_res_738_ = l_BitVec_ule(v_n_735_, v_x_736_, v_y_737_);
lean_dec(v_y_737_);
lean_dec(v_x_736_);
lean_dec(v_n_735_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
LEAN_EXPORT uint8_t l_BitVec_slt(lean_object* v_n_740_, lean_object* v_x_741_, lean_object* v_y_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_743_ = l_BitVec_toInt(v_n_740_, v_x_741_);
v___x_744_ = l_BitVec_toInt(v_n_740_, v_y_742_);
v___x_745_ = lean_int_dec_lt(v___x_743_, v___x_744_);
lean_dec(v___x_744_);
lean_dec(v___x_743_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_BitVec_slt___boxed(lean_object* v_n_746_, lean_object* v_x_747_, lean_object* v_y_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l_BitVec_slt(v_n_746_, v_x_747_, v_y_748_);
lean_dec(v_n_746_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT uint8_t l_BitVec_sle(lean_object* v_n_751_, lean_object* v_x_752_, lean_object* v_y_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_754_ = l_BitVec_toInt(v_n_751_, v_x_752_);
v___x_755_ = l_BitVec_toInt(v_n_751_, v_y_753_);
v___x_756_ = lean_int_dec_le(v___x_754_, v___x_755_);
lean_dec(v___x_755_);
lean_dec(v___x_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sle___boxed(lean_object* v_n_757_, lean_object* v_x_758_, lean_object* v_y_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_BitVec_sle(v_n_757_, v_x_758_, v_y_759_);
lean_dec(v_n_757_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___redArg(lean_object* v_x_762_){
_start:
{
lean_inc(v_x_762_);
return v_x_762_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___redArg___boxed(lean_object* v_x_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_BitVec_cast___redArg(v_x_763_);
lean_dec(v_x_763_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast(lean_object* v_n_765_, lean_object* v_m_766_, lean_object* v_eq_767_, lean_object* v_x_768_){
_start:
{
lean_inc(v_x_768_);
return v_x_768_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cast___boxed(lean_object* v_n_769_, lean_object* v_m_770_, lean_object* v_eq_771_, lean_object* v_x_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_BitVec_cast(v_n_769_, v_m_770_, v_eq_771_, v_x_772_);
lean_dec(v_x_772_);
lean_dec(v_m_770_);
lean_dec(v_n_769_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___redArg(lean_object* v_start_774_, lean_object* v_len_775_, lean_object* v_x_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_nat_shiftr(v_x_776_, v_start_774_);
v___x_778_ = l_BitVec_ofNat(v_len_775_, v___x_777_);
lean_dec(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___redArg___boxed(lean_object* v_start_779_, lean_object* v_len_780_, lean_object* v_x_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_BitVec_extractLsb_x27___redArg(v_start_779_, v_len_780_, v_x_781_);
lean_dec(v_x_781_);
lean_dec(v_len_780_);
lean_dec(v_start_779_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27(lean_object* v_n_783_, lean_object* v_start_784_, lean_object* v_len_785_, lean_object* v_x_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_BitVec_extractLsb_x27___redArg(v_start_784_, v_len_785_, v_x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb_x27___boxed(lean_object* v_n_788_, lean_object* v_start_789_, lean_object* v_len_790_, lean_object* v_x_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_BitVec_extractLsb_x27(v_n_788_, v_start_789_, v_len_790_, v_x_791_);
lean_dec(v_x_791_);
lean_dec(v_len_790_);
lean_dec(v_start_789_);
lean_dec(v_n_788_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___redArg(lean_object* v_hi_793_, lean_object* v_lo_794_, lean_object* v_x_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_796_ = lean_nat_sub(v_hi_793_, v_lo_794_);
v___x_797_ = lean_unsigned_to_nat(1u);
v___x_798_ = lean_nat_add(v___x_796_, v___x_797_);
lean_dec(v___x_796_);
v___x_799_ = l_BitVec_extractLsb_x27___redArg(v_lo_794_, v___x_798_, v_x_795_);
lean_dec(v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___redArg___boxed(lean_object* v_hi_800_, lean_object* v_lo_801_, lean_object* v_x_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_BitVec_extractLsb___redArg(v_hi_800_, v_lo_801_, v_x_802_);
lean_dec(v_x_802_);
lean_dec(v_lo_801_);
lean_dec(v_hi_800_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb(lean_object* v_n_804_, lean_object* v_hi_805_, lean_object* v_lo_806_, lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_BitVec_extractLsb___redArg(v_hi_805_, v_lo_806_, v_x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractLsb___boxed(lean_object* v_n_809_, lean_object* v_hi_810_, lean_object* v_lo_811_, lean_object* v_x_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_BitVec_extractLsb(v_n_809_, v_hi_810_, v_lo_811_, v_x_812_);
lean_dec(v_x_812_);
lean_dec(v_lo_811_);
lean_dec(v_hi_810_);
lean_dec(v_n_809_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___redArg(lean_object* v_x_814_){
_start:
{
lean_inc(v_x_814_);
return v_x_814_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___redArg___boxed(lean_object* v_x_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_BitVec_setWidth_x27___redArg(v_x_815_);
lean_dec(v_x_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27(lean_object* v_n_817_, lean_object* v_w_818_, lean_object* v_le_819_, lean_object* v_x_820_){
_start:
{
lean_inc(v_x_820_);
return v_x_820_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth_x27___boxed(lean_object* v_n_821_, lean_object* v_w_822_, lean_object* v_le_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_BitVec_setWidth_x27(v_n_821_, v_w_822_, v_le_823_, v_x_824_);
lean_dec(v_x_824_);
lean_dec(v_w_822_);
lean_dec(v_n_821_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___redArg(lean_object* v_msbs_826_, lean_object* v_m_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = lean_nat_shiftl(v_msbs_826_, v_m_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___redArg___boxed(lean_object* v_msbs_829_, lean_object* v_m_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_BitVec_shiftLeftZeroExtend___redArg(v_msbs_829_, v_m_830_);
lean_dec(v_m_830_);
lean_dec(v_msbs_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend(lean_object* v_w_832_, lean_object* v_msbs_833_, lean_object* v_m_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = lean_nat_shiftl(v_msbs_833_, v_m_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftZeroExtend___boxed(lean_object* v_w_836_, lean_object* v_msbs_837_, lean_object* v_m_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_BitVec_shiftLeftZeroExtend(v_w_836_, v_msbs_837_, v_m_838_);
lean_dec(v_m_838_);
lean_dec(v_msbs_837_);
lean_dec(v_w_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth(lean_object* v_w_840_, lean_object* v_v_841_, lean_object* v_x_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = lean_nat_dec_le(v_w_840_, v_v_841_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
v___x_844_ = l_BitVec_ofNat(v_v_841_, v_x_842_);
return v___x_844_;
}
else
{
lean_inc(v_x_842_);
return v_x_842_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_setWidth___boxed(lean_object* v_w_845_, lean_object* v_v_846_, lean_object* v_x_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_BitVec_setWidth(v_w_845_, v_v_846_, v_x_847_);
lean_dec(v_x_847_);
lean_dec(v_v_846_);
lean_dec(v_w_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zeroExtend(lean_object* v_w_849_, lean_object* v_v_850_, lean_object* v_x_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_BitVec_setWidth(v_w_849_, v_v_850_, v_x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_BitVec_zeroExtend___boxed(lean_object* v_w_853_, lean_object* v_v_854_, lean_object* v_x_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_BitVec_zeroExtend(v_w_853_, v_v_854_, v_x_855_);
lean_dec(v_x_855_);
lean_dec(v_v_854_);
lean_dec(v_w_853_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_BitVec_truncate(lean_object* v_w_857_, lean_object* v_v_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_BitVec_setWidth(v_w_857_, v_v_858_, v_x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_BitVec_truncate___boxed(lean_object* v_w_861_, lean_object* v_v_862_, lean_object* v_x_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_BitVec_truncate(v_w_861_, v_v_862_, v_x_863_);
lean_dec(v_x_863_);
lean_dec(v_v_862_);
lean_dec(v_w_861_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_BitVec_signExtend(lean_object* v_w_865_, lean_object* v_v_866_, lean_object* v_x_867_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = l_BitVec_toInt(v_w_865_, v_x_867_);
v___x_869_ = l_BitVec_ofInt(v_v_866_, v___x_868_);
lean_dec(v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_BitVec_signExtend___boxed(lean_object* v_w_870_, lean_object* v_v_871_, lean_object* v_x_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_BitVec_signExtend(v_w_870_, v_v_871_, v_x_872_);
lean_dec(v_v_871_);
lean_dec(v_w_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___redArg(lean_object* v_x_874_, lean_object* v_y_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = lean_nat_land(v_x_874_, v_y_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___redArg___boxed(lean_object* v_x_877_, lean_object* v_y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_BitVec_and___redArg(v_x_877_, v_y_878_);
lean_dec(v_y_878_);
lean_dec(v_x_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and(lean_object* v_n_880_, lean_object* v_x_881_, lean_object* v_y_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = lean_nat_land(v_x_881_, v_y_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_BitVec_and___boxed(lean_object* v_n_884_, lean_object* v_x_885_, lean_object* v_y_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_BitVec_and(v_n_884_, v_x_885_, v_y_886_);
lean_dec(v_y_886_);
lean_dec(v_x_885_);
lean_dec(v_n_884_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instAndOp(lean_object* v_w_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = lean_alloc_closure((void*)(l_BitVec_and___boxed), 3, 1);
lean_closure_set(v___x_889_, 0, v_w_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___redArg(lean_object* v_x_890_, lean_object* v_y_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_nat_lor(v_x_890_, v_y_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___redArg___boxed(lean_object* v_x_893_, lean_object* v_y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_BitVec_or___redArg(v_x_893_, v_y_894_);
lean_dec(v_y_894_);
lean_dec(v_x_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or(lean_object* v_n_896_, lean_object* v_x_897_, lean_object* v_y_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = lean_nat_lor(v_x_897_, v_y_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_BitVec_or___boxed(lean_object* v_n_900_, lean_object* v_x_901_, lean_object* v_y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_BitVec_or(v_n_900_, v_x_901_, v_y_902_);
lean_dec(v_y_902_);
lean_dec(v_x_901_);
lean_dec(v_n_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instOrOp(lean_object* v_w_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = lean_alloc_closure((void*)(l_BitVec_or___boxed), 3, 1);
lean_closure_set(v___x_905_, 0, v_w_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___redArg(lean_object* v_x_906_, lean_object* v_y_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_nat_lxor(v_x_906_, v_y_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___redArg___boxed(lean_object* v_x_909_, lean_object* v_y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_BitVec_xor___redArg(v_x_909_, v_y_910_);
lean_dec(v_y_910_);
lean_dec(v_x_909_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor(lean_object* v_n_912_, lean_object* v_x_913_, lean_object* v_y_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lean_nat_lxor(v_x_913_, v_y_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_BitVec_xor___boxed(lean_object* v_n_916_, lean_object* v_x_917_, lean_object* v_y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_BitVec_xor(v_n_916_, v_x_917_, v_y_918_);
lean_dec(v_y_918_);
lean_dec(v_x_917_);
lean_dec(v_n_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instXorOp(lean_object* v_w_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = lean_alloc_closure((void*)(l_BitVec_xor___boxed), 3, 1);
lean_closure_set(v___x_921_, 0, v_w_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_BitVec_not(lean_object* v_n_922_, lean_object* v_x_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = l_BitVec_allOnes(v_n_922_);
v___x_925_ = lean_nat_lxor(v___x_924_, v_x_923_);
lean_dec(v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_BitVec_not___boxed(lean_object* v_n_926_, lean_object* v_x_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_BitVec_not(v_n_926_, v_x_927_);
lean_dec(v_x_927_);
lean_dec(v_n_926_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instComplement(lean_object* v_w_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = lean_alloc_closure((void*)(l_BitVec_not___boxed), 2, 1);
lean_closure_set(v___x_930_, 0, v_w_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeft(lean_object* v_n_931_, lean_object* v_x_932_, lean_object* v_s_933_){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_nat_shiftl(v_x_932_, v_s_933_);
v___x_935_ = l_BitVec_ofNat(v_n_931_, v___x_934_);
lean_dec(v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeft___boxed(lean_object* v_n_936_, lean_object* v_x_937_, lean_object* v_s_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_BitVec_shiftLeft(v_n_936_, v_x_937_, v_s_938_);
lean_dec(v_s_938_);
lean_dec(v_x_937_);
lean_dec(v_n_936_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeftNat(lean_object* v_w_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_closure((void*)(l_BitVec_shiftLeft___boxed), 3, 1);
lean_closure_set(v___x_941_, 0, v_w_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___redArg(lean_object* v_x_942_, lean_object* v_s_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = lean_nat_shiftr(v_x_942_, v_s_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___redArg___boxed(lean_object* v_x_945_, lean_object* v_s_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_BitVec_ushiftRight___redArg(v_x_945_, v_s_946_);
lean_dec(v_s_946_);
lean_dec(v_x_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight(lean_object* v_n_948_, lean_object* v_x_949_, lean_object* v_s_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = lean_nat_shiftr(v_x_949_, v_s_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRight___boxed(lean_object* v_n_952_, lean_object* v_x_953_, lean_object* v_s_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_BitVec_ushiftRight(v_n_952_, v_x_953_, v_s_954_);
lean_dec(v_s_954_);
lean_dec(v_x_953_);
lean_dec(v_n_952_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRightNat(lean_object* v_w_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_closure((void*)(l_BitVec_ushiftRight___boxed), 3, 1);
lean_closure_set(v___x_957_, 0, v_w_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight(lean_object* v_n_958_, lean_object* v_x_959_, lean_object* v_s_960_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = l_BitVec_toInt(v_n_958_, v_x_959_);
v___x_962_ = l_Int_shiftRight(v___x_961_, v_s_960_);
lean_dec(v___x_961_);
v___x_963_ = l_BitVec_ofInt(v_n_958_, v___x_962_);
lean_dec(v___x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight___boxed(lean_object* v_n_964_, lean_object* v_x_965_, lean_object* v_s_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_BitVec_sshiftRight(v_n_964_, v_x_965_, v_s_966_);
lean_dec(v_s_966_);
lean_dec(v_n_964_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg___lam__0(lean_object* v_m_968_, lean_object* v_x_969_, lean_object* v_y_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_BitVec_shiftLeft(v_m_968_, v_x_969_, v_y_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg___lam__0___boxed(lean_object* v_m_972_, lean_object* v_x_973_, lean_object* v_y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_BitVec_instHShiftLeft___redArg___lam__0(v_m_972_, v_x_973_, v_y_974_);
lean_dec(v_y_974_);
lean_dec(v_x_973_);
lean_dec(v_m_972_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___redArg(lean_object* v_m_976_){
_start:
{
lean_object* v___f_977_; 
v___f_977_ = lean_alloc_closure((void*)(l_BitVec_instHShiftLeft___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_977_, 0, v_m_976_);
return v___f_977_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft(lean_object* v_m_978_, lean_object* v_n_979_){
_start:
{
lean_object* v___f_980_; 
v___f_980_ = lean_alloc_closure((void*)(l_BitVec_instHShiftLeft___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_980_, 0, v_m_978_);
return v___f_980_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftLeft___boxed(lean_object* v_m_981_, lean_object* v_n_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_BitVec_instHShiftLeft(v_m_981_, v_n_982_);
lean_dec(v_n_982_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___redArg(){
_start:
{
lean_object* v___f_986_; 
v___f_986_ = ((lean_object*)(l_BitVec_instHShiftRight___redArg___closed__0));
return v___f_986_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___redArg___boxed(lean_object* v___dummy_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_BitVec_instHShiftRight___redArg();
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight(lean_object* v_m_989_, lean_object* v_n_990_){
_start:
{
lean_object* v___f_991_; 
v___f_991_ = ((lean_object*)(l_BitVec_instHShiftRight___redArg___closed__0));
return v___f_991_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHShiftRight___boxed(lean_object* v_m_992_, lean_object* v_n_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_BitVec_instHShiftRight(v_m_992_, v_n_993_);
lean_dec(v_n_993_);
lean_dec(v_m_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg(lean_object* v_n_995_, lean_object* v_a_996_, lean_object* v_s_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_BitVec_sshiftRight(v_n_995_, v_a_996_, v_s_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___redArg___boxed(lean_object* v_n_999_, lean_object* v_a_1000_, lean_object* v_s_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_BitVec_sshiftRight_x27___redArg(v_n_999_, v_a_1000_, v_s_1001_);
lean_dec(v_s_1001_);
lean_dec(v_n_999_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27(lean_object* v_n_1003_, lean_object* v_m_1004_, lean_object* v_a_1005_, lean_object* v_s_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_BitVec_sshiftRight(v_n_1003_, v_a_1005_, v_s_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRight_x27___boxed(lean_object* v_n_1008_, lean_object* v_m_1009_, lean_object* v_a_1010_, lean_object* v_s_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_BitVec_sshiftRight_x27(v_n_1008_, v_m_1009_, v_a_1010_, v_s_1011_);
lean_dec(v_s_1011_);
lean_dec(v_m_1009_);
lean_dec(v_n_1008_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux(lean_object* v_w_1013_, lean_object* v_x_1014_, lean_object* v_n_1015_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1016_ = l_BitVec_shiftLeft(v_w_1013_, v_x_1014_, v_n_1015_);
v___x_1017_ = lean_nat_sub(v_w_1013_, v_n_1015_);
v___x_1018_ = lean_nat_shiftr(v_x_1014_, v___x_1017_);
lean_dec(v___x_1017_);
v___x_1019_ = lean_nat_lor(v___x_1016_, v___x_1018_);
lean_dec(v___x_1018_);
lean_dec(v___x_1016_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeftAux___boxed(lean_object* v_w_1020_, lean_object* v_x_1021_, lean_object* v_n_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_BitVec_rotateLeftAux(v_w_1020_, v_x_1021_, v_n_1022_);
lean_dec(v_n_1022_);
lean_dec(v_x_1021_);
lean_dec(v_w_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft(lean_object* v_w_1024_, lean_object* v_x_1025_, lean_object* v_n_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_nat_mod(v_n_1026_, v_w_1024_);
v___x_1028_ = l_BitVec_rotateLeftAux(v_w_1024_, v_x_1025_, v___x_1027_);
lean_dec(v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateLeft___boxed(lean_object* v_w_1029_, lean_object* v_x_1030_, lean_object* v_n_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_BitVec_rotateLeft(v_w_1029_, v_x_1030_, v_n_1031_);
lean_dec(v_n_1031_);
lean_dec(v_x_1030_);
lean_dec(v_w_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux(lean_object* v_w_1033_, lean_object* v_x_1034_, lean_object* v_n_1035_){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1036_ = lean_nat_shiftr(v_x_1034_, v_n_1035_);
v___x_1037_ = lean_nat_sub(v_w_1033_, v_n_1035_);
v___x_1038_ = l_BitVec_shiftLeft(v_w_1033_, v_x_1034_, v___x_1037_);
lean_dec(v___x_1037_);
v___x_1039_ = lean_nat_lor(v___x_1036_, v___x_1038_);
lean_dec(v___x_1038_);
lean_dec(v___x_1036_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRightAux___boxed(lean_object* v_w_1040_, lean_object* v_x_1041_, lean_object* v_n_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_BitVec_rotateRightAux(v_w_1040_, v_x_1041_, v_n_1042_);
lean_dec(v_n_1042_);
lean_dec(v_x_1041_);
lean_dec(v_w_1040_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight(lean_object* v_w_1044_, lean_object* v_x_1045_, lean_object* v_n_1046_){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_nat_mod(v_n_1046_, v_w_1044_);
v___x_1048_ = l_BitVec_rotateRightAux(v_w_1044_, v_x_1045_, v___x_1047_);
lean_dec(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_BitVec_rotateRight___boxed(lean_object* v_w_1049_, lean_object* v_x_1050_, lean_object* v_n_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_BitVec_rotateRight(v_w_1049_, v_x_1050_, v_n_1051_);
lean_dec(v_n_1051_);
lean_dec(v_x_1050_);
lean_dec(v_w_1049_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___redArg(lean_object* v_m_1053_, lean_object* v_msbs_1054_, lean_object* v_lsbs_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_nat_shiftl(v_msbs_1054_, v_m_1053_);
v___x_1057_ = lean_nat_lor(v___x_1056_, v_lsbs_1055_);
lean_dec(v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___redArg___boxed(lean_object* v_m_1058_, lean_object* v_msbs_1059_, lean_object* v_lsbs_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_BitVec_append___redArg(v_m_1058_, v_msbs_1059_, v_lsbs_1060_);
lean_dec(v_lsbs_1060_);
lean_dec(v_msbs_1059_);
lean_dec(v_m_1058_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append(lean_object* v_n_1062_, lean_object* v_m_1063_, lean_object* v_msbs_1064_, lean_object* v_lsbs_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_BitVec_append___redArg(v_m_1063_, v_msbs_1064_, v_lsbs_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_BitVec_append___boxed(lean_object* v_n_1067_, lean_object* v_m_1068_, lean_object* v_msbs_1069_, lean_object* v_lsbs_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_BitVec_append(v_n_1067_, v_m_1068_, v_msbs_1069_, v_lsbs_1070_);
lean_dec(v_lsbs_1070_);
lean_dec(v_msbs_1069_);
lean_dec(v_m_1068_);
lean_dec(v_n_1067_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHAppendHAddNat(lean_object* v_w_1072_, lean_object* v_v_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_alloc_closure((void*)(l_BitVec_append___boxed), 4, 2);
lean_closure_set(v___x_1074_, 0, v_w_1072_);
lean_closure_set(v___x_1074_, 1, v_v_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate(lean_object* v_w_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
lean_object* v_zero_1078_; uint8_t v_isZero_1079_; 
v_zero_1078_ = lean_unsigned_to_nat(0u);
v_isZero_1079_ = lean_nat_dec_eq(v_x_1076_, v_zero_1078_);
if (v_isZero_1079_ == 1)
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1080_;
}
else
{
lean_object* v_one_1081_; lean_object* v_n_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_one_1081_ = lean_unsigned_to_nat(1u);
v_n_1082_ = lean_nat_sub(v_x_1076_, v_one_1081_);
v___x_1083_ = lean_nat_mul(v_w_1075_, v_n_1082_);
v___x_1084_ = l_BitVec_replicate(v_w_1075_, v_n_1082_, v_x_1077_);
lean_dec(v_n_1082_);
v___x_1085_ = l_BitVec_append___redArg(v___x_1083_, v_x_1077_, v___x_1084_);
lean_dec(v___x_1084_);
lean_dec(v___x_1083_);
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_replicate___boxed(lean_object* v_w_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_BitVec_replicate(v_w_1086_, v_x_1087_, v_x_1088_);
lean_dec(v_x_1088_);
lean_dec(v_x_1087_);
lean_dec(v_w_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___redArg(lean_object* v_msbs_1090_, uint8_t v_lsb_1091_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = l_BitVec_ofBool(v_lsb_1091_);
v___x_1094_ = l_BitVec_append___redArg(v___x_1092_, v_msbs_1090_, v___x_1093_);
lean_dec(v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___redArg___boxed(lean_object* v_msbs_1095_, lean_object* v_lsb_1096_){
_start:
{
uint8_t v_lsb_boxed_1097_; lean_object* v_res_1098_; 
v_lsb_boxed_1097_ = lean_unbox(v_lsb_1096_);
v_res_1098_ = l_BitVec_concat___redArg(v_msbs_1095_, v_lsb_boxed_1097_);
lean_dec(v_msbs_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat(lean_object* v_n_1099_, lean_object* v_msbs_1100_, uint8_t v_lsb_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_BitVec_concat___redArg(v_msbs_1100_, v_lsb_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_BitVec_concat___boxed(lean_object* v_n_1103_, lean_object* v_msbs_1104_, lean_object* v_lsb_1105_){
_start:
{
uint8_t v_lsb_boxed_1106_; lean_object* v_res_1107_; 
v_lsb_boxed_1106_ = lean_unbox(v_lsb_1105_);
v_res_1107_ = l_BitVec_concat(v_n_1103_, v_msbs_1104_, v_lsb_boxed_1106_);
lean_dec(v_msbs_1104_);
lean_dec(v_n_1103_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat(lean_object* v_n_1108_, lean_object* v_x_1109_, uint8_t v_b_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v_n_1108_, v___x_1111_);
v___x_1113_ = l_BitVec_concat___redArg(v_x_1109_, v_b_1110_);
v___x_1114_ = l_BitVec_setWidth(v___x_1112_, v_n_1108_, v___x_1113_);
lean_dec(v___x_1113_);
lean_dec(v___x_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftConcat___boxed(lean_object* v_n_1115_, lean_object* v_x_1116_, lean_object* v_b_1117_){
_start:
{
uint8_t v_b_boxed_1118_; lean_object* v_res_1119_; 
v_b_boxed_1118_ = lean_unbox(v_b_1117_);
v_res_1119_ = l_BitVec_shiftConcat(v_n_1115_, v_x_1116_, v_b_boxed_1118_);
lean_dec(v_x_1116_);
lean_dec(v_n_1115_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cons(lean_object* v_n_1120_, uint8_t v_msb_1121_, lean_object* v_lsbs_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = l_BitVec_ofBool(v_msb_1121_);
v___x_1124_ = l_BitVec_append___redArg(v_n_1120_, v___x_1123_, v_lsbs_1122_);
lean_dec(v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cons___boxed(lean_object* v_n_1125_, lean_object* v_msb_1126_, lean_object* v_lsbs_1127_){
_start:
{
uint8_t v_msb_boxed_1128_; lean_object* v_res_1129_; 
v_msb_boxed_1128_ = lean_unbox(v_msb_1126_);
v_res_1129_ = l_BitVec_cons(v_n_1125_, v_msb_boxed_1128_, v_lsbs_1127_);
lean_dec(v_lsbs_1127_);
lean_dec(v_n_1125_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow(lean_object* v_w_1130_, lean_object* v_i_1131_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = l_BitVec_ofNat(v_w_1130_, v___x_1132_);
v___x_1134_ = l_BitVec_shiftLeft(v_w_1130_, v___x_1133_, v_i_1131_);
lean_dec(v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_BitVec_twoPow___boxed(lean_object* v_w_1135_, lean_object* v_i_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_BitVec_twoPow(v_w_1135_, v_i_1136_);
lean_dec(v_i_1136_);
lean_dec(v_w_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMin(lean_object* v_w_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = lean_nat_sub(v_w_1138_, v___x_1139_);
v___x_1141_ = l_BitVec_twoPow(v_w_1138_, v___x_1140_);
lean_dec(v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMin___boxed(lean_object* v_w_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_BitVec_intMin(v_w_1142_);
lean_dec(v_w_1142_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMax(lean_object* v_w_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = lean_nat_sub(v_w_1144_, v___x_1145_);
v___x_1147_ = l_BitVec_twoPow(v_w_1144_, v___x_1146_);
lean_dec(v___x_1146_);
v___x_1148_ = l_BitVec_ofNat(v_w_1144_, v___x_1145_);
v___x_1149_ = l_BitVec_sub(v_w_1144_, v___x_1147_, v___x_1148_);
lean_dec(v___x_1148_);
lean_dec(v___x_1147_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_BitVec_intMax___boxed(lean_object* v_w_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_BitVec_intMax(v_w_1150_);
lean_dec(v_w_1150_);
return v_res_1151_;
}
}
LEAN_EXPORT uint64_t l_BitVec_hash(lean_object* v_n_1152_, lean_object* v_bv_1153_){
_start:
{
lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = lean_unsigned_to_nat(64u);
v___x_1155_ = lean_nat_dec_le(v_n_1152_, v___x_1154_);
if (v___x_1155_ == 0)
{
uint64_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint64_t v___x_1160_; uint64_t v___x_1161_; 
v___x_1156_ = lean_uint64_of_nat(v_bv_1153_);
v___x_1157_ = lean_nat_sub(v_n_1152_, v___x_1154_);
v___x_1158_ = lean_nat_shiftr(v_bv_1153_, v___x_1154_);
v___x_1159_ = l_BitVec_setWidth(v_n_1152_, v___x_1157_, v___x_1158_);
lean_dec(v___x_1158_);
v___x_1160_ = l_BitVec_hash(v___x_1157_, v___x_1159_);
lean_dec(v___x_1159_);
lean_dec(v___x_1157_);
v___x_1161_ = lean_uint64_mix_hash(v___x_1156_, v___x_1160_);
return v___x_1161_;
}
else
{
uint64_t v___x_1162_; 
v___x_1162_ = lean_uint64_of_nat(v_bv_1153_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_hash___boxed(lean_object* v_n_1163_, lean_object* v_bv_1164_){
_start:
{
uint64_t v_res_1165_; lean_object* v_r_1166_; 
v_res_1165_ = l_BitVec_hash(v_n_1163_, v_bv_1164_);
lean_dec(v_bv_1164_);
lean_dec(v_n_1163_);
v_r_1166_ = lean_box_uint64(v_res_1165_);
return v_r_1166_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instHashable(lean_object* v_n_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_closure((void*)(l_BitVec_hash___boxed), 2, 1);
lean_closure_set(v___x_1168_, 0, v_n_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE(lean_object* v_x_1169_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1170_;
}
else
{
lean_object* v_head_1171_; lean_object* v_tail_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; 
v_head_1171_ = lean_ctor_get(v_x_1169_, 0);
v_tail_1172_ = lean_ctor_get(v_x_1169_, 1);
v___x_1173_ = l_List_lengthTR___redArg(v_tail_1172_);
v___x_1174_ = l_BitVec_ofBoolListBE(v_tail_1172_);
v___x_1175_ = lean_unbox(v_head_1171_);
v___x_1176_ = l_BitVec_cons(v___x_1173_, v___x_1175_, v___x_1174_);
lean_dec(v___x_1174_);
lean_dec(v___x_1173_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListBE___boxed(lean_object* v_x_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_BitVec_ofBoolListBE(v_x_1177_);
lean_dec(v_x_1177_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE(lean_object* v_x_1179_){
_start:
{
if (lean_obj_tag(v_x_1179_) == 0)
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_obj_once(&l_BitVec_nil___closed__0, &l_BitVec_nil___closed__0_once, _init_l_BitVec_nil___closed__0);
return v___x_1180_;
}
else
{
lean_object* v_head_1181_; lean_object* v_tail_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; lean_object* v___x_1185_; 
v_head_1181_ = lean_ctor_get(v_x_1179_, 0);
v_tail_1182_ = lean_ctor_get(v_x_1179_, 1);
v___x_1183_ = l_BitVec_ofBoolListLE(v_tail_1182_);
v___x_1184_ = lean_unbox(v_head_1181_);
v___x_1185_ = l_BitVec_concat___redArg(v___x_1183_, v___x_1184_);
lean_dec(v___x_1183_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ofBoolListLE___boxed(lean_object* v_x_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_BitVec_ofBoolListLE(v_x_1186_);
lean_dec(v_x_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uaddOverflow(lean_object* v_w_1188_, lean_object* v_x_1189_, lean_object* v_y_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1191_ = lean_unsigned_to_nat(2u);
v___x_1192_ = lean_nat_pow(v___x_1191_, v_w_1188_);
v___x_1193_ = lean_nat_add(v_x_1189_, v_y_1190_);
v___x_1194_ = lean_nat_dec_le(v___x_1192_, v___x_1193_);
lean_dec(v___x_1193_);
lean_dec(v___x_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_BitVec_uaddOverflow___boxed(lean_object* v_w_1195_, lean_object* v_x_1196_, lean_object* v_y_1197_){
_start:
{
uint8_t v_res_1198_; lean_object* v_r_1199_; 
v_res_1198_ = l_BitVec_uaddOverflow(v_w_1195_, v_x_1196_, v_y_1197_);
lean_dec(v_y_1197_);
lean_dec(v_x_1196_);
lean_dec(v_w_1195_);
v_r_1199_ = lean_box(v_res_1198_);
return v_r_1199_;
}
}
static lean_object* _init_l_BitVec_saddOverflow___closed__0(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_unsigned_to_nat(2u);
v___x_1201_ = lean_nat_to_int(v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT uint8_t l_BitVec_saddOverflow(lean_object* v_w_1202_, lean_object* v_x_1203_, lean_object* v_y_1204_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1205_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_nat_sub(v_w_1202_, v___x_1206_);
v___x_1208_ = l_Int_pow(v___x_1205_, v___x_1207_);
lean_dec(v___x_1207_);
v___x_1209_ = l_BitVec_toInt(v_w_1202_, v_x_1203_);
v___x_1210_ = l_BitVec_toInt(v_w_1202_, v_y_1204_);
v___x_1211_ = lean_int_add(v___x_1209_, v___x_1210_);
lean_dec(v___x_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_int_dec_le(v___x_1208_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_int_neg(v___x_1208_);
lean_dec(v___x_1208_);
v___x_1214_ = lean_int_dec_lt(v___x_1211_, v___x_1213_);
lean_dec(v___x_1213_);
lean_dec(v___x_1211_);
return v___x_1214_;
}
else
{
lean_dec(v___x_1211_);
lean_dec(v___x_1208_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_saddOverflow___boxed(lean_object* v_w_1215_, lean_object* v_x_1216_, lean_object* v_y_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = l_BitVec_saddOverflow(v_w_1215_, v_x_1216_, v_y_1217_);
lean_dec(v_w_1215_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
LEAN_EXPORT uint8_t l_BitVec_usubOverflow___redArg(lean_object* v_x_1220_, lean_object* v_y_1221_){
_start:
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_nat_dec_lt(v_x_1220_, v_y_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___redArg___boxed(lean_object* v_x_1223_, lean_object* v_y_1224_){
_start:
{
uint8_t v_res_1225_; lean_object* v_r_1226_; 
v_res_1225_ = l_BitVec_usubOverflow___redArg(v_x_1223_, v_y_1224_);
lean_dec(v_y_1224_);
lean_dec(v_x_1223_);
v_r_1226_ = lean_box(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT uint8_t l_BitVec_usubOverflow(lean_object* v_w_1227_, lean_object* v_x_1228_, lean_object* v_y_1229_){
_start:
{
uint8_t v___x_1230_; 
v___x_1230_ = lean_nat_dec_lt(v_x_1228_, v_y_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_BitVec_usubOverflow___boxed(lean_object* v_w_1231_, lean_object* v_x_1232_, lean_object* v_y_1233_){
_start:
{
uint8_t v_res_1234_; lean_object* v_r_1235_; 
v_res_1234_ = l_BitVec_usubOverflow(v_w_1231_, v_x_1232_, v_y_1233_);
lean_dec(v_y_1233_);
lean_dec(v_x_1232_);
lean_dec(v_w_1231_);
v_r_1235_ = lean_box(v_res_1234_);
return v_r_1235_;
}
}
LEAN_EXPORT uint8_t l_BitVec_ssubOverflow(lean_object* v_w_1236_, lean_object* v_x_1237_, lean_object* v_y_1238_){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1239_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1240_ = lean_unsigned_to_nat(1u);
v___x_1241_ = lean_nat_sub(v_w_1236_, v___x_1240_);
v___x_1242_ = l_Int_pow(v___x_1239_, v___x_1241_);
lean_dec(v___x_1241_);
v___x_1243_ = l_BitVec_toInt(v_w_1236_, v_x_1237_);
v___x_1244_ = l_BitVec_toInt(v_w_1236_, v_y_1238_);
v___x_1245_ = lean_int_sub(v___x_1243_, v___x_1244_);
lean_dec(v___x_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_int_dec_le(v___x_1242_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = lean_int_neg(v___x_1242_);
lean_dec(v___x_1242_);
v___x_1248_ = lean_int_dec_lt(v___x_1245_, v___x_1247_);
lean_dec(v___x_1247_);
lean_dec(v___x_1245_);
return v___x_1248_;
}
else
{
lean_dec(v___x_1245_);
lean_dec(v___x_1242_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ssubOverflow___boxed(lean_object* v_w_1249_, lean_object* v_x_1250_, lean_object* v_y_1251_){
_start:
{
uint8_t v_res_1252_; lean_object* v_r_1253_; 
v_res_1252_ = l_BitVec_ssubOverflow(v_w_1249_, v_x_1250_, v_y_1251_);
lean_dec(v_w_1249_);
v_r_1253_ = lean_box(v_res_1252_);
return v_r_1253_;
}
}
LEAN_EXPORT uint8_t l_BitVec_negOverflow(lean_object* v_w_1254_, lean_object* v_x_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1256_ = l_BitVec_toInt(v_w_1254_, v_x_1255_);
v___x_1257_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1258_ = lean_unsigned_to_nat(1u);
v___x_1259_ = lean_nat_sub(v_w_1254_, v___x_1258_);
v___x_1260_ = l_Int_pow(v___x_1257_, v___x_1259_);
lean_dec(v___x_1259_);
v___x_1261_ = lean_int_neg(v___x_1260_);
lean_dec(v___x_1260_);
v___x_1262_ = lean_int_dec_eq(v___x_1256_, v___x_1261_);
lean_dec(v___x_1261_);
lean_dec(v___x_1256_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_BitVec_negOverflow___boxed(lean_object* v_w_1263_, lean_object* v_x_1264_){
_start:
{
uint8_t v_res_1265_; lean_object* v_r_1266_; 
v_res_1265_ = l_BitVec_negOverflow(v_w_1263_, v_x_1264_);
lean_dec(v_w_1263_);
v_r_1266_ = lean_box(v_res_1265_);
return v_r_1266_;
}
}
LEAN_EXPORT uint8_t l_BitVec_sdivOverflow(lean_object* v_w_1267_, lean_object* v_x_1268_, lean_object* v_y_1269_){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1270_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_sub(v_w_1267_, v___x_1271_);
v___x_1273_ = l_Int_pow(v___x_1270_, v___x_1272_);
lean_dec(v___x_1272_);
v___x_1274_ = l_BitVec_toInt(v_w_1267_, v_x_1268_);
v___x_1275_ = l_BitVec_toInt(v_w_1267_, v_y_1269_);
v___x_1276_ = lean_int_ediv(v___x_1274_, v___x_1275_);
lean_dec(v___x_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_int_dec_le(v___x_1273_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = lean_int_neg(v___x_1273_);
lean_dec(v___x_1273_);
v___x_1279_ = lean_int_dec_lt(v___x_1276_, v___x_1278_);
lean_dec(v___x_1278_);
lean_dec(v___x_1276_);
return v___x_1279_;
}
else
{
lean_dec(v___x_1276_);
lean_dec(v___x_1273_);
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sdivOverflow___boxed(lean_object* v_w_1280_, lean_object* v_x_1281_, lean_object* v_y_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_BitVec_sdivOverflow(v_w_1280_, v_x_1281_, v_y_1282_);
lean_dec(v_w_1280_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse(lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
lean_object* v_zero_1287_; uint8_t v_isZero_1288_; 
v_zero_1287_ = lean_unsigned_to_nat(0u);
v_isZero_1288_ = lean_nat_dec_eq(v_x_1285_, v_zero_1287_);
if (v_isZero_1288_ == 1)
{
lean_inc(v_x_1286_);
return v_x_1286_;
}
else
{
lean_object* v_one_1289_; lean_object* v_n_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_one_1289_ = lean_unsigned_to_nat(1u);
v_n_1290_ = lean_nat_sub(v_x_1285_, v_one_1289_);
v___x_1291_ = lean_nat_add(v_n_1290_, v_one_1289_);
v___x_1292_ = l_BitVec_setWidth(v___x_1291_, v_n_1290_, v_x_1286_);
v___x_1293_ = l_BitVec_reverse(v_n_1290_, v___x_1292_);
lean_dec(v___x_1292_);
lean_dec(v_n_1290_);
v___x_1294_ = lean_nat_dec_lt(v_zero_1287_, v___x_1291_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; 
lean_dec(v___x_1291_);
v___x_1295_ = l_BitVec_concat___redArg(v___x_1293_, v___x_1294_);
lean_dec(v___x_1293_);
return v___x_1295_;
}
else
{
lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_nat_sub(v___x_1291_, v_one_1289_);
lean_dec(v___x_1291_);
v___x_1297_ = l_Nat_testBit(v_x_1286_, v___x_1296_);
lean_dec(v___x_1296_);
v___x_1298_ = l_BitVec_concat___redArg(v___x_1293_, v___x_1297_);
lean_dec(v___x_1293_);
return v___x_1298_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_reverse___boxed(lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_BitVec_reverse(v_x_1299_, v_x_1300_);
lean_dec(v_x_1300_);
lean_dec(v_x_1299_);
return v_res_1301_;
}
}
LEAN_EXPORT uint8_t l_BitVec_umulOverflow(lean_object* v_w_1302_, lean_object* v_x_1303_, lean_object* v_y_1304_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1305_ = lean_unsigned_to_nat(2u);
v___x_1306_ = lean_nat_pow(v___x_1305_, v_w_1302_);
v___x_1307_ = lean_nat_mul(v_x_1303_, v_y_1304_);
v___x_1308_ = lean_nat_dec_le(v___x_1306_, v___x_1307_);
lean_dec(v___x_1307_);
lean_dec(v___x_1306_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_BitVec_umulOverflow___boxed(lean_object* v_w_1309_, lean_object* v_x_1310_, lean_object* v_y_1311_){
_start:
{
uint8_t v_res_1312_; lean_object* v_r_1313_; 
v_res_1312_ = l_BitVec_umulOverflow(v_w_1309_, v_x_1310_, v_y_1311_);
lean_dec(v_y_1311_);
lean_dec(v_x_1310_);
lean_dec(v_w_1309_);
v_r_1313_ = lean_box(v_res_1312_);
return v_r_1313_;
}
}
LEAN_EXPORT uint8_t l_BitVec_smulOverflow(lean_object* v_w_1314_, lean_object* v_x_1315_, lean_object* v_y_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1317_ = lean_obj_once(&l_BitVec_saddOverflow___closed__0, &l_BitVec_saddOverflow___closed__0_once, _init_l_BitVec_saddOverflow___closed__0);
v___x_1318_ = lean_unsigned_to_nat(1u);
v___x_1319_ = lean_nat_sub(v_w_1314_, v___x_1318_);
v___x_1320_ = l_Int_pow(v___x_1317_, v___x_1319_);
lean_dec(v___x_1319_);
v___x_1321_ = l_BitVec_toInt(v_w_1314_, v_x_1315_);
v___x_1322_ = l_BitVec_toInt(v_w_1314_, v_y_1316_);
v___x_1323_ = lean_int_mul(v___x_1321_, v___x_1322_);
lean_dec(v___x_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_int_dec_le(v___x_1320_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = lean_int_neg(v___x_1320_);
lean_dec(v___x_1320_);
v___x_1326_ = lean_int_dec_lt(v___x_1323_, v___x_1325_);
lean_dec(v___x_1325_);
lean_dec(v___x_1323_);
return v___x_1326_;
}
else
{
lean_dec(v___x_1323_);
lean_dec(v___x_1320_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_smulOverflow___boxed(lean_object* v_w_1327_, lean_object* v_x_1328_, lean_object* v_y_1329_){
_start:
{
uint8_t v_res_1330_; lean_object* v_r_1331_; 
v_res_1330_ = l_BitVec_smulOverflow(v_w_1327_, v_x_1328_, v_y_1329_);
lean_dec(v_w_1327_);
v_r_1331_ = lean_box(v_res_1330_);
return v_r_1331_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec(lean_object* v_w_1332_, lean_object* v_x_1333_, lean_object* v_n_1334_){
_start:
{
lean_object* v_zero_1335_; uint8_t v_isZero_1336_; 
v_zero_1335_ = lean_unsigned_to_nat(0u);
v_isZero_1336_ = lean_nat_dec_eq(v_n_1334_, v_zero_1335_);
if (v_isZero_1336_ == 1)
{
uint8_t v___x_1337_; 
lean_dec(v_n_1334_);
v___x_1337_ = l_Nat_testBit(v_x_1333_, v_zero_1335_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = l_BitVec_ofNat(v_w_1332_, v_w_1332_);
return v___x_1338_;
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1339_ = lean_unsigned_to_nat(1u);
v___x_1340_ = lean_nat_sub(v_w_1332_, v___x_1339_);
v___x_1341_ = l_BitVec_ofNat(v_w_1332_, v___x_1340_);
lean_dec(v___x_1340_);
return v___x_1341_;
}
}
else
{
uint8_t v___x_1342_; 
v___x_1342_ = l_Nat_testBit(v_x_1333_, v_n_1334_);
if (v___x_1342_ == 0)
{
lean_object* v_one_1343_; lean_object* v_n_1344_; 
v_one_1343_ = lean_unsigned_to_nat(1u);
v_n_1344_ = lean_nat_sub(v_n_1334_, v_one_1343_);
lean_dec(v_n_1334_);
v_n_1334_ = v_n_1344_;
goto _start;
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = lean_nat_sub(v_w_1332_, v___x_1346_);
v___x_1348_ = lean_nat_sub(v___x_1347_, v_n_1334_);
lean_dec(v_n_1334_);
lean_dec(v___x_1347_);
v___x_1349_ = l_BitVec_ofNat(v_w_1332_, v___x_1348_);
lean_dec(v___x_1348_);
return v___x_1349_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_clzAuxRec___boxed(lean_object* v_w_1350_, lean_object* v_x_1351_, lean_object* v_n_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_BitVec_clzAuxRec(v_w_1350_, v_x_1351_, v_n_1352_);
lean_dec(v_x_1351_);
lean_dec(v_w_1350_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clz(lean_object* v_w_1354_, lean_object* v_x_1355_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = lean_nat_sub(v_w_1354_, v___x_1356_);
v___x_1358_ = l_BitVec_clzAuxRec(v_w_1354_, v_x_1355_, v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_BitVec_clz___boxed(lean_object* v_w_1359_, lean_object* v_x_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_BitVec_clz(v_w_1359_, v_x_1360_);
lean_dec(v_x_1360_);
lean_dec(v_w_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ctz(lean_object* v_w_1362_, lean_object* v_x_1363_){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = l_BitVec_reverse(v_w_1362_, v_x_1363_);
v___x_1365_ = l_BitVec_clz(v_w_1362_, v___x_1364_);
lean_dec(v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ctz___boxed(lean_object* v_w_1366_, lean_object* v_x_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_BitVec_ctz(v_w_1366_, v_x_1367_);
lean_dec(v_x_1367_);
lean_dec(v_w_1366_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg(lean_object* v_x_1369_, lean_object* v_pos_1370_, lean_object* v_acc_1371_){
_start:
{
lean_object* v_zero_1372_; uint8_t v_isZero_1373_; 
v_zero_1372_ = lean_unsigned_to_nat(0u);
v_isZero_1373_ = lean_nat_dec_eq(v_pos_1370_, v_zero_1372_);
if (v_isZero_1373_ == 1)
{
lean_dec(v_pos_1370_);
return v_acc_1371_;
}
else
{
lean_object* v_one_1374_; lean_object* v_n_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_one_1374_ = lean_unsigned_to_nat(1u);
v_n_1375_ = lean_nat_sub(v_pos_1370_, v_one_1374_);
lean_dec(v_pos_1370_);
v___x_1376_ = l_Nat_testBit(v_x_1369_, v_n_1375_);
v___x_1377_ = l_Bool_toNat(v___x_1376_);
v___x_1378_ = lean_nat_add(v_acc_1371_, v___x_1377_);
lean_dec(v___x_1377_);
lean_dec(v_acc_1371_);
v_pos_1370_ = v_n_1375_;
v_acc_1371_ = v___x_1378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___redArg___boxed(lean_object* v_x_1380_, lean_object* v_pos_1381_, lean_object* v_acc_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_BitVec_cpopNatRec___redArg(v_x_1380_, v_pos_1381_, v_acc_1382_);
lean_dec(v_x_1380_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec(lean_object* v_w_1384_, lean_object* v_x_1385_, lean_object* v_pos_1386_, lean_object* v_acc_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_BitVec_cpopNatRec___redArg(v_x_1385_, v_pos_1386_, v_acc_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopNatRec___boxed(lean_object* v_w_1389_, lean_object* v_x_1390_, lean_object* v_pos_1391_, lean_object* v_acc_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_BitVec_cpopNatRec(v_w_1389_, v_x_1390_, v_pos_1391_, v_acc_1392_);
lean_dec(v_x_1390_);
lean_dec(v_w_1389_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpop(lean_object* v_w_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = lean_unsigned_to_nat(0u);
lean_inc(v_w_1394_);
v___x_1397_ = l_BitVec_cpopNatRec___redArg(v_x_1395_, v_w_1394_, v___x_1396_);
v___x_1398_ = l_BitVec_ofNat(v_w_1394_, v___x_1397_);
lean_dec(v___x_1397_);
lean_dec(v_w_1394_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpop___boxed(lean_object* v_w_1399_, lean_object* v_x_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_BitVec_cpop(v_w_1399_, v_x_1400_);
lean_dec(v_x_1400_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg___lam__0(lean_object* v_x_1402_, lean_object* v_y_1403_){
_start:
{
uint8_t v___x_1404_; 
v___x_1404_ = lean_nat_dec_le(v_x_1402_, v_y_1403_);
if (v___x_1404_ == 0)
{
lean_inc(v_y_1403_);
return v_y_1403_;
}
else
{
lean_inc(v_x_1402_);
return v_x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg___lam__0___boxed(lean_object* v_x_1405_, lean_object* v_y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_BitVec_instMin___redArg___lam__0(v_x_1405_, v_y_1406_);
lean_dec(v_y_1406_);
lean_dec(v_x_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg(){
_start:
{
lean_object* v___f_1410_; 
v___f_1410_ = ((lean_object*)(l_BitVec_instMin___redArg___closed__0));
return v___f_1410_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___redArg___boxed(lean_object* v___dummy_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_BitVec_instMin___redArg();
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin(lean_object* v_w_1413_){
_start:
{
lean_object* v___f_1414_; 
v___f_1414_ = ((lean_object*)(l_BitVec_instMin___redArg___closed__0));
return v___f_1414_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMin___boxed(lean_object* v_w_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_BitVec_instMin(v_w_1415_);
lean_dec(v_w_1415_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg___lam__0(lean_object* v_x_1417_, lean_object* v_y_1418_){
_start:
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_nat_dec_le(v_x_1417_, v_y_1418_);
if (v___x_1419_ == 0)
{
lean_inc(v_x_1417_);
return v_x_1417_;
}
else
{
lean_inc(v_y_1418_);
return v_y_1418_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg___lam__0___boxed(lean_object* v_x_1420_, lean_object* v_y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_BitVec_instMax___redArg___lam__0(v_x_1420_, v_y_1421_);
lean_dec(v_y_1421_);
lean_dec(v_x_1420_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg(){
_start:
{
lean_object* v___f_1425_; 
v___f_1425_ = ((lean_object*)(l_BitVec_instMax___redArg___closed__0));
return v___f_1425_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___redArg___boxed(lean_object* v___dummy_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_BitVec_instMax___redArg();
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax(lean_object* v_w_1428_){
_start:
{
lean_object* v___f_1429_; 
v___f_1429_ = ((lean_object*)(l_BitVec_instMax___redArg___closed__0));
return v___f_1429_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instMax___boxed(lean_object* v_w_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_BitVec_instMax(v_w_1430_);
lean_dec(v_w_1430_);
return v_res_1431_;
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
