// Lean compiler output
// Module: Init.Core
// Imports: public import Init.SizeOf public import Init.Tactics
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_inline___redArg(lean_object*);
LEAN_EXPORT lean_object* l_inline___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_inline(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_inline___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_eagerReduce___redArg(lean_object*);
LEAN_EXPORT lean_object* l_eagerReduce___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_eagerReduce(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_eagerReduce___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_flip___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_flip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqEmpty___redArg();
LEAN_EXPORT lean_object* l_instDecidableEqEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqEmpty(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instDecidableEqEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqPEmpty___redArg();
LEAN_EXPORT lean_object* l_instDecidableEqPEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqPEmpty(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instDecidableEqPEmpty___boxed(lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
LEAN_EXPORT lean_object* l_Thunk_mk___boxed(lean_object*, lean_object*);
lean_object* lean_thunk_pure(lean_object*);
LEAN_EXPORT lean_object* l_Thunk_pure___boxed(lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Thunk_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Thunk_fnImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Thunk_fnImpl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Thunk_fnImpl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Thunk_fnImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Thunk_map___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Thunk_map___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Thunk_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Thunk_map(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Thunk_bind___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Thunk_bind___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Thunk_bind___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Thunk_bind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_thunkCoe___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_thunkCoe___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_thunkCoe___redArg___lam__1(lean_object*);
static const lean_closure_object l_thunkCoe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_thunkCoe___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_thunkCoe___redArg___closed__0 = (const lean_object*)&l_thunkCoe___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_thunkCoe___redArg();
LEAN_EXPORT lean_object* l_thunkCoe___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_thunkCoe(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedThunk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedThunk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Eq_ndrecOn___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Eq_ndrecOn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Eq_ndrecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Eq_ndrecOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___x3c_x2d_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_<->_"};
static const lean_object* l_term___x3c_x2d_x3e___00__closed__0 = (const lean_object*)&l_term___x3c_x2d_x3e___00__closed__0_value;
static const lean_ctor_object l_term___x3c_x2d_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x3c_x2d_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 221, 185, 27, 126, 151, 59, 120)}};
static const lean_object* l_term___x3c_x2d_x3e___00__closed__1 = (const lean_object*)&l_term___x3c_x2d_x3e___00__closed__1_value;
static const lean_string_object l_term___x3c_x2d_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_term___x3c_x2d_x3e___00__closed__2 = (const lean_object*)&l_term___x3c_x2d_x3e___00__closed__2_value;
static const lean_ctor_object l_term___x3c_x2d_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x3c_x2d_x3e___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_term___x3c_x2d_x3e___00__closed__3 = (const lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value;
static const lean_string_object l_term___x3c_x2d_x3e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " <-> "};
static const lean_object* l_term___x3c_x2d_x3e___00__closed__4 = (const lean_object*)&l_term___x3c_x2d_x3e___00__closed__4_value;
static const lean_ctor_object l_term___x3c_x2d_x3e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__4_value)}};
static const lean_object* l_term___x3c_x2d_x3e___00__closed__5 = (const lean_object*)&l_term___x3c_x2d_x3e___00__closed__5_value;
static const lean_string_object l_term___x3c_x2d_x3e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_term___x3c_x2d_x3e___00__closed__6 = (const lean_object*)&l_term___x3c_x2d_x3e___00__closed__6_value;
static const lean_ctor_object l_term___x3c_x2d_x3e___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x3c_x2d_x3e___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_term___x3c_x2d_x3e___00__closed__7 = (const lean_object*)&l_term___x3c_x2d_x3e___00__closed__7_value;
static const lean_ctor_object l_term___x3c_x2d_x3e___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__7_value),((lean_object*)(((size_t)(21) << 1) | 1))}};
static const lean_object* l_term___x3c_x2d_x3e___00__closed__8 = (const lean_object*)&l_term___x3c_x2d_x3e___00__closed__8_value;
static const lean_ctor_object l_term___x3c_x2d_x3e___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___x3c_x2d_x3e___00__closed__5_value),((lean_object*)&l_term___x3c_x2d_x3e___00__closed__8_value)}};
static const lean_object* l_term___x3c_x2d_x3e___00__closed__9 = (const lean_object*)&l_term___x3c_x2d_x3e___00__closed__9_value;
static const lean_ctor_object l_term___x3c_x2d_x3e___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__1_value),((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)&l_term___x3c_x2d_x3e___00__closed__9_value)}};
static const lean_object* l_term___x3c_x2d_x3e___00__closed__10 = (const lean_object*)&l_term___x3c_x2d_x3e___00__closed__10_value;
LEAN_EXPORT const lean_object* l_term___x3c_x2d_x3e__ = (const lean_object*)&l_term___x3c_x2d_x3e___00__closed__10_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__2_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__8 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__8_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7_value)}};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__9 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__9_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__10 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__10_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__8_value),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__10_value)}};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__12 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__12_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__Core______unexpand__Iff__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___aux__Init__Core______unexpand__Iff__1___closed__0 = (const lean_object*)&l___aux__Init__Core______unexpand__Iff__1___closed__0_value;
static const lean_ctor_object l___aux__Init__Core______unexpand__Iff__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______unexpand__Iff__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___aux__Init__Core______unexpand__Iff__1___closed__1 = (const lean_object*)&l___aux__Init__Core______unexpand__Iff__1___closed__1_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___u2194___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_↔_"};
static const lean_object* l_term___u2194___00__closed__0 = (const lean_object*)&l_term___u2194___00__closed__0_value;
static const lean_ctor_object l_term___u2194___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___u2194___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 124, 41, 198, 228, 162, 237, 244)}};
static const lean_object* l_term___u2194___00__closed__1 = (const lean_object*)&l_term___u2194___00__closed__1_value;
static const lean_string_object l_term___u2194___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↔ "};
static const lean_object* l_term___u2194___00__closed__2 = (const lean_object*)&l_term___u2194___00__closed__2_value;
static const lean_ctor_object l_term___u2194___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___u2194___00__closed__2_value)}};
static const lean_object* l_term___u2194___00__closed__3 = (const lean_object*)&l_term___u2194___00__closed__3_value;
static const lean_ctor_object l_term___u2194___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___u2194___00__closed__3_value),((lean_object*)&l_term___x3c_x2d_x3e___00__closed__8_value)}};
static const lean_object* l_term___u2194___00__closed__4 = (const lean_object*)&l_term___u2194___00__closed__4_value;
static const lean_ctor_object l_term___u2194___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___u2194___00__closed__1_value),((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)&l_term___u2194___00__closed__4_value)}};
static const lean_object* l_term___u2194___00__closed__5 = (const lean_object*)&l_term___u2194___00__closed__5_value;
LEAN_EXPORT const lean_object* l_term___u2194__ = (const lean_object*)&l_term___u2194___00__closed__5_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2194____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2194____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Sum_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Sum_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_inl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_inl_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_inr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_inr_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___u2295___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊕_"};
static const lean_object* l_term___u2295___00__closed__0 = (const lean_object*)&l_term___u2295___00__closed__0_value;
static const lean_ctor_object l_term___u2295___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___u2295___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 117, 43, 15, 38, 4, 232, 178)}};
static const lean_object* l_term___u2295___00__closed__1 = (const lean_object*)&l_term___u2295___00__closed__1_value;
static const lean_string_object l_term___u2295___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊕ "};
static const lean_object* l_term___u2295___00__closed__2 = (const lean_object*)&l_term___u2295___00__closed__2_value;
static const lean_ctor_object l_term___u2295___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___u2295___00__closed__2_value)}};
static const lean_object* l_term___u2295___00__closed__3 = (const lean_object*)&l_term___u2295___00__closed__3_value;
static const lean_ctor_object l_term___u2295___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__7_value),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l_term___u2295___00__closed__4 = (const lean_object*)&l_term___u2295___00__closed__4_value;
static const lean_ctor_object l_term___u2295___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___u2295___00__closed__3_value),((lean_object*)&l_term___u2295___00__closed__4_value)}};
static const lean_object* l_term___u2295___00__closed__5 = (const lean_object*)&l_term___u2295___00__closed__5_value;
static const lean_ctor_object l_term___u2295___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___u2295___00__closed__1_value),((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l_term___u2295___00__closed__5_value)}};
static const lean_object* l_term___u2295___00__closed__6 = (const lean_object*)&l_term___u2295___00__closed__6_value;
LEAN_EXPORT const lean_object* l_term___u2295__ = (const lean_object*)&l_term___u2295___00__closed__6_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2295____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sum"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2295____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2295____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___u2295____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___u2295____1___closed__1;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2295____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___u2295____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 106, 118, 161, 227, 189, 67, 81)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2295____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2295____1___closed__2_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2295____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2295____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2295____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2295____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2295____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2295____1___closed__2_value)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2295____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2295____1___closed__4_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2295____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2295____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2295____1___closed__5 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2295____1___closed__5_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2295____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2295____1___closed__3_value),((lean_object*)&l___aux__Init__Core______macroRules__term___u2295____1___closed__5_value)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2295____1___closed__6 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2295____1___closed__6_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Sum__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Sum__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSum_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_PSum_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PSum_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSum_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSum_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSum_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSum_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSum_inl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSum_inl_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSum_inr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSum_inr_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___u2295_x27___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "term_⊕'_"};
static const lean_object* l_term___u2295_x27___00__closed__0 = (const lean_object*)&l_term___u2295_x27___00__closed__0_value;
static const lean_ctor_object l_term___u2295_x27___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___u2295_x27___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 48, 98, 83, 163, 173, 42, 152)}};
static const lean_object* l_term___u2295_x27___00__closed__1 = (const lean_object*)&l_term___u2295_x27___00__closed__1_value;
static const lean_string_object l_term___u2295_x27___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = " ⊕' "};
static const lean_object* l_term___u2295_x27___00__closed__2 = (const lean_object*)&l_term___u2295_x27___00__closed__2_value;
static const lean_ctor_object l_term___u2295_x27___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___u2295_x27___00__closed__2_value)}};
static const lean_object* l_term___u2295_x27___00__closed__3 = (const lean_object*)&l_term___u2295_x27___00__closed__3_value;
static const lean_ctor_object l_term___u2295_x27___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___u2295_x27___00__closed__3_value),((lean_object*)&l_term___u2295___00__closed__4_value)}};
static const lean_object* l_term___u2295_x27___00__closed__4 = (const lean_object*)&l_term___u2295_x27___00__closed__4_value;
static const lean_ctor_object l_term___u2295_x27___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___u2295_x27___00__closed__1_value),((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l_term___u2295_x27___00__closed__4_value)}};
static const lean_object* l_term___u2295_x27___00__closed__5 = (const lean_object*)&l_term___u2295_x27___00__closed__5_value;
LEAN_EXPORT const lean_object* l_term___u2295_x27__ = (const lean_object*)&l_term___u2295_x27___00__closed__5_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PSum"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2_value)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__4_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__5 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__5_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__3_value),((lean_object*)&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__5_value)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__6 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__6_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__PSum__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__PSum__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSum_inhabitedLeft___redArg(lean_object*);
LEAN_EXPORT lean_object* l_PSum_inhabitedLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSum_inhabitedRight___redArg(lean_object*);
LEAN_EXPORT lean_object* l_PSum_inhabitedRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_done_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_yield_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_yield_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedForInStep_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedForInStep_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedForInStep___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedForInStep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_pure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_pure_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_return_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_return_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_break_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_break_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_continue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_continue_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_return_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_return_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_break_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_break_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_pureReturn_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_pureReturn_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_break_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_break_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_continue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_continue_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___u2248___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≈_"};
static const lean_object* l_term___u2248___00__closed__0 = (const lean_object*)&l_term___u2248___00__closed__0_value;
static const lean_ctor_object l_term___u2248___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___u2248___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 75, 182, 127, 139, 38, 183, 58)}};
static const lean_object* l_term___u2248___00__closed__1 = (const lean_object*)&l_term___u2248___00__closed__1_value;
static const lean_string_object l_term___u2248___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≈ "};
static const lean_object* l_term___u2248___00__closed__2 = (const lean_object*)&l_term___u2248___00__closed__2_value;
static const lean_ctor_object l_term___u2248___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___u2248___00__closed__2_value)}};
static const lean_object* l_term___u2248___00__closed__3 = (const lean_object*)&l_term___u2248___00__closed__3_value;
static const lean_ctor_object l_term___u2248___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__7_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_term___u2248___00__closed__4 = (const lean_object*)&l_term___u2248___00__closed__4_value;
static const lean_ctor_object l_term___u2248___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___u2248___00__closed__3_value),((lean_object*)&l_term___u2248___00__closed__4_value)}};
static const lean_object* l_term___u2248___00__closed__5 = (const lean_object*)&l_term___u2248___00__closed__5_value;
static const lean_ctor_object l_term___u2248___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___u2248___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_term___u2248___00__closed__5_value)}};
static const lean_object* l_term___u2248___00__closed__6 = (const lean_object*)&l_term___u2248___00__closed__6_value;
LEAN_EXPORT const lean_object* l_term___u2248__ = (const lean_object*)&l_term___u2248___00__closed__6_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2248____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "HasEquiv.Equiv"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2248____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2248____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___u2248____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___u2248____1___closed__1;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2248____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HasEquiv"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2248____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2248____1___closed__2_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2248____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2248____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2248____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2248____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___u2248____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 235, 200, 91, 245, 36, 119, 204)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2248____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2248____1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__term___u2248____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(123, 211, 194, 76, 11, 68, 97, 149)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2248____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2248____1___closed__4_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2248____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2248____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2248____1___closed__5 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2248____1___closed__5_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2248____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2248____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2248____1___closed__6 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2248____1___closed__6_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2248____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2248____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasEquiv__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasEquiv__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___u2286___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊆_"};
static const lean_object* l_term___u2286___00__closed__0 = (const lean_object*)&l_term___u2286___00__closed__0_value;
static const lean_ctor_object l_term___u2286___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___u2286___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 90, 218, 225, 73, 214, 71)}};
static const lean_object* l_term___u2286___00__closed__1 = (const lean_object*)&l_term___u2286___00__closed__1_value;
static const lean_string_object l_term___u2286___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊆ "};
static const lean_object* l_term___u2286___00__closed__2 = (const lean_object*)&l_term___u2286___00__closed__2_value;
static const lean_ctor_object l_term___u2286___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___u2286___00__closed__2_value)}};
static const lean_object* l_term___u2286___00__closed__3 = (const lean_object*)&l_term___u2286___00__closed__3_value;
static const lean_ctor_object l_term___u2286___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___u2286___00__closed__3_value),((lean_object*)&l_term___u2248___00__closed__4_value)}};
static const lean_object* l_term___u2286___00__closed__4 = (const lean_object*)&l_term___u2286___00__closed__4_value;
static const lean_ctor_object l_term___u2286___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___u2286___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_term___u2286___00__closed__4_value)}};
static const lean_object* l_term___u2286___00__closed__5 = (const lean_object*)&l_term___u2286___00__closed__5_value;
LEAN_EXPORT const lean_object* l_term___u2286__ = (const lean_object*)&l_term___u2286___00__closed__5_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2286____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Subset"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2286____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2286____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___u2286____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___u2286____1___closed__1;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2286____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___u2286____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 82, 82, 84, 163, 206, 185, 124)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2286____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2286____1___closed__2_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2286____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "HasSubset"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2286____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2286____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2286____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___u2286____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(106, 253, 191, 3, 166, 233, 20, 214)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2286____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2286____1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__term___u2286____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 184, 40, 142, 220, 246, 232, 92)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2286____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2286____1___closed__4_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2286____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2286____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2286____1___closed__5 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2286____1___closed__5_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2286____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2286____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2286____1___closed__6 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2286____1___closed__6_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2286____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2286____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSubset__Subset__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSubset__Subset__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___u2282___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊂_"};
static const lean_object* l_term___u2282___00__closed__0 = (const lean_object*)&l_term___u2282___00__closed__0_value;
static const lean_ctor_object l_term___u2282___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___u2282___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 36, 104, 26, 7, 158, 117, 91)}};
static const lean_object* l_term___u2282___00__closed__1 = (const lean_object*)&l_term___u2282___00__closed__1_value;
static const lean_string_object l_term___u2282___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊂ "};
static const lean_object* l_term___u2282___00__closed__2 = (const lean_object*)&l_term___u2282___00__closed__2_value;
static const lean_ctor_object l_term___u2282___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___u2282___00__closed__2_value)}};
static const lean_object* l_term___u2282___00__closed__3 = (const lean_object*)&l_term___u2282___00__closed__3_value;
static const lean_ctor_object l_term___u2282___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___u2282___00__closed__3_value),((lean_object*)&l_term___u2248___00__closed__4_value)}};
static const lean_object* l_term___u2282___00__closed__4 = (const lean_object*)&l_term___u2282___00__closed__4_value;
static const lean_ctor_object l_term___u2282___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___u2282___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_term___u2282___00__closed__4_value)}};
static const lean_object* l_term___u2282___00__closed__5 = (const lean_object*)&l_term___u2282___00__closed__5_value;
LEAN_EXPORT const lean_object* l_term___u2282__ = (const lean_object*)&l_term___u2282___00__closed__5_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2282____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SSubset"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2282____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2282____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___u2282____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___u2282____1___closed__1;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2282____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___u2282____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 101, 8, 196, 212, 53, 38, 158)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2282____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2282____1___closed__2_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2282____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "HasSSubset"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2282____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2282____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2282____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___u2282____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 19, 96, 185, 166, 168, 236, 21)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2282____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2282____1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__term___u2282____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 122, 156, 254, 146, 115, 10, 58)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2282____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2282____1___closed__4_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2282____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2282____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2282____1___closed__5 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2282____1___closed__5_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2282____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2282____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2282____1___closed__6 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2282____1___closed__6_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2282____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2282____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSSubset__SSubset__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSSubset__SSubset__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___u2287___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊇_"};
static const lean_object* l_term___u2287___00__closed__0 = (const lean_object*)&l_term___u2287___00__closed__0_value;
static const lean_ctor_object l_term___u2287___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___u2287___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 48, 9, 251, 76, 50, 57, 116)}};
static const lean_object* l_term___u2287___00__closed__1 = (const lean_object*)&l_term___u2287___00__closed__1_value;
static const lean_string_object l_term___u2287___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊇ "};
static const lean_object* l_term___u2287___00__closed__2 = (const lean_object*)&l_term___u2287___00__closed__2_value;
static const lean_ctor_object l_term___u2287___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___u2287___00__closed__2_value)}};
static const lean_object* l_term___u2287___00__closed__3 = (const lean_object*)&l_term___u2287___00__closed__3_value;
static const lean_ctor_object l_term___u2287___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___u2287___00__closed__3_value),((lean_object*)&l_term___u2248___00__closed__4_value)}};
static const lean_object* l_term___u2287___00__closed__4 = (const lean_object*)&l_term___u2287___00__closed__4_value;
static const lean_ctor_object l_term___u2287___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___u2287___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_term___u2287___00__closed__4_value)}};
static const lean_object* l_term___u2287___00__closed__5 = (const lean_object*)&l_term___u2287___00__closed__5_value;
LEAN_EXPORT const lean_object* l_term___u2287__ = (const lean_object*)&l_term___u2287___00__closed__5_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2287____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Superset"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2287____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2287____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___u2287____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___u2287____1___closed__1;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2287____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___u2287____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 166, 42, 174, 203, 247, 104, 192)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2287____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2287____1___closed__2_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2287____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2287____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2287____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2287____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2287____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2287____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2287____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2287____1___closed__4_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2287____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2287____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Superset__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Superset__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___u2283___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_⊃_"};
static const lean_object* l_term___u2283___00__closed__0 = (const lean_object*)&l_term___u2283___00__closed__0_value;
static const lean_ctor_object l_term___u2283___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___u2283___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 217, 255, 107, 39, 224, 209, 40)}};
static const lean_object* l_term___u2283___00__closed__1 = (const lean_object*)&l_term___u2283___00__closed__1_value;
static const lean_string_object l_term___u2283___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ⊃ "};
static const lean_object* l_term___u2283___00__closed__2 = (const lean_object*)&l_term___u2283___00__closed__2_value;
static const lean_ctor_object l_term___u2283___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___u2283___00__closed__2_value)}};
static const lean_object* l_term___u2283___00__closed__3 = (const lean_object*)&l_term___u2283___00__closed__3_value;
static const lean_ctor_object l_term___u2283___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___u2283___00__closed__3_value),((lean_object*)&l_term___u2248___00__closed__4_value)}};
static const lean_object* l_term___u2283___00__closed__4 = (const lean_object*)&l_term___u2283___00__closed__4_value;
static const lean_ctor_object l_term___u2283___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___u2283___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_term___u2283___00__closed__4_value)}};
static const lean_object* l_term___u2283___00__closed__5 = (const lean_object*)&l_term___u2283___00__closed__5_value;
LEAN_EXPORT const lean_object* l_term___u2283__ = (const lean_object*)&l_term___u2283___00__closed__5_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2283____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "SSuperset"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2283____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2283____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___u2283____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___u2283____1___closed__1;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2283____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___u2283____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 76, 205, 136, 239, 243, 82, 249)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2283____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2283____1___closed__2_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2283____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2283____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2283____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2283____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2283____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2283____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2283____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2283____1___closed__4_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2283____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2283____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SSuperset__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SSuperset__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___u222a___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_∪_"};
static const lean_object* l_term___u222a___00__closed__0 = (const lean_object*)&l_term___u222a___00__closed__0_value;
static const lean_ctor_object l_term___u222a___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___u222a___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 164, 141, 67, 105, 98, 49, 125)}};
static const lean_object* l_term___u222a___00__closed__1 = (const lean_object*)&l_term___u222a___00__closed__1_value;
static const lean_string_object l_term___u222a___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ∪ "};
static const lean_object* l_term___u222a___00__closed__2 = (const lean_object*)&l_term___u222a___00__closed__2_value;
static const lean_ctor_object l_term___u222a___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___u222a___00__closed__2_value)}};
static const lean_object* l_term___u222a___00__closed__3 = (const lean_object*)&l_term___u222a___00__closed__3_value;
static const lean_ctor_object l_term___u222a___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__7_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l_term___u222a___00__closed__4 = (const lean_object*)&l_term___u222a___00__closed__4_value;
static const lean_ctor_object l_term___u222a___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___u222a___00__closed__3_value),((lean_object*)&l_term___u222a___00__closed__4_value)}};
static const lean_object* l_term___u222a___00__closed__5 = (const lean_object*)&l_term___u222a___00__closed__5_value;
static const lean_ctor_object l_term___u222a___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___u222a___00__closed__1_value),((lean_object*)(((size_t)(65) << 1) | 1)),((lean_object*)(((size_t)(65) << 1) | 1)),((lean_object*)&l_term___u222a___00__closed__5_value)}};
static const lean_object* l_term___u222a___00__closed__6 = (const lean_object*)&l_term___u222a___00__closed__6_value;
LEAN_EXPORT const lean_object* l_term___u222a__ = (const lean_object*)&l_term___u222a___00__closed__6_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u222a____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Union.union"};
static const lean_object* l___aux__Init__Core______macroRules__term___u222a____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u222a____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___u222a____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___u222a____1___closed__1;
static const lean_string_object l___aux__Init__Core______macroRules__term___u222a____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Union"};
static const lean_object* l___aux__Init__Core______macroRules__term___u222a____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u222a____1___closed__2_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u222a____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "union"};
static const lean_object* l___aux__Init__Core______macroRules__term___u222a____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u222a____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u222a____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___u222a____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 240, 120, 228, 82, 30, 29, 63)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u222a____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u222a____1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__term___u222a____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 232, 222, 78, 141, 7, 185, 206)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u222a____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u222a____1___closed__4_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u222a____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u222a____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u222a____1___closed__5 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u222a____1___closed__5_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u222a____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u222a____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u222a____1___closed__6 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u222a____1___closed__6_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u222a____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u222a____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Union__union__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Union__union__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___u2229___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_∩_"};
static const lean_object* l_term___u2229___00__closed__0 = (const lean_object*)&l_term___u2229___00__closed__0_value;
static const lean_ctor_object l_term___u2229___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___u2229___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(210, 13, 234, 13, 169, 12, 47, 99)}};
static const lean_object* l_term___u2229___00__closed__1 = (const lean_object*)&l_term___u2229___00__closed__1_value;
static const lean_string_object l_term___u2229___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ∩ "};
static const lean_object* l_term___u2229___00__closed__2 = (const lean_object*)&l_term___u2229___00__closed__2_value;
static const lean_ctor_object l_term___u2229___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___u2229___00__closed__2_value)}};
static const lean_object* l_term___u2229___00__closed__3 = (const lean_object*)&l_term___u2229___00__closed__3_value;
static const lean_ctor_object l_term___u2229___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__7_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l_term___u2229___00__closed__4 = (const lean_object*)&l_term___u2229___00__closed__4_value;
static const lean_ctor_object l_term___u2229___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___u2229___00__closed__3_value),((lean_object*)&l_term___u2229___00__closed__4_value)}};
static const lean_object* l_term___u2229___00__closed__5 = (const lean_object*)&l_term___u2229___00__closed__5_value;
static const lean_ctor_object l_term___u2229___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___u2229___00__closed__1_value),((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)&l_term___u2229___00__closed__5_value)}};
static const lean_object* l_term___u2229___00__closed__6 = (const lean_object*)&l_term___u2229___00__closed__6_value;
LEAN_EXPORT const lean_object* l_term___u2229__ = (const lean_object*)&l_term___u2229___00__closed__6_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2229____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Inter.inter"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2229____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2229____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___u2229____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___u2229____1___closed__1;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2229____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Inter"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2229____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2229____1___closed__2_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2229____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "inter"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2229____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2229____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2229____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___u2229____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(80, 146, 231, 194, 197, 246, 22, 133)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2229____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2229____1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__term___u2229____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(137, 135, 247, 172, 206, 128, 55, 121)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2229____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2229____1___closed__4_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2229____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2229____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2229____1___closed__5 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2229____1___closed__5_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2229____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2229____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2229____1___closed__6 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2229____1___closed__6_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2229____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2229____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Inter__inter__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Inter__inter__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___x5c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_\\_"};
static const lean_object* l_term___x5c___00__closed__0 = (const lean_object*)&l_term___x5c___00__closed__0_value;
static const lean_ctor_object l_term___x5c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x5c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 126, 27, 196, 42, 167, 114, 60)}};
static const lean_object* l_term___x5c___00__closed__1 = (const lean_object*)&l_term___x5c___00__closed__1_value;
static const lean_string_object l_term___x5c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " \\ "};
static const lean_object* l_term___x5c___00__closed__2 = (const lean_object*)&l_term___x5c___00__closed__2_value;
static const lean_ctor_object l_term___x5c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___x5c___00__closed__2_value)}};
static const lean_object* l_term___x5c___00__closed__3 = (const lean_object*)&l_term___x5c___00__closed__3_value;
static const lean_ctor_object l_term___x5c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___x5c___00__closed__3_value),((lean_object*)&l_term___u2229___00__closed__4_value)}};
static const lean_object* l_term___x5c___00__closed__4 = (const lean_object*)&l_term___x5c___00__closed__4_value;
static const lean_ctor_object l_term___x5c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___x5c___00__closed__1_value),((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)&l_term___x5c___00__closed__4_value)}};
static const lean_object* l_term___x5c___00__closed__5 = (const lean_object*)&l_term___x5c___00__closed__5_value;
LEAN_EXPORT const lean_object* l_term___x5c__ = (const lean_object*)&l_term___x5c___00__closed__5_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___x5c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "SDiff.sdiff"};
static const lean_object* l___aux__Init__Core______macroRules__term___x5c____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x5c____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___x5c____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___x5c____1___closed__1;
static const lean_string_object l___aux__Init__Core______macroRules__term___x5c____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SDiff"};
static const lean_object* l___aux__Init__Core______macroRules__term___x5c____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x5c____1___closed__2_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___x5c____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sdiff"};
static const lean_object* l___aux__Init__Core______macroRules__term___x5c____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x5c____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x5c____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___x5c____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(220, 237, 99, 38, 147, 140, 36, 191)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x5c____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x5c____1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__term___x5c____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 249, 143, 59, 92, 216, 130, 128)}};
static const lean_object* l___aux__Init__Core______macroRules__term___x5c____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x5c____1___closed__4_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x5c____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x5c____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___x5c____1___closed__5 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x5c____1___closed__5_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x5c____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x5c____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___x5c____1___closed__6 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x5c____1___closed__6_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x5c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x5c____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SDiff__sdiff__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SDiff__sdiff__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term_x7b_x7d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term{}"};
static const lean_object* l_term_x7b_x7d___closed__0 = (const lean_object*)&l_term_x7b_x7d___closed__0_value;
static const lean_ctor_object l_term_x7b_x7d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_x7b_x7d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 141, 217, 101, 193, 131, 35, 71)}};
static const lean_object* l_term_x7b_x7d___closed__1 = (const lean_object*)&l_term_x7b_x7d___closed__1_value;
static const lean_string_object l_term_x7b_x7d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_term_x7b_x7d___closed__2 = (const lean_object*)&l_term_x7b_x7d___closed__2_value;
static const lean_ctor_object l_term_x7b_x7d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_x7b_x7d___closed__2_value)}};
static const lean_object* l_term_x7b_x7d___closed__3 = (const lean_object*)&l_term_x7b_x7d___closed__3_value;
static const lean_string_object l_term_x7b_x7d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_term_x7b_x7d___closed__4 = (const lean_object*)&l_term_x7b_x7d___closed__4_value;
static const lean_ctor_object l_term_x7b_x7d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_x7b_x7d___closed__4_value)}};
static const lean_object* l_term_x7b_x7d___closed__5 = (const lean_object*)&l_term_x7b_x7d___closed__5_value;
static const lean_ctor_object l_term_x7b_x7d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term_x7b_x7d___closed__3_value),((lean_object*)&l_term_x7b_x7d___closed__5_value)}};
static const lean_object* l_term_x7b_x7d___closed__6 = (const lean_object*)&l_term_x7b_x7d___closed__6_value;
static const lean_ctor_object l_term_x7b_x7d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_term_x7b_x7d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_term_x7b_x7d___closed__6_value)}};
static const lean_object* l_term_x7b_x7d___closed__7 = (const lean_object*)&l_term_x7b_x7d___closed__7_value;
LEAN_EXPORT const lean_object* l_term_x7b_x7d = (const lean_object*)&l_term_x7b_x7d___closed__7_value;
static const lean_string_object l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "EmptyCollection.emptyCollection"};
static const lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1;
static const lean_string_object l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "EmptyCollection"};
static const lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__2_value;
static const lean_string_object l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "emptyCollection"};
static const lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(236, 209, 69, 209, 212, 29, 83, 196)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(3, 53, 136, 5, 91, 228, 156, 207)}};
static const lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__5 = (const lean_object*)&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__5_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6 = (const lean_object*)&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term_u2205___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "term∅"};
static const lean_object* l_term_u2205___closed__0 = (const lean_object*)&l_term_u2205___closed__0_value;
static const lean_ctor_object l_term_u2205___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_u2205___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 213, 176, 183, 122, 236, 171, 252)}};
static const lean_object* l_term_u2205___closed__1 = (const lean_object*)&l_term_u2205___closed__1_value;
static const lean_string_object l_term_u2205___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∅"};
static const lean_object* l_term_u2205___closed__2 = (const lean_object*)&l_term_u2205___closed__2_value;
static const lean_ctor_object l_term_u2205___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_u2205___closed__2_value)}};
static const lean_object* l_term_u2205___closed__3 = (const lean_object*)&l_term_u2205___closed__3_value;
static const lean_ctor_object l_term_u2205___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_term_u2205___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_term_u2205___closed__3_value)}};
static const lean_object* l_term_u2205___closed__4 = (const lean_object*)&l_term_u2205___closed__4_value;
LEAN_EXPORT const lean_object* l_term_u2205 = (const lean_object*)&l_term_u2205___closed__4_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_u2205__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_u2205__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedTask_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedTask_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedTask(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Task_pure___boxed(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Task_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_Task_Priority_max;
LEAN_EXPORT lean_object* l_Task_Priority_dedicated;
lean_object* lean_task_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Task_spawn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Task_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Task_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_strict_or(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_strictOr___boxed(lean_object*, lean_object*);
uint8_t lean_strict_and(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_strictAnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_bne___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_bne___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_bne(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_bne___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___x21_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_!=_"};
static const lean_object* l_term___x21_x3d___00__closed__0 = (const lean_object*)&l_term___x21_x3d___00__closed__0_value;
static const lean_ctor_object l_term___x21_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x21_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 225, 231, 157, 50, 119, 29, 175)}};
static const lean_object* l_term___x21_x3d___00__closed__1 = (const lean_object*)&l_term___x21_x3d___00__closed__1_value;
static const lean_string_object l_term___x21_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " != "};
static const lean_object* l_term___x21_x3d___00__closed__2 = (const lean_object*)&l_term___x21_x3d___00__closed__2_value;
static const lean_ctor_object l_term___x21_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___x21_x3d___00__closed__2_value)}};
static const lean_object* l_term___x21_x3d___00__closed__3 = (const lean_object*)&l_term___x21_x3d___00__closed__3_value;
static const lean_ctor_object l_term___x21_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___x21_x3d___00__closed__3_value),((lean_object*)&l_term___u2248___00__closed__4_value)}};
static const lean_object* l_term___x21_x3d___00__closed__4 = (const lean_object*)&l_term___x21_x3d___00__closed__4_value;
static const lean_ctor_object l_term___x21_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___x21_x3d___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_term___x21_x3d___00__closed__4_value)}};
static const lean_object* l_term___x21_x3d___00__closed__5 = (const lean_object*)&l_term___x21_x3d___00__closed__5_value;
LEAN_EXPORT const lean_object* l_term___x21_x3d__ = (const lean_object*)&l_term___x21_x3d___00__closed__5_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bne"};
static const lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 187, 84, 23, 255, 12, 25, 13)}};
static const lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__bne__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__bne__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "binrel_no_prop"};
static const lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__0_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value_aux_1),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value_aux_2),((lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 122, 90, 92, 171, 187, 176, 37)}};
static const lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "binrel_no_prop%"};
static const lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__2_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqOfLawfulBEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___u2260___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≠_"};
static const lean_object* l_term___u2260___00__closed__0 = (const lean_object*)&l_term___u2260___00__closed__0_value;
static const lean_ctor_object l_term___u2260___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___u2260___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 22, 203, 44, 60, 124, 87, 95)}};
static const lean_object* l_term___u2260___00__closed__1 = (const lean_object*)&l_term___u2260___00__closed__1_value;
static const lean_string_object l_term___u2260___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≠ "};
static const lean_object* l_term___u2260___00__closed__2 = (const lean_object*)&l_term___u2260___00__closed__2_value;
static const lean_ctor_object l_term___u2260___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___u2260___00__closed__2_value)}};
static const lean_object* l_term___u2260___00__closed__3 = (const lean_object*)&l_term___u2260___00__closed__3_value;
static const lean_ctor_object l_term___u2260___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x2d_x3e___00__closed__3_value),((lean_object*)&l_term___u2260___00__closed__3_value),((lean_object*)&l_term___u2248___00__closed__4_value)}};
static const lean_object* l_term___u2260___00__closed__4 = (const lean_object*)&l_term___u2260___00__closed__4_value;
static const lean_ctor_object l_term___u2260___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___u2260___00__closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_term___u2260___00__closed__4_value)}};
static const lean_object* l_term___u2260___00__closed__5 = (const lean_object*)&l_term___u2260___00__closed__5_value;
LEAN_EXPORT const lean_object* l_term___u2260__ = (const lean_object*)&l_term___u2260___00__closed__5_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2260____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2260____1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2260____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__term___u2260____1___closed__1;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2260____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___u2260____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2260____1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2260____1___closed__2_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2260____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2260____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2260____1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2260____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2260____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2260____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2260____1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2260____1___closed__4_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Ne__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Ne__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__Core______macroRules__term___u2260____2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binrel"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2260____2___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2260____2___closed__0_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value_aux_1),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value_aux_2),((lean_object*)&l___aux__Init__Core______macroRules__term___u2260____2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 238, 75, 93, 70, 164, 233, 165)}};
static const lean_object* l___aux__Init__Core______macroRules__term___u2260____2___closed__1 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2260____2___closed__1_value;
static const lean_string_object l___aux__Init__Core______macroRules__term___u2260____2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "binrel%"};
static const lean_object* l___aux__Init__Core______macroRules__term___u2260____2___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__term___u2260____2___closed__2_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__0 = (const lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__0_value;
static const lean_string_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__1 = (const lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__1_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value_aux_1),((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value_aux_2),((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2 = (const lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2_value;
static const lean_string_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3 = (const lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4 = (const lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4_value;
static const lean_string_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Iff.rfl"};
static const lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__5 = (const lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__5_value;
static lean_once_cell_t l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6;
static const lean_string_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__7 = (const lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__7_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8_value_aux_0),((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(197, 85, 193, 93, 217, 248, 54, 49)}};
static const lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8 = (const lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__9 = (const lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__9_value;
static const lean_ctor_object l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__10 = (const lean_object*)&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__10_value;
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instTransIff;
LEAN_EXPORT uint8_t l_toBoolUsing___redArg(uint8_t);
LEAN_EXPORT lean_object* l_toBoolUsing___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_toBoolUsing(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_toBoolUsing___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableTrue;
LEAN_EXPORT uint8_t l_instDecidableFalse;
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__iff___redArg(uint8_t);
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__iff___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__iff(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__iff___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__eq___redArg(uint8_t);
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__eq___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__eq(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__eq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableIff___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instDecidableIff___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableIff(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instDecidableIff___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_iteInduction___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_iteInduction___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_iteInduction(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_iteInduction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableDite___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableDite___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableDite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableDite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_noConfusionEnum___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_noConfusionEnum___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_noConfusionEnum___redArg___closed__0 = (const lean_object*)&l_noConfusionEnum___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_noConfusionEnum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedProp;
LEAN_EXPORT lean_object* l_instInhabitedNonScalar_default;
LEAN_EXPORT lean_object* l_instInhabitedNonScalar;
LEAN_EXPORT lean_object* l_instInhabitedPNonScalar_default;
LEAN_EXPORT lean_object* l_instInhabitedPNonScalar;
LEAN_EXPORT lean_object* l_instInhabitedTrue;
LEAN_EXPORT uint8_t l_Subtype_instBEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instBEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instBEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Subtype_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Subtype_instDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_inhabitedLeft___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Sum_inhabitedLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_inhabitedRight___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Sum_inhabitedRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqSum_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqSum_decEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqSum_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqSum___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqSum___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqSum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedMProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedMProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedPProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedPProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqProd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqProd___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Prod_lexLtDec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_lexLtDec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Prod_lexLtDec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_lexLtDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_map___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqSigma___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqSigma___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqSigma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqSigma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqPSigma___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqPSigma___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqPSigma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqPSigma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedPUnit;
LEAN_EXPORT uint8_t l_instDecidableEqPUnit___redArg();
LEAN_EXPORT lean_object* l_instDecidableEqPUnit___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqPUnit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid___redArg();
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqOfIff___redArg(uint8_t);
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqOfIff(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Not_elim___redArg();
LEAN_EXPORT lean_object* l_Not_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Not_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_And_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_And_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Iff_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Iff_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quot_rec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quot_rec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quot_recOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quot_recOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quot_recOnSubsingleton___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quot_recOnSubsingleton(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quot_hrecOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quot_hrecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Quotient_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Quotient_mk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_mk_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Quotient_mk_x27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Quotient_mk_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_mk_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_liftOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_liftOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_rec___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_rec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_recOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_recOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_hrecOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_hrecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_lift_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_lift_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_liftOn_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_liftOn_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Quotient_decidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_decidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Quotient_decidableEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_decidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quot_pliftOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quot_pliftOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_pliftOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quotient_pliftOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Setoid_trivial___redArg();
LEAN_EXPORT lean_object* l_Setoid_trivial___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Setoid_trivial(lean_object*);
LEAN_EXPORT lean_object* l_Squash_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Squash_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Squash_mk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Squash_mk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Squash_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Squash_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_opaqueId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_opaqueId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_opaqueId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_opaqueId___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___redArg(lean_object* v_inst_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_dec_ref(v_inst_1_);
if (lean_obj_tag(v_x_3_) == 0)
{
uint8_t v___x_4_; 
v___x_4_ = 1;
return v___x_4_;
}
else
{
uint8_t v___x_5_; 
lean_dec_ref_known(v_x_3_, 1);
v___x_5_ = 0;
return v___x_5_;
}
}
else
{
if (lean_obj_tag(v_x_3_) == 0)
{
uint8_t v___x_6_; 
lean_dec_ref_known(v_x_2_, 1);
lean_dec_ref(v_inst_1_);
v___x_6_ = 0;
return v___x_6_;
}
else
{
lean_object* v_val_7_; lean_object* v_val_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_val_7_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v_x_2_, 1);
v_val_8_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v_x_3_, 1);
v___x_9_ = lean_apply_2(v_inst_1_, v_val_7_, v_val_8_);
v___x_10_ = lean_unbox(v___x_9_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___redArg___boxed(lean_object* v_inst_11_, lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_instBEqOption_beq___redArg(v_inst_11_, v_x_12_, v_x_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq(lean_object* v_00_u03b1_16_, lean_object* v_inst_17_, lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = l_instBEqOption_beq___redArg(v_inst_17_, v_x_18_, v_x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___boxed(lean_object* v_00_u03b1_21_, lean_object* v_inst_22_, lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_instBEqOption_beq(v_00_u03b1_21_, v_inst_22_, v_x_23_, v_x_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* l_instBEqOption___redArg(lean_object* v_inst_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_alloc_closure((void*)(l_instBEqOption_beq___boxed), 4, 2);
lean_closure_set(v___x_28_, 0, lean_box(0));
lean_closure_set(v___x_28_, 1, v_inst_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_instBEqOption(lean_object* v_00_u03b1_29_, lean_object* v_inst_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_alloc_closure((void*)(l_instBEqOption_beq___boxed), 4, 2);
lean_closure_set(v___x_31_, 0, lean_box(0));
lean_closure_set(v___x_31_, 1, v_inst_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_inline___redArg(lean_object* v_a_32_){
_start:
{
lean_inc(v_a_32_);
return v_a_32_;
}
}
LEAN_EXPORT lean_object* l_inline___redArg___boxed(lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_inline___redArg(v_a_33_);
lean_dec(v_a_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_inline(lean_object* v_00_u03b1_35_, lean_object* v_a_36_){
_start:
{
lean_inc(v_a_36_);
return v_a_36_;
}
}
LEAN_EXPORT lean_object* l_inline___boxed(lean_object* v_00_u03b1_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_inline(v_00_u03b1_37_, v_a_38_);
lean_dec(v_a_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_eagerReduce___redArg(lean_object* v_a_40_){
_start:
{
lean_inc(v_a_40_);
return v_a_40_;
}
}
LEAN_EXPORT lean_object* l_eagerReduce___redArg___boxed(lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_eagerReduce___redArg(v_a_41_);
lean_dec(v_a_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_eagerReduce(lean_object* v_00_u03b1_43_, lean_object* v_a_44_){
_start:
{
lean_inc(v_a_44_);
return v_a_44_;
}
}
LEAN_EXPORT lean_object* l_eagerReduce___boxed(lean_object* v_00_u03b1_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_eagerReduce(v_00_u03b1_45_, v_a_46_);
lean_dec(v_a_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_flip___redArg(lean_object* v_f_48_, lean_object* v_b_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_apply_2(v_f_48_, v_a_50_, v_b_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_flip(lean_object* v_00_u03b1_52_, lean_object* v_00_u03b2_53_, lean_object* v_00_u03c6_54_, lean_object* v_f_55_, lean_object* v_b_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_apply_2(v_f_55_, v_a_57_, v_b_56_);
return v___x_58_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqEmpty___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_instDecidableEqEmpty___redArg___boxed(lean_object* v___dummy_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_instDecidableEqEmpty___redArg();
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqEmpty(uint8_t v_a_63_, uint8_t v_b_64_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_instDecidableEqEmpty___boxed(lean_object* v_a_65_, lean_object* v_b_66_){
_start:
{
uint8_t v_a_boxed_67_; uint8_t v_b_boxed_68_; uint8_t v_res_69_; lean_object* v_r_70_; 
v_a_boxed_67_ = lean_unbox(v_a_65_);
v_b_boxed_68_ = lean_unbox(v_b_66_);
v_res_69_ = l_instDecidableEqEmpty(v_a_boxed_67_, v_b_boxed_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPEmpty___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPEmpty___redArg___boxed(lean_object* v___dummy_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_instDecidableEqPEmpty___redArg();
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPEmpty(uint8_t v_a_75_, uint8_t v_b_76_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPEmpty___boxed(lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
uint8_t v_a_boxed_79_; uint8_t v_b_boxed_80_; uint8_t v_res_81_; lean_object* v_r_82_; 
v_a_boxed_79_ = lean_unbox(v_a_77_);
v_b_boxed_80_ = lean_unbox(v_b_78_);
v_res_81_ = l_instDecidableEqPEmpty(v_a_boxed_79_, v_b_boxed_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT lean_object* l_Thunk_mk___boxed(lean_object* v_00_u03b1_85_, lean_object* v_fn_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lean_mk_thunk(v_fn_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Thunk_pure___boxed(lean_object* v_00_u03b1_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = lean_thunk_pure(v_a_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Thunk_get___boxed(lean_object* v_00_u03b1_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lean_thunk_get_own(v_x_96_);
lean_dec_ref(v_x_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Thunk_fnImpl___redArg(lean_object* v_x_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_thunk_get_own(v_x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Thunk_fnImpl___redArg___boxed(lean_object* v_x_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Thunk_fnImpl___redArg(v_x_100_);
lean_dec_ref(v_x_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Thunk_fnImpl(lean_object* v_00_u03b1_102_, lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_thunk_get_own(v_x_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Thunk_fnImpl___boxed(lean_object* v_00_u03b1_106_, lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Thunk_fnImpl(v_00_u03b1_106_, v_x_107_, v_x_108_);
lean_dec_ref(v_x_107_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Thunk_map___redArg___lam__0(lean_object* v_x_110_, lean_object* v_f_111_, lean_object* v_x_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_thunk_get_own(v_x_110_);
v___x_114_ = lean_apply_1(v_f_111_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Thunk_map___redArg___lam__0___boxed(lean_object* v_x_115_, lean_object* v_f_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Thunk_map___redArg___lam__0(v_x_115_, v_f_116_, v_x_117_);
lean_dec_ref(v_x_115_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Thunk_map___redArg(lean_object* v_f_119_, lean_object* v_x_120_){
_start:
{
lean_object* v___f_121_; lean_object* v___x_122_; 
v___f_121_ = lean_alloc_closure((void*)(l_Thunk_map___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_121_, 0, v_x_120_);
lean_closure_set(v___f_121_, 1, v_f_119_);
v___x_122_ = lean_mk_thunk(v___f_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Thunk_map(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_f_125_, lean_object* v_x_126_){
_start:
{
lean_object* v___f_127_; lean_object* v___x_128_; 
v___f_127_ = lean_alloc_closure((void*)(l_Thunk_map___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_127_, 0, v_x_126_);
lean_closure_set(v___f_127_, 1, v_f_125_);
v___x_128_ = lean_mk_thunk(v___f_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Thunk_bind___redArg___lam__0(lean_object* v_x_129_, lean_object* v_f_130_, lean_object* v_x_131_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_thunk_get_own(v_x_129_);
v___x_133_ = lean_apply_1(v_f_130_, v___x_132_);
v___x_134_ = lean_thunk_get_own(v___x_133_);
lean_dec_ref(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Thunk_bind___redArg___lam__0___boxed(lean_object* v_x_135_, lean_object* v_f_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Thunk_bind___redArg___lam__0(v_x_135_, v_f_136_, v_x_137_);
lean_dec_ref(v_x_135_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Thunk_bind___redArg(lean_object* v_x_139_, lean_object* v_f_140_){
_start:
{
lean_object* v___f_141_; lean_object* v___x_142_; 
v___f_141_ = lean_alloc_closure((void*)(l_Thunk_bind___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_141_, 0, v_x_139_);
lean_closure_set(v___f_141_, 1, v_f_140_);
v___x_142_ = lean_mk_thunk(v___f_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Thunk_bind(lean_object* v_00_u03b1_143_, lean_object* v_00_u03b2_144_, lean_object* v_x_145_, lean_object* v_f_146_){
_start:
{
lean_object* v___f_147_; lean_object* v___x_148_; 
v___f_147_ = lean_alloc_closure((void*)(l_Thunk_bind___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_147_, 0, v_x_145_);
lean_closure_set(v___f_147_, 1, v_f_146_);
v___x_148_ = lean_mk_thunk(v___f_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe___redArg___lam__0(lean_object* v_a_149_, lean_object* v_x_150_){
_start:
{
lean_inc(v_a_149_);
return v_a_149_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe___redArg___lam__0___boxed(lean_object* v_a_151_, lean_object* v_x_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_thunkCoe___redArg___lam__0(v_a_151_, v_x_152_);
lean_dec(v_a_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe___redArg___lam__1(lean_object* v_a_154_){
_start:
{
lean_object* v___f_155_; lean_object* v___x_156_; 
v___f_155_ = lean_alloc_closure((void*)(l_thunkCoe___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_155_, 0, v_a_154_);
v___x_156_ = lean_mk_thunk(v___f_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe___redArg(){
_start:
{
lean_object* v___f_159_; 
v___f_159_ = ((lean_object*)(l_thunkCoe___redArg___closed__0));
return v___f_159_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe___redArg___boxed(lean_object* v___dummy_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_thunkCoe___redArg();
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe(lean_object* v_00_u03b1_162_){
_start:
{
lean_object* v___f_163_; 
v___f_163_ = ((lean_object*)(l_thunkCoe___redArg___closed__0));
return v___f_163_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedThunk___redArg(lean_object* v_inst_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_thunk_pure(v_inst_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedThunk(lean_object* v_00_u03b1_166_, lean_object* v_inst_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_thunk_pure(v_inst_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn___redArg(lean_object* v_m_169_){
_start:
{
lean_inc(v_m_169_);
return v_m_169_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn___redArg___boxed(lean_object* v_m_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Eq_ndrecOn___redArg(v_m_170_);
lean_dec(v_m_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn(lean_object* v_00_u03b1_172_, lean_object* v_a_173_, lean_object* v_motive_174_, lean_object* v_b_175_, lean_object* v_h_176_, lean_object* v_m_177_){
_start:
{
lean_inc(v_m_177_);
return v_m_177_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn___boxed(lean_object* v_00_u03b1_178_, lean_object* v_a_179_, lean_object* v_motive_180_, lean_object* v_b_181_, lean_object* v_h_182_, lean_object* v_m_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Eq_ndrecOn(v_00_u03b1_178_, v_a_179_, v_motive_180_, v_b_181_, v_h_182_, v_m_183_);
lean_dec(v_m_183_);
lean_dec(v_b_181_);
lean_dec(v_a_179_);
return v_res_184_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5));
v___x_221_ = l_String_toRawSubstring_x27(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1(lean_object* v_x_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = ((lean_object*)(l_term___x3c_x2d_x3e___00__closed__1));
lean_inc(v_x_238_);
v___x_242_ = l_Lean_Syntax_isOfKind(v_x_238_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec(v_x_238_);
v___x_243_ = lean_box(1);
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v_a_240_);
return v___x_244_;
}
else
{
lean_object* v_quotContext_245_; lean_object* v_currMacroScope_246_; lean_object* v_ref_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_quotContext_245_ = lean_ctor_get(v_a_239_, 1);
v_currMacroScope_246_ = lean_ctor_get(v_a_239_, 2);
v_ref_247_ = lean_ctor_get(v_a_239_, 5);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = l_Lean_Syntax_getArg(v_x_238_, v___x_248_);
v___x_250_ = lean_unsigned_to_nat(2u);
v___x_251_ = l_Lean_Syntax_getArg(v_x_238_, v___x_250_);
lean_dec(v_x_238_);
v___x_252_ = 0;
v___x_253_ = l_Lean_SourceInfo_fromRef(v_ref_247_, v___x_252_);
v___x_254_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_255_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6, &l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6_once, _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6);
v___x_256_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7));
lean_inc(v_currMacroScope_246_);
lean_inc(v_quotContext_245_);
v___x_257_ = l_Lean_addMacroScope(v_quotContext_245_, v___x_256_, v_currMacroScope_246_);
v___x_258_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11));
lean_inc_n(v___x_253_, 2);
v___x_259_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_259_, 0, v___x_253_);
lean_ctor_set(v___x_259_, 1, v___x_255_);
lean_ctor_set(v___x_259_, 2, v___x_257_);
lean_ctor_set(v___x_259_, 3, v___x_258_);
v___x_260_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_261_ = l_Lean_Syntax_node2(v___x_253_, v___x_260_, v___x_249_, v___x_251_);
v___x_262_ = l_Lean_Syntax_node2(v___x_253_, v___x_254_, v___x_259_, v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_a_240_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___boxed(lean_object* v_x_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1(v_x_264_, v_a_265_, v_a_266_);
lean_dec_ref(v_a_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__1(lean_object* v_x_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_271_);
v___x_275_ = l_Lean_Syntax_isOfKind(v_x_271_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v_x_271_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_a_273_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = l_Lean_Syntax_getArg(v_x_271_, v___x_278_);
v___x_280_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_279_);
v___x_281_ = l_Lean_Syntax_isOfKind(v___x_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v___x_279_);
lean_dec(v_x_271_);
v___x_282_ = lean_box(0);
v___x_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_a_273_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = l_Lean_Syntax_getArg(v_x_271_, v___x_284_);
lean_dec(v_x_271_);
v___x_286_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_285_);
v___x_287_ = l_Lean_Syntax_matchesNull(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec(v___x_285_);
lean_dec(v___x_279_);
v___x_288_ = lean_box(0);
v___x_289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v_a_273_);
return v___x_289_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_ref_292_; uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_290_ = l_Lean_Syntax_getArg(v___x_285_, v___x_278_);
v___x_291_ = l_Lean_Syntax_getArg(v___x_285_, v___x_284_);
lean_dec(v___x_285_);
v_ref_292_ = l_Lean_replaceRef(v___x_279_, v_a_272_);
lean_dec(v___x_279_);
v___x_293_ = 0;
v___x_294_ = l_Lean_SourceInfo_fromRef(v_ref_292_, v___x_293_);
lean_dec(v_ref_292_);
v___x_295_ = ((lean_object*)(l_term___x3c_x2d_x3e___00__closed__1));
v___x_296_ = ((lean_object*)(l_term___x3c_x2d_x3e___00__closed__4));
lean_inc(v___x_294_);
v___x_297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_294_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Lean_Syntax_node3(v___x_294_, v___x_295_, v___x_290_, v___x_297_, v___x_291_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_a_273_);
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__1___boxed(lean_object* v_x_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___aux__Init__Core______unexpand__Iff__1(v_x_300_, v_a_301_, v_a_302_);
lean_dec(v_a_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2194____1(lean_object* v_x_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = ((lean_object*)(l_term___u2194___00__closed__1));
lean_inc(v_x_320_);
v___x_324_ = l_Lean_Syntax_isOfKind(v_x_320_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec(v_x_320_);
v___x_325_ = lean_box(1);
v___x_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v_a_322_);
return v___x_326_;
}
else
{
lean_object* v_quotContext_327_; lean_object* v_currMacroScope_328_; lean_object* v_ref_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_quotContext_327_ = lean_ctor_get(v_a_321_, 1);
v_currMacroScope_328_ = lean_ctor_get(v_a_321_, 2);
v_ref_329_ = lean_ctor_get(v_a_321_, 5);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = l_Lean_Syntax_getArg(v_x_320_, v___x_330_);
v___x_332_ = lean_unsigned_to_nat(2u);
v___x_333_ = l_Lean_Syntax_getArg(v_x_320_, v___x_332_);
lean_dec(v_x_320_);
v___x_334_ = 0;
v___x_335_ = l_Lean_SourceInfo_fromRef(v_ref_329_, v___x_334_);
v___x_336_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_337_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6, &l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6_once, _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6);
v___x_338_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7));
lean_inc(v_currMacroScope_328_);
lean_inc(v_quotContext_327_);
v___x_339_ = l_Lean_addMacroScope(v_quotContext_327_, v___x_338_, v_currMacroScope_328_);
v___x_340_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11));
lean_inc_n(v___x_335_, 2);
v___x_341_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_341_, 0, v___x_335_);
lean_ctor_set(v___x_341_, 1, v___x_337_);
lean_ctor_set(v___x_341_, 2, v___x_339_);
lean_ctor_set(v___x_341_, 3, v___x_340_);
v___x_342_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_343_ = l_Lean_Syntax_node2(v___x_335_, v___x_342_, v___x_331_, v___x_333_);
v___x_344_ = l_Lean_Syntax_node2(v___x_335_, v___x_336_, v___x_341_, v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_a_322_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2194____1___boxed(lean_object* v_x_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___aux__Init__Core______macroRules__term___u2194____1(v_x_346_, v_a_347_, v_a_348_);
lean_dec_ref(v_a_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__2(lean_object* v_x_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_350_);
v___x_354_ = l_Lean_Syntax_isOfKind(v_x_350_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v_x_350_);
v___x_355_ = lean_box(0);
v___x_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_a_352_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = l_Lean_Syntax_getArg(v_x_350_, v___x_357_);
v___x_359_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_358_);
v___x_360_ = l_Lean_Syntax_isOfKind(v___x_358_, v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec(v___x_358_);
lean_dec(v_x_350_);
v___x_361_ = lean_box(0);
v___x_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v_a_352_);
return v___x_362_;
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = l_Lean_Syntax_getArg(v_x_350_, v___x_363_);
lean_dec(v_x_350_);
v___x_365_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_364_);
v___x_366_ = l_Lean_Syntax_matchesNull(v___x_364_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec(v___x_364_);
lean_dec(v___x_358_);
v___x_367_ = lean_box(0);
v___x_368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v_a_352_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_ref_371_; uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_369_ = l_Lean_Syntax_getArg(v___x_364_, v___x_357_);
v___x_370_ = l_Lean_Syntax_getArg(v___x_364_, v___x_363_);
lean_dec(v___x_364_);
v_ref_371_ = l_Lean_replaceRef(v___x_358_, v_a_351_);
lean_dec(v___x_358_);
v___x_372_ = 0;
v___x_373_ = l_Lean_SourceInfo_fromRef(v_ref_371_, v___x_372_);
lean_dec(v_ref_371_);
v___x_374_ = ((lean_object*)(l_term___u2194___00__closed__1));
v___x_375_ = ((lean_object*)(l_term___u2194___00__closed__2));
lean_inc(v___x_373_);
v___x_376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_373_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = l_Lean_Syntax_node3(v___x_373_, v___x_374_, v___x_369_, v___x_376_, v___x_370_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v_a_352_);
return v___x_378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__2___boxed(lean_object* v_x_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___aux__Init__Core______unexpand__Iff__2(v_x_379_, v_a_380_, v_a_381_);
lean_dec(v_a_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___redArg(lean_object* v_x_383_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
lean_object* v___x_384_; 
v___x_384_ = lean_unsigned_to_nat(0u);
return v___x_384_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_unsigned_to_nat(1u);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___redArg___boxed(lean_object* v_x_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Sum_ctorIdx___redArg(v_x_386_);
lean_dec_ref(v_x_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_x_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Sum_ctorIdx___redArg(v_x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___boxed(lean_object* v_00_u03b1_392_, lean_object* v_00_u03b2_393_, lean_object* v_x_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Sum_ctorIdx(v_00_u03b1_392_, v_00_u03b2_393_, v_x_394_);
lean_dec_ref(v_x_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim___redArg(lean_object* v_t_396_, lean_object* v_k_397_){
_start:
{
lean_object* v_val_398_; lean_object* v___x_399_; 
v_val_398_ = lean_ctor_get(v_t_396_, 0);
lean_inc(v_val_398_);
lean_dec_ref(v_t_396_);
v___x_399_ = lean_apply_1(v_k_397_, v_val_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim(lean_object* v_00_u03b1_400_, lean_object* v_00_u03b2_401_, lean_object* v_motive_402_, lean_object* v_ctorIdx_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_k_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Sum_ctorElim___redArg(v_t_404_, v_k_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim___boxed(lean_object* v_00_u03b1_408_, lean_object* v_00_u03b2_409_, lean_object* v_motive_410_, lean_object* v_ctorIdx_411_, lean_object* v_t_412_, lean_object* v_h_413_, lean_object* v_k_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Sum_ctorElim(v_00_u03b1_408_, v_00_u03b2_409_, v_motive_410_, v_ctorIdx_411_, v_t_412_, v_h_413_, v_k_414_);
lean_dec(v_ctorIdx_411_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Sum_inl_elim___redArg(lean_object* v_t_416_, lean_object* v_inl_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Sum_ctorElim___redArg(v_t_416_, v_inl_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Sum_inl_elim(lean_object* v_00_u03b1_419_, lean_object* v_00_u03b2_420_, lean_object* v_motive_421_, lean_object* v_t_422_, lean_object* v_h_423_, lean_object* v_inl_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Sum_ctorElim___redArg(v_t_422_, v_inl_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Sum_inr_elim___redArg(lean_object* v_t_426_, lean_object* v_inr_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Sum_ctorElim___redArg(v_t_426_, v_inr_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Sum_inr_elim(lean_object* v_00_u03b1_429_, lean_object* v_00_u03b2_430_, lean_object* v_motive_431_, lean_object* v_t_432_, lean_object* v_h_433_, lean_object* v_inr_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Sum_ctorElim___redArg(v_t_432_, v_inr_434_);
return v___x_435_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2295____1___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__0));
v___x_457_ = l_String_toRawSubstring_x27(v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295____1(lean_object* v_x_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = ((lean_object*)(l_term___u2295___00__closed__1));
lean_inc(v_x_471_);
v___x_475_ = l_Lean_Syntax_isOfKind(v_x_471_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec(v_x_471_);
v___x_476_ = lean_box(1);
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v_a_473_);
return v___x_477_;
}
else
{
lean_object* v_quotContext_478_; lean_object* v_currMacroScope_479_; lean_object* v_ref_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_quotContext_478_ = lean_ctor_get(v_a_472_, 1);
v_currMacroScope_479_ = lean_ctor_get(v_a_472_, 2);
v_ref_480_ = lean_ctor_get(v_a_472_, 5);
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = l_Lean_Syntax_getArg(v_x_471_, v___x_481_);
v___x_483_ = lean_unsigned_to_nat(2u);
v___x_484_ = l_Lean_Syntax_getArg(v_x_471_, v___x_483_);
lean_dec(v_x_471_);
v___x_485_ = 0;
v___x_486_ = l_Lean_SourceInfo_fromRef(v_ref_480_, v___x_485_);
v___x_487_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_488_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2295____1___closed__1, &l___aux__Init__Core______macroRules__term___u2295____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2295____1___closed__1);
v___x_489_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__2));
lean_inc(v_currMacroScope_479_);
lean_inc(v_quotContext_478_);
v___x_490_ = l_Lean_addMacroScope(v_quotContext_478_, v___x_489_, v_currMacroScope_479_);
v___x_491_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__6));
lean_inc_n(v___x_486_, 2);
v___x_492_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_492_, 0, v___x_486_);
lean_ctor_set(v___x_492_, 1, v___x_488_);
lean_ctor_set(v___x_492_, 2, v___x_490_);
lean_ctor_set(v___x_492_, 3, v___x_491_);
v___x_493_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_494_ = l_Lean_Syntax_node2(v___x_486_, v___x_493_, v___x_482_, v___x_484_);
v___x_495_ = l_Lean_Syntax_node2(v___x_486_, v___x_487_, v___x_492_, v___x_494_);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v_a_473_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295____1___boxed(lean_object* v_x_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___aux__Init__Core______macroRules__term___u2295____1(v_x_497_, v_a_498_, v_a_499_);
lean_dec_ref(v_a_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Sum__1(lean_object* v_x_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_501_);
v___x_505_ = l_Lean_Syntax_isOfKind(v_x_501_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v_x_501_);
v___x_506_ = lean_box(0);
v___x_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_a_503_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = l_Lean_Syntax_getArg(v_x_501_, v___x_508_);
v___x_510_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_509_);
v___x_511_ = l_Lean_Syntax_isOfKind(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v___x_509_);
lean_dec(v_x_501_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v_a_503_);
return v___x_513_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = l_Lean_Syntax_getArg(v_x_501_, v___x_514_);
lean_dec(v_x_501_);
v___x_516_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_515_);
v___x_517_ = l_Lean_Syntax_matchesNull(v___x_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec(v___x_515_);
lean_dec(v___x_509_);
v___x_518_ = lean_box(0);
v___x_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v_a_503_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_ref_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_520_ = l_Lean_Syntax_getArg(v___x_515_, v___x_508_);
v___x_521_ = l_Lean_Syntax_getArg(v___x_515_, v___x_514_);
lean_dec(v___x_515_);
v_ref_522_ = l_Lean_replaceRef(v___x_509_, v_a_502_);
lean_dec(v___x_509_);
v___x_523_ = 0;
v___x_524_ = l_Lean_SourceInfo_fromRef(v_ref_522_, v___x_523_);
lean_dec(v_ref_522_);
v___x_525_ = ((lean_object*)(l_term___u2295___00__closed__1));
v___x_526_ = ((lean_object*)(l_term___u2295___00__closed__2));
lean_inc(v___x_524_);
v___x_527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_524_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_Syntax_node3(v___x_524_, v___x_525_, v___x_520_, v___x_527_, v___x_521_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v_a_503_);
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Sum__1___boxed(lean_object* v_x_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___aux__Init__Core______unexpand__Sum__1(v_x_530_, v_a_531_, v_a_532_);
lean_dec(v_a_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___redArg(lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
lean_object* v___x_535_; 
v___x_535_ = lean_unsigned_to_nat(0u);
return v___x_535_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = lean_unsigned_to_nat(1u);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___redArg___boxed(lean_object* v_x_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_PSum_ctorIdx___redArg(v_x_537_);
lean_dec_ref(v_x_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx(lean_object* v_00_u03b1_539_, lean_object* v_00_u03b2_540_, lean_object* v_x_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_PSum_ctorIdx___redArg(v_x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___boxed(lean_object* v_00_u03b1_543_, lean_object* v_00_u03b2_544_, lean_object* v_x_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_PSum_ctorIdx(v_00_u03b1_543_, v_00_u03b2_544_, v_x_545_);
lean_dec_ref(v_x_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim___redArg(lean_object* v_t_547_, lean_object* v_k_548_){
_start:
{
lean_object* v_val_549_; lean_object* v___x_550_; 
v_val_549_ = lean_ctor_get(v_t_547_, 0);
lean_inc(v_val_549_);
lean_dec_ref(v_t_547_);
v___x_550_ = lean_apply_1(v_k_548_, v_val_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim(lean_object* v_00_u03b1_551_, lean_object* v_00_u03b2_552_, lean_object* v_motive_553_, lean_object* v_ctorIdx_554_, lean_object* v_t_555_, lean_object* v_h_556_, lean_object* v_k_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_PSum_ctorElim___redArg(v_t_555_, v_k_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim___boxed(lean_object* v_00_u03b1_559_, lean_object* v_00_u03b2_560_, lean_object* v_motive_561_, lean_object* v_ctorIdx_562_, lean_object* v_t_563_, lean_object* v_h_564_, lean_object* v_k_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_PSum_ctorElim(v_00_u03b1_559_, v_00_u03b2_560_, v_motive_561_, v_ctorIdx_562_, v_t_563_, v_h_564_, v_k_565_);
lean_dec(v_ctorIdx_562_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_PSum_inl_elim___redArg(lean_object* v_t_567_, lean_object* v_inl_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_PSum_ctorElim___redArg(v_t_567_, v_inl_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_PSum_inl_elim(lean_object* v_00_u03b1_570_, lean_object* v_00_u03b2_571_, lean_object* v_motive_572_, lean_object* v_t_573_, lean_object* v_h_574_, lean_object* v_inl_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_PSum_ctorElim___redArg(v_t_573_, v_inl_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_PSum_inr_elim___redArg(lean_object* v_t_577_, lean_object* v_inr_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_PSum_ctorElim___redArg(v_t_577_, v_inr_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_PSum_inr_elim(lean_object* v_00_u03b1_580_, lean_object* v_00_u03b2_581_, lean_object* v_motive_582_, lean_object* v_t_583_, lean_object* v_h_584_, lean_object* v_inr_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_PSum_ctorElim___redArg(v_t_583_, v_inr_585_);
return v___x_586_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0));
v___x_605_ = l_String_toRawSubstring_x27(v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1(lean_object* v_x_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = ((lean_object*)(l_term___u2295_x27___00__closed__1));
lean_inc(v_x_619_);
v___x_623_ = l_Lean_Syntax_isOfKind(v_x_619_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v_x_619_);
v___x_624_ = lean_box(1);
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v_a_621_);
return v___x_625_;
}
else
{
lean_object* v_quotContext_626_; lean_object* v_currMacroScope_627_; lean_object* v_ref_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_quotContext_626_ = lean_ctor_get(v_a_620_, 1);
v_currMacroScope_627_ = lean_ctor_get(v_a_620_, 2);
v_ref_628_ = lean_ctor_get(v_a_620_, 5);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = l_Lean_Syntax_getArg(v_x_619_, v___x_629_);
v___x_631_ = lean_unsigned_to_nat(2u);
v___x_632_ = l_Lean_Syntax_getArg(v_x_619_, v___x_631_);
lean_dec(v_x_619_);
v___x_633_ = 0;
v___x_634_ = l_Lean_SourceInfo_fromRef(v_ref_628_, v___x_633_);
v___x_635_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_636_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1, &l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1);
v___x_637_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2));
lean_inc(v_currMacroScope_627_);
lean_inc(v_quotContext_626_);
v___x_638_ = l_Lean_addMacroScope(v_quotContext_626_, v___x_637_, v_currMacroScope_627_);
v___x_639_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__6));
lean_inc_n(v___x_634_, 2);
v___x_640_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_640_, 0, v___x_634_);
lean_ctor_set(v___x_640_, 1, v___x_636_);
lean_ctor_set(v___x_640_, 2, v___x_638_);
lean_ctor_set(v___x_640_, 3, v___x_639_);
v___x_641_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_642_ = l_Lean_Syntax_node2(v___x_634_, v___x_641_, v___x_630_, v___x_632_);
v___x_643_ = l_Lean_Syntax_node2(v___x_634_, v___x_635_, v___x_640_, v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v_a_621_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1___boxed(lean_object* v_x_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___aux__Init__Core______macroRules__term___u2295_x27____1(v_x_645_, v_a_646_, v_a_647_);
lean_dec_ref(v_a_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__PSum__1(lean_object* v_x_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_649_);
v___x_653_ = l_Lean_Syntax_isOfKind(v_x_649_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec(v_x_649_);
v___x_654_ = lean_box(0);
v___x_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_a_651_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = l_Lean_Syntax_getArg(v_x_649_, v___x_656_);
v___x_658_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_657_);
v___x_659_ = l_Lean_Syntax_isOfKind(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v___x_657_);
lean_dec(v_x_649_);
v___x_660_ = lean_box(0);
v___x_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v_a_651_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_662_ = lean_unsigned_to_nat(1u);
v___x_663_ = l_Lean_Syntax_getArg(v_x_649_, v___x_662_);
lean_dec(v_x_649_);
v___x_664_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_663_);
v___x_665_ = l_Lean_Syntax_matchesNull(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec(v___x_663_);
lean_dec(v___x_657_);
v___x_666_ = lean_box(0);
v___x_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v_a_651_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_ref_670_; uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_668_ = l_Lean_Syntax_getArg(v___x_663_, v___x_656_);
v___x_669_ = l_Lean_Syntax_getArg(v___x_663_, v___x_662_);
lean_dec(v___x_663_);
v_ref_670_ = l_Lean_replaceRef(v___x_657_, v_a_650_);
lean_dec(v___x_657_);
v___x_671_ = 0;
v___x_672_ = l_Lean_SourceInfo_fromRef(v_ref_670_, v___x_671_);
lean_dec(v_ref_670_);
v___x_673_ = ((lean_object*)(l_term___u2295_x27___00__closed__1));
v___x_674_ = ((lean_object*)(l_term___u2295_x27___00__closed__2));
lean_inc(v___x_672_);
v___x_675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_672_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = l_Lean_Syntax_node3(v___x_672_, v___x_673_, v___x_668_, v___x_675_, v___x_669_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v_a_651_);
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__PSum__1___boxed(lean_object* v_x_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___aux__Init__Core______unexpand__PSum__1(v_x_678_, v_a_679_, v_a_680_);
lean_dec(v_a_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedLeft___redArg(lean_object* v_inst_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v_inst_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedLeft(lean_object* v_00_u03b1_684_, lean_object* v_00_u03b2_685_, lean_object* v_inst_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v_inst_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedRight___redArg(lean_object* v_inst_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v_inst_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedRight(lean_object* v_00_u03b1_690_, lean_object* v_00_u03b2_691_, lean_object* v_inst_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v_inst_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___redArg(lean_object* v_x_694_){
_start:
{
if (lean_obj_tag(v_x_694_) == 0)
{
lean_object* v___x_695_; 
v___x_695_ = lean_unsigned_to_nat(0u);
return v___x_695_;
}
else
{
lean_object* v___x_696_; 
v___x_696_ = lean_unsigned_to_nat(1u);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___redArg___boxed(lean_object* v_x_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_ForInStep_ctorIdx___redArg(v_x_697_);
lean_dec_ref(v_x_697_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx(lean_object* v_00_u03b1_699_, lean_object* v_x_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_ForInStep_ctorIdx___redArg(v_x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___boxed(lean_object* v_00_u03b1_702_, lean_object* v_x_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_ForInStep_ctorIdx(v_00_u03b1_702_, v_x_703_);
lean_dec_ref(v_x_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim___redArg(lean_object* v_t_705_, lean_object* v_k_706_){
_start:
{
lean_object* v_a_707_; lean_object* v___x_708_; 
v_a_707_ = lean_ctor_get(v_t_705_, 0);
lean_inc(v_a_707_);
lean_dec_ref(v_t_705_);
v___x_708_ = lean_apply_1(v_k_706_, v_a_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim(lean_object* v_00_u03b1_709_, lean_object* v_motive_710_, lean_object* v_ctorIdx_711_, lean_object* v_t_712_, lean_object* v_h_713_, lean_object* v_k_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_ForInStep_ctorElim___redArg(v_t_712_, v_k_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim___boxed(lean_object* v_00_u03b1_716_, lean_object* v_motive_717_, lean_object* v_ctorIdx_718_, lean_object* v_t_719_, lean_object* v_h_720_, lean_object* v_k_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_ForInStep_ctorElim(v_00_u03b1_716_, v_motive_717_, v_ctorIdx_718_, v_t_719_, v_h_720_, v_k_721_);
lean_dec(v_ctorIdx_718_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_done_elim___redArg(lean_object* v_t_723_, lean_object* v_done_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_ForInStep_ctorElim___redArg(v_t_723_, v_done_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_done_elim(lean_object* v_00_u03b1_726_, lean_object* v_motive_727_, lean_object* v_t_728_, lean_object* v_h_729_, lean_object* v_done_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_ForInStep_ctorElim___redArg(v_t_728_, v_done_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_yield_elim___redArg(lean_object* v_t_732_, lean_object* v_yield_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_ForInStep_ctorElim___redArg(v_t_732_, v_yield_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_yield_elim(lean_object* v_00_u03b1_735_, lean_object* v_motive_736_, lean_object* v_t_737_, lean_object* v_h_738_, lean_object* v_yield_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_ForInStep_ctorElim___redArg(v_t_737_, v_yield_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep_default___redArg(lean_object* v_inst_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v_inst_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep_default(lean_object* v_00_u03b1_743_, lean_object* v_inst_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v_inst_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep___redArg(lean_object* v_inst_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v_inst_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep(lean_object* v_a_748_, lean_object* v_inst_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v_inst_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___redArg(lean_object* v_x_751_){
_start:
{
switch(lean_obj_tag(v_x_751_))
{
case 0:
{
lean_object* v___x_752_; 
v___x_752_ = lean_unsigned_to_nat(0u);
return v___x_752_;
}
case 1:
{
lean_object* v___x_753_; 
v___x_753_ = lean_unsigned_to_nat(1u);
return v___x_753_;
}
case 2:
{
lean_object* v___x_754_; 
v___x_754_ = lean_unsigned_to_nat(2u);
return v___x_754_;
}
default: 
{
lean_object* v___x_755_; 
v___x_755_ = lean_unsigned_to_nat(3u);
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___redArg___boxed(lean_object* v_x_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_DoResultPRBC_ctorIdx___redArg(v_x_756_);
lean_dec_ref(v_x_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx(lean_object* v_00_u03b1_758_, lean_object* v_00_u03b2_759_, lean_object* v_00_u03c3_760_, lean_object* v_x_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_DoResultPRBC_ctorIdx___redArg(v_x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___boxed(lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_00_u03c3_765_, lean_object* v_x_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_DoResultPRBC_ctorIdx(v_00_u03b1_763_, v_00_u03b2_764_, v_00_u03c3_765_, v_x_766_);
lean_dec_ref(v_x_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim___redArg(lean_object* v_t_768_, lean_object* v_k_769_){
_start:
{
switch(lean_obj_tag(v_t_768_))
{
case 2:
{
lean_object* v_a_770_; lean_object* v___x_771_; 
v_a_770_ = lean_ctor_get(v_t_768_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v_t_768_, 1);
v___x_771_ = lean_apply_1(v_k_769_, v_a_770_);
return v___x_771_;
}
case 3:
{
lean_object* v_a_772_; lean_object* v___x_773_; 
v_a_772_ = lean_ctor_get(v_t_768_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v_t_768_, 1);
v___x_773_ = lean_apply_1(v_k_769_, v_a_772_);
return v___x_773_;
}
default: 
{
lean_object* v_a_774_; lean_object* v_a_775_; lean_object* v___x_776_; 
v_a_774_ = lean_ctor_get(v_t_768_, 0);
lean_inc(v_a_774_);
v_a_775_ = lean_ctor_get(v_t_768_, 1);
lean_inc(v_a_775_);
lean_dec_ref(v_t_768_);
v___x_776_ = lean_apply_2(v_k_769_, v_a_774_, v_a_775_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim(lean_object* v_00_u03b1_777_, lean_object* v_00_u03b2_778_, lean_object* v_00_u03c3_779_, lean_object* v_motive_780_, lean_object* v_ctorIdx_781_, lean_object* v_t_782_, lean_object* v_h_783_, lean_object* v_k_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_DoResultPRBC_ctorElim___redArg(v_t_782_, v_k_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim___boxed(lean_object* v_00_u03b1_786_, lean_object* v_00_u03b2_787_, lean_object* v_00_u03c3_788_, lean_object* v_motive_789_, lean_object* v_ctorIdx_790_, lean_object* v_t_791_, lean_object* v_h_792_, lean_object* v_k_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_DoResultPRBC_ctorElim(v_00_u03b1_786_, v_00_u03b2_787_, v_00_u03c3_788_, v_motive_789_, v_ctorIdx_790_, v_t_791_, v_h_792_, v_k_793_);
lean_dec(v_ctorIdx_790_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_pure_elim___redArg(lean_object* v_t_795_, lean_object* v_pure_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_DoResultPRBC_ctorElim___redArg(v_t_795_, v_pure_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_pure_elim(lean_object* v_00_u03b1_798_, lean_object* v_00_u03b2_799_, lean_object* v_00_u03c3_800_, lean_object* v_motive_801_, lean_object* v_t_802_, lean_object* v_h_803_, lean_object* v_pure_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_DoResultPRBC_ctorElim___redArg(v_t_802_, v_pure_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_return_elim___redArg(lean_object* v_t_806_, lean_object* v_return_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_DoResultPRBC_ctorElim___redArg(v_t_806_, v_return_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_return_elim(lean_object* v_00_u03b1_809_, lean_object* v_00_u03b2_810_, lean_object* v_00_u03c3_811_, lean_object* v_motive_812_, lean_object* v_t_813_, lean_object* v_h_814_, lean_object* v_return_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_DoResultPRBC_ctorElim___redArg(v_t_813_, v_return_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_break_elim___redArg(lean_object* v_t_817_, lean_object* v_break_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_DoResultPRBC_ctorElim___redArg(v_t_817_, v_break_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_break_elim(lean_object* v_00_u03b1_820_, lean_object* v_00_u03b2_821_, lean_object* v_00_u03c3_822_, lean_object* v_motive_823_, lean_object* v_t_824_, lean_object* v_h_825_, lean_object* v_break_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_DoResultPRBC_ctorElim___redArg(v_t_824_, v_break_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_continue_elim___redArg(lean_object* v_t_828_, lean_object* v_continue_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_DoResultPRBC_ctorElim___redArg(v_t_828_, v_continue_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_continue_elim(lean_object* v_00_u03b1_831_, lean_object* v_00_u03b2_832_, lean_object* v_00_u03c3_833_, lean_object* v_motive_834_, lean_object* v_t_835_, lean_object* v_h_836_, lean_object* v_continue_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_DoResultPRBC_ctorElim___redArg(v_t_835_, v_continue_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___redArg(lean_object* v_x_839_){
_start:
{
if (lean_obj_tag(v_x_839_) == 0)
{
lean_object* v___x_840_; 
v___x_840_ = lean_unsigned_to_nat(0u);
return v___x_840_;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = lean_unsigned_to_nat(1u);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___redArg___boxed(lean_object* v_x_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_DoResultPR_ctorIdx___redArg(v_x_842_);
lean_dec_ref(v_x_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx(lean_object* v_00_u03b1_844_, lean_object* v_00_u03b2_845_, lean_object* v_00_u03c3_846_, lean_object* v_x_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_DoResultPR_ctorIdx___redArg(v_x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___boxed(lean_object* v_00_u03b1_849_, lean_object* v_00_u03b2_850_, lean_object* v_00_u03c3_851_, lean_object* v_x_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_DoResultPR_ctorIdx(v_00_u03b1_849_, v_00_u03b2_850_, v_00_u03c3_851_, v_x_852_);
lean_dec_ref(v_x_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___redArg(lean_object* v_t_854_, lean_object* v_k_855_){
_start:
{
lean_object* v_a_856_; lean_object* v_a_857_; lean_object* v___x_858_; 
v_a_856_ = lean_ctor_get(v_t_854_, 0);
lean_inc(v_a_856_);
v_a_857_ = lean_ctor_get(v_t_854_, 1);
lean_inc(v_a_857_);
lean_dec_ref(v_t_854_);
v___x_858_ = lean_apply_2(v_k_855_, v_a_856_, v_a_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim(lean_object* v_00_u03b1_859_, lean_object* v_00_u03b2_860_, lean_object* v_00_u03c3_861_, lean_object* v_motive_862_, lean_object* v_ctorIdx_863_, lean_object* v_t_864_, lean_object* v_h_865_, lean_object* v_k_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_DoResultPR_ctorElim___redArg(v_t_864_, v_k_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___boxed(lean_object* v_00_u03b1_868_, lean_object* v_00_u03b2_869_, lean_object* v_00_u03c3_870_, lean_object* v_motive_871_, lean_object* v_ctorIdx_872_, lean_object* v_t_873_, lean_object* v_h_874_, lean_object* v_k_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_DoResultPR_ctorElim(v_00_u03b1_868_, v_00_u03b2_869_, v_00_u03c3_870_, v_motive_871_, v_ctorIdx_872_, v_t_873_, v_h_874_, v_k_875_);
lean_dec(v_ctorIdx_872_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim___redArg(lean_object* v_t_877_, lean_object* v_pure_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_DoResultPR_ctorElim___redArg(v_t_877_, v_pure_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim(lean_object* v_00_u03b1_880_, lean_object* v_00_u03b2_881_, lean_object* v_00_u03c3_882_, lean_object* v_motive_883_, lean_object* v_t_884_, lean_object* v_h_885_, lean_object* v_pure_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_DoResultPR_ctorElim___redArg(v_t_884_, v_pure_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_return_elim___redArg(lean_object* v_t_888_, lean_object* v_return_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_DoResultPR_ctorElim___redArg(v_t_888_, v_return_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_return_elim(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_00_u03c3_893_, lean_object* v_motive_894_, lean_object* v_t_895_, lean_object* v_h_896_, lean_object* v_return_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_DoResultPR_ctorElim___redArg(v_t_895_, v_return_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___redArg(lean_object* v_x_899_){
_start:
{
if (lean_obj_tag(v_x_899_) == 0)
{
lean_object* v___x_900_; 
v___x_900_ = lean_unsigned_to_nat(0u);
return v___x_900_;
}
else
{
lean_object* v___x_901_; 
v___x_901_ = lean_unsigned_to_nat(1u);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___redArg___boxed(lean_object* v_x_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_DoResultBC_ctorIdx___redArg(v_x_902_);
lean_dec_ref(v_x_902_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx(lean_object* v_00_u03c3_904_, lean_object* v_x_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_DoResultBC_ctorIdx___redArg(v_x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___boxed(lean_object* v_00_u03c3_907_, lean_object* v_x_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_DoResultBC_ctorIdx(v_00_u03c3_907_, v_x_908_);
lean_dec_ref(v_x_908_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___redArg(lean_object* v_t_910_, lean_object* v_k_911_){
_start:
{
lean_object* v_a_912_; lean_object* v___x_913_; 
v_a_912_ = lean_ctor_get(v_t_910_, 0);
lean_inc(v_a_912_);
lean_dec_ref(v_t_910_);
v___x_913_ = lean_apply_1(v_k_911_, v_a_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim(lean_object* v_00_u03c3_914_, lean_object* v_motive_915_, lean_object* v_ctorIdx_916_, lean_object* v_t_917_, lean_object* v_h_918_, lean_object* v_k_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_DoResultBC_ctorElim___redArg(v_t_917_, v_k_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___boxed(lean_object* v_00_u03c3_921_, lean_object* v_motive_922_, lean_object* v_ctorIdx_923_, lean_object* v_t_924_, lean_object* v_h_925_, lean_object* v_k_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_DoResultBC_ctorElim(v_00_u03c3_921_, v_motive_922_, v_ctorIdx_923_, v_t_924_, v_h_925_, v_k_926_);
lean_dec(v_ctorIdx_923_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_break_elim___redArg(lean_object* v_t_928_, lean_object* v_break_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_DoResultBC_ctorElim___redArg(v_t_928_, v_break_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_break_elim(lean_object* v_00_u03c3_931_, lean_object* v_motive_932_, lean_object* v_t_933_, lean_object* v_h_934_, lean_object* v_break_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_DoResultBC_ctorElim___redArg(v_t_933_, v_break_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim___redArg(lean_object* v_t_937_, lean_object* v_continue_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_DoResultBC_ctorElim___redArg(v_t_937_, v_continue_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim(lean_object* v_00_u03c3_940_, lean_object* v_motive_941_, lean_object* v_t_942_, lean_object* v_h_943_, lean_object* v_continue_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_DoResultBC_ctorElim___redArg(v_t_942_, v_continue_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___redArg(lean_object* v_x_946_){
_start:
{
switch(lean_obj_tag(v_x_946_))
{
case 0:
{
lean_object* v___x_947_; 
v___x_947_ = lean_unsigned_to_nat(0u);
return v___x_947_;
}
case 1:
{
lean_object* v___x_948_; 
v___x_948_ = lean_unsigned_to_nat(1u);
return v___x_948_;
}
default: 
{
lean_object* v___x_949_; 
v___x_949_ = lean_unsigned_to_nat(2u);
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___redArg___boxed(lean_object* v_x_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_DoResultSBC_ctorIdx___redArg(v_x_950_);
lean_dec_ref(v_x_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx(lean_object* v_00_u03b1_952_, lean_object* v_00_u03c3_953_, lean_object* v_x_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_DoResultSBC_ctorIdx___redArg(v_x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___boxed(lean_object* v_00_u03b1_956_, lean_object* v_00_u03c3_957_, lean_object* v_x_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_DoResultSBC_ctorIdx(v_00_u03b1_956_, v_00_u03c3_957_, v_x_958_);
lean_dec_ref(v_x_958_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim___redArg(lean_object* v_t_960_, lean_object* v_k_961_){
_start:
{
if (lean_obj_tag(v_t_960_) == 0)
{
lean_object* v_a_962_; lean_object* v_a_963_; lean_object* v___x_964_; 
v_a_962_ = lean_ctor_get(v_t_960_, 0);
lean_inc(v_a_962_);
v_a_963_ = lean_ctor_get(v_t_960_, 1);
lean_inc(v_a_963_);
lean_dec_ref_known(v_t_960_, 2);
v___x_964_ = lean_apply_2(v_k_961_, v_a_962_, v_a_963_);
return v___x_964_;
}
else
{
lean_object* v_a_965_; lean_object* v___x_966_; 
v_a_965_ = lean_ctor_get(v_t_960_, 0);
lean_inc(v_a_965_);
lean_dec_ref(v_t_960_);
v___x_966_ = lean_apply_1(v_k_961_, v_a_965_);
return v___x_966_;
}
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim(lean_object* v_00_u03b1_967_, lean_object* v_00_u03c3_968_, lean_object* v_motive_969_, lean_object* v_ctorIdx_970_, lean_object* v_t_971_, lean_object* v_h_972_, lean_object* v_k_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_DoResultSBC_ctorElim___redArg(v_t_971_, v_k_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim___boxed(lean_object* v_00_u03b1_975_, lean_object* v_00_u03c3_976_, lean_object* v_motive_977_, lean_object* v_ctorIdx_978_, lean_object* v_t_979_, lean_object* v_h_980_, lean_object* v_k_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_DoResultSBC_ctorElim(v_00_u03b1_975_, v_00_u03c3_976_, v_motive_977_, v_ctorIdx_978_, v_t_979_, v_h_980_, v_k_981_);
lean_dec(v_ctorIdx_978_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_pureReturn_elim___redArg(lean_object* v_t_983_, lean_object* v_pureReturn_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_DoResultSBC_ctorElim___redArg(v_t_983_, v_pureReturn_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_pureReturn_elim(lean_object* v_00_u03b1_986_, lean_object* v_00_u03c3_987_, lean_object* v_motive_988_, lean_object* v_t_989_, lean_object* v_h_990_, lean_object* v_pureReturn_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_DoResultSBC_ctorElim___redArg(v_t_989_, v_pureReturn_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_break_elim___redArg(lean_object* v_t_993_, lean_object* v_break_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_DoResultSBC_ctorElim___redArg(v_t_993_, v_break_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_break_elim(lean_object* v_00_u03b1_996_, lean_object* v_00_u03c3_997_, lean_object* v_motive_998_, lean_object* v_t_999_, lean_object* v_h_1000_, lean_object* v_break_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_DoResultSBC_ctorElim___redArg(v_t_999_, v_break_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_continue_elim___redArg(lean_object* v_t_1003_, lean_object* v_continue_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_DoResultSBC_ctorElim___redArg(v_t_1003_, v_continue_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_continue_elim(lean_object* v_00_u03b1_1006_, lean_object* v_00_u03c3_1007_, lean_object* v_motive_1008_, lean_object* v_t_1009_, lean_object* v_h_1010_, lean_object* v_continue_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_DoResultSBC_ctorElim___redArg(v_t_1009_, v_continue_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2248____1___closed__1(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2248____1___closed__0));
v___x_1034_ = l_String_toRawSubstring_x27(v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2248____1(lean_object* v_x_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = ((lean_object*)(l_term___u2248___00__closed__1));
lean_inc(v_x_1046_);
v___x_1050_ = l_Lean_Syntax_isOfKind(v_x_1046_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_dec(v_x_1046_);
v___x_1051_ = lean_box(1);
v___x_1052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v_a_1048_);
return v___x_1052_;
}
else
{
lean_object* v_quotContext_1053_; lean_object* v_currMacroScope_1054_; lean_object* v_ref_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_quotContext_1053_ = lean_ctor_get(v_a_1047_, 1);
v_currMacroScope_1054_ = lean_ctor_get(v_a_1047_, 2);
v_ref_1055_ = lean_ctor_get(v_a_1047_, 5);
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = l_Lean_Syntax_getArg(v_x_1046_, v___x_1056_);
v___x_1058_ = lean_unsigned_to_nat(2u);
v___x_1059_ = l_Lean_Syntax_getArg(v_x_1046_, v___x_1058_);
lean_dec(v_x_1046_);
v___x_1060_ = 0;
v___x_1061_ = l_Lean_SourceInfo_fromRef(v_ref_1055_, v___x_1060_);
v___x_1062_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1063_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2248____1___closed__1, &l___aux__Init__Core______macroRules__term___u2248____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2248____1___closed__1);
v___x_1064_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2248____1___closed__4));
lean_inc(v_currMacroScope_1054_);
lean_inc(v_quotContext_1053_);
v___x_1065_ = l_Lean_addMacroScope(v_quotContext_1053_, v___x_1064_, v_currMacroScope_1054_);
v___x_1066_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2248____1___closed__6));
lean_inc_n(v___x_1061_, 2);
v___x_1067_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1061_);
lean_ctor_set(v___x_1067_, 1, v___x_1063_);
lean_ctor_set(v___x_1067_, 2, v___x_1065_);
lean_ctor_set(v___x_1067_, 3, v___x_1066_);
v___x_1068_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1069_ = l_Lean_Syntax_node2(v___x_1061_, v___x_1068_, v___x_1057_, v___x_1059_);
v___x_1070_ = l_Lean_Syntax_node2(v___x_1061_, v___x_1062_, v___x_1067_, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v_a_1048_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2248____1___boxed(lean_object* v_x_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l___aux__Init__Core______macroRules__term___u2248____1(v_x_1072_, v_a_1073_, v_a_1074_);
lean_dec_ref(v_a_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasEquiv__Equiv__1(lean_object* v_x_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1076_);
v___x_1080_ = l_Lean_Syntax_isOfKind(v_x_1076_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec(v_x_1076_);
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v_a_1078_);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = l_Lean_Syntax_getArg(v_x_1076_, v___x_1083_);
v___x_1085_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1084_);
v___x_1086_ = l_Lean_Syntax_isOfKind(v___x_1084_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_dec(v___x_1084_);
lean_dec(v_x_1076_);
v___x_1087_ = lean_box(0);
v___x_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v_a_1078_);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = l_Lean_Syntax_getArg(v_x_1076_, v___x_1089_);
lean_dec(v_x_1076_);
v___x_1091_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1090_);
v___x_1092_ = l_Lean_Syntax_matchesNull(v___x_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_dec(v___x_1090_);
lean_dec(v___x_1084_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v_a_1078_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v_ref_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1095_ = l_Lean_Syntax_getArg(v___x_1090_, v___x_1083_);
v___x_1096_ = l_Lean_Syntax_getArg(v___x_1090_, v___x_1089_);
lean_dec(v___x_1090_);
v_ref_1097_ = l_Lean_replaceRef(v___x_1084_, v_a_1077_);
lean_dec(v___x_1084_);
v___x_1098_ = 0;
v___x_1099_ = l_Lean_SourceInfo_fromRef(v_ref_1097_, v___x_1098_);
lean_dec(v_ref_1097_);
v___x_1100_ = ((lean_object*)(l_term___u2248___00__closed__1));
v___x_1101_ = ((lean_object*)(l_term___u2248___00__closed__2));
lean_inc(v___x_1099_);
v___x_1102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1099_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_Syntax_node3(v___x_1099_, v___x_1100_, v___x_1095_, v___x_1102_, v___x_1096_);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v_a_1078_);
return v___x_1104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasEquiv__Equiv__1___boxed(lean_object* v_x_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l___aux__Init__Core______unexpand__HasEquiv__Equiv__1(v_x_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1106_);
return v_res_1108_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2286____1___closed__1(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2286____1___closed__0));
v___x_1127_ = l_String_toRawSubstring_x27(v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2286____1(lean_object* v_x_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_term___u2286___00__closed__1));
lean_inc(v_x_1140_);
v___x_1144_ = l_Lean_Syntax_isOfKind(v_x_1140_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec(v_x_1140_);
v___x_1145_ = lean_box(1);
v___x_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v_a_1142_);
return v___x_1146_;
}
else
{
lean_object* v_quotContext_1147_; lean_object* v_currMacroScope_1148_; lean_object* v_ref_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_quotContext_1147_ = lean_ctor_get(v_a_1141_, 1);
v_currMacroScope_1148_ = lean_ctor_get(v_a_1141_, 2);
v_ref_1149_ = lean_ctor_get(v_a_1141_, 5);
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = l_Lean_Syntax_getArg(v_x_1140_, v___x_1150_);
v___x_1152_ = lean_unsigned_to_nat(2u);
v___x_1153_ = l_Lean_Syntax_getArg(v_x_1140_, v___x_1152_);
lean_dec(v_x_1140_);
v___x_1154_ = 0;
v___x_1155_ = l_Lean_SourceInfo_fromRef(v_ref_1149_, v___x_1154_);
v___x_1156_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1157_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2286____1___closed__1, &l___aux__Init__Core______macroRules__term___u2286____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2286____1___closed__1);
v___x_1158_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2286____1___closed__2));
lean_inc(v_currMacroScope_1148_);
lean_inc(v_quotContext_1147_);
v___x_1159_ = l_Lean_addMacroScope(v_quotContext_1147_, v___x_1158_, v_currMacroScope_1148_);
v___x_1160_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2286____1___closed__6));
lean_inc_n(v___x_1155_, 2);
v___x_1161_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1155_);
lean_ctor_set(v___x_1161_, 1, v___x_1157_);
lean_ctor_set(v___x_1161_, 2, v___x_1159_);
lean_ctor_set(v___x_1161_, 3, v___x_1160_);
v___x_1162_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1163_ = l_Lean_Syntax_node2(v___x_1155_, v___x_1162_, v___x_1151_, v___x_1153_);
v___x_1164_ = l_Lean_Syntax_node2(v___x_1155_, v___x_1156_, v___x_1161_, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v_a_1142_);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2286____1___boxed(lean_object* v_x_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___aux__Init__Core______macroRules__term___u2286____1(v_x_1166_, v_a_1167_, v_a_1168_);
lean_dec_ref(v_a_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSubset__Subset__1(lean_object* v_x_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1170_);
v___x_1174_ = l_Lean_Syntax_isOfKind(v_x_1170_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v_x_1170_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v_a_1172_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = l_Lean_Syntax_getArg(v_x_1170_, v___x_1177_);
v___x_1179_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1178_);
v___x_1180_ = l_Lean_Syntax_isOfKind(v___x_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v___x_1178_);
lean_dec(v_x_1170_);
v___x_1181_ = lean_box(0);
v___x_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v_a_1172_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1183_ = lean_unsigned_to_nat(1u);
v___x_1184_ = l_Lean_Syntax_getArg(v_x_1170_, v___x_1183_);
lean_dec(v_x_1170_);
v___x_1185_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1184_);
v___x_1186_ = l_Lean_Syntax_matchesNull(v___x_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec(v___x_1184_);
lean_dec(v___x_1178_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v_a_1172_);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_ref_1191_; uint8_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1189_ = l_Lean_Syntax_getArg(v___x_1184_, v___x_1177_);
v___x_1190_ = l_Lean_Syntax_getArg(v___x_1184_, v___x_1183_);
lean_dec(v___x_1184_);
v_ref_1191_ = l_Lean_replaceRef(v___x_1178_, v_a_1171_);
lean_dec(v___x_1178_);
v___x_1192_ = 0;
v___x_1193_ = l_Lean_SourceInfo_fromRef(v_ref_1191_, v___x_1192_);
lean_dec(v_ref_1191_);
v___x_1194_ = ((lean_object*)(l_term___u2286___00__closed__1));
v___x_1195_ = ((lean_object*)(l_term___u2286___00__closed__2));
lean_inc(v___x_1193_);
v___x_1196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1193_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = l_Lean_Syntax_node3(v___x_1193_, v___x_1194_, v___x_1189_, v___x_1196_, v___x_1190_);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v_a_1172_);
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSubset__Subset__1___boxed(lean_object* v_x_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___aux__Init__Core______unexpand__HasSubset__Subset__1(v_x_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1200_);
return v_res_1202_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2282____1___closed__1(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2282____1___closed__0));
v___x_1221_ = l_String_toRawSubstring_x27(v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2282____1(lean_object* v_x_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = ((lean_object*)(l_term___u2282___00__closed__1));
lean_inc(v_x_1234_);
v___x_1238_ = l_Lean_Syntax_isOfKind(v_x_1234_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec(v_x_1234_);
v___x_1239_ = lean_box(1);
v___x_1240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v_a_1236_);
return v___x_1240_;
}
else
{
lean_object* v_quotContext_1241_; lean_object* v_currMacroScope_1242_; lean_object* v_ref_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_quotContext_1241_ = lean_ctor_get(v_a_1235_, 1);
v_currMacroScope_1242_ = lean_ctor_get(v_a_1235_, 2);
v_ref_1243_ = lean_ctor_get(v_a_1235_, 5);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = l_Lean_Syntax_getArg(v_x_1234_, v___x_1244_);
v___x_1246_ = lean_unsigned_to_nat(2u);
v___x_1247_ = l_Lean_Syntax_getArg(v_x_1234_, v___x_1246_);
lean_dec(v_x_1234_);
v___x_1248_ = 0;
v___x_1249_ = l_Lean_SourceInfo_fromRef(v_ref_1243_, v___x_1248_);
v___x_1250_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1251_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2282____1___closed__1, &l___aux__Init__Core______macroRules__term___u2282____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2282____1___closed__1);
v___x_1252_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2282____1___closed__2));
lean_inc(v_currMacroScope_1242_);
lean_inc(v_quotContext_1241_);
v___x_1253_ = l_Lean_addMacroScope(v_quotContext_1241_, v___x_1252_, v_currMacroScope_1242_);
v___x_1254_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2282____1___closed__6));
lean_inc_n(v___x_1249_, 2);
v___x_1255_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1249_);
lean_ctor_set(v___x_1255_, 1, v___x_1251_);
lean_ctor_set(v___x_1255_, 2, v___x_1253_);
lean_ctor_set(v___x_1255_, 3, v___x_1254_);
v___x_1256_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1257_ = l_Lean_Syntax_node2(v___x_1249_, v___x_1256_, v___x_1245_, v___x_1247_);
v___x_1258_ = l_Lean_Syntax_node2(v___x_1249_, v___x_1250_, v___x_1255_, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v_a_1236_);
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2282____1___boxed(lean_object* v_x_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___aux__Init__Core______macroRules__term___u2282____1(v_x_1260_, v_a_1261_, v_a_1262_);
lean_dec_ref(v_a_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSSubset__SSubset__1(lean_object* v_x_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1267_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1264_);
v___x_1268_ = l_Lean_Syntax_isOfKind(v_x_1264_, v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec(v_x_1264_);
v___x_1269_ = lean_box(0);
v___x_1270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v_a_1266_);
return v___x_1270_;
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = l_Lean_Syntax_getArg(v_x_1264_, v___x_1271_);
v___x_1273_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1272_);
v___x_1274_ = l_Lean_Syntax_isOfKind(v___x_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec(v___x_1272_);
lean_dec(v_x_1264_);
v___x_1275_ = lean_box(0);
v___x_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_a_1266_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = l_Lean_Syntax_getArg(v_x_1264_, v___x_1277_);
lean_dec(v_x_1264_);
v___x_1279_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1278_);
v___x_1280_ = l_Lean_Syntax_matchesNull(v___x_1278_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec(v___x_1278_);
lean_dec(v___x_1272_);
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v_a_1266_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v_ref_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1283_ = l_Lean_Syntax_getArg(v___x_1278_, v___x_1271_);
v___x_1284_ = l_Lean_Syntax_getArg(v___x_1278_, v___x_1277_);
lean_dec(v___x_1278_);
v_ref_1285_ = l_Lean_replaceRef(v___x_1272_, v_a_1265_);
lean_dec(v___x_1272_);
v___x_1286_ = 0;
v___x_1287_ = l_Lean_SourceInfo_fromRef(v_ref_1285_, v___x_1286_);
lean_dec(v_ref_1285_);
v___x_1288_ = ((lean_object*)(l_term___u2282___00__closed__1));
v___x_1289_ = ((lean_object*)(l_term___u2282___00__closed__2));
lean_inc(v___x_1287_);
v___x_1290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1287_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = l_Lean_Syntax_node3(v___x_1287_, v___x_1288_, v___x_1283_, v___x_1290_, v___x_1284_);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v_a_1266_);
return v___x_1292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSSubset__SSubset__1___boxed(lean_object* v_x_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l___aux__Init__Core______unexpand__HasSSubset__SSubset__1(v_x_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1294_);
return v_res_1296_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2287____1___closed__1(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2287____1___closed__0));
v___x_1315_ = l_String_toRawSubstring_x27(v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2287____1(lean_object* v_x_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_term___u2287___00__closed__1));
lean_inc(v_x_1324_);
v___x_1328_ = l_Lean_Syntax_isOfKind(v_x_1324_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec(v_x_1324_);
v___x_1329_ = lean_box(1);
v___x_1330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v_a_1326_);
return v___x_1330_;
}
else
{
lean_object* v_quotContext_1331_; lean_object* v_currMacroScope_1332_; lean_object* v_ref_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_quotContext_1331_ = lean_ctor_get(v_a_1325_, 1);
v_currMacroScope_1332_ = lean_ctor_get(v_a_1325_, 2);
v_ref_1333_ = lean_ctor_get(v_a_1325_, 5);
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = l_Lean_Syntax_getArg(v_x_1324_, v___x_1334_);
v___x_1336_ = lean_unsigned_to_nat(2u);
v___x_1337_ = l_Lean_Syntax_getArg(v_x_1324_, v___x_1336_);
lean_dec(v_x_1324_);
v___x_1338_ = 0;
v___x_1339_ = l_Lean_SourceInfo_fromRef(v_ref_1333_, v___x_1338_);
v___x_1340_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1341_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2287____1___closed__1, &l___aux__Init__Core______macroRules__term___u2287____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2287____1___closed__1);
v___x_1342_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2287____1___closed__2));
lean_inc(v_currMacroScope_1332_);
lean_inc(v_quotContext_1331_);
v___x_1343_ = l_Lean_addMacroScope(v_quotContext_1331_, v___x_1342_, v_currMacroScope_1332_);
v___x_1344_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2287____1___closed__4));
lean_inc_n(v___x_1339_, 2);
v___x_1345_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1339_);
lean_ctor_set(v___x_1345_, 1, v___x_1341_);
lean_ctor_set(v___x_1345_, 2, v___x_1343_);
lean_ctor_set(v___x_1345_, 3, v___x_1344_);
v___x_1346_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1347_ = l_Lean_Syntax_node2(v___x_1339_, v___x_1346_, v___x_1335_, v___x_1337_);
v___x_1348_ = l_Lean_Syntax_node2(v___x_1339_, v___x_1340_, v___x_1345_, v___x_1347_);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v_a_1326_);
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2287____1___boxed(lean_object* v_x_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___aux__Init__Core______macroRules__term___u2287____1(v_x_1350_, v_a_1351_, v_a_1352_);
lean_dec_ref(v_a_1351_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Superset__1(lean_object* v_x_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1354_);
v___x_1358_ = l_Lean_Syntax_isOfKind(v_x_1354_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec(v_x_1354_);
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v_a_1356_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = l_Lean_Syntax_getArg(v_x_1354_, v___x_1361_);
v___x_1363_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1362_);
v___x_1364_ = l_Lean_Syntax_isOfKind(v___x_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec(v___x_1362_);
lean_dec(v_x_1354_);
v___x_1365_ = lean_box(0);
v___x_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v_a_1356_);
return v___x_1366_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = l_Lean_Syntax_getArg(v_x_1354_, v___x_1367_);
lean_dec(v_x_1354_);
v___x_1369_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1368_);
v___x_1370_ = l_Lean_Syntax_matchesNull(v___x_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec(v___x_1368_);
lean_dec(v___x_1362_);
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v_a_1356_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v_ref_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1373_ = l_Lean_Syntax_getArg(v___x_1368_, v___x_1361_);
v___x_1374_ = l_Lean_Syntax_getArg(v___x_1368_, v___x_1367_);
lean_dec(v___x_1368_);
v_ref_1375_ = l_Lean_replaceRef(v___x_1362_, v_a_1355_);
lean_dec(v___x_1362_);
v___x_1376_ = 0;
v___x_1377_ = l_Lean_SourceInfo_fromRef(v_ref_1375_, v___x_1376_);
lean_dec(v_ref_1375_);
v___x_1378_ = ((lean_object*)(l_term___u2287___00__closed__1));
v___x_1379_ = ((lean_object*)(l_term___u2287___00__closed__2));
lean_inc(v___x_1377_);
v___x_1380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1377_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = l_Lean_Syntax_node3(v___x_1377_, v___x_1378_, v___x_1373_, v___x_1380_, v___x_1374_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v_a_1356_);
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Superset__1___boxed(lean_object* v_x_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___aux__Init__Core______unexpand__Superset__1(v_x_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1384_);
return v_res_1386_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2283____1___closed__1(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2283____1___closed__0));
v___x_1405_ = l_String_toRawSubstring_x27(v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2283____1(lean_object* v_x_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = ((lean_object*)(l_term___u2283___00__closed__1));
lean_inc(v_x_1414_);
v___x_1418_ = l_Lean_Syntax_isOfKind(v_x_1414_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec(v_x_1414_);
v___x_1419_ = lean_box(1);
v___x_1420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
lean_ctor_set(v___x_1420_, 1, v_a_1416_);
return v___x_1420_;
}
else
{
lean_object* v_quotContext_1421_; lean_object* v_currMacroScope_1422_; lean_object* v_ref_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_quotContext_1421_ = lean_ctor_get(v_a_1415_, 1);
v_currMacroScope_1422_ = lean_ctor_get(v_a_1415_, 2);
v_ref_1423_ = lean_ctor_get(v_a_1415_, 5);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = l_Lean_Syntax_getArg(v_x_1414_, v___x_1424_);
v___x_1426_ = lean_unsigned_to_nat(2u);
v___x_1427_ = l_Lean_Syntax_getArg(v_x_1414_, v___x_1426_);
lean_dec(v_x_1414_);
v___x_1428_ = 0;
v___x_1429_ = l_Lean_SourceInfo_fromRef(v_ref_1423_, v___x_1428_);
v___x_1430_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1431_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2283____1___closed__1, &l___aux__Init__Core______macroRules__term___u2283____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2283____1___closed__1);
v___x_1432_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2283____1___closed__2));
lean_inc(v_currMacroScope_1422_);
lean_inc(v_quotContext_1421_);
v___x_1433_ = l_Lean_addMacroScope(v_quotContext_1421_, v___x_1432_, v_currMacroScope_1422_);
v___x_1434_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2283____1___closed__4));
lean_inc_n(v___x_1429_, 2);
v___x_1435_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1429_);
lean_ctor_set(v___x_1435_, 1, v___x_1431_);
lean_ctor_set(v___x_1435_, 2, v___x_1433_);
lean_ctor_set(v___x_1435_, 3, v___x_1434_);
v___x_1436_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1437_ = l_Lean_Syntax_node2(v___x_1429_, v___x_1436_, v___x_1425_, v___x_1427_);
v___x_1438_ = l_Lean_Syntax_node2(v___x_1429_, v___x_1430_, v___x_1435_, v___x_1437_);
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
lean_ctor_set(v___x_1439_, 1, v_a_1416_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2283____1___boxed(lean_object* v_x_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___aux__Init__Core______macroRules__term___u2283____1(v_x_1440_, v_a_1441_, v_a_1442_);
lean_dec_ref(v_a_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SSuperset__1(lean_object* v_x_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1444_);
v___x_1448_ = l_Lean_Syntax_isOfKind(v_x_1444_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec(v_x_1444_);
v___x_1449_ = lean_box(0);
v___x_1450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v_a_1446_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1451_);
v___x_1453_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1452_);
v___x_1454_ = l_Lean_Syntax_isOfKind(v___x_1452_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec(v___x_1452_);
lean_dec(v_x_1444_);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
lean_ctor_set(v___x_1456_, 1, v_a_1446_);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1457_ = lean_unsigned_to_nat(1u);
v___x_1458_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1457_);
lean_dec(v_x_1444_);
v___x_1459_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1458_);
v___x_1460_ = l_Lean_Syntax_matchesNull(v___x_1458_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec(v___x_1458_);
lean_dec(v___x_1452_);
v___x_1461_ = lean_box(0);
v___x_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v_a_1446_);
return v___x_1462_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v_ref_1465_; uint8_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1463_ = l_Lean_Syntax_getArg(v___x_1458_, v___x_1451_);
v___x_1464_ = l_Lean_Syntax_getArg(v___x_1458_, v___x_1457_);
lean_dec(v___x_1458_);
v_ref_1465_ = l_Lean_replaceRef(v___x_1452_, v_a_1445_);
lean_dec(v___x_1452_);
v___x_1466_ = 0;
v___x_1467_ = l_Lean_SourceInfo_fromRef(v_ref_1465_, v___x_1466_);
lean_dec(v_ref_1465_);
v___x_1468_ = ((lean_object*)(l_term___u2283___00__closed__1));
v___x_1469_ = ((lean_object*)(l_term___u2283___00__closed__2));
lean_inc(v___x_1467_);
v___x_1470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1467_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = l_Lean_Syntax_node3(v___x_1467_, v___x_1468_, v___x_1463_, v___x_1470_, v___x_1464_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_ctor_set(v___x_1472_, 1, v_a_1446_);
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SSuperset__1___boxed(lean_object* v_x_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___aux__Init__Core______unexpand__SSuperset__1(v_x_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_a_1474_);
return v_res_1476_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u222a____1___closed__1(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u222a____1___closed__0));
v___x_1497_ = l_String_toRawSubstring_x27(v___x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u222a____1(lean_object* v_x_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_term___u222a___00__closed__1));
lean_inc(v_x_1509_);
v___x_1513_ = l_Lean_Syntax_isOfKind(v_x_1509_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec(v_x_1509_);
v___x_1514_ = lean_box(1);
v___x_1515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v_a_1511_);
return v___x_1515_;
}
else
{
lean_object* v_quotContext_1516_; lean_object* v_currMacroScope_1517_; lean_object* v_ref_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_quotContext_1516_ = lean_ctor_get(v_a_1510_, 1);
v_currMacroScope_1517_ = lean_ctor_get(v_a_1510_, 2);
v_ref_1518_ = lean_ctor_get(v_a_1510_, 5);
v___x_1519_ = lean_unsigned_to_nat(0u);
v___x_1520_ = l_Lean_Syntax_getArg(v_x_1509_, v___x_1519_);
v___x_1521_ = lean_unsigned_to_nat(2u);
v___x_1522_ = l_Lean_Syntax_getArg(v_x_1509_, v___x_1521_);
lean_dec(v_x_1509_);
v___x_1523_ = 0;
v___x_1524_ = l_Lean_SourceInfo_fromRef(v_ref_1518_, v___x_1523_);
v___x_1525_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1526_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u222a____1___closed__1, &l___aux__Init__Core______macroRules__term___u222a____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u222a____1___closed__1);
v___x_1527_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u222a____1___closed__4));
lean_inc(v_currMacroScope_1517_);
lean_inc(v_quotContext_1516_);
v___x_1528_ = l_Lean_addMacroScope(v_quotContext_1516_, v___x_1527_, v_currMacroScope_1517_);
v___x_1529_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u222a____1___closed__6));
lean_inc_n(v___x_1524_, 2);
v___x_1530_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1524_);
lean_ctor_set(v___x_1530_, 1, v___x_1526_);
lean_ctor_set(v___x_1530_, 2, v___x_1528_);
lean_ctor_set(v___x_1530_, 3, v___x_1529_);
v___x_1531_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1532_ = l_Lean_Syntax_node2(v___x_1524_, v___x_1531_, v___x_1520_, v___x_1522_);
v___x_1533_ = l_Lean_Syntax_node2(v___x_1524_, v___x_1525_, v___x_1530_, v___x_1532_);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v_a_1511_);
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u222a____1___boxed(lean_object* v_x_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l___aux__Init__Core______macroRules__term___u222a____1(v_x_1535_, v_a_1536_, v_a_1537_);
lean_dec_ref(v_a_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Union__union__1(lean_object* v_x_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1542_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1539_);
v___x_1543_ = l_Lean_Syntax_isOfKind(v_x_1539_, v___x_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec(v_x_1539_);
v___x_1544_ = lean_box(0);
v___x_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v_a_1541_);
return v___x_1545_;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = l_Lean_Syntax_getArg(v_x_1539_, v___x_1546_);
v___x_1548_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1547_);
v___x_1549_ = l_Lean_Syntax_isOfKind(v___x_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec(v___x_1547_);
lean_dec(v_x_1539_);
v___x_1550_ = lean_box(0);
v___x_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v_a_1541_);
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = l_Lean_Syntax_getArg(v_x_1539_, v___x_1552_);
lean_dec(v_x_1539_);
v___x_1554_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1553_);
v___x_1555_ = l_Lean_Syntax_matchesNull(v___x_1553_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec(v___x_1553_);
lean_dec(v___x_1547_);
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v_a_1541_);
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v_ref_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1558_ = l_Lean_Syntax_getArg(v___x_1553_, v___x_1546_);
v___x_1559_ = l_Lean_Syntax_getArg(v___x_1553_, v___x_1552_);
lean_dec(v___x_1553_);
v_ref_1560_ = l_Lean_replaceRef(v___x_1547_, v_a_1540_);
lean_dec(v___x_1547_);
v___x_1561_ = 0;
v___x_1562_ = l_Lean_SourceInfo_fromRef(v_ref_1560_, v___x_1561_);
lean_dec(v_ref_1560_);
v___x_1563_ = ((lean_object*)(l_term___u222a___00__closed__1));
v___x_1564_ = ((lean_object*)(l_term___u222a___00__closed__2));
lean_inc(v___x_1562_);
v___x_1565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1562_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_Syntax_node3(v___x_1562_, v___x_1563_, v___x_1558_, v___x_1565_, v___x_1559_);
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
lean_ctor_set(v___x_1567_, 1, v_a_1541_);
return v___x_1567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Union__union__1___boxed(lean_object* v_x_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l___aux__Init__Core______unexpand__Union__union__1(v_x_1568_, v_a_1569_, v_a_1570_);
lean_dec(v_a_1569_);
return v_res_1571_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2229____1___closed__1(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2229____1___closed__0));
v___x_1592_ = l_String_toRawSubstring_x27(v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2229____1(lean_object* v_x_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = ((lean_object*)(l_term___u2229___00__closed__1));
lean_inc(v_x_1604_);
v___x_1608_ = l_Lean_Syntax_isOfKind(v_x_1604_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec(v_x_1604_);
v___x_1609_ = lean_box(1);
v___x_1610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_a_1606_);
return v___x_1610_;
}
else
{
lean_object* v_quotContext_1611_; lean_object* v_currMacroScope_1612_; lean_object* v_ref_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_quotContext_1611_ = lean_ctor_get(v_a_1605_, 1);
v_currMacroScope_1612_ = lean_ctor_get(v_a_1605_, 2);
v_ref_1613_ = lean_ctor_get(v_a_1605_, 5);
v___x_1614_ = lean_unsigned_to_nat(0u);
v___x_1615_ = l_Lean_Syntax_getArg(v_x_1604_, v___x_1614_);
v___x_1616_ = lean_unsigned_to_nat(2u);
v___x_1617_ = l_Lean_Syntax_getArg(v_x_1604_, v___x_1616_);
lean_dec(v_x_1604_);
v___x_1618_ = 0;
v___x_1619_ = l_Lean_SourceInfo_fromRef(v_ref_1613_, v___x_1618_);
v___x_1620_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1621_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2229____1___closed__1, &l___aux__Init__Core______macroRules__term___u2229____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2229____1___closed__1);
v___x_1622_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2229____1___closed__4));
lean_inc(v_currMacroScope_1612_);
lean_inc(v_quotContext_1611_);
v___x_1623_ = l_Lean_addMacroScope(v_quotContext_1611_, v___x_1622_, v_currMacroScope_1612_);
v___x_1624_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2229____1___closed__6));
lean_inc_n(v___x_1619_, 2);
v___x_1625_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1619_);
lean_ctor_set(v___x_1625_, 1, v___x_1621_);
lean_ctor_set(v___x_1625_, 2, v___x_1623_);
lean_ctor_set(v___x_1625_, 3, v___x_1624_);
v___x_1626_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1627_ = l_Lean_Syntax_node2(v___x_1619_, v___x_1626_, v___x_1615_, v___x_1617_);
v___x_1628_ = l_Lean_Syntax_node2(v___x_1619_, v___x_1620_, v___x_1625_, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v_a_1606_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2229____1___boxed(lean_object* v_x_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___aux__Init__Core______macroRules__term___u2229____1(v_x_1630_, v_a_1631_, v_a_1632_);
lean_dec_ref(v_a_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Inter__inter__1(lean_object* v_x_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1634_);
v___x_1638_ = l_Lean_Syntax_isOfKind(v_x_1634_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec(v_x_1634_);
v___x_1639_ = lean_box(0);
v___x_1640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v_a_1636_);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = l_Lean_Syntax_getArg(v_x_1634_, v___x_1641_);
v___x_1643_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1642_);
v___x_1644_ = l_Lean_Syntax_isOfKind(v___x_1642_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v___x_1642_);
lean_dec(v_x_1634_);
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v_a_1636_);
return v___x_1646_;
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = l_Lean_Syntax_getArg(v_x_1634_, v___x_1647_);
lean_dec(v_x_1634_);
v___x_1649_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1648_);
v___x_1650_ = l_Lean_Syntax_matchesNull(v___x_1648_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec(v___x_1648_);
lean_dec(v___x_1642_);
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v_a_1636_);
return v___x_1652_;
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v_ref_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1653_ = l_Lean_Syntax_getArg(v___x_1648_, v___x_1641_);
v___x_1654_ = l_Lean_Syntax_getArg(v___x_1648_, v___x_1647_);
lean_dec(v___x_1648_);
v_ref_1655_ = l_Lean_replaceRef(v___x_1642_, v_a_1635_);
lean_dec(v___x_1642_);
v___x_1656_ = 0;
v___x_1657_ = l_Lean_SourceInfo_fromRef(v_ref_1655_, v___x_1656_);
lean_dec(v_ref_1655_);
v___x_1658_ = ((lean_object*)(l_term___u2229___00__closed__1));
v___x_1659_ = ((lean_object*)(l_term___u2229___00__closed__2));
lean_inc(v___x_1657_);
v___x_1660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1657_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = l_Lean_Syntax_node3(v___x_1657_, v___x_1658_, v___x_1653_, v___x_1660_, v___x_1654_);
v___x_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
lean_ctor_set(v___x_1662_, 1, v_a_1636_);
return v___x_1662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Inter__inter__1___boxed(lean_object* v_x_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___aux__Init__Core______unexpand__Inter__inter__1(v_x_1663_, v_a_1664_, v_a_1665_);
lean_dec(v_a_1664_);
return v_res_1666_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x5c____1___closed__1(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x5c____1___closed__0));
v___x_1685_ = l_String_toRawSubstring_x27(v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x5c____1(lean_object* v_x_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_term___x5c___00__closed__1));
lean_inc(v_x_1697_);
v___x_1701_ = l_Lean_Syntax_isOfKind(v_x_1697_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec(v_x_1697_);
v___x_1702_ = lean_box(1);
v___x_1703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v_a_1699_);
return v___x_1703_;
}
else
{
lean_object* v_quotContext_1704_; lean_object* v_currMacroScope_1705_; lean_object* v_ref_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_quotContext_1704_ = lean_ctor_get(v_a_1698_, 1);
v_currMacroScope_1705_ = lean_ctor_get(v_a_1698_, 2);
v_ref_1706_ = lean_ctor_get(v_a_1698_, 5);
v___x_1707_ = lean_unsigned_to_nat(0u);
v___x_1708_ = l_Lean_Syntax_getArg(v_x_1697_, v___x_1707_);
v___x_1709_ = lean_unsigned_to_nat(2u);
v___x_1710_ = l_Lean_Syntax_getArg(v_x_1697_, v___x_1709_);
lean_dec(v_x_1697_);
v___x_1711_ = 0;
v___x_1712_ = l_Lean_SourceInfo_fromRef(v_ref_1706_, v___x_1711_);
v___x_1713_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1714_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x5c____1___closed__1, &l___aux__Init__Core______macroRules__term___x5c____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x5c____1___closed__1);
v___x_1715_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x5c____1___closed__4));
lean_inc(v_currMacroScope_1705_);
lean_inc(v_quotContext_1704_);
v___x_1716_ = l_Lean_addMacroScope(v_quotContext_1704_, v___x_1715_, v_currMacroScope_1705_);
v___x_1717_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x5c____1___closed__6));
lean_inc_n(v___x_1712_, 2);
v___x_1718_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1712_);
lean_ctor_set(v___x_1718_, 1, v___x_1714_);
lean_ctor_set(v___x_1718_, 2, v___x_1716_);
lean_ctor_set(v___x_1718_, 3, v___x_1717_);
v___x_1719_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1720_ = l_Lean_Syntax_node2(v___x_1712_, v___x_1719_, v___x_1708_, v___x_1710_);
v___x_1721_ = l_Lean_Syntax_node2(v___x_1712_, v___x_1713_, v___x_1718_, v___x_1720_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v_a_1699_);
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x5c____1___boxed(lean_object* v_x_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___aux__Init__Core______macroRules__term___x5c____1(v_x_1723_, v_a_1724_, v_a_1725_);
lean_dec_ref(v_a_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SDiff__sdiff__1(lean_object* v_x_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1727_);
v___x_1731_ = l_Lean_Syntax_isOfKind(v_x_1727_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v_x_1727_);
v___x_1732_ = lean_box(0);
v___x_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v_a_1729_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1734_ = lean_unsigned_to_nat(0u);
v___x_1735_ = l_Lean_Syntax_getArg(v_x_1727_, v___x_1734_);
v___x_1736_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1735_);
v___x_1737_ = l_Lean_Syntax_isOfKind(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v___x_1735_);
lean_dec(v_x_1727_);
v___x_1738_ = lean_box(0);
v___x_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v_a_1729_);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1740_ = lean_unsigned_to_nat(1u);
v___x_1741_ = l_Lean_Syntax_getArg(v_x_1727_, v___x_1740_);
lean_dec(v_x_1727_);
v___x_1742_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1741_);
v___x_1743_ = l_Lean_Syntax_matchesNull(v___x_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec(v___x_1741_);
lean_dec(v___x_1735_);
v___x_1744_ = lean_box(0);
v___x_1745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v_a_1729_);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v_ref_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1746_ = l_Lean_Syntax_getArg(v___x_1741_, v___x_1734_);
v___x_1747_ = l_Lean_Syntax_getArg(v___x_1741_, v___x_1740_);
lean_dec(v___x_1741_);
v_ref_1748_ = l_Lean_replaceRef(v___x_1735_, v_a_1728_);
lean_dec(v___x_1735_);
v___x_1749_ = 0;
v___x_1750_ = l_Lean_SourceInfo_fromRef(v_ref_1748_, v___x_1749_);
lean_dec(v_ref_1748_);
v___x_1751_ = ((lean_object*)(l_term___x5c___00__closed__1));
v___x_1752_ = ((lean_object*)(l_term___x5c___00__closed__2));
lean_inc(v___x_1750_);
v___x_1753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1750_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = l_Lean_Syntax_node3(v___x_1750_, v___x_1751_, v___x_1746_, v___x_1753_, v___x_1747_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v_a_1729_);
return v___x_1755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SDiff__sdiff__1___boxed(lean_object* v_x_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l___aux__Init__Core______unexpand__SDiff__sdiff__1(v_x_1756_, v_a_1757_, v_a_1758_);
lean_dec(v_a_1757_);
return v_res_1759_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__0));
v___x_1780_ = l_String_toRawSubstring_x27(v___x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1(lean_object* v_x_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = ((lean_object*)(l_term_x7b_x7d___closed__1));
v___x_1796_ = l_Lean_Syntax_isOfKind(v_x_1792_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_box(1);
v___x_1798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
lean_ctor_set(v___x_1798_, 1, v_a_1794_);
return v___x_1798_;
}
else
{
lean_object* v_quotContext_1799_; lean_object* v_currMacroScope_1800_; lean_object* v_ref_1801_; uint8_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v_quotContext_1799_ = lean_ctor_get(v_a_1793_, 1);
v_currMacroScope_1800_ = lean_ctor_get(v_a_1793_, 2);
v_ref_1801_ = lean_ctor_get(v_a_1793_, 5);
v___x_1802_ = 0;
v___x_1803_ = l_Lean_SourceInfo_fromRef(v_ref_1801_, v___x_1802_);
v___x_1804_ = lean_obj_once(&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1, &l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1_once, _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1);
v___x_1805_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4));
lean_inc(v_currMacroScope_1800_);
lean_inc(v_quotContext_1799_);
v___x_1806_ = l_Lean_addMacroScope(v_quotContext_1799_, v___x_1805_, v_currMacroScope_1800_);
v___x_1807_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6));
v___x_1808_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1803_);
lean_ctor_set(v___x_1808_, 1, v___x_1804_);
lean_ctor_set(v___x_1808_, 2, v___x_1806_);
lean_ctor_set(v___x_1808_, 3, v___x_1807_);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v_a_1794_);
return v___x_1809_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1___boxed(lean_object* v_x_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___aux__Init__Core______macroRules__term_x7b_x7d__1(v_x_1810_, v_a_1811_, v_a_1812_);
lean_dec_ref(v_a_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1(lean_object* v_x_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v_x_1814_);
v___x_1818_ = l_Lean_Syntax_isOfKind(v_x_1814_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec(v_x_1814_);
v___x_1819_ = lean_box(0);
v___x_1820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v_a_1816_);
return v___x_1820_;
}
else
{
lean_object* v_ref_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v_ref_1821_ = l_Lean_replaceRef(v_x_1814_, v_a_1815_);
lean_dec(v_x_1814_);
v___x_1822_ = 0;
v___x_1823_ = l_Lean_SourceInfo_fromRef(v_ref_1821_, v___x_1822_);
lean_dec(v_ref_1821_);
v___x_1824_ = ((lean_object*)(l_term_x7b_x7d___closed__1));
v___x_1825_ = ((lean_object*)(l_term_x7b_x7d___closed__2));
lean_inc_n(v___x_1823_, 2);
v___x_1826_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1823_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = ((lean_object*)(l_term_x7b_x7d___closed__4));
v___x_1828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1823_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = l_Lean_Syntax_node2(v___x_1823_, v___x_1824_, v___x_1826_, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v_a_1816_);
return v___x_1830_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1___boxed(lean_object* v_x_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1(v_x_1831_, v_a_1832_, v_a_1833_);
lean_dec(v_a_1832_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_u2205__1(lean_object* v_x_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = ((lean_object*)(l_term_u2205___closed__1));
v___x_1850_ = l_Lean_Syntax_isOfKind(v_x_1846_, v___x_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_box(1);
v___x_1852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v_a_1848_);
return v___x_1852_;
}
else
{
lean_object* v_quotContext_1853_; lean_object* v_currMacroScope_1854_; lean_object* v_ref_1855_; uint8_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v_quotContext_1853_ = lean_ctor_get(v_a_1847_, 1);
v_currMacroScope_1854_ = lean_ctor_get(v_a_1847_, 2);
v_ref_1855_ = lean_ctor_get(v_a_1847_, 5);
v___x_1856_ = 0;
v___x_1857_ = l_Lean_SourceInfo_fromRef(v_ref_1855_, v___x_1856_);
v___x_1858_ = lean_obj_once(&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1, &l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1_once, _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1);
v___x_1859_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4));
lean_inc(v_currMacroScope_1854_);
lean_inc(v_quotContext_1853_);
v___x_1860_ = l_Lean_addMacroScope(v_quotContext_1853_, v___x_1859_, v_currMacroScope_1854_);
v___x_1861_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6));
v___x_1862_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1857_);
lean_ctor_set(v___x_1862_, 1, v___x_1858_);
lean_ctor_set(v___x_1862_, 2, v___x_1860_);
lean_ctor_set(v___x_1862_, 3, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v_a_1848_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_u2205__1___boxed(lean_object* v_x_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l___aux__Init__Core______macroRules__term_u2205__1(v_x_1864_, v_a_1865_, v_a_1866_);
lean_dec_ref(v_a_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2(lean_object* v_x_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1871_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v_x_1868_);
v___x_1872_ = l_Lean_Syntax_isOfKind(v_x_1868_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_dec(v_x_1868_);
v___x_1873_ = lean_box(0);
v___x_1874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v_a_1870_);
return v___x_1874_;
}
else
{
lean_object* v_ref_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_ref_1875_ = l_Lean_replaceRef(v_x_1868_, v_a_1869_);
lean_dec(v_x_1868_);
v___x_1876_ = 0;
v___x_1877_ = l_Lean_SourceInfo_fromRef(v_ref_1875_, v___x_1876_);
lean_dec(v_ref_1875_);
v___x_1878_ = ((lean_object*)(l_term_u2205___closed__1));
v___x_1879_ = ((lean_object*)(l_term_u2205___closed__2));
lean_inc(v___x_1877_);
v___x_1880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1877_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = l_Lean_Syntax_node1(v___x_1877_, v___x_1878_, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v_a_1870_);
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2___boxed(lean_object* v_x_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2(v_x_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask_default___redArg(lean_object* v_inst_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v_inst_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask_default(lean_object* v_00_u03b1_1889_, lean_object* v_inst_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v_inst_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask___redArg(lean_object* v_inst_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_inst_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask(lean_object* v_a_1894_, lean_object* v_inst_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_inst_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Task_pure___boxed(lean_object* v_00_u03b1_1899_, lean_object* v_get_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = lean_task_pure(v_get_1900_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Task_get___boxed(lean_object* v_00_u03b1_1904_, lean_object* v_self_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = lean_task_get_own(v_self_1905_);
return v_res_1906_;
}
}
static lean_object* _init_l_Task_Priority_default(void){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_unsigned_to_nat(0u);
return v___x_1907_;
}
}
static lean_object* _init_l_Task_Priority_max(void){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_unsigned_to_nat(8u);
return v___x_1908_;
}
}
static lean_object* _init_l_Task_Priority_dedicated(void){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_unsigned_to_nat(9u);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Task_spawn___boxed(lean_object* v_00_u03b1_1913_, lean_object* v_fn_1914_, lean_object* v_prio_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = lean_task_spawn(v_fn_1914_, v_prio_1915_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Task_map___boxed(lean_object* v_00_u03b1_1923_, lean_object* v_00_u03b2_1924_, lean_object* v_f_1925_, lean_object* v_x_1926_, lean_object* v_prio_1927_, lean_object* v_sync_1928_){
_start:
{
uint8_t v_sync_boxed_1929_; lean_object* v_res_1930_; 
v_sync_boxed_1929_ = lean_unbox(v_sync_1928_);
v_res_1930_ = lean_task_map(v_f_1925_, v_x_1926_, v_prio_1927_, v_sync_boxed_1929_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Task_bind___boxed(lean_object* v_00_u03b1_1937_, lean_object* v_00_u03b2_1938_, lean_object* v_x_1939_, lean_object* v_f_1940_, lean_object* v_prio_1941_, lean_object* v_sync_1942_){
_start:
{
uint8_t v_sync_boxed_1943_; lean_object* v_res_1944_; 
v_sync_boxed_1943_ = lean_unbox(v_sync_1942_);
v_res_1944_ = lean_task_bind(v_x_1939_, v_f_1940_, v_prio_1941_, v_sync_boxed_1943_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_strictOr___boxed(lean_object* v_b_u2081_1947_, lean_object* v_b_u2082_1948_){
_start:
{
uint8_t v_b_u2081_boxed_1949_; uint8_t v_b_u2082_boxed_1950_; uint8_t v_res_1951_; lean_object* v_r_1952_; 
v_b_u2081_boxed_1949_ = lean_unbox(v_b_u2081_1947_);
v_b_u2082_boxed_1950_ = lean_unbox(v_b_u2082_1948_);
v_res_1951_ = lean_strict_or(v_b_u2081_boxed_1949_, v_b_u2082_boxed_1950_);
v_r_1952_ = lean_box(v_res_1951_);
return v_r_1952_;
}
}
LEAN_EXPORT lean_object* l_strictAnd___boxed(lean_object* v_b_u2081_1955_, lean_object* v_b_u2082_1956_){
_start:
{
uint8_t v_b_u2081_boxed_1957_; uint8_t v_b_u2082_boxed_1958_; uint8_t v_res_1959_; lean_object* v_r_1960_; 
v_b_u2081_boxed_1957_ = lean_unbox(v_b_u2081_1955_);
v_b_u2082_boxed_1958_ = lean_unbox(v_b_u2082_1956_);
v_res_1959_ = lean_strict_and(v_b_u2081_boxed_1957_, v_b_u2082_boxed_1958_);
v_r_1960_ = lean_box(v_res_1959_);
return v_r_1960_;
}
}
LEAN_EXPORT uint8_t l_bne___redArg(lean_object* v_inst_1961_, lean_object* v_a_1962_, lean_object* v_b_1963_){
_start:
{
lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = lean_apply_2(v_inst_1961_, v_a_1962_, v_b_1963_);
v___x_1965_ = lean_unbox(v___x_1964_);
if (v___x_1965_ == 0)
{
uint8_t v___x_1966_; 
v___x_1966_ = 1;
return v___x_1966_;
}
else
{
uint8_t v___x_1967_; 
v___x_1967_ = 0;
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l_bne___redArg___boxed(lean_object* v_inst_1968_, lean_object* v_a_1969_, lean_object* v_b_1970_){
_start:
{
uint8_t v_res_1971_; lean_object* v_r_1972_; 
v_res_1971_ = l_bne___redArg(v_inst_1968_, v_a_1969_, v_b_1970_);
v_r_1972_ = lean_box(v_res_1971_);
return v_r_1972_;
}
}
LEAN_EXPORT uint8_t l_bne(lean_object* v_00_u03b1_1973_, lean_object* v_inst_1974_, lean_object* v_a_1975_, lean_object* v_b_1976_){
_start:
{
lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1977_ = lean_apply_2(v_inst_1974_, v_a_1975_, v_b_1976_);
v___x_1978_ = lean_unbox(v___x_1977_);
if (v___x_1978_ == 0)
{
uint8_t v___x_1979_; 
v___x_1979_ = 1;
return v___x_1979_;
}
else
{
uint8_t v___x_1980_; 
v___x_1980_ = 0;
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l_bne___boxed(lean_object* v_00_u03b1_1981_, lean_object* v_inst_1982_, lean_object* v_a_1983_, lean_object* v_b_1984_){
_start:
{
uint8_t v_res_1985_; lean_object* v_r_1986_; 
v_res_1985_ = l_bne(v_00_u03b1_1981_, v_inst_1982_, v_a_1983_, v_b_1984_);
v_r_1986_ = lean_box(v_res_1985_);
return v_r_1986_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0));
v___x_2005_ = l_String_toRawSubstring_x27(v___x_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1(lean_object* v_x_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
lean_inc(v_x_2014_);
v___x_2018_ = l_Lean_Syntax_isOfKind(v_x_2014_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_dec(v_x_2014_);
v___x_2019_ = lean_box(1);
v___x_2020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v_a_2016_);
return v___x_2020_;
}
else
{
lean_object* v_quotContext_2021_; lean_object* v_currMacroScope_2022_; lean_object* v_ref_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_quotContext_2021_ = lean_ctor_get(v_a_2015_, 1);
v_currMacroScope_2022_ = lean_ctor_get(v_a_2015_, 2);
v_ref_2023_ = lean_ctor_get(v_a_2015_, 5);
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = l_Lean_Syntax_getArg(v_x_2014_, v___x_2024_);
v___x_2026_ = lean_unsigned_to_nat(2u);
v___x_2027_ = l_Lean_Syntax_getArg(v_x_2014_, v___x_2026_);
lean_dec(v_x_2014_);
v___x_2028_ = 0;
v___x_2029_ = l_Lean_SourceInfo_fromRef(v_ref_2023_, v___x_2028_);
v___x_2030_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_2031_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1, &l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1);
v___x_2032_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2));
lean_inc(v_currMacroScope_2022_);
lean_inc(v_quotContext_2021_);
v___x_2033_ = l_Lean_addMacroScope(v_quotContext_2021_, v___x_2032_, v_currMacroScope_2022_);
v___x_2034_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4));
lean_inc_n(v___x_2029_, 2);
v___x_2035_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2029_);
lean_ctor_set(v___x_2035_, 1, v___x_2031_);
lean_ctor_set(v___x_2035_, 2, v___x_2033_);
lean_ctor_set(v___x_2035_, 3, v___x_2034_);
v___x_2036_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_2037_ = l_Lean_Syntax_node2(v___x_2029_, v___x_2036_, v___x_2025_, v___x_2027_);
v___x_2038_ = l_Lean_Syntax_node2(v___x_2029_, v___x_2030_, v___x_2035_, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
lean_ctor_set(v___x_2039_, 1, v_a_2016_);
return v___x_2039_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1___boxed(lean_object* v_x_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___aux__Init__Core______macroRules__term___x21_x3d____1(v_x_2040_, v_a_2041_, v_a_2042_);
lean_dec_ref(v_a_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__bne__1(lean_object* v_x_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_2044_);
v___x_2048_ = l_Lean_Syntax_isOfKind(v_x_2044_, v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_dec(v_x_2044_);
v___x_2049_ = lean_box(0);
v___x_2050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v_a_2046_);
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2051_ = lean_unsigned_to_nat(0u);
v___x_2052_ = l_Lean_Syntax_getArg(v_x_2044_, v___x_2051_);
v___x_2053_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_2052_);
v___x_2054_ = l_Lean_Syntax_isOfKind(v___x_2052_, v___x_2053_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_dec(v___x_2052_);
lean_dec(v_x_2044_);
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v_a_2046_);
return v___x_2056_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2057_ = lean_unsigned_to_nat(1u);
v___x_2058_ = l_Lean_Syntax_getArg(v_x_2044_, v___x_2057_);
lean_dec(v_x_2044_);
v___x_2059_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2058_);
v___x_2060_ = l_Lean_Syntax_matchesNull(v___x_2058_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec(v___x_2058_);
lean_dec(v___x_2052_);
v___x_2061_ = lean_box(0);
v___x_2062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v_a_2046_);
return v___x_2062_;
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v_ref_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2063_ = l_Lean_Syntax_getArg(v___x_2058_, v___x_2051_);
v___x_2064_ = l_Lean_Syntax_getArg(v___x_2058_, v___x_2057_);
lean_dec(v___x_2058_);
v_ref_2065_ = l_Lean_replaceRef(v___x_2052_, v_a_2045_);
lean_dec(v___x_2052_);
v___x_2066_ = 0;
v___x_2067_ = l_Lean_SourceInfo_fromRef(v_ref_2065_, v___x_2066_);
lean_dec(v_ref_2065_);
v___x_2068_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
v___x_2069_ = ((lean_object*)(l_term___x21_x3d___00__closed__2));
lean_inc(v___x_2067_);
v___x_2070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2067_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = l_Lean_Syntax_node3(v___x_2067_, v___x_2068_, v___x_2063_, v___x_2070_, v___x_2064_);
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v_a_2046_);
return v___x_2072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__bne__1___boxed(lean_object* v_x_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l___aux__Init__Core______unexpand__bne__1(v_x_2073_, v_a_2074_, v_a_2075_);
lean_dec(v_a_2074_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2(lean_object* v_x_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
lean_inc(v_x_2084_);
v___x_2088_ = l_Lean_Syntax_isOfKind(v_x_2084_, v___x_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec(v_x_2084_);
v___x_2089_ = lean_box(1);
v___x_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v_a_2086_);
return v___x_2090_;
}
else
{
lean_object* v_quotContext_2091_; lean_object* v_currMacroScope_2092_; lean_object* v_ref_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_quotContext_2091_ = lean_ctor_get(v_a_2085_, 1);
v_currMacroScope_2092_ = lean_ctor_get(v_a_2085_, 2);
v_ref_2093_ = lean_ctor_get(v_a_2085_, 5);
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = l_Lean_Syntax_getArg(v_x_2084_, v___x_2094_);
v___x_2096_ = lean_unsigned_to_nat(2u);
v___x_2097_ = l_Lean_Syntax_getArg(v_x_2084_, v___x_2096_);
lean_dec(v_x_2084_);
v___x_2098_ = 0;
v___x_2099_ = l_Lean_SourceInfo_fromRef(v_ref_2093_, v___x_2098_);
v___x_2100_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1));
v___x_2101_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__2));
lean_inc_n(v___x_2099_, 2);
v___x_2102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2099_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1, &l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1);
v___x_2104_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2));
lean_inc(v_currMacroScope_2092_);
lean_inc(v_quotContext_2091_);
v___x_2105_ = l_Lean_addMacroScope(v_quotContext_2091_, v___x_2104_, v_currMacroScope_2092_);
v___x_2106_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4));
v___x_2107_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2099_);
lean_ctor_set(v___x_2107_, 1, v___x_2103_);
lean_ctor_set(v___x_2107_, 2, v___x_2105_);
lean_ctor_set(v___x_2107_, 3, v___x_2106_);
v___x_2108_ = l_Lean_Syntax_node4(v___x_2099_, v___x_2100_, v___x_2102_, v___x_2107_, v___x_2095_, v___x_2097_);
v___x_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v_a_2086_);
return v___x_2109_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2___boxed(lean_object* v_x_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___aux__Init__Core______macroRules__term___x21_x3d____2(v_x_2110_, v_a_2111_, v_a_2112_);
lean_dec_ref(v_a_2111_);
return v_res_2113_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_2114_, lean_object* v_x_2115_, lean_object* v_y_2116_){
_start:
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = lean_apply_2(v_inst_2114_, v_x_2115_, v_y_2116_);
v___x_2118_ = lean_unbox(v___x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_2119_, lean_object* v_x_2120_, lean_object* v_y_2121_){
_start:
{
uint8_t v_res_2122_; lean_object* v_r_2123_; 
v_res_2122_ = l_instDecidableEqOfLawfulBEq___redArg(v_inst_2119_, v_x_2120_, v_y_2121_);
v_r_2123_ = lean_box(v_res_2122_);
return v_r_2123_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_2124_, lean_object* v_inst_2125_, lean_object* v_inst_2126_, lean_object* v_x_2127_, lean_object* v_y_2128_){
_start:
{
lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = lean_apply_2(v_inst_2125_, v_x_2127_, v_y_2128_);
v___x_2130_ = lean_unbox(v___x_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_x_2134_, lean_object* v_y_2135_){
_start:
{
uint8_t v_res_2136_; lean_object* v_r_2137_; 
v_res_2136_ = l_instDecidableEqOfLawfulBEq(v_00_u03b1_2131_, v_inst_2132_, v_inst_2133_, v_x_2134_, v_y_2135_);
v_r_2137_ = lean_box(v_res_2136_);
return v_r_2137_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__0));
v___x_2156_ = l_String_toRawSubstring_x27(v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____1(lean_object* v_x_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = ((lean_object*)(l_term___u2260___00__closed__1));
lean_inc(v_x_2165_);
v___x_2169_ = l_Lean_Syntax_isOfKind(v_x_2165_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec(v_x_2165_);
v___x_2170_ = lean_box(1);
v___x_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v_a_2167_);
return v___x_2171_;
}
else
{
lean_object* v_quotContext_2172_; lean_object* v_currMacroScope_2173_; lean_object* v_ref_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_quotContext_2172_ = lean_ctor_get(v_a_2166_, 1);
v_currMacroScope_2173_ = lean_ctor_get(v_a_2166_, 2);
v_ref_2174_ = lean_ctor_get(v_a_2166_, 5);
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = l_Lean_Syntax_getArg(v_x_2165_, v___x_2175_);
v___x_2177_ = lean_unsigned_to_nat(2u);
v___x_2178_ = l_Lean_Syntax_getArg(v_x_2165_, v___x_2177_);
lean_dec(v_x_2165_);
v___x_2179_ = 0;
v___x_2180_ = l_Lean_SourceInfo_fromRef(v_ref_2174_, v___x_2179_);
v___x_2181_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_2182_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2260____1___closed__1, &l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1);
v___x_2183_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__2));
lean_inc(v_currMacroScope_2173_);
lean_inc(v_quotContext_2172_);
v___x_2184_ = l_Lean_addMacroScope(v_quotContext_2172_, v___x_2183_, v_currMacroScope_2173_);
v___x_2185_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__4));
lean_inc_n(v___x_2180_, 2);
v___x_2186_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2180_);
lean_ctor_set(v___x_2186_, 1, v___x_2182_);
lean_ctor_set(v___x_2186_, 2, v___x_2184_);
lean_ctor_set(v___x_2186_, 3, v___x_2185_);
v___x_2187_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_2188_ = l_Lean_Syntax_node2(v___x_2180_, v___x_2187_, v___x_2176_, v___x_2178_);
v___x_2189_ = l_Lean_Syntax_node2(v___x_2180_, v___x_2181_, v___x_2186_, v___x_2188_);
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v_a_2167_);
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____1___boxed(lean_object* v_x_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l___aux__Init__Core______macroRules__term___u2260____1(v_x_2191_, v_a_2192_, v_a_2193_);
lean_dec_ref(v_a_2192_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Ne__1(lean_object* v_x_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_2195_);
v___x_2199_ = l_Lean_Syntax_isOfKind(v_x_2195_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec(v_x_2195_);
v___x_2200_ = lean_box(0);
v___x_2201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v_a_2197_);
return v___x_2201_;
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = l_Lean_Syntax_getArg(v_x_2195_, v___x_2202_);
v___x_2204_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_2203_);
v___x_2205_ = l_Lean_Syntax_isOfKind(v___x_2203_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec(v___x_2203_);
lean_dec(v_x_2195_);
v___x_2206_ = lean_box(0);
v___x_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v_a_2197_);
return v___x_2207_;
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2208_ = lean_unsigned_to_nat(1u);
v___x_2209_ = l_Lean_Syntax_getArg(v_x_2195_, v___x_2208_);
lean_dec(v_x_2195_);
v___x_2210_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2209_);
v___x_2211_ = l_Lean_Syntax_matchesNull(v___x_2209_, v___x_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec(v___x_2209_);
lean_dec(v___x_2203_);
v___x_2212_ = lean_box(0);
v___x_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v_a_2197_);
return v___x_2213_;
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v_ref_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2214_ = l_Lean_Syntax_getArg(v___x_2209_, v___x_2202_);
v___x_2215_ = l_Lean_Syntax_getArg(v___x_2209_, v___x_2208_);
lean_dec(v___x_2209_);
v_ref_2216_ = l_Lean_replaceRef(v___x_2203_, v_a_2196_);
lean_dec(v___x_2203_);
v___x_2217_ = 0;
v___x_2218_ = l_Lean_SourceInfo_fromRef(v_ref_2216_, v___x_2217_);
lean_dec(v_ref_2216_);
v___x_2219_ = ((lean_object*)(l_term___u2260___00__closed__1));
v___x_2220_ = ((lean_object*)(l_term___u2260___00__closed__2));
lean_inc(v___x_2218_);
v___x_2221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2218_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = l_Lean_Syntax_node3(v___x_2218_, v___x_2219_, v___x_2214_, v___x_2221_, v___x_2215_);
v___x_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v_a_2197_);
return v___x_2223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Ne__1___boxed(lean_object* v_x_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l___aux__Init__Core______unexpand__Ne__1(v_x_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____2(lean_object* v_x_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v___x_2238_; uint8_t v___x_2239_; 
v___x_2238_ = ((lean_object*)(l_term___u2260___00__closed__1));
lean_inc(v_x_2235_);
v___x_2239_ = l_Lean_Syntax_isOfKind(v_x_2235_, v___x_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
lean_dec(v_x_2235_);
v___x_2240_ = lean_box(1);
v___x_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
lean_ctor_set(v___x_2241_, 1, v_a_2237_);
return v___x_2241_;
}
else
{
lean_object* v_quotContext_2242_; lean_object* v_currMacroScope_2243_; lean_object* v_ref_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v_quotContext_2242_ = lean_ctor_get(v_a_2236_, 1);
v_currMacroScope_2243_ = lean_ctor_get(v_a_2236_, 2);
v_ref_2244_ = lean_ctor_get(v_a_2236_, 5);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = l_Lean_Syntax_getArg(v_x_2235_, v___x_2245_);
v___x_2247_ = lean_unsigned_to_nat(2u);
v___x_2248_ = l_Lean_Syntax_getArg(v_x_2235_, v___x_2247_);
lean_dec(v_x_2235_);
v___x_2249_ = 0;
v___x_2250_ = l_Lean_SourceInfo_fromRef(v_ref_2244_, v___x_2249_);
v___x_2251_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____2___closed__1));
v___x_2252_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____2___closed__2));
lean_inc_n(v___x_2250_, 2);
v___x_2253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2250_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2260____1___closed__1, &l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1);
v___x_2255_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__2));
lean_inc(v_currMacroScope_2243_);
lean_inc(v_quotContext_2242_);
v___x_2256_ = l_Lean_addMacroScope(v_quotContext_2242_, v___x_2255_, v_currMacroScope_2243_);
v___x_2257_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__4));
v___x_2258_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2250_);
lean_ctor_set(v___x_2258_, 1, v___x_2254_);
lean_ctor_set(v___x_2258_, 2, v___x_2256_);
lean_ctor_set(v___x_2258_, 3, v___x_2257_);
v___x_2259_ = l_Lean_Syntax_node4(v___x_2250_, v___x_2251_, v___x_2253_, v___x_2258_, v___x_2246_, v___x_2248_);
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
lean_ctor_set(v___x_2260_, 1, v_a_2237_);
return v___x_2260_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____2___boxed(lean_object* v_x_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l___aux__Init__Core______macroRules__term___u2260____2(v_x_2261_, v_a_2262_, v_a_2263_);
lean_dec_ref(v_a_2262_);
return v_res_2264_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__5));
v___x_2280_ = l_String_toRawSubstring_x27(v___x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1(lean_object* v_x_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2294_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2));
v___x_2295_ = l_Lean_Syntax_isOfKind(v_x_2291_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = lean_box(1);
v___x_2297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_ctor_set(v___x_2297_, 1, v_a_2293_);
return v___x_2297_;
}
else
{
lean_object* v_quotContext_2298_; lean_object* v_currMacroScope_2299_; lean_object* v_ref_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_quotContext_2298_ = lean_ctor_get(v_a_2292_, 1);
v_currMacroScope_2299_ = lean_ctor_get(v_a_2292_, 2);
v_ref_2300_ = lean_ctor_get(v_a_2292_, 5);
v___x_2301_ = 0;
v___x_2302_ = l_Lean_SourceInfo_fromRef(v_ref_2300_, v___x_2301_);
v___x_2303_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3));
v___x_2304_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4));
lean_inc_n(v___x_2302_, 2);
v___x_2305_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2302_);
lean_ctor_set(v___x_2305_, 1, v___x_2303_);
v___x_2306_ = lean_obj_once(&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6, &l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6_once, _init_l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6);
v___x_2307_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8));
lean_inc(v_currMacroScope_2299_);
lean_inc(v_quotContext_2298_);
v___x_2308_ = l_Lean_addMacroScope(v_quotContext_2298_, v___x_2307_, v_currMacroScope_2299_);
v___x_2309_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__10));
v___x_2310_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2302_);
lean_ctor_set(v___x_2310_, 1, v___x_2306_);
lean_ctor_set(v___x_2310_, 2, v___x_2308_);
lean_ctor_set(v___x_2310_, 3, v___x_2309_);
v___x_2311_ = l_Lean_Syntax_node2(v___x_2302_, v___x_2304_, v___x_2305_, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v_a_2293_);
return v___x_2312_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___boxed(lean_object* v_x_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1(v_x_2313_, v_a_2314_, v_a_2315_);
lean_dec_ref(v_a_2314_);
return v_res_2316_;
}
}
static lean_object* _init_l_instTransIff(void){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_box(0);
return v___x_2317_;
}
}
LEAN_EXPORT uint8_t l_toBoolUsing___redArg(uint8_t v_d_2318_){
_start:
{
return v_d_2318_;
}
}
LEAN_EXPORT lean_object* l_toBoolUsing___redArg___boxed(lean_object* v_d_2319_){
_start:
{
uint8_t v_d_boxed_2320_; uint8_t v_res_2321_; lean_object* v_r_2322_; 
v_d_boxed_2320_ = lean_unbox(v_d_2319_);
v_res_2321_ = l_toBoolUsing___redArg(v_d_boxed_2320_);
v_r_2322_ = lean_box(v_res_2321_);
return v_r_2322_;
}
}
LEAN_EXPORT uint8_t l_toBoolUsing(lean_object* v_p_2323_, uint8_t v_d_2324_){
_start:
{
return v_d_2324_;
}
}
LEAN_EXPORT lean_object* l_toBoolUsing___boxed(lean_object* v_p_2325_, lean_object* v_d_2326_){
_start:
{
uint8_t v_d_boxed_2327_; uint8_t v_res_2328_; lean_object* v_r_2329_; 
v_d_boxed_2327_ = lean_unbox(v_d_2326_);
v_res_2328_ = l_toBoolUsing(v_p_2325_, v_d_boxed_2327_);
v_r_2329_ = lean_box(v_res_2328_);
return v_r_2329_;
}
}
static uint8_t _init_l_instDecidableTrue(void){
_start:
{
uint8_t v___x_2330_; 
v___x_2330_ = 1;
return v___x_2330_;
}
}
static uint8_t _init_l_instDecidableFalse(void){
_start:
{
uint8_t v___x_2331_; 
v___x_2331_ = 0;
return v___x_2331_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__iff___redArg(uint8_t v_dp_2332_){
_start:
{
return v_dp_2332_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__iff___redArg___boxed(lean_object* v_dp_2333_){
_start:
{
uint8_t v_dp_boxed_2334_; uint8_t v_res_2335_; lean_object* v_r_2336_; 
v_dp_boxed_2334_ = lean_unbox(v_dp_2333_);
v_res_2335_ = l_decidable__of__decidable__of__iff___redArg(v_dp_boxed_2334_);
v_r_2336_ = lean_box(v_res_2335_);
return v_r_2336_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__iff(lean_object* v_p_2337_, lean_object* v_q_2338_, uint8_t v_dp_2339_, lean_object* v_h_2340_){
_start:
{
return v_dp_2339_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__iff___boxed(lean_object* v_p_2341_, lean_object* v_q_2342_, lean_object* v_dp_2343_, lean_object* v_h_2344_){
_start:
{
uint8_t v_dp_boxed_2345_; uint8_t v_res_2346_; lean_object* v_r_2347_; 
v_dp_boxed_2345_ = lean_unbox(v_dp_2343_);
v_res_2346_ = l_decidable__of__decidable__of__iff(v_p_2341_, v_q_2342_, v_dp_boxed_2345_, v_h_2344_);
v_r_2347_ = lean_box(v_res_2346_);
return v_r_2347_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__eq___redArg(uint8_t v_inst_2348_){
_start:
{
return v_inst_2348_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__eq___redArg___boxed(lean_object* v_inst_2349_){
_start:
{
uint8_t v_inst_8__boxed_2350_; uint8_t v_res_2351_; lean_object* v_r_2352_; 
v_inst_8__boxed_2350_ = lean_unbox(v_inst_2349_);
v_res_2351_ = l_decidable__of__decidable__of__eq___redArg(v_inst_8__boxed_2350_);
v_r_2352_ = lean_box(v_res_2351_);
return v_r_2352_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__eq(lean_object* v_p_2353_, lean_object* v_q_2354_, uint8_t v_inst_2355_, lean_object* v_h_2356_){
_start:
{
return v_inst_2355_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__eq___boxed(lean_object* v_p_2357_, lean_object* v_q_2358_, lean_object* v_inst_2359_, lean_object* v_h_2360_){
_start:
{
uint8_t v_inst_11__boxed_2361_; uint8_t v_res_2362_; lean_object* v_r_2363_; 
v_inst_11__boxed_2361_ = lean_unbox(v_inst_2359_);
v_res_2362_ = l_decidable__of__decidable__of__eq(v_p_2357_, v_q_2358_, v_inst_11__boxed_2361_, v_h_2360_);
v_r_2363_ = lean_box(v_res_2362_);
return v_r_2363_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIff___redArg(uint8_t v_dp_2364_, uint8_t v_dq_2365_){
_start:
{
if (v_dq_2365_ == 0)
{
if (v_dp_2364_ == 0)
{
uint8_t v___x_2366_; 
v___x_2366_ = 1;
return v___x_2366_;
}
else
{
return v_dq_2365_;
}
}
else
{
return v_dp_2364_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableIff___redArg___boxed(lean_object* v_dp_2367_, lean_object* v_dq_2368_){
_start:
{
uint8_t v_dp_boxed_2369_; uint8_t v_dq_boxed_2370_; uint8_t v_res_2371_; lean_object* v_r_2372_; 
v_dp_boxed_2369_ = lean_unbox(v_dp_2367_);
v_dq_boxed_2370_ = lean_unbox(v_dq_2368_);
v_res_2371_ = l_instDecidableIff___redArg(v_dp_boxed_2369_, v_dq_boxed_2370_);
v_r_2372_ = lean_box(v_res_2371_);
return v_r_2372_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIff(lean_object* v_p_2373_, lean_object* v_q_2374_, uint8_t v_dp_2375_, uint8_t v_dq_2376_){
_start:
{
if (v_dq_2376_ == 0)
{
if (v_dp_2375_ == 0)
{
uint8_t v___x_2377_; 
v___x_2377_ = 1;
return v___x_2377_;
}
else
{
return v_dq_2376_;
}
}
else
{
return v_dp_2375_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableIff___boxed(lean_object* v_p_2378_, lean_object* v_q_2379_, lean_object* v_dp_2380_, lean_object* v_dq_2381_){
_start:
{
uint8_t v_dp_boxed_2382_; uint8_t v_dq_boxed_2383_; uint8_t v_res_2384_; lean_object* v_r_2385_; 
v_dp_boxed_2382_ = lean_unbox(v_dp_2380_);
v_dq_boxed_2383_ = lean_unbox(v_dq_2381_);
v_res_2384_ = l_instDecidableIff(v_p_2378_, v_q_2379_, v_dp_boxed_2382_, v_dq_boxed_2383_);
v_r_2385_ = lean_box(v_res_2384_);
return v_r_2385_;
}
}
LEAN_EXPORT lean_object* l_iteInduction___redArg(uint8_t v_inst_2386_, lean_object* v_hpos_2387_, lean_object* v_hneg_2388_){
_start:
{
if (v_inst_2386_ == 0)
{
lean_object* v___x_2389_; 
lean_dec(v_hpos_2387_);
v___x_2389_ = lean_apply_1(v_hneg_2388_, lean_box(0));
return v___x_2389_;
}
else
{
lean_object* v___x_2390_; 
lean_dec(v_hneg_2388_);
v___x_2390_ = lean_apply_1(v_hpos_2387_, lean_box(0));
return v___x_2390_;
}
}
}
LEAN_EXPORT lean_object* l_iteInduction___redArg___boxed(lean_object* v_inst_2391_, lean_object* v_hpos_2392_, lean_object* v_hneg_2393_){
_start:
{
uint8_t v_inst_boxed_2394_; lean_object* v_res_2395_; 
v_inst_boxed_2394_ = lean_unbox(v_inst_2391_);
v_res_2395_ = l_iteInduction___redArg(v_inst_boxed_2394_, v_hpos_2392_, v_hneg_2393_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_iteInduction(lean_object* v_00_u03b1_2396_, lean_object* v_c_2397_, uint8_t v_inst_2398_, lean_object* v_motive_2399_, lean_object* v_t_2400_, lean_object* v_e_2401_, lean_object* v_hpos_2402_, lean_object* v_hneg_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_iteInduction___redArg(v_inst_2398_, v_hpos_2402_, v_hneg_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_iteInduction___boxed(lean_object* v_00_u03b1_2405_, lean_object* v_c_2406_, lean_object* v_inst_2407_, lean_object* v_motive_2408_, lean_object* v_t_2409_, lean_object* v_e_2410_, lean_object* v_hpos_2411_, lean_object* v_hneg_2412_){
_start:
{
uint8_t v_inst_boxed_2413_; lean_object* v_res_2414_; 
v_inst_boxed_2413_ = lean_unbox(v_inst_2407_);
v_res_2414_ = l_iteInduction(v_00_u03b1_2405_, v_c_2406_, v_inst_boxed_2413_, v_motive_2408_, v_t_2409_, v_e_2410_, v_hpos_2411_, v_hneg_2412_);
lean_dec(v_e_2410_);
lean_dec(v_t_2409_);
return v_res_2414_;
}
}
LEAN_EXPORT uint8_t l_instDecidableDite___redArg(uint8_t v_dC_2415_, lean_object* v_dT_2416_, lean_object* v_dE_2417_){
_start:
{
if (v_dC_2415_ == 0)
{
lean_object* v___x_2418_; uint8_t v___x_2419_; 
lean_dec_ref(v_dT_2416_);
v___x_2418_ = lean_apply_1(v_dE_2417_, lean_box(0));
v___x_2419_ = lean_unbox(v___x_2418_);
return v___x_2419_;
}
else
{
lean_object* v___x_2420_; uint8_t v___x_2421_; 
lean_dec_ref(v_dE_2417_);
v___x_2420_ = lean_apply_1(v_dT_2416_, lean_box(0));
v___x_2421_ = lean_unbox(v___x_2420_);
return v___x_2421_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableDite___redArg___boxed(lean_object* v_dC_2422_, lean_object* v_dT_2423_, lean_object* v_dE_2424_){
_start:
{
uint8_t v_dC_boxed_2425_; uint8_t v_res_2426_; lean_object* v_r_2427_; 
v_dC_boxed_2425_ = lean_unbox(v_dC_2422_);
v_res_2426_ = l_instDecidableDite___redArg(v_dC_boxed_2425_, v_dT_2423_, v_dE_2424_);
v_r_2427_ = lean_box(v_res_2426_);
return v_r_2427_;
}
}
LEAN_EXPORT uint8_t l_instDecidableDite(lean_object* v_c_2428_, lean_object* v_t_2429_, lean_object* v_e_2430_, uint8_t v_dC_2431_, lean_object* v_dT_2432_, lean_object* v_dE_2433_){
_start:
{
if (v_dC_2431_ == 0)
{
lean_object* v___x_2434_; uint8_t v___x_2435_; 
lean_dec_ref(v_dT_2432_);
v___x_2434_ = lean_apply_1(v_dE_2433_, lean_box(0));
v___x_2435_ = lean_unbox(v___x_2434_);
return v___x_2435_;
}
else
{
lean_object* v___x_2436_; uint8_t v___x_2437_; 
lean_dec_ref(v_dE_2433_);
v___x_2436_ = lean_apply_1(v_dT_2432_, lean_box(0));
v___x_2437_ = lean_unbox(v___x_2436_);
return v___x_2437_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableDite___boxed(lean_object* v_c_2438_, lean_object* v_t_2439_, lean_object* v_e_2440_, lean_object* v_dC_2441_, lean_object* v_dT_2442_, lean_object* v_dE_2443_){
_start:
{
uint8_t v_dC_boxed_2444_; uint8_t v_res_2445_; lean_object* v_r_2446_; 
v_dC_boxed_2444_ = lean_unbox(v_dC_2441_);
v_res_2445_ = l_instDecidableDite(v_c_2438_, v_t_2439_, v_e_2440_, v_dC_boxed_2444_, v_dT_2442_, v_dE_2443_);
v_r_2446_ = lean_box(v_res_2445_);
return v_r_2446_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg___lam__0(lean_object* v_a_2447_){
_start:
{
lean_inc(v_a_2447_);
return v_a_2447_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg___lam__0___boxed(lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_noConfusionEnum___redArg___lam__0(v_a_2448_);
lean_dec(v_a_2448_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg(lean_object* v_f_2451_, lean_object* v_x_2452_, lean_object* v_y_2453_){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; lean_object* v___f_2457_; 
lean_inc_ref(v_f_2451_);
v___x_2454_ = lean_apply_1(v_f_2451_, v_x_2452_);
v___x_2455_ = lean_apply_1(v_f_2451_, v_y_2453_);
v___x_2456_ = lean_nat_dec_eq(v___x_2454_, v___x_2455_);
lean_dec(v___x_2455_);
lean_dec(v___x_2454_);
v___f_2457_ = ((lean_object*)(l_noConfusionEnum___redArg___closed__0));
return v___f_2457_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum(lean_object* v_00_u03b1_2458_, lean_object* v_f_2459_, lean_object* v_P_2460_, lean_object* v_x_2461_, lean_object* v_y_2462_, lean_object* v_h_2463_){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; lean_object* v___f_2467_; 
lean_inc_ref(v_f_2459_);
v___x_2464_ = lean_apply_1(v_f_2459_, v_x_2461_);
v___x_2465_ = lean_apply_1(v_f_2459_, v_y_2462_);
v___x_2466_ = lean_nat_dec_eq(v___x_2464_, v___x_2465_);
lean_dec(v___x_2465_);
lean_dec(v___x_2464_);
v___f_2467_ = ((lean_object*)(l_noConfusionEnum___redArg___closed__0));
return v___f_2467_;
}
}
static lean_object* _init_l_instInhabitedProp(void){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_box(0);
return v___x_2468_;
}
}
static lean_object* _init_l_instInhabitedNonScalar_default(void){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_unsigned_to_nat(0u);
return v___x_2469_;
}
}
static lean_object* _init_l_instInhabitedNonScalar(void){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_unsigned_to_nat(0u);
return v___x_2470_;
}
}
static lean_object* _init_l_instInhabitedPNonScalar_default(void){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_unsigned_to_nat(0u);
return v___x_2471_;
}
}
static lean_object* _init_l_instInhabitedPNonScalar(void){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_unsigned_to_nat(0u);
return v___x_2472_;
}
}
static lean_object* _init_l_instInhabitedTrue(void){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_box(0);
return v___x_2473_;
}
}
LEAN_EXPORT uint8_t l_Subtype_instBEq___redArg___lam__0(lean_object* v_inst_2474_, lean_object* v_x_2475_, lean_object* v_y_2476_){
_start:
{
lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2477_ = lean_apply_2(v_inst_2474_, v_x_2475_, v_y_2476_);
v___x_2478_ = lean_unbox(v___x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq___redArg___lam__0___boxed(lean_object* v_inst_2479_, lean_object* v_x_2480_, lean_object* v_y_2481_){
_start:
{
uint8_t v_res_2482_; lean_object* v_r_2483_; 
v_res_2482_ = l_Subtype_instBEq___redArg___lam__0(v_inst_2479_, v_x_2480_, v_y_2481_);
v_r_2483_ = lean_box(v_res_2482_);
return v_r_2483_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq___redArg(lean_object* v_inst_2484_){
_start:
{
lean_object* v___f_2485_; 
v___f_2485_ = lean_alloc_closure((void*)(l_Subtype_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2485_, 0, v_inst_2484_);
return v___f_2485_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq(lean_object* v_00_u03b1_2486_, lean_object* v_p_2487_, lean_object* v_inst_2488_){
_start:
{
lean_object* v___f_2489_; 
v___f_2489_ = lean_alloc_closure((void*)(l_Subtype_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2489_, 0, v_inst_2488_);
return v___f_2489_;
}
}
LEAN_EXPORT uint8_t l_Subtype_instDecidableEq___redArg(lean_object* v_inst_2490_, lean_object* v_x_2491_, lean_object* v_x_2492_){
_start:
{
lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = lean_apply_2(v_inst_2490_, v_x_2491_, v_x_2492_);
v___x_2494_ = lean_unbox(v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instDecidableEq___redArg___boxed(lean_object* v_inst_2495_, lean_object* v_x_2496_, lean_object* v_x_2497_){
_start:
{
uint8_t v_res_2498_; lean_object* v_r_2499_; 
v_res_2498_ = l_Subtype_instDecidableEq___redArg(v_inst_2495_, v_x_2496_, v_x_2497_);
v_r_2499_ = lean_box(v_res_2498_);
return v_r_2499_;
}
}
LEAN_EXPORT uint8_t l_Subtype_instDecidableEq(lean_object* v_00_u03b1_2500_, lean_object* v_p_2501_, lean_object* v_inst_2502_, lean_object* v_x_2503_, lean_object* v_x_2504_){
_start:
{
lean_object* v___x_2505_; uint8_t v___x_2506_; 
v___x_2505_ = lean_apply_2(v_inst_2502_, v_x_2503_, v_x_2504_);
v___x_2506_ = lean_unbox(v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instDecidableEq___boxed(lean_object* v_00_u03b1_2507_, lean_object* v_p_2508_, lean_object* v_inst_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_){
_start:
{
uint8_t v_res_2512_; lean_object* v_r_2513_; 
v_res_2512_ = l_Subtype_instDecidableEq(v_00_u03b1_2507_, v_p_2508_, v_inst_2509_, v_x_2510_, v_x_2511_);
v_r_2513_ = lean_box(v_res_2512_);
return v_r_2513_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedLeft___redArg(lean_object* v_inst_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v_inst_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedLeft(lean_object* v_00_u03b1_2516_, lean_object* v_00_u03b2_2517_, lean_object* v_inst_2518_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2519_, 0, v_inst_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedRight___redArg(lean_object* v_inst_2520_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2521_, 0, v_inst_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedRight(lean_object* v_00_u03b1_2522_, lean_object* v_00_u03b2_2523_, lean_object* v_inst_2524_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_inst_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum_decEq___redArg(lean_object* v_inst_2526_, lean_object* v_inst_2527_, lean_object* v_x_2528_, lean_object* v_x_2529_){
_start:
{
if (lean_obj_tag(v_x_2528_) == 0)
{
lean_dec_ref(v_inst_2527_);
if (lean_obj_tag(v_x_2529_) == 0)
{
lean_object* v_val_2530_; lean_object* v_val_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v_val_2530_ = lean_ctor_get(v_x_2528_, 0);
lean_inc(v_val_2530_);
lean_dec_ref_known(v_x_2528_, 1);
v_val_2531_ = lean_ctor_get(v_x_2529_, 0);
lean_inc(v_val_2531_);
lean_dec_ref_known(v_x_2529_, 1);
v___x_2532_ = lean_apply_2(v_inst_2526_, v_val_2530_, v_val_2531_);
v___x_2533_ = lean_unbox(v___x_2532_);
return v___x_2533_;
}
else
{
uint8_t v___x_2534_; 
lean_dec_ref_known(v_x_2529_, 1);
lean_dec_ref_known(v_x_2528_, 1);
lean_dec_ref(v_inst_2526_);
v___x_2534_ = 0;
return v___x_2534_;
}
}
else
{
lean_dec_ref(v_inst_2526_);
if (lean_obj_tag(v_x_2529_) == 0)
{
uint8_t v___x_2535_; 
lean_dec_ref_known(v_x_2529_, 1);
lean_dec_ref_known(v_x_2528_, 1);
lean_dec_ref(v_inst_2527_);
v___x_2535_ = 0;
return v___x_2535_;
}
else
{
lean_object* v_val_2536_; lean_object* v_val_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v_val_2536_ = lean_ctor_get(v_x_2528_, 0);
lean_inc(v_val_2536_);
lean_dec_ref_known(v_x_2528_, 1);
v_val_2537_ = lean_ctor_get(v_x_2529_, 0);
lean_inc(v_val_2537_);
lean_dec_ref_known(v_x_2529_, 1);
v___x_2538_ = lean_apply_2(v_inst_2527_, v_val_2536_, v_val_2537_);
v___x_2539_ = lean_unbox(v___x_2538_);
return v___x_2539_;
}
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum_decEq___redArg___boxed(lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_x_2542_, lean_object* v_x_2543_){
_start:
{
uint8_t v_res_2544_; lean_object* v_r_2545_; 
v_res_2544_ = l_instDecidableEqSum_decEq___redArg(v_inst_2540_, v_inst_2541_, v_x_2542_, v_x_2543_);
v_r_2545_ = lean_box(v_res_2544_);
return v_r_2545_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum_decEq(lean_object* v_00_u03b1_2546_, lean_object* v_00_u03b2_2547_, lean_object* v_inst_2548_, lean_object* v_inst_2549_, lean_object* v_x_2550_, lean_object* v_x_2551_){
_start:
{
uint8_t v___x_2552_; 
v___x_2552_ = l_instDecidableEqSum_decEq___redArg(v_inst_2548_, v_inst_2549_, v_x_2550_, v_x_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum_decEq___boxed(lean_object* v_00_u03b1_2553_, lean_object* v_00_u03b2_2554_, lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_x_2557_, lean_object* v_x_2558_){
_start:
{
uint8_t v_res_2559_; lean_object* v_r_2560_; 
v_res_2559_ = l_instDecidableEqSum_decEq(v_00_u03b1_2553_, v_00_u03b2_2554_, v_inst_2555_, v_inst_2556_, v_x_2557_, v_x_2558_);
v_r_2560_ = lean_box(v_res_2559_);
return v_r_2560_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum___redArg(lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_){
_start:
{
uint8_t v___x_2565_; 
v___x_2565_ = l_instDecidableEqSum_decEq___redArg(v_inst_2561_, v_inst_2562_, v_x_2563_, v_x_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum___redArg___boxed(lean_object* v_inst_2566_, lean_object* v_inst_2567_, lean_object* v_x_2568_, lean_object* v_x_2569_){
_start:
{
uint8_t v_res_2570_; lean_object* v_r_2571_; 
v_res_2570_ = l_instDecidableEqSum___redArg(v_inst_2566_, v_inst_2567_, v_x_2568_, v_x_2569_);
v_r_2571_ = lean_box(v_res_2570_);
return v_r_2571_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum(lean_object* v_00_u03b1_2572_, lean_object* v_00_u03b2_2573_, lean_object* v_inst_2574_, lean_object* v_inst_2575_, lean_object* v_x_2576_, lean_object* v_x_2577_){
_start:
{
uint8_t v___x_2578_; 
v___x_2578_ = l_instDecidableEqSum_decEq___redArg(v_inst_2574_, v_inst_2575_, v_x_2576_, v_x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum___boxed(lean_object* v_00_u03b1_2579_, lean_object* v_00_u03b2_2580_, lean_object* v_inst_2581_, lean_object* v_inst_2582_, lean_object* v_x_2583_, lean_object* v_x_2584_){
_start:
{
uint8_t v_res_2585_; lean_object* v_r_2586_; 
v_res_2585_ = l_instDecidableEqSum(v_00_u03b1_2579_, v_00_u03b2_2580_, v_inst_2581_, v_inst_2582_, v_x_2583_, v_x_2584_);
v_r_2586_ = lean_box(v_res_2585_);
return v_r_2586_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedProd___redArg(lean_object* v_inst_2587_, lean_object* v_inst_2588_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2589_, 0, v_inst_2587_);
lean_ctor_set(v___x_2589_, 1, v_inst_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedProd(lean_object* v_00_u03b1_2590_, lean_object* v_00_u03b2_2591_, lean_object* v_inst_2592_, lean_object* v_inst_2593_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2594_, 0, v_inst_2592_);
lean_ctor_set(v___x_2594_, 1, v_inst_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedMProd___redArg(lean_object* v_inst_2595_, lean_object* v_inst_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v_inst_2595_);
lean_ctor_set(v___x_2597_, 1, v_inst_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedMProd(lean_object* v_00_u03b1_2598_, lean_object* v_00_u03b2_2599_, lean_object* v_inst_2600_, lean_object* v_inst_2601_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2602_, 0, v_inst_2600_);
lean_ctor_set(v___x_2602_, 1, v_inst_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedPProd___redArg(lean_object* v_inst_2603_, lean_object* v_inst_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v_inst_2603_);
lean_ctor_set(v___x_2605_, 1, v_inst_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedPProd(lean_object* v_00_u03b1_2606_, lean_object* v_00_u03b2_2607_, lean_object* v_inst_2608_, lean_object* v_inst_2609_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v_inst_2608_);
lean_ctor_set(v___x_2610_, 1, v_inst_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqProd___redArg(lean_object* v_h_2611_, lean_object* v_h_x27_2612_, lean_object* v_x_2613_, lean_object* v_x_2614_){
_start:
{
lean_object* v_fst_2615_; lean_object* v_snd_2616_; lean_object* v_fst_2617_; lean_object* v_snd_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; 
v_fst_2615_ = lean_ctor_get(v_x_2613_, 0);
lean_inc(v_fst_2615_);
v_snd_2616_ = lean_ctor_get(v_x_2613_, 1);
lean_inc(v_snd_2616_);
lean_dec_ref(v_x_2613_);
v_fst_2617_ = lean_ctor_get(v_x_2614_, 0);
lean_inc(v_fst_2617_);
v_snd_2618_ = lean_ctor_get(v_x_2614_, 1);
lean_inc(v_snd_2618_);
lean_dec_ref(v_x_2614_);
v___x_2619_ = lean_apply_2(v_h_2611_, v_fst_2615_, v_fst_2617_);
v___x_2620_ = lean_unbox(v___x_2619_);
if (v___x_2620_ == 0)
{
uint8_t v___x_2621_; 
lean_dec(v_snd_2618_);
lean_dec(v_snd_2616_);
lean_dec_ref(v_h_x27_2612_);
v___x_2621_ = lean_unbox(v___x_2619_);
return v___x_2621_;
}
else
{
lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = lean_apply_2(v_h_x27_2612_, v_snd_2616_, v_snd_2618_);
v___x_2623_ = lean_unbox(v___x_2622_);
return v___x_2623_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqProd___redArg___boxed(lean_object* v_h_2624_, lean_object* v_h_x27_2625_, lean_object* v_x_2626_, lean_object* v_x_2627_){
_start:
{
uint8_t v_res_2628_; lean_object* v_r_2629_; 
v_res_2628_ = l_instDecidableEqProd___redArg(v_h_2624_, v_h_x27_2625_, v_x_2626_, v_x_2627_);
v_r_2629_ = lean_box(v_res_2628_);
return v_r_2629_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqProd(lean_object* v_00_u03b1_2630_, lean_object* v_00_u03b2_2631_, lean_object* v_h_2632_, lean_object* v_h_x27_2633_, lean_object* v_x_2634_, lean_object* v_x_2635_){
_start:
{
uint8_t v___x_2636_; 
v___x_2636_ = l_instDecidableEqProd___redArg(v_h_2632_, v_h_x27_2633_, v_x_2634_, v_x_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqProd___boxed(lean_object* v_00_u03b1_2637_, lean_object* v_00_u03b2_2638_, lean_object* v_h_2639_, lean_object* v_h_x27_2640_, lean_object* v_x_2641_, lean_object* v_x_2642_){
_start:
{
uint8_t v_res_2643_; lean_object* v_r_2644_; 
v_res_2643_ = l_instDecidableEqProd(v_00_u03b1_2637_, v_00_u03b2_2638_, v_h_2639_, v_h_x27_2640_, v_x_2641_, v_x_2642_);
v_r_2644_ = lean_box(v_res_2643_);
return v_r_2644_;
}
}
LEAN_EXPORT uint8_t l_instBEqProd___redArg___lam__0(lean_object* v_inst_2645_, lean_object* v_inst_2646_, lean_object* v_x_2647_, lean_object* v_x_2648_){
_start:
{
lean_object* v_fst_2649_; lean_object* v_snd_2650_; lean_object* v_fst_2651_; lean_object* v_snd_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v_fst_2649_ = lean_ctor_get(v_x_2647_, 0);
lean_inc(v_fst_2649_);
v_snd_2650_ = lean_ctor_get(v_x_2647_, 1);
lean_inc(v_snd_2650_);
lean_dec_ref(v_x_2647_);
v_fst_2651_ = lean_ctor_get(v_x_2648_, 0);
lean_inc(v_fst_2651_);
v_snd_2652_ = lean_ctor_get(v_x_2648_, 1);
lean_inc(v_snd_2652_);
lean_dec_ref(v_x_2648_);
v___x_2653_ = lean_apply_2(v_inst_2645_, v_fst_2649_, v_fst_2651_);
v___x_2654_ = lean_unbox(v___x_2653_);
if (v___x_2654_ == 0)
{
uint8_t v___x_2655_; 
lean_dec(v_snd_2652_);
lean_dec(v_snd_2650_);
lean_dec_ref(v_inst_2646_);
v___x_2655_ = lean_unbox(v___x_2653_);
return v___x_2655_;
}
else
{
lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2656_ = lean_apply_2(v_inst_2646_, v_snd_2650_, v_snd_2652_);
v___x_2657_ = lean_unbox(v___x_2656_);
return v___x_2657_;
}
}
}
LEAN_EXPORT lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object* v_inst_2658_, lean_object* v_inst_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_){
_start:
{
uint8_t v_res_2662_; lean_object* v_r_2663_; 
v_res_2662_ = l_instBEqProd___redArg___lam__0(v_inst_2658_, v_inst_2659_, v_x_2660_, v_x_2661_);
v_r_2663_ = lean_box(v_res_2662_);
return v_r_2663_;
}
}
LEAN_EXPORT lean_object* l_instBEqProd___redArg(lean_object* v_inst_2664_, lean_object* v_inst_2665_){
_start:
{
lean_object* v___f_2666_; 
v___f_2666_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2666_, 0, v_inst_2664_);
lean_closure_set(v___f_2666_, 1, v_inst_2665_);
return v___f_2666_;
}
}
LEAN_EXPORT lean_object* l_instBEqProd(lean_object* v_00_u03b1_2667_, lean_object* v_00_u03b2_2668_, lean_object* v_inst_2669_, lean_object* v_inst_2670_){
_start:
{
lean_object* v___f_2671_; 
v___f_2671_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2671_, 0, v_inst_2669_);
lean_closure_set(v___f_2671_, 1, v_inst_2670_);
return v___f_2671_;
}
}
LEAN_EXPORT uint8_t l_Prod_lexLtDec___redArg(lean_object* v_inst_2672_, lean_object* v_inst_2673_, lean_object* v_inst_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_){
_start:
{
lean_object* v_fst_2677_; lean_object* v_snd_2678_; lean_object* v_fst_2679_; lean_object* v_snd_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v_fst_2677_ = lean_ctor_get(v_x_2675_, 0);
lean_inc_n(v_fst_2677_, 2);
v_snd_2678_ = lean_ctor_get(v_x_2675_, 1);
lean_inc(v_snd_2678_);
lean_dec_ref(v_x_2675_);
v_fst_2679_ = lean_ctor_get(v_x_2676_, 0);
lean_inc_n(v_fst_2679_, 2);
v_snd_2680_ = lean_ctor_get(v_x_2676_, 1);
lean_inc(v_snd_2680_);
lean_dec_ref(v_x_2676_);
v___x_2681_ = lean_apply_2(v_inst_2673_, v_fst_2677_, v_fst_2679_);
v___x_2682_ = lean_unbox(v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; uint8_t v___x_2684_; 
v___x_2683_ = lean_apply_2(v_inst_2672_, v_fst_2677_, v_fst_2679_);
v___x_2684_ = lean_unbox(v___x_2683_);
if (v___x_2684_ == 0)
{
uint8_t v___x_2685_; 
lean_dec(v_snd_2680_);
lean_dec(v_snd_2678_);
lean_dec_ref(v_inst_2674_);
v___x_2685_ = lean_unbox(v___x_2683_);
return v___x_2685_;
}
else
{
lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2686_ = lean_apply_2(v_inst_2674_, v_snd_2678_, v_snd_2680_);
v___x_2687_ = lean_unbox(v___x_2686_);
return v___x_2687_;
}
}
else
{
uint8_t v___x_2688_; 
lean_dec(v_snd_2680_);
lean_dec(v_fst_2679_);
lean_dec(v_snd_2678_);
lean_dec(v_fst_2677_);
lean_dec_ref(v_inst_2674_);
lean_dec_ref(v_inst_2672_);
v___x_2688_ = lean_unbox(v___x_2681_);
return v___x_2688_;
}
}
}
LEAN_EXPORT lean_object* l_Prod_lexLtDec___redArg___boxed(lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_x_2692_, lean_object* v_x_2693_){
_start:
{
uint8_t v_res_2694_; lean_object* v_r_2695_; 
v_res_2694_ = l_Prod_lexLtDec___redArg(v_inst_2689_, v_inst_2690_, v_inst_2691_, v_x_2692_, v_x_2693_);
v_r_2695_ = lean_box(v_res_2694_);
return v_r_2695_;
}
}
LEAN_EXPORT uint8_t l_Prod_lexLtDec(lean_object* v_00_u03b1_2696_, lean_object* v_00_u03b2_2697_, lean_object* v_inst_2698_, lean_object* v_inst_2699_, lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_x_2703_, lean_object* v_x_2704_){
_start:
{
uint8_t v___x_2705_; 
v___x_2705_ = l_Prod_lexLtDec___redArg(v_inst_2700_, v_inst_2701_, v_inst_2702_, v_x_2703_, v_x_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Prod_lexLtDec___boxed(lean_object* v_00_u03b1_2706_, lean_object* v_00_u03b2_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_x_2713_, lean_object* v_x_2714_){
_start:
{
uint8_t v_res_2715_; lean_object* v_r_2716_; 
v_res_2715_ = l_Prod_lexLtDec(v_00_u03b1_2706_, v_00_u03b2_2707_, v_inst_2708_, v_inst_2709_, v_inst_2710_, v_inst_2711_, v_inst_2712_, v_x_2713_, v_x_2714_);
v_r_2716_ = lean_box(v_res_2715_);
return v_r_2716_;
}
}
LEAN_EXPORT lean_object* l_Prod_map___redArg(lean_object* v_f_2717_, lean_object* v_g_2718_, lean_object* v_x_2719_){
_start:
{
lean_object* v_fst_2720_; lean_object* v_snd_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2730_; 
v_fst_2720_ = lean_ctor_get(v_x_2719_, 0);
v_snd_2721_ = lean_ctor_get(v_x_2719_, 1);
v_isSharedCheck_2730_ = !lean_is_exclusive(v_x_2719_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2723_ = v_x_2719_;
v_isShared_2724_ = v_isSharedCheck_2730_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_snd_2721_);
lean_inc(v_fst_2720_);
lean_dec(v_x_2719_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2730_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2725_ = lean_apply_1(v_f_2717_, v_fst_2720_);
v___x_2726_ = lean_apply_1(v_g_2718_, v_snd_2721_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 1, v___x_2726_);
lean_ctor_set(v___x_2723_, 0, v___x_2725_);
v___x_2728_ = v___x_2723_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_map(lean_object* v_00_u03b1_u2081_2731_, lean_object* v_00_u03b1_u2082_2732_, lean_object* v_00_u03b2_u2081_2733_, lean_object* v_00_u03b2_u2082_2734_, lean_object* v_f_2735_, lean_object* v_g_2736_, lean_object* v_x_2737_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Prod_map___redArg(v_f_2735_, v_g_2736_, v_x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSigma___redArg(lean_object* v_h_u2081_2739_, lean_object* v_h_u2082_2740_, lean_object* v_x_2741_, lean_object* v_x_2742_){
_start:
{
lean_object* v_fst_2743_; lean_object* v_snd_2744_; lean_object* v_fst_2745_; lean_object* v_snd_2746_; lean_object* v_decide_2747_; uint8_t v___x_2748_; 
v_fst_2743_ = lean_ctor_get(v_x_2741_, 0);
lean_inc_n(v_fst_2743_, 2);
v_snd_2744_ = lean_ctor_get(v_x_2741_, 1);
lean_inc(v_snd_2744_);
lean_dec_ref(v_x_2741_);
v_fst_2745_ = lean_ctor_get(v_x_2742_, 0);
lean_inc(v_fst_2745_);
v_snd_2746_ = lean_ctor_get(v_x_2742_, 1);
lean_inc(v_snd_2746_);
lean_dec_ref(v_x_2742_);
v_decide_2747_ = lean_apply_2(v_h_u2081_2739_, v_fst_2743_, v_fst_2745_);
v___x_2748_ = lean_unbox(v_decide_2747_);
if (v___x_2748_ == 0)
{
uint8_t v___x_2749_; 
lean_dec(v_snd_2746_);
lean_dec(v_snd_2744_);
lean_dec(v_fst_2743_);
lean_dec_ref(v_h_u2082_2740_);
v___x_2749_ = lean_unbox(v_decide_2747_);
return v___x_2749_;
}
else
{
lean_object* v_decide_2750_; uint8_t v___x_2751_; 
v_decide_2750_ = lean_apply_3(v_h_u2082_2740_, v_fst_2743_, v_snd_2744_, v_snd_2746_);
v___x_2751_ = lean_unbox(v_decide_2750_);
if (v___x_2751_ == 0)
{
uint8_t v___x_2752_; 
v___x_2752_ = lean_unbox(v_decide_2750_);
return v___x_2752_;
}
else
{
uint8_t v___x_2753_; 
v___x_2753_ = lean_unbox(v_decide_2747_);
return v___x_2753_;
}
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSigma___redArg___boxed(lean_object* v_h_u2081_2754_, lean_object* v_h_u2082_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_){
_start:
{
uint8_t v_res_2758_; lean_object* v_r_2759_; 
v_res_2758_ = l_instDecidableEqSigma___redArg(v_h_u2081_2754_, v_h_u2082_2755_, v_x_2756_, v_x_2757_);
v_r_2759_ = lean_box(v_res_2758_);
return v_r_2759_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSigma(lean_object* v_00_u03b1_2760_, lean_object* v_00_u03b2_2761_, lean_object* v_h_u2081_2762_, lean_object* v_h_u2082_2763_, lean_object* v_x_2764_, lean_object* v_x_2765_){
_start:
{
uint8_t v___x_2766_; 
v___x_2766_ = l_instDecidableEqSigma___redArg(v_h_u2081_2762_, v_h_u2082_2763_, v_x_2764_, v_x_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSigma___boxed(lean_object* v_00_u03b1_2767_, lean_object* v_00_u03b2_2768_, lean_object* v_h_u2081_2769_, lean_object* v_h_u2082_2770_, lean_object* v_x_2771_, lean_object* v_x_2772_){
_start:
{
uint8_t v_res_2773_; lean_object* v_r_2774_; 
v_res_2773_ = l_instDecidableEqSigma(v_00_u03b1_2767_, v_00_u03b2_2768_, v_h_u2081_2769_, v_h_u2082_2770_, v_x_2771_, v_x_2772_);
v_r_2774_ = lean_box(v_res_2773_);
return v_r_2774_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPSigma___redArg(lean_object* v_h_u2081_2775_, lean_object* v_h_u2082_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_){
_start:
{
lean_object* v_fst_2779_; lean_object* v_snd_2780_; lean_object* v_fst_2781_; lean_object* v_snd_2782_; lean_object* v_decide_2783_; uint8_t v___x_2784_; 
v_fst_2779_ = lean_ctor_get(v_x_2777_, 0);
lean_inc_n(v_fst_2779_, 2);
v_snd_2780_ = lean_ctor_get(v_x_2777_, 1);
lean_inc(v_snd_2780_);
lean_dec_ref(v_x_2777_);
v_fst_2781_ = lean_ctor_get(v_x_2778_, 0);
lean_inc(v_fst_2781_);
v_snd_2782_ = lean_ctor_get(v_x_2778_, 1);
lean_inc(v_snd_2782_);
lean_dec_ref(v_x_2778_);
v_decide_2783_ = lean_apply_2(v_h_u2081_2775_, v_fst_2779_, v_fst_2781_);
v___x_2784_ = lean_unbox(v_decide_2783_);
if (v___x_2784_ == 0)
{
uint8_t v___x_2785_; 
lean_dec(v_snd_2782_);
lean_dec(v_snd_2780_);
lean_dec(v_fst_2779_);
lean_dec_ref(v_h_u2082_2776_);
v___x_2785_ = lean_unbox(v_decide_2783_);
return v___x_2785_;
}
else
{
lean_object* v_decide_2786_; uint8_t v___x_2787_; 
v_decide_2786_ = lean_apply_3(v_h_u2082_2776_, v_fst_2779_, v_snd_2780_, v_snd_2782_);
v___x_2787_ = lean_unbox(v_decide_2786_);
if (v___x_2787_ == 0)
{
uint8_t v___x_2788_; 
v___x_2788_ = lean_unbox(v_decide_2786_);
return v___x_2788_;
}
else
{
uint8_t v___x_2789_; 
v___x_2789_ = lean_unbox(v_decide_2783_);
return v___x_2789_;
}
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPSigma___redArg___boxed(lean_object* v_h_u2081_2790_, lean_object* v_h_u2082_2791_, lean_object* v_x_2792_, lean_object* v_x_2793_){
_start:
{
uint8_t v_res_2794_; lean_object* v_r_2795_; 
v_res_2794_ = l_instDecidableEqPSigma___redArg(v_h_u2081_2790_, v_h_u2082_2791_, v_x_2792_, v_x_2793_);
v_r_2795_ = lean_box(v_res_2794_);
return v_r_2795_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPSigma(lean_object* v_00_u03b1_2796_, lean_object* v_00_u03b2_2797_, lean_object* v_h_u2081_2798_, lean_object* v_h_u2082_2799_, lean_object* v_x_2800_, lean_object* v_x_2801_){
_start:
{
uint8_t v___x_2802_; 
v___x_2802_ = l_instDecidableEqPSigma___redArg(v_h_u2081_2798_, v_h_u2082_2799_, v_x_2800_, v_x_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPSigma___boxed(lean_object* v_00_u03b1_2803_, lean_object* v_00_u03b2_2804_, lean_object* v_h_u2081_2805_, lean_object* v_h_u2082_2806_, lean_object* v_x_2807_, lean_object* v_x_2808_){
_start:
{
uint8_t v_res_2809_; lean_object* v_r_2810_; 
v_res_2809_ = l_instDecidableEqPSigma(v_00_u03b1_2803_, v_00_u03b2_2804_, v_h_u2081_2805_, v_h_u2082_2806_, v_x_2807_, v_x_2808_);
v_r_2810_ = lean_box(v_res_2809_);
return v_r_2810_;
}
}
static lean_object* _init_l_instInhabitedPUnit(void){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_box(0);
return v___x_2811_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPUnit___redArg(){
_start:
{
uint8_t v___x_2813_; 
v___x_2813_ = 1;
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPUnit___redArg___boxed(lean_object* v___dummy_2814_){
_start:
{
uint8_t v_res_2815_; lean_object* v_r_2816_; 
v_res_2815_ = l_instDecidableEqPUnit___redArg();
v_r_2816_ = lean_box(v_res_2815_);
return v_r_2816_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPUnit(lean_object* v_a_2817_, lean_object* v_b_2818_){
_start:
{
uint8_t v___x_2819_; 
v___x_2819_ = 1;
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPUnit___boxed(lean_object* v_a_2820_, lean_object* v_b_2821_){
_start:
{
uint8_t v_res_2822_; lean_object* v_r_2823_; 
v_res_2822_ = l_instDecidableEqPUnit(v_a_2820_, v_b_2821_);
v_r_2823_ = lean_box(v_res_2822_);
return v_r_2823_;
}
}
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid___redArg(){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = lean_box(0);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid___redArg___boxed(lean_object* v___dummy_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_instHasEquivOfSetoid___redArg();
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid(lean_object* v_00_u03b1_2828_, lean_object* v_inst_2829_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = lean_box(0);
return v___x_2830_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfIff___redArg(uint8_t v_d_2831_){
_start:
{
return v_d_2831_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___redArg___boxed(lean_object* v_d_2832_){
_start:
{
uint8_t v_d_boxed_2833_; uint8_t v_res_2834_; lean_object* v_r_2835_; 
v_d_boxed_2833_ = lean_unbox(v_d_2832_);
v_res_2834_ = l_instDecidableEqOfIff___redArg(v_d_boxed_2833_);
v_r_2835_ = lean_box(v_res_2834_);
return v_r_2835_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfIff(lean_object* v_p_2836_, lean_object* v_q_2837_, uint8_t v_d_2838_){
_start:
{
return v_d_2838_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___boxed(lean_object* v_p_2839_, lean_object* v_q_2840_, lean_object* v_d_2841_){
_start:
{
uint8_t v_d_boxed_2842_; uint8_t v_res_2843_; lean_object* v_r_2844_; 
v_d_boxed_2842_ = lean_unbox(v_d_2841_);
v_res_2843_ = l_instDecidableEqOfIff(v_p_2839_, v_q_2840_, v_d_boxed_2842_);
v_r_2844_ = lean_box(v_res_2843_);
return v_r_2844_;
}
}
LEAN_EXPORT lean_object* l_Not_elim___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Not_elim___redArg___boxed(lean_object* v___dummy_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Not_elim___redArg();
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Not_elim(lean_object* v_a_2848_, lean_object* v_00_u03b1_2849_, lean_object* v_H1_2850_, lean_object* v_H2_2851_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_And_elim___redArg(lean_object* v_f_2852_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_apply_2(v_f_2852_, lean_box(0), lean_box(0));
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_And_elim(lean_object* v_a_2854_, lean_object* v_b_2855_, lean_object* v_00_u03b1_2856_, lean_object* v_f_2857_, lean_object* v_h_2858_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = lean_apply_2(v_f_2857_, lean_box(0), lean_box(0));
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Iff_elim___redArg(lean_object* v_f_2860_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = lean_apply_2(v_f_2860_, lean_box(0), lean_box(0));
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Iff_elim(lean_object* v_a_2862_, lean_object* v_b_2863_, lean_object* v_00_u03b1_2864_, lean_object* v_f_2865_, lean_object* v_h_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_apply_2(v_f_2865_, lean_box(0), lean_box(0));
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Quot_rec___redArg(lean_object* v_f_2868_, lean_object* v_q_2869_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = lean_apply_1(v_f_2868_, v_q_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Quot_rec(lean_object* v_00_u03b1_2871_, lean_object* v_r_2872_, lean_object* v_motive_2873_, lean_object* v_f_2874_, lean_object* v_h_2875_, lean_object* v_q_2876_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = lean_apply_1(v_f_2874_, v_q_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOn___redArg(lean_object* v_q_2878_, lean_object* v_f_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = lean_apply_1(v_f_2879_, v_q_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOn(lean_object* v_00_u03b1_2881_, lean_object* v_r_2882_, lean_object* v_motive_2883_, lean_object* v_q_2884_, lean_object* v_f_2885_, lean_object* v_h_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = lean_apply_1(v_f_2885_, v_q_2884_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOnSubsingleton___redArg(lean_object* v_q_2888_, lean_object* v_f_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = lean_apply_1(v_f_2889_, v_q_2888_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOnSubsingleton(lean_object* v_00_u03b1_2891_, lean_object* v_r_2892_, lean_object* v_motive_2893_, lean_object* v_h_2894_, lean_object* v_q_2895_, lean_object* v_f_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_apply_1(v_f_2896_, v_q_2895_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Quot_hrecOn___redArg(lean_object* v_q_2898_, lean_object* v_f_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_apply_1(v_f_2899_, v_q_2898_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Quot_hrecOn(lean_object* v_00_u03b1_2901_, lean_object* v_r_2902_, lean_object* v_motive_2903_, lean_object* v_q_2904_, lean_object* v_f_2905_, lean_object* v_c_2906_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_apply_1(v_f_2905_, v_q_2904_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___redArg(lean_object* v_a_2908_){
_start:
{
lean_inc(v_a_2908_);
return v_a_2908_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___redArg___boxed(lean_object* v_a_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Quotient_mk___redArg(v_a_2909_);
lean_dec(v_a_2909_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk(lean_object* v_00_u03b1_2911_, lean_object* v_s_2912_, lean_object* v_a_2913_){
_start:
{
lean_inc(v_a_2913_);
return v_a_2913_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___boxed(lean_object* v_00_u03b1_2914_, lean_object* v_s_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Quotient_mk(v_00_u03b1_2914_, v_s_2915_, v_a_2916_);
lean_dec(v_a_2916_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___redArg(lean_object* v_a_2918_){
_start:
{
lean_inc(v_a_2918_);
return v_a_2918_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___redArg___boxed(lean_object* v_a_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Quotient_mk_x27___redArg(v_a_2919_);
lean_dec(v_a_2919_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27(lean_object* v_00_u03b1_2921_, lean_object* v_s_2922_, lean_object* v_a_2923_){
_start:
{
lean_inc(v_a_2923_);
return v_a_2923_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___boxed(lean_object* v_00_u03b1_2924_, lean_object* v_s_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Quotient_mk_x27(v_00_u03b1_2924_, v_s_2925_, v_a_2926_);
lean_dec(v_a_2926_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift___redArg(lean_object* v_f_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_apply_1(v_f_2928_, v_a_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift(lean_object* v_00_u03b1_2931_, lean_object* v_00_u03b2_2932_, lean_object* v_s_2933_, lean_object* v_f_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_apply_1(v_f_2934_, v_a_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn___redArg(lean_object* v_q_2938_, lean_object* v_f_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = lean_apply_1(v_f_2939_, v_q_2938_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn(lean_object* v_00_u03b1_2941_, lean_object* v_00_u03b2_2942_, lean_object* v_s_2943_, lean_object* v_q_2944_, lean_object* v_f_2945_, lean_object* v_c_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_apply_1(v_f_2945_, v_q_2944_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Quotient_rec___redArg(lean_object* v_f_2948_, lean_object* v_q_2949_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_apply_1(v_f_2948_, v_q_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Quotient_rec(lean_object* v_00_u03b1_2951_, lean_object* v_s_2952_, lean_object* v_motive_2953_, lean_object* v_f_2954_, lean_object* v_h_2955_, lean_object* v_q_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = lean_apply_1(v_f_2954_, v_q_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOn___redArg(lean_object* v_q_2958_, lean_object* v_f_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_apply_1(v_f_2959_, v_q_2958_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOn(lean_object* v_00_u03b1_2961_, lean_object* v_s_2962_, lean_object* v_motive_2963_, lean_object* v_q_2964_, lean_object* v_f_2965_, lean_object* v_h_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_apply_1(v_f_2965_, v_q_2964_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton___redArg(lean_object* v_q_2968_, lean_object* v_f_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = lean_apply_1(v_f_2969_, v_q_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton(lean_object* v_00_u03b1_2971_, lean_object* v_s_2972_, lean_object* v_motive_2973_, lean_object* v_h_2974_, lean_object* v_q_2975_, lean_object* v_f_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_apply_1(v_f_2976_, v_q_2975_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Quotient_hrecOn___redArg(lean_object* v_q_2978_, lean_object* v_f_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_apply_1(v_f_2979_, v_q_2978_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Quotient_hrecOn(lean_object* v_00_u03b1_2981_, lean_object* v_s_2982_, lean_object* v_motive_2983_, lean_object* v_q_2984_, lean_object* v_f_2985_, lean_object* v_c_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_apply_1(v_f_2985_, v_q_2984_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift_u2082___redArg(lean_object* v_f_2988_, lean_object* v_q_u2081_2989_, lean_object* v_q_u2082_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_apply_2(v_f_2988_, v_q_u2081_2989_, v_q_u2082_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift_u2082(lean_object* v_00_u03b1_2992_, lean_object* v_00_u03b2_2993_, lean_object* v_00_u03c6_2994_, lean_object* v_s_u2081_2995_, lean_object* v_s_u2082_2996_, lean_object* v_f_2997_, lean_object* v_c_2998_, lean_object* v_q_u2081_2999_, lean_object* v_q_u2082_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_apply_2(v_f_2997_, v_q_u2081_2999_, v_q_u2082_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn_u2082___redArg(lean_object* v_q_u2081_3002_, lean_object* v_q_u2082_3003_, lean_object* v_f_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_apply_2(v_f_3004_, v_q_u2081_3002_, v_q_u2082_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn_u2082(lean_object* v_00_u03b1_3006_, lean_object* v_00_u03b2_3007_, lean_object* v_00_u03c6_3008_, lean_object* v_s_u2081_3009_, lean_object* v_s_u2082_3010_, lean_object* v_q_u2081_3011_, lean_object* v_q_u2082_3012_, lean_object* v_f_3013_, lean_object* v_c_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_apply_2(v_f_3013_, v_q_u2081_3011_, v_q_u2082_3012_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton_u2082___redArg(lean_object* v_q_u2081_3016_, lean_object* v_q_u2082_3017_, lean_object* v_g_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = lean_apply_2(v_g_3018_, v_q_u2081_3016_, v_q_u2082_3017_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton_u2082(lean_object* v_00_u03b1_3020_, lean_object* v_00_u03b2_3021_, lean_object* v_s_u2081_3022_, lean_object* v_s_u2082_3023_, lean_object* v_motive_3024_, lean_object* v_s_3025_, lean_object* v_q_u2081_3026_, lean_object* v_q_u2082_3027_, lean_object* v_g_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_apply_2(v_g_3028_, v_q_u2081_3026_, v_q_u2082_3027_);
return v___x_3029_;
}
}
LEAN_EXPORT uint8_t l_Quotient_decidableEq___redArg(lean_object* v_d_3030_, lean_object* v_q_u2081_3031_, lean_object* v_q_u2082_3032_){
_start:
{
lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = lean_apply_2(v_d_3030_, v_q_u2081_3031_, v_q_u2082_3032_);
v___x_3034_ = lean_unbox(v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Quotient_decidableEq___redArg___boxed(lean_object* v_d_3035_, lean_object* v_q_u2081_3036_, lean_object* v_q_u2082_3037_){
_start:
{
uint8_t v_res_3038_; lean_object* v_r_3039_; 
v_res_3038_ = l_Quotient_decidableEq___redArg(v_d_3035_, v_q_u2081_3036_, v_q_u2082_3037_);
v_r_3039_ = lean_box(v_res_3038_);
return v_r_3039_;
}
}
LEAN_EXPORT uint8_t l_Quotient_decidableEq(lean_object* v_00_u03b1_3040_, lean_object* v_s_3041_, lean_object* v_d_3042_, lean_object* v_q_u2081_3043_, lean_object* v_q_u2082_3044_){
_start:
{
lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = lean_apply_2(v_d_3042_, v_q_u2081_3043_, v_q_u2082_3044_);
v___x_3046_ = lean_unbox(v___x_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Quotient_decidableEq___boxed(lean_object* v_00_u03b1_3047_, lean_object* v_s_3048_, lean_object* v_d_3049_, lean_object* v_q_u2081_3050_, lean_object* v_q_u2082_3051_){
_start:
{
uint8_t v_res_3052_; lean_object* v_r_3053_; 
v_res_3052_ = l_Quotient_decidableEq(v_00_u03b1_3047_, v_s_3048_, v_d_3049_, v_q_u2081_3050_, v_q_u2082_3051_);
v_r_3053_ = lean_box(v_res_3052_);
return v_r_3053_;
}
}
LEAN_EXPORT lean_object* l_Quot_pliftOn___redArg(lean_object* v_q_3054_, lean_object* v_f_3055_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_apply_2(v_f_3055_, v_q_3054_, lean_box(0));
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Quot_pliftOn(lean_object* v_00_u03b2_3057_, lean_object* v_00_u03b1_3058_, lean_object* v_r_3059_, lean_object* v_q_3060_, lean_object* v_f_3061_, lean_object* v_h_3062_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_apply_2(v_f_3061_, v_q_3060_, lean_box(0));
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Quotient_pliftOn___redArg(lean_object* v_q_3064_, lean_object* v_f_3065_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = lean_apply_2(v_f_3065_, v_q_3064_, lean_box(0));
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Quotient_pliftOn(lean_object* v_00_u03b2_3067_, lean_object* v_00_u03b1_3068_, lean_object* v_s_3069_, lean_object* v_q_3070_, lean_object* v_f_3071_, lean_object* v_h_3072_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = lean_apply_2(v_f_3071_, v_q_3070_, lean_box(0));
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Setoid_trivial___redArg(){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_box(0);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Setoid_trivial___redArg___boxed(lean_object* v___dummy_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Setoid_trivial___redArg();
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Setoid_trivial(lean_object* v_00_u03b1_3078_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = lean_box(0);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___redArg(lean_object* v_x_3080_){
_start:
{
lean_inc(v_x_3080_);
return v_x_3080_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___redArg___boxed(lean_object* v_x_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Squash_mk___redArg(v_x_3081_);
lean_dec(v_x_3081_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk(lean_object* v_00_u03b1_3083_, lean_object* v_x_3084_){
_start:
{
lean_inc(v_x_3084_);
return v_x_3084_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___boxed(lean_object* v_00_u03b1_3085_, lean_object* v_x_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_Squash_mk(v_00_u03b1_3085_, v_x_3086_);
lean_dec(v_x_3086_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Squash_lift___redArg(lean_object* v_s_3088_, lean_object* v_f_3089_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_apply_1(v_f_3089_, v_s_3088_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Squash_lift(lean_object* v_00_u03b1_3091_, lean_object* v_00_u03b2_3092_, lean_object* v_inst_3093_, lean_object* v_s_3094_, lean_object* v_f_3095_){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_apply_1(v_f_3095_, v_s_3094_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___redArg(lean_object* v_x_3097_){
_start:
{
lean_inc(v_x_3097_);
return v_x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___redArg___boxed(lean_object* v_x_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_opaqueId___redArg(v_x_3098_);
lean_dec(v_x_3098_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId(lean_object* v_00_u03b1_3100_, lean_object* v_x_3101_){
_start:
{
lean_inc(v_x_3101_);
return v_x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___boxed(lean_object* v_00_u03b1_3102_, lean_object* v_x_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_opaqueId(v_00_u03b1_3102_, v_x_3103_);
lean_dec(v_x_3103_);
return v_res_3104_;
}
}
lean_object* runtime_initialize_Init_SizeOf(uint8_t builtin);
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Core(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_SizeOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Task_Priority_default = _init_l_Task_Priority_default();
lean_mark_persistent(l_Task_Priority_default);
l_Task_Priority_max = _init_l_Task_Priority_max();
lean_mark_persistent(l_Task_Priority_max);
l_Task_Priority_dedicated = _init_l_Task_Priority_dedicated();
lean_mark_persistent(l_Task_Priority_dedicated);
l_instTransIff = _init_l_instTransIff();
l_instDecidableTrue = _init_l_instDecidableTrue();
l_instDecidableFalse = _init_l_instDecidableFalse();
l_instInhabitedProp = _init_l_instInhabitedProp();
l_instInhabitedNonScalar_default = _init_l_instInhabitedNonScalar_default();
lean_mark_persistent(l_instInhabitedNonScalar_default);
l_instInhabitedNonScalar = _init_l_instInhabitedNonScalar();
lean_mark_persistent(l_instInhabitedNonScalar);
l_instInhabitedPNonScalar_default = _init_l_instInhabitedPNonScalar_default();
lean_mark_persistent(l_instInhabitedPNonScalar_default);
l_instInhabitedPNonScalar = _init_l_instInhabitedPNonScalar();
lean_mark_persistent(l_instInhabitedPNonScalar);
l_instInhabitedTrue = _init_l_instInhabitedTrue();
l_instInhabitedPUnit = _init_l_instInhabitedPUnit();
lean_mark_persistent(l_instInhabitedPUnit);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Core(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_SizeOf(uint8_t builtin);
lean_object* initialize_Init_Tactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Core(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_SizeOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Core(builtin);
}
#ifdef __cplusplus
}
#endif
