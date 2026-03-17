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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instDecidableEqEmpty(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instDecidableEqEmpty___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_thunkCoe___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_thunkCoe___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_thunkCoe___lam__1(lean_object*);
static const lean_closure_object l_thunkCoe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_thunkCoe___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_thunkCoe___closed__0 = (const lean_object*)&l_thunkCoe___closed__0_value;
LEAN_EXPORT lean_object* l_thunkCoe(lean_object*);
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
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_noConfusionEnum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instDecidableEqPUnit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqOfIff___redArg(uint8_t);
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqOfIff(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Not_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_And_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_And_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Iff_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Iff_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quot_liftOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Quot_liftOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Setoid_trivial(lean_object*);
LEAN_EXPORT lean_object* l_Squash_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Squash_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Squash_mk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Squash_mk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Squash_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Squash_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_reduceBool(uint8_t);
LEAN_EXPORT lean_object* l_Lean_reduceBool___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_reduceNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_reduceNat___boxed(lean_object*);
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
lean_dec_ref(v_x_3_);
v___x_5_ = 0;
return v___x_5_;
}
}
else
{
if (lean_obj_tag(v_x_3_) == 0)
{
uint8_t v___x_6_; 
lean_dec_ref(v_x_2_);
lean_dec_ref(v_inst_1_);
v___x_6_ = 0;
return v___x_6_;
}
else
{
lean_object* v_val_7_; lean_object* v_val_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_val_7_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_val_7_);
lean_dec_ref(v_x_2_);
v_val_8_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_val_8_);
lean_dec_ref(v_x_3_);
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
LEAN_EXPORT uint8_t l_instDecidableEqEmpty(uint8_t v_a_59_, uint8_t v_b_60_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_instDecidableEqEmpty___boxed(lean_object* v_a_61_, lean_object* v_b_62_){
_start:
{
uint8_t v_a_boxed_63_; uint8_t v_b_boxed_64_; uint8_t v_res_65_; lean_object* v_r_66_; 
v_a_boxed_63_ = lean_unbox(v_a_61_);
v_b_boxed_64_ = lean_unbox(v_b_62_);
v_res_65_ = l_instDecidableEqEmpty(v_a_boxed_63_, v_b_boxed_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPEmpty(uint8_t v_a_67_, uint8_t v_b_68_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPEmpty___boxed(lean_object* v_a_69_, lean_object* v_b_70_){
_start:
{
uint8_t v_a_boxed_71_; uint8_t v_b_boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_a_boxed_71_ = lean_unbox(v_a_69_);
v_b_boxed_72_ = lean_unbox(v_b_70_);
v_res_73_ = l_instDecidableEqPEmpty(v_a_boxed_71_, v_b_boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_Thunk_mk___boxed(lean_object* v_00_u03b1_77_, lean_object* v_fn_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lean_mk_thunk(v_fn_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Thunk_pure___boxed(lean_object* v_00_u03b1_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = lean_thunk_pure(v_a_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Thunk_get___boxed(lean_object* v_00_u03b1_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = lean_thunk_get_own(v_x_88_);
lean_dec_ref(v_x_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Thunk_fnImpl___redArg(lean_object* v_x_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_thunk_get_own(v_x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Thunk_fnImpl___redArg___boxed(lean_object* v_x_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Thunk_fnImpl___redArg(v_x_92_);
lean_dec_ref(v_x_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Thunk_fnImpl(lean_object* v_00_u03b1_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_thunk_get_own(v_x_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Thunk_fnImpl___boxed(lean_object* v_00_u03b1_98_, lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Thunk_fnImpl(v_00_u03b1_98_, v_x_99_, v_x_100_);
lean_dec_ref(v_x_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Thunk_map___redArg___lam__0(lean_object* v_x_102_, lean_object* v_f_103_, lean_object* v_x_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_thunk_get_own(v_x_102_);
v___x_106_ = lean_apply_1(v_f_103_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Thunk_map___redArg___lam__0___boxed(lean_object* v_x_107_, lean_object* v_f_108_, lean_object* v_x_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Thunk_map___redArg___lam__0(v_x_107_, v_f_108_, v_x_109_);
lean_dec_ref(v_x_107_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Thunk_map___redArg(lean_object* v_f_111_, lean_object* v_x_112_){
_start:
{
lean_object* v___f_113_; lean_object* v___x_114_; 
v___f_113_ = lean_alloc_closure((void*)(l_Thunk_map___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_113_, 0, v_x_112_);
lean_closure_set(v___f_113_, 1, v_f_111_);
v___x_114_ = lean_mk_thunk(v___f_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Thunk_map(lean_object* v_00_u03b1_115_, lean_object* v_00_u03b2_116_, lean_object* v_f_117_, lean_object* v_x_118_){
_start:
{
lean_object* v___f_119_; lean_object* v___x_120_; 
v___f_119_ = lean_alloc_closure((void*)(l_Thunk_map___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_119_, 0, v_x_118_);
lean_closure_set(v___f_119_, 1, v_f_117_);
v___x_120_ = lean_mk_thunk(v___f_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Thunk_bind___redArg___lam__0(lean_object* v_x_121_, lean_object* v_f_122_, lean_object* v_x_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = lean_thunk_get_own(v_x_121_);
v___x_125_ = lean_apply_1(v_f_122_, v___x_124_);
v___x_126_ = lean_thunk_get_own(v___x_125_);
lean_dec_ref(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Thunk_bind___redArg___lam__0___boxed(lean_object* v_x_127_, lean_object* v_f_128_, lean_object* v_x_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Thunk_bind___redArg___lam__0(v_x_127_, v_f_128_, v_x_129_);
lean_dec_ref(v_x_127_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Thunk_bind___redArg(lean_object* v_x_131_, lean_object* v_f_132_){
_start:
{
lean_object* v___f_133_; lean_object* v___x_134_; 
v___f_133_ = lean_alloc_closure((void*)(l_Thunk_bind___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_133_, 0, v_x_131_);
lean_closure_set(v___f_133_, 1, v_f_132_);
v___x_134_ = lean_mk_thunk(v___f_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Thunk_bind(lean_object* v_00_u03b1_135_, lean_object* v_00_u03b2_136_, lean_object* v_x_137_, lean_object* v_f_138_){
_start:
{
lean_object* v___f_139_; lean_object* v___x_140_; 
v___f_139_ = lean_alloc_closure((void*)(l_Thunk_bind___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_139_, 0, v_x_137_);
lean_closure_set(v___f_139_, 1, v_f_138_);
v___x_140_ = lean_mk_thunk(v___f_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe___lam__0(lean_object* v_a_141_, lean_object* v_x_142_){
_start:
{
lean_inc(v_a_141_);
return v_a_141_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe___lam__0___boxed(lean_object* v_a_143_, lean_object* v_x_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_thunkCoe___lam__0(v_a_143_, v_x_144_);
lean_dec(v_a_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe___lam__1(lean_object* v_a_146_){
_start:
{
lean_object* v___f_147_; lean_object* v___x_148_; 
v___f_147_ = lean_alloc_closure((void*)(l_thunkCoe___lam__0___boxed), 2, 1);
lean_closure_set(v___f_147_, 0, v_a_146_);
v___x_148_ = lean_mk_thunk(v___f_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe(lean_object* v_00_u03b1_150_){
_start:
{
lean_object* v___f_151_; 
v___f_151_ = ((lean_object*)(l_thunkCoe___closed__0));
return v___f_151_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn___redArg(lean_object* v_m_152_){
_start:
{
lean_inc(v_m_152_);
return v_m_152_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn___redArg___boxed(lean_object* v_m_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Eq_ndrecOn___redArg(v_m_153_);
lean_dec(v_m_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn(lean_object* v_00_u03b1_155_, lean_object* v_a_156_, lean_object* v_motive_157_, lean_object* v_b_158_, lean_object* v_h_159_, lean_object* v_m_160_){
_start:
{
lean_inc(v_m_160_);
return v_m_160_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn___boxed(lean_object* v_00_u03b1_161_, lean_object* v_a_162_, lean_object* v_motive_163_, lean_object* v_b_164_, lean_object* v_h_165_, lean_object* v_m_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Eq_ndrecOn(v_00_u03b1_161_, v_a_162_, v_motive_163_, v_b_164_, v_h_165_, v_m_166_);
lean_dec(v_m_166_);
lean_dec(v_b_164_);
lean_dec(v_a_162_);
return v_res_167_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5));
v___x_204_ = l_String_toRawSubstring_x27(v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1(lean_object* v_x_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = ((lean_object*)(l_term___x3c_x2d_x3e___00__closed__1));
lean_inc(v_x_221_);
v___x_225_ = l_Lean_Syntax_isOfKind(v_x_221_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec_ref(v_a_222_);
lean_dec(v_x_221_);
v___x_226_ = lean_box(1);
v___x_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_a_223_);
return v___x_227_;
}
else
{
lean_object* v_quotContext_228_; lean_object* v_currMacroScope_229_; lean_object* v_ref_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_quotContext_228_ = lean_ctor_get(v_a_222_, 1);
lean_inc(v_quotContext_228_);
v_currMacroScope_229_ = lean_ctor_get(v_a_222_, 2);
lean_inc(v_currMacroScope_229_);
v_ref_230_ = lean_ctor_get(v_a_222_, 5);
lean_inc(v_ref_230_);
lean_dec_ref(v_a_222_);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = l_Lean_Syntax_getArg(v_x_221_, v___x_231_);
v___x_233_ = lean_unsigned_to_nat(2u);
v___x_234_ = l_Lean_Syntax_getArg(v_x_221_, v___x_233_);
lean_dec(v_x_221_);
v___x_235_ = 0;
v___x_236_ = l_Lean_SourceInfo_fromRef(v_ref_230_, v___x_235_);
lean_dec(v_ref_230_);
v___x_237_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_238_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6, &l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6_once, _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6);
v___x_239_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7));
v___x_240_ = l_Lean_addMacroScope(v_quotContext_228_, v___x_239_, v_currMacroScope_229_);
v___x_241_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11));
lean_inc(v___x_236_);
v___x_242_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_242_, 0, v___x_236_);
lean_ctor_set(v___x_242_, 1, v___x_238_);
lean_ctor_set(v___x_242_, 2, v___x_240_);
lean_ctor_set(v___x_242_, 3, v___x_241_);
v___x_243_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_236_);
v___x_244_ = l_Lean_Syntax_node2(v___x_236_, v___x_243_, v___x_232_, v___x_234_);
v___x_245_ = l_Lean_Syntax_node2(v___x_236_, v___x_237_, v___x_242_, v___x_244_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v_a_223_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__1(lean_object* v_x_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_250_);
v___x_254_ = l_Lean_Syntax_isOfKind(v_x_250_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v_x_250_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v_a_252_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = l_Lean_Syntax_getArg(v_x_250_, v___x_257_);
v___x_259_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_258_);
v___x_260_ = l_Lean_Syntax_isOfKind(v___x_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec(v___x_258_);
lean_dec(v_x_250_);
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v_a_252_);
return v___x_262_;
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = l_Lean_Syntax_getArg(v_x_250_, v___x_263_);
lean_dec(v_x_250_);
v___x_265_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_264_);
v___x_266_ = l_Lean_Syntax_matchesNull(v___x_264_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v___x_264_);
lean_dec(v___x_258_);
v___x_267_ = lean_box(0);
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v_a_252_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_ref_271_; uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_269_ = l_Lean_Syntax_getArg(v___x_264_, v___x_257_);
v___x_270_ = l_Lean_Syntax_getArg(v___x_264_, v___x_263_);
lean_dec(v___x_264_);
v_ref_271_ = l_Lean_replaceRef(v___x_258_, v_a_251_);
lean_dec(v___x_258_);
v___x_272_ = 0;
v___x_273_ = l_Lean_SourceInfo_fromRef(v_ref_271_, v___x_272_);
lean_dec(v_ref_271_);
v___x_274_ = ((lean_object*)(l_term___x3c_x2d_x3e___00__closed__1));
v___x_275_ = ((lean_object*)(l_term___x3c_x2d_x3e___00__closed__4));
lean_inc(v___x_273_);
v___x_276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_273_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = l_Lean_Syntax_node3(v___x_273_, v___x_274_, v___x_269_, v___x_276_, v___x_270_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_a_252_);
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__1___boxed(lean_object* v_x_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___aux__Init__Core______unexpand__Iff__1(v_x_279_, v_a_280_, v_a_281_);
lean_dec(v_a_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2194____1(lean_object* v_x_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = ((lean_object*)(l_term___u2194___00__closed__1));
lean_inc(v_x_299_);
v___x_303_ = l_Lean_Syntax_isOfKind(v_x_299_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec_ref(v_a_300_);
lean_dec(v_x_299_);
v___x_304_ = lean_box(1);
v___x_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v_a_301_);
return v___x_305_;
}
else
{
lean_object* v_quotContext_306_; lean_object* v_currMacroScope_307_; lean_object* v_ref_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_quotContext_306_ = lean_ctor_get(v_a_300_, 1);
lean_inc(v_quotContext_306_);
v_currMacroScope_307_ = lean_ctor_get(v_a_300_, 2);
lean_inc(v_currMacroScope_307_);
v_ref_308_ = lean_ctor_get(v_a_300_, 5);
lean_inc(v_ref_308_);
lean_dec_ref(v_a_300_);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = l_Lean_Syntax_getArg(v_x_299_, v___x_309_);
v___x_311_ = lean_unsigned_to_nat(2u);
v___x_312_ = l_Lean_Syntax_getArg(v_x_299_, v___x_311_);
lean_dec(v_x_299_);
v___x_313_ = 0;
v___x_314_ = l_Lean_SourceInfo_fromRef(v_ref_308_, v___x_313_);
lean_dec(v_ref_308_);
v___x_315_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_316_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6, &l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6_once, _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6);
v___x_317_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7));
v___x_318_ = l_Lean_addMacroScope(v_quotContext_306_, v___x_317_, v_currMacroScope_307_);
v___x_319_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11));
lean_inc(v___x_314_);
v___x_320_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_320_, 0, v___x_314_);
lean_ctor_set(v___x_320_, 1, v___x_316_);
lean_ctor_set(v___x_320_, 2, v___x_318_);
lean_ctor_set(v___x_320_, 3, v___x_319_);
v___x_321_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_314_);
v___x_322_ = l_Lean_Syntax_node2(v___x_314_, v___x_321_, v___x_310_, v___x_312_);
v___x_323_ = l_Lean_Syntax_node2(v___x_314_, v___x_315_, v___x_320_, v___x_322_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v_a_301_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__2(lean_object* v_x_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_325_);
v___x_329_ = l_Lean_Syntax_isOfKind(v_x_325_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_x_325_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v_a_327_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = l_Lean_Syntax_getArg(v_x_325_, v___x_332_);
v___x_334_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_333_);
v___x_335_ = l_Lean_Syntax_isOfKind(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v___x_333_);
lean_dec(v_x_325_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v_a_327_);
return v___x_337_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = l_Lean_Syntax_getArg(v_x_325_, v___x_338_);
lean_dec(v_x_325_);
v___x_340_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_339_);
v___x_341_ = l_Lean_Syntax_matchesNull(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v___x_339_);
lean_dec(v___x_333_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_a_327_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_ref_346_; uint8_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_344_ = l_Lean_Syntax_getArg(v___x_339_, v___x_332_);
v___x_345_ = l_Lean_Syntax_getArg(v___x_339_, v___x_338_);
lean_dec(v___x_339_);
v_ref_346_ = l_Lean_replaceRef(v___x_333_, v_a_326_);
lean_dec(v___x_333_);
v___x_347_ = 0;
v___x_348_ = l_Lean_SourceInfo_fromRef(v_ref_346_, v___x_347_);
lean_dec(v_ref_346_);
v___x_349_ = ((lean_object*)(l_term___u2194___00__closed__1));
v___x_350_ = ((lean_object*)(l_term___u2194___00__closed__2));
lean_inc(v___x_348_);
v___x_351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_348_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = l_Lean_Syntax_node3(v___x_348_, v___x_349_, v___x_344_, v___x_351_, v___x_345_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v_a_327_);
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__2___boxed(lean_object* v_x_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___aux__Init__Core______unexpand__Iff__2(v_x_354_, v_a_355_, v_a_356_);
lean_dec(v_a_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___redArg(lean_object* v_x_358_){
_start:
{
if (lean_obj_tag(v_x_358_) == 0)
{
lean_object* v___x_359_; 
v___x_359_ = lean_unsigned_to_nat(0u);
return v___x_359_;
}
else
{
lean_object* v___x_360_; 
v___x_360_ = lean_unsigned_to_nat(1u);
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___redArg___boxed(lean_object* v_x_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Sum_ctorIdx___redArg(v_x_361_);
lean_dec_ref(v_x_361_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx(lean_object* v_00_u03b1_363_, lean_object* v_00_u03b2_364_, lean_object* v_x_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Sum_ctorIdx___redArg(v_x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___boxed(lean_object* v_00_u03b1_367_, lean_object* v_00_u03b2_368_, lean_object* v_x_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Sum_ctorIdx(v_00_u03b1_367_, v_00_u03b2_368_, v_x_369_);
lean_dec_ref(v_x_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim___redArg(lean_object* v_t_371_, lean_object* v_k_372_){
_start:
{
lean_object* v_val_373_; lean_object* v___x_374_; 
v_val_373_ = lean_ctor_get(v_t_371_, 0);
lean_inc(v_val_373_);
lean_dec_ref(v_t_371_);
v___x_374_ = lean_apply_1(v_k_372_, v_val_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim(lean_object* v_00_u03b1_375_, lean_object* v_00_u03b2_376_, lean_object* v_motive_377_, lean_object* v_ctorIdx_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_k_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Sum_ctorElim___redArg(v_t_379_, v_k_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim___boxed(lean_object* v_00_u03b1_383_, lean_object* v_00_u03b2_384_, lean_object* v_motive_385_, lean_object* v_ctorIdx_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_k_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Sum_ctorElim(v_00_u03b1_383_, v_00_u03b2_384_, v_motive_385_, v_ctorIdx_386_, v_t_387_, v_h_388_, v_k_389_);
lean_dec(v_ctorIdx_386_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Sum_inl_elim___redArg(lean_object* v_t_391_, lean_object* v_inl_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Sum_ctorElim___redArg(v_t_391_, v_inl_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Sum_inl_elim(lean_object* v_00_u03b1_394_, lean_object* v_00_u03b2_395_, lean_object* v_motive_396_, lean_object* v_t_397_, lean_object* v_h_398_, lean_object* v_inl_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Sum_ctorElim___redArg(v_t_397_, v_inl_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Sum_inr_elim___redArg(lean_object* v_t_401_, lean_object* v_inr_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Sum_ctorElim___redArg(v_t_401_, v_inr_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Sum_inr_elim(lean_object* v_00_u03b1_404_, lean_object* v_00_u03b2_405_, lean_object* v_motive_406_, lean_object* v_t_407_, lean_object* v_h_408_, lean_object* v_inr_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Sum_ctorElim___redArg(v_t_407_, v_inr_409_);
return v___x_410_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2295____1___closed__1(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__0));
v___x_432_ = l_String_toRawSubstring_x27(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295____1(lean_object* v_x_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = ((lean_object*)(l_term___u2295___00__closed__1));
lean_inc(v_x_446_);
v___x_450_ = l_Lean_Syntax_isOfKind(v_x_446_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec_ref(v_a_447_);
lean_dec(v_x_446_);
v___x_451_ = lean_box(1);
v___x_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v_a_448_);
return v___x_452_;
}
else
{
lean_object* v_quotContext_453_; lean_object* v_currMacroScope_454_; lean_object* v_ref_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_quotContext_453_ = lean_ctor_get(v_a_447_, 1);
lean_inc(v_quotContext_453_);
v_currMacroScope_454_ = lean_ctor_get(v_a_447_, 2);
lean_inc(v_currMacroScope_454_);
v_ref_455_ = lean_ctor_get(v_a_447_, 5);
lean_inc(v_ref_455_);
lean_dec_ref(v_a_447_);
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = l_Lean_Syntax_getArg(v_x_446_, v___x_456_);
v___x_458_ = lean_unsigned_to_nat(2u);
v___x_459_ = l_Lean_Syntax_getArg(v_x_446_, v___x_458_);
lean_dec(v_x_446_);
v___x_460_ = 0;
v___x_461_ = l_Lean_SourceInfo_fromRef(v_ref_455_, v___x_460_);
lean_dec(v_ref_455_);
v___x_462_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_463_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2295____1___closed__1, &l___aux__Init__Core______macroRules__term___u2295____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2295____1___closed__1);
v___x_464_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__2));
v___x_465_ = l_Lean_addMacroScope(v_quotContext_453_, v___x_464_, v_currMacroScope_454_);
v___x_466_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__6));
lean_inc(v___x_461_);
v___x_467_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_467_, 0, v___x_461_);
lean_ctor_set(v___x_467_, 1, v___x_463_);
lean_ctor_set(v___x_467_, 2, v___x_465_);
lean_ctor_set(v___x_467_, 3, v___x_466_);
v___x_468_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_461_);
v___x_469_ = l_Lean_Syntax_node2(v___x_461_, v___x_468_, v___x_457_, v___x_459_);
v___x_470_ = l_Lean_Syntax_node2(v___x_461_, v___x_462_, v___x_467_, v___x_469_);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v_a_448_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Sum__1(lean_object* v_x_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_472_);
v___x_476_ = l_Lean_Syntax_isOfKind(v_x_472_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_x_472_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v_a_474_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = l_Lean_Syntax_getArg(v_x_472_, v___x_479_);
v___x_481_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_480_);
v___x_482_ = l_Lean_Syntax_isOfKind(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v___x_480_);
lean_dec(v_x_472_);
v___x_483_ = lean_box(0);
v___x_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v_a_474_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = l_Lean_Syntax_getArg(v_x_472_, v___x_485_);
lean_dec(v_x_472_);
v___x_487_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_486_);
v___x_488_ = l_Lean_Syntax_matchesNull(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v___x_486_);
lean_dec(v___x_480_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_a_474_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v_ref_493_; uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_491_ = l_Lean_Syntax_getArg(v___x_486_, v___x_479_);
v___x_492_ = l_Lean_Syntax_getArg(v___x_486_, v___x_485_);
lean_dec(v___x_486_);
v_ref_493_ = l_Lean_replaceRef(v___x_480_, v_a_473_);
lean_dec(v___x_480_);
v___x_494_ = 0;
v___x_495_ = l_Lean_SourceInfo_fromRef(v_ref_493_, v___x_494_);
lean_dec(v_ref_493_);
v___x_496_ = ((lean_object*)(l_term___u2295___00__closed__1));
v___x_497_ = ((lean_object*)(l_term___u2295___00__closed__2));
lean_inc(v___x_495_);
v___x_498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_495_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_Syntax_node3(v___x_495_, v___x_496_, v___x_491_, v___x_498_, v___x_492_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v_a_474_);
return v___x_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Sum__1___boxed(lean_object* v_x_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l___aux__Init__Core______unexpand__Sum__1(v_x_501_, v_a_502_, v_a_503_);
lean_dec(v_a_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___redArg(lean_object* v_x_505_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v___x_506_; 
v___x_506_ = lean_unsigned_to_nat(0u);
return v___x_506_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_unsigned_to_nat(1u);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___redArg___boxed(lean_object* v_x_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_PSum_ctorIdx___redArg(v_x_508_);
lean_dec_ref(v_x_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx(lean_object* v_00_u03b1_510_, lean_object* v_00_u03b2_511_, lean_object* v_x_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_PSum_ctorIdx___redArg(v_x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___boxed(lean_object* v_00_u03b1_514_, lean_object* v_00_u03b2_515_, lean_object* v_x_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_PSum_ctorIdx(v_00_u03b1_514_, v_00_u03b2_515_, v_x_516_);
lean_dec_ref(v_x_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim___redArg(lean_object* v_t_518_, lean_object* v_k_519_){
_start:
{
lean_object* v_val_520_; lean_object* v___x_521_; 
v_val_520_ = lean_ctor_get(v_t_518_, 0);
lean_inc(v_val_520_);
lean_dec_ref(v_t_518_);
v___x_521_ = lean_apply_1(v_k_519_, v_val_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim(lean_object* v_00_u03b1_522_, lean_object* v_00_u03b2_523_, lean_object* v_motive_524_, lean_object* v_ctorIdx_525_, lean_object* v_t_526_, lean_object* v_h_527_, lean_object* v_k_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_PSum_ctorElim___redArg(v_t_526_, v_k_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim___boxed(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_motive_532_, lean_object* v_ctorIdx_533_, lean_object* v_t_534_, lean_object* v_h_535_, lean_object* v_k_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_PSum_ctorElim(v_00_u03b1_530_, v_00_u03b2_531_, v_motive_532_, v_ctorIdx_533_, v_t_534_, v_h_535_, v_k_536_);
lean_dec(v_ctorIdx_533_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_PSum_inl_elim___redArg(lean_object* v_t_538_, lean_object* v_inl_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_PSum_ctorElim___redArg(v_t_538_, v_inl_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_PSum_inl_elim(lean_object* v_00_u03b1_541_, lean_object* v_00_u03b2_542_, lean_object* v_motive_543_, lean_object* v_t_544_, lean_object* v_h_545_, lean_object* v_inl_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_PSum_ctorElim___redArg(v_t_544_, v_inl_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_PSum_inr_elim___redArg(lean_object* v_t_548_, lean_object* v_inr_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_PSum_ctorElim___redArg(v_t_548_, v_inr_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_PSum_inr_elim(lean_object* v_00_u03b1_551_, lean_object* v_00_u03b2_552_, lean_object* v_motive_553_, lean_object* v_t_554_, lean_object* v_h_555_, lean_object* v_inr_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_PSum_ctorElim___redArg(v_t_554_, v_inr_556_);
return v___x_557_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0));
v___x_576_ = l_String_toRawSubstring_x27(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1(lean_object* v_x_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = ((lean_object*)(l_term___u2295_x27___00__closed__1));
lean_inc(v_x_590_);
v___x_594_ = l_Lean_Syntax_isOfKind(v_x_590_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec_ref(v_a_591_);
lean_dec(v_x_590_);
v___x_595_ = lean_box(1);
v___x_596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v_a_592_);
return v___x_596_;
}
else
{
lean_object* v_quotContext_597_; lean_object* v_currMacroScope_598_; lean_object* v_ref_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_quotContext_597_ = lean_ctor_get(v_a_591_, 1);
lean_inc(v_quotContext_597_);
v_currMacroScope_598_ = lean_ctor_get(v_a_591_, 2);
lean_inc(v_currMacroScope_598_);
v_ref_599_ = lean_ctor_get(v_a_591_, 5);
lean_inc(v_ref_599_);
lean_dec_ref(v_a_591_);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = l_Lean_Syntax_getArg(v_x_590_, v___x_600_);
v___x_602_ = lean_unsigned_to_nat(2u);
v___x_603_ = l_Lean_Syntax_getArg(v_x_590_, v___x_602_);
lean_dec(v_x_590_);
v___x_604_ = 0;
v___x_605_ = l_Lean_SourceInfo_fromRef(v_ref_599_, v___x_604_);
lean_dec(v_ref_599_);
v___x_606_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_607_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1, &l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1);
v___x_608_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2));
v___x_609_ = l_Lean_addMacroScope(v_quotContext_597_, v___x_608_, v_currMacroScope_598_);
v___x_610_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__6));
lean_inc(v___x_605_);
v___x_611_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_611_, 0, v___x_605_);
lean_ctor_set(v___x_611_, 1, v___x_607_);
lean_ctor_set(v___x_611_, 2, v___x_609_);
lean_ctor_set(v___x_611_, 3, v___x_610_);
v___x_612_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_605_);
v___x_613_ = l_Lean_Syntax_node2(v___x_605_, v___x_612_, v___x_601_, v___x_603_);
v___x_614_ = l_Lean_Syntax_node2(v___x_605_, v___x_606_, v___x_611_, v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_a_592_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__PSum__1(lean_object* v_x_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_616_);
v___x_620_ = l_Lean_Syntax_isOfKind(v_x_616_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v_x_616_);
v___x_621_ = lean_box(0);
v___x_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_a_618_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = l_Lean_Syntax_getArg(v_x_616_, v___x_623_);
v___x_625_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_624_);
v___x_626_ = l_Lean_Syntax_isOfKind(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v___x_624_);
lean_dec(v_x_616_);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v_a_618_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = l_Lean_Syntax_getArg(v_x_616_, v___x_629_);
lean_dec(v_x_616_);
v___x_631_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_630_);
v___x_632_ = l_Lean_Syntax_matchesNull(v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v___x_630_);
lean_dec(v___x_624_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v_a_618_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_ref_637_; uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_635_ = l_Lean_Syntax_getArg(v___x_630_, v___x_623_);
v___x_636_ = l_Lean_Syntax_getArg(v___x_630_, v___x_629_);
lean_dec(v___x_630_);
v_ref_637_ = l_Lean_replaceRef(v___x_624_, v_a_617_);
lean_dec(v___x_624_);
v___x_638_ = 0;
v___x_639_ = l_Lean_SourceInfo_fromRef(v_ref_637_, v___x_638_);
lean_dec(v_ref_637_);
v___x_640_ = ((lean_object*)(l_term___u2295_x27___00__closed__1));
v___x_641_ = ((lean_object*)(l_term___u2295_x27___00__closed__2));
lean_inc(v___x_639_);
v___x_642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_639_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = l_Lean_Syntax_node3(v___x_639_, v___x_640_, v___x_635_, v___x_642_, v___x_636_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v_a_618_);
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__PSum__1___boxed(lean_object* v_x_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___aux__Init__Core______unexpand__PSum__1(v_x_645_, v_a_646_, v_a_647_);
lean_dec(v_a_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedLeft___redArg(lean_object* v_inst_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v_inst_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedLeft(lean_object* v_00_u03b1_651_, lean_object* v_00_u03b2_652_, lean_object* v_inst_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v_inst_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedRight___redArg(lean_object* v_inst_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v_inst_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedRight(lean_object* v_00_u03b1_657_, lean_object* v_00_u03b2_658_, lean_object* v_inst_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_660_, 0, v_inst_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___redArg(lean_object* v_x_661_){
_start:
{
if (lean_obj_tag(v_x_661_) == 0)
{
lean_object* v___x_662_; 
v___x_662_ = lean_unsigned_to_nat(0u);
return v___x_662_;
}
else
{
lean_object* v___x_663_; 
v___x_663_ = lean_unsigned_to_nat(1u);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___redArg___boxed(lean_object* v_x_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_ForInStep_ctorIdx___redArg(v_x_664_);
lean_dec_ref(v_x_664_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx(lean_object* v_00_u03b1_666_, lean_object* v_x_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_ForInStep_ctorIdx___redArg(v_x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___boxed(lean_object* v_00_u03b1_669_, lean_object* v_x_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_ForInStep_ctorIdx(v_00_u03b1_669_, v_x_670_);
lean_dec_ref(v_x_670_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim___redArg(lean_object* v_t_672_, lean_object* v_k_673_){
_start:
{
lean_object* v_a_674_; lean_object* v___x_675_; 
v_a_674_ = lean_ctor_get(v_t_672_, 0);
lean_inc(v_a_674_);
lean_dec_ref(v_t_672_);
v___x_675_ = lean_apply_1(v_k_673_, v_a_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim(lean_object* v_00_u03b1_676_, lean_object* v_motive_677_, lean_object* v_ctorIdx_678_, lean_object* v_t_679_, lean_object* v_h_680_, lean_object* v_k_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_ForInStep_ctorElim___redArg(v_t_679_, v_k_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim___boxed(lean_object* v_00_u03b1_683_, lean_object* v_motive_684_, lean_object* v_ctorIdx_685_, lean_object* v_t_686_, lean_object* v_h_687_, lean_object* v_k_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_ForInStep_ctorElim(v_00_u03b1_683_, v_motive_684_, v_ctorIdx_685_, v_t_686_, v_h_687_, v_k_688_);
lean_dec(v_ctorIdx_685_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_done_elim___redArg(lean_object* v_t_690_, lean_object* v_done_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_ForInStep_ctorElim___redArg(v_t_690_, v_done_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_done_elim(lean_object* v_00_u03b1_693_, lean_object* v_motive_694_, lean_object* v_t_695_, lean_object* v_h_696_, lean_object* v_done_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_ForInStep_ctorElim___redArg(v_t_695_, v_done_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_yield_elim___redArg(lean_object* v_t_699_, lean_object* v_yield_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_ForInStep_ctorElim___redArg(v_t_699_, v_yield_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_yield_elim(lean_object* v_00_u03b1_702_, lean_object* v_motive_703_, lean_object* v_t_704_, lean_object* v_h_705_, lean_object* v_yield_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_ForInStep_ctorElim___redArg(v_t_704_, v_yield_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep_default___redArg(lean_object* v_inst_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v_inst_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep_default(lean_object* v_a_710_, lean_object* v_inst_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v_inst_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep___redArg(lean_object* v_inst_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v_inst_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep(lean_object* v_a_715_, lean_object* v_inst_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_inst_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___redArg(lean_object* v_x_718_){
_start:
{
switch(lean_obj_tag(v_x_718_))
{
case 0:
{
lean_object* v___x_719_; 
v___x_719_ = lean_unsigned_to_nat(0u);
return v___x_719_;
}
case 1:
{
lean_object* v___x_720_; 
v___x_720_ = lean_unsigned_to_nat(1u);
return v___x_720_;
}
case 2:
{
lean_object* v___x_721_; 
v___x_721_ = lean_unsigned_to_nat(2u);
return v___x_721_;
}
default: 
{
lean_object* v___x_722_; 
v___x_722_ = lean_unsigned_to_nat(3u);
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___redArg___boxed(lean_object* v_x_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_DoResultPRBC_ctorIdx___redArg(v_x_723_);
lean_dec_ref(v_x_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx(lean_object* v_00_u03b1_725_, lean_object* v_00_u03b2_726_, lean_object* v_00_u03c3_727_, lean_object* v_x_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_DoResultPRBC_ctorIdx___redArg(v_x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___boxed(lean_object* v_00_u03b1_730_, lean_object* v_00_u03b2_731_, lean_object* v_00_u03c3_732_, lean_object* v_x_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_DoResultPRBC_ctorIdx(v_00_u03b1_730_, v_00_u03b2_731_, v_00_u03c3_732_, v_x_733_);
lean_dec_ref(v_x_733_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim___redArg(lean_object* v_t_735_, lean_object* v_k_736_){
_start:
{
switch(lean_obj_tag(v_t_735_))
{
case 2:
{
lean_object* v_a_737_; lean_object* v___x_738_; 
v_a_737_ = lean_ctor_get(v_t_735_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v_t_735_);
v___x_738_ = lean_apply_1(v_k_736_, v_a_737_);
return v___x_738_;
}
case 3:
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v_t_735_, 0);
lean_inc(v_a_739_);
lean_dec_ref(v_t_735_);
v___x_740_ = lean_apply_1(v_k_736_, v_a_739_);
return v___x_740_;
}
default: 
{
lean_object* v_a_741_; lean_object* v_a_742_; lean_object* v___x_743_; 
v_a_741_ = lean_ctor_get(v_t_735_, 0);
lean_inc(v_a_741_);
v_a_742_ = lean_ctor_get(v_t_735_, 1);
lean_inc(v_a_742_);
lean_dec_ref(v_t_735_);
v___x_743_ = lean_apply_2(v_k_736_, v_a_741_, v_a_742_);
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim(lean_object* v_00_u03b1_744_, lean_object* v_00_u03b2_745_, lean_object* v_00_u03c3_746_, lean_object* v_motive_747_, lean_object* v_ctorIdx_748_, lean_object* v_t_749_, lean_object* v_h_750_, lean_object* v_k_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_DoResultPRBC_ctorElim___redArg(v_t_749_, v_k_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim___boxed(lean_object* v_00_u03b1_753_, lean_object* v_00_u03b2_754_, lean_object* v_00_u03c3_755_, lean_object* v_motive_756_, lean_object* v_ctorIdx_757_, lean_object* v_t_758_, lean_object* v_h_759_, lean_object* v_k_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_DoResultPRBC_ctorElim(v_00_u03b1_753_, v_00_u03b2_754_, v_00_u03c3_755_, v_motive_756_, v_ctorIdx_757_, v_t_758_, v_h_759_, v_k_760_);
lean_dec(v_ctorIdx_757_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_pure_elim___redArg(lean_object* v_t_762_, lean_object* v_pure_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_DoResultPRBC_ctorElim___redArg(v_t_762_, v_pure_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_pure_elim(lean_object* v_00_u03b1_765_, lean_object* v_00_u03b2_766_, lean_object* v_00_u03c3_767_, lean_object* v_motive_768_, lean_object* v_t_769_, lean_object* v_h_770_, lean_object* v_pure_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_DoResultPRBC_ctorElim___redArg(v_t_769_, v_pure_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_return_elim___redArg(lean_object* v_t_773_, lean_object* v_return_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_DoResultPRBC_ctorElim___redArg(v_t_773_, v_return_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_return_elim(lean_object* v_00_u03b1_776_, lean_object* v_00_u03b2_777_, lean_object* v_00_u03c3_778_, lean_object* v_motive_779_, lean_object* v_t_780_, lean_object* v_h_781_, lean_object* v_return_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_DoResultPRBC_ctorElim___redArg(v_t_780_, v_return_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_break_elim___redArg(lean_object* v_t_784_, lean_object* v_break_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_DoResultPRBC_ctorElim___redArg(v_t_784_, v_break_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_break_elim(lean_object* v_00_u03b1_787_, lean_object* v_00_u03b2_788_, lean_object* v_00_u03c3_789_, lean_object* v_motive_790_, lean_object* v_t_791_, lean_object* v_h_792_, lean_object* v_break_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_DoResultPRBC_ctorElim___redArg(v_t_791_, v_break_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_continue_elim___redArg(lean_object* v_t_795_, lean_object* v_continue_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_DoResultPRBC_ctorElim___redArg(v_t_795_, v_continue_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_continue_elim(lean_object* v_00_u03b1_798_, lean_object* v_00_u03b2_799_, lean_object* v_00_u03c3_800_, lean_object* v_motive_801_, lean_object* v_t_802_, lean_object* v_h_803_, lean_object* v_continue_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_DoResultPRBC_ctorElim___redArg(v_t_802_, v_continue_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___redArg(lean_object* v_x_806_){
_start:
{
if (lean_obj_tag(v_x_806_) == 0)
{
lean_object* v___x_807_; 
v___x_807_ = lean_unsigned_to_nat(0u);
return v___x_807_;
}
else
{
lean_object* v___x_808_; 
v___x_808_ = lean_unsigned_to_nat(1u);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___redArg___boxed(lean_object* v_x_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_DoResultPR_ctorIdx___redArg(v_x_809_);
lean_dec_ref(v_x_809_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx(lean_object* v_00_u03b1_811_, lean_object* v_00_u03b2_812_, lean_object* v_00_u03c3_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_DoResultPR_ctorIdx___redArg(v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___boxed(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_00_u03c3_818_, lean_object* v_x_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_DoResultPR_ctorIdx(v_00_u03b1_816_, v_00_u03b2_817_, v_00_u03c3_818_, v_x_819_);
lean_dec_ref(v_x_819_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___redArg(lean_object* v_t_821_, lean_object* v_k_822_){
_start:
{
lean_object* v_a_823_; lean_object* v_a_824_; lean_object* v___x_825_; 
v_a_823_ = lean_ctor_get(v_t_821_, 0);
lean_inc(v_a_823_);
v_a_824_ = lean_ctor_get(v_t_821_, 1);
lean_inc(v_a_824_);
lean_dec_ref(v_t_821_);
v___x_825_ = lean_apply_2(v_k_822_, v_a_823_, v_a_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim(lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_00_u03c3_828_, lean_object* v_motive_829_, lean_object* v_ctorIdx_830_, lean_object* v_t_831_, lean_object* v_h_832_, lean_object* v_k_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_DoResultPR_ctorElim___redArg(v_t_831_, v_k_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___boxed(lean_object* v_00_u03b1_835_, lean_object* v_00_u03b2_836_, lean_object* v_00_u03c3_837_, lean_object* v_motive_838_, lean_object* v_ctorIdx_839_, lean_object* v_t_840_, lean_object* v_h_841_, lean_object* v_k_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_DoResultPR_ctorElim(v_00_u03b1_835_, v_00_u03b2_836_, v_00_u03c3_837_, v_motive_838_, v_ctorIdx_839_, v_t_840_, v_h_841_, v_k_842_);
lean_dec(v_ctorIdx_839_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim___redArg(lean_object* v_t_844_, lean_object* v_pure_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_DoResultPR_ctorElim___redArg(v_t_844_, v_pure_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim(lean_object* v_00_u03b1_847_, lean_object* v_00_u03b2_848_, lean_object* v_00_u03c3_849_, lean_object* v_motive_850_, lean_object* v_t_851_, lean_object* v_h_852_, lean_object* v_pure_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_DoResultPR_ctorElim___redArg(v_t_851_, v_pure_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_return_elim___redArg(lean_object* v_t_855_, lean_object* v_return_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_DoResultPR_ctorElim___redArg(v_t_855_, v_return_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_return_elim(lean_object* v_00_u03b1_858_, lean_object* v_00_u03b2_859_, lean_object* v_00_u03c3_860_, lean_object* v_motive_861_, lean_object* v_t_862_, lean_object* v_h_863_, lean_object* v_return_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_DoResultPR_ctorElim___redArg(v_t_862_, v_return_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___redArg(lean_object* v_x_866_){
_start:
{
if (lean_obj_tag(v_x_866_) == 0)
{
lean_object* v___x_867_; 
v___x_867_ = lean_unsigned_to_nat(0u);
return v___x_867_;
}
else
{
lean_object* v___x_868_; 
v___x_868_ = lean_unsigned_to_nat(1u);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___redArg___boxed(lean_object* v_x_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_DoResultBC_ctorIdx___redArg(v_x_869_);
lean_dec_ref(v_x_869_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx(lean_object* v_00_u03c3_871_, lean_object* v_x_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_DoResultBC_ctorIdx___redArg(v_x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___boxed(lean_object* v_00_u03c3_874_, lean_object* v_x_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_DoResultBC_ctorIdx(v_00_u03c3_874_, v_x_875_);
lean_dec_ref(v_x_875_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___redArg(lean_object* v_t_877_, lean_object* v_k_878_){
_start:
{
lean_object* v_a_879_; lean_object* v___x_880_; 
v_a_879_ = lean_ctor_get(v_t_877_, 0);
lean_inc(v_a_879_);
lean_dec_ref(v_t_877_);
v___x_880_ = lean_apply_1(v_k_878_, v_a_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim(lean_object* v_00_u03c3_881_, lean_object* v_motive_882_, lean_object* v_ctorIdx_883_, lean_object* v_t_884_, lean_object* v_h_885_, lean_object* v_k_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_DoResultBC_ctorElim___redArg(v_t_884_, v_k_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___boxed(lean_object* v_00_u03c3_888_, lean_object* v_motive_889_, lean_object* v_ctorIdx_890_, lean_object* v_t_891_, lean_object* v_h_892_, lean_object* v_k_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_DoResultBC_ctorElim(v_00_u03c3_888_, v_motive_889_, v_ctorIdx_890_, v_t_891_, v_h_892_, v_k_893_);
lean_dec(v_ctorIdx_890_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_break_elim___redArg(lean_object* v_t_895_, lean_object* v_break_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_DoResultBC_ctorElim___redArg(v_t_895_, v_break_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_break_elim(lean_object* v_00_u03c3_898_, lean_object* v_motive_899_, lean_object* v_t_900_, lean_object* v_h_901_, lean_object* v_break_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_DoResultBC_ctorElim___redArg(v_t_900_, v_break_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim___redArg(lean_object* v_t_904_, lean_object* v_continue_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_DoResultBC_ctorElim___redArg(v_t_904_, v_continue_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim(lean_object* v_00_u03c3_907_, lean_object* v_motive_908_, lean_object* v_t_909_, lean_object* v_h_910_, lean_object* v_continue_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_DoResultBC_ctorElim___redArg(v_t_909_, v_continue_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___redArg(lean_object* v_x_913_){
_start:
{
switch(lean_obj_tag(v_x_913_))
{
case 0:
{
lean_object* v___x_914_; 
v___x_914_ = lean_unsigned_to_nat(0u);
return v___x_914_;
}
case 1:
{
lean_object* v___x_915_; 
v___x_915_ = lean_unsigned_to_nat(1u);
return v___x_915_;
}
default: 
{
lean_object* v___x_916_; 
v___x_916_ = lean_unsigned_to_nat(2u);
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___redArg___boxed(lean_object* v_x_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_DoResultSBC_ctorIdx___redArg(v_x_917_);
lean_dec_ref(v_x_917_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx(lean_object* v_00_u03b1_919_, lean_object* v_00_u03c3_920_, lean_object* v_x_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_DoResultSBC_ctorIdx___redArg(v_x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___boxed(lean_object* v_00_u03b1_923_, lean_object* v_00_u03c3_924_, lean_object* v_x_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_DoResultSBC_ctorIdx(v_00_u03b1_923_, v_00_u03c3_924_, v_x_925_);
lean_dec_ref(v_x_925_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim___redArg(lean_object* v_t_927_, lean_object* v_k_928_){
_start:
{
if (lean_obj_tag(v_t_927_) == 0)
{
lean_object* v_a_929_; lean_object* v_a_930_; lean_object* v___x_931_; 
v_a_929_ = lean_ctor_get(v_t_927_, 0);
lean_inc(v_a_929_);
v_a_930_ = lean_ctor_get(v_t_927_, 1);
lean_inc(v_a_930_);
lean_dec_ref(v_t_927_);
v___x_931_ = lean_apply_2(v_k_928_, v_a_929_, v_a_930_);
return v___x_931_;
}
else
{
lean_object* v_a_932_; lean_object* v___x_933_; 
v_a_932_ = lean_ctor_get(v_t_927_, 0);
lean_inc(v_a_932_);
lean_dec_ref(v_t_927_);
v___x_933_ = lean_apply_1(v_k_928_, v_a_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim(lean_object* v_00_u03b1_934_, lean_object* v_00_u03c3_935_, lean_object* v_motive_936_, lean_object* v_ctorIdx_937_, lean_object* v_t_938_, lean_object* v_h_939_, lean_object* v_k_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_DoResultSBC_ctorElim___redArg(v_t_938_, v_k_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim___boxed(lean_object* v_00_u03b1_942_, lean_object* v_00_u03c3_943_, lean_object* v_motive_944_, lean_object* v_ctorIdx_945_, lean_object* v_t_946_, lean_object* v_h_947_, lean_object* v_k_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_DoResultSBC_ctorElim(v_00_u03b1_942_, v_00_u03c3_943_, v_motive_944_, v_ctorIdx_945_, v_t_946_, v_h_947_, v_k_948_);
lean_dec(v_ctorIdx_945_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_pureReturn_elim___redArg(lean_object* v_t_950_, lean_object* v_pureReturn_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_DoResultSBC_ctorElim___redArg(v_t_950_, v_pureReturn_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_pureReturn_elim(lean_object* v_00_u03b1_953_, lean_object* v_00_u03c3_954_, lean_object* v_motive_955_, lean_object* v_t_956_, lean_object* v_h_957_, lean_object* v_pureReturn_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_DoResultSBC_ctorElim___redArg(v_t_956_, v_pureReturn_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_break_elim___redArg(lean_object* v_t_960_, lean_object* v_break_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_DoResultSBC_ctorElim___redArg(v_t_960_, v_break_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_break_elim(lean_object* v_00_u03b1_963_, lean_object* v_00_u03c3_964_, lean_object* v_motive_965_, lean_object* v_t_966_, lean_object* v_h_967_, lean_object* v_break_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_DoResultSBC_ctorElim___redArg(v_t_966_, v_break_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_continue_elim___redArg(lean_object* v_t_970_, lean_object* v_continue_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_DoResultSBC_ctorElim___redArg(v_t_970_, v_continue_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_continue_elim(lean_object* v_00_u03b1_973_, lean_object* v_00_u03c3_974_, lean_object* v_motive_975_, lean_object* v_t_976_, lean_object* v_h_977_, lean_object* v_continue_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_DoResultSBC_ctorElim___redArg(v_t_976_, v_continue_978_);
return v___x_979_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2248____1___closed__1(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2248____1___closed__0));
v___x_1001_ = l_String_toRawSubstring_x27(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2248____1(lean_object* v_x_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_term___u2248___00__closed__1));
lean_inc(v_x_1013_);
v___x_1017_ = l_Lean_Syntax_isOfKind(v_x_1013_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_dec_ref(v_a_1014_);
lean_dec(v_x_1013_);
v___x_1018_ = lean_box(1);
v___x_1019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v_a_1015_);
return v___x_1019_;
}
else
{
lean_object* v_quotContext_1020_; lean_object* v_currMacroScope_1021_; lean_object* v_ref_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v_quotContext_1020_ = lean_ctor_get(v_a_1014_, 1);
lean_inc(v_quotContext_1020_);
v_currMacroScope_1021_ = lean_ctor_get(v_a_1014_, 2);
lean_inc(v_currMacroScope_1021_);
v_ref_1022_ = lean_ctor_get(v_a_1014_, 5);
lean_inc(v_ref_1022_);
lean_dec_ref(v_a_1014_);
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = l_Lean_Syntax_getArg(v_x_1013_, v___x_1023_);
v___x_1025_ = lean_unsigned_to_nat(2u);
v___x_1026_ = l_Lean_Syntax_getArg(v_x_1013_, v___x_1025_);
lean_dec(v_x_1013_);
v___x_1027_ = 0;
v___x_1028_ = l_Lean_SourceInfo_fromRef(v_ref_1022_, v___x_1027_);
lean_dec(v_ref_1022_);
v___x_1029_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1030_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2248____1___closed__1, &l___aux__Init__Core______macroRules__term___u2248____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2248____1___closed__1);
v___x_1031_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2248____1___closed__4));
v___x_1032_ = l_Lean_addMacroScope(v_quotContext_1020_, v___x_1031_, v_currMacroScope_1021_);
v___x_1033_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2248____1___closed__6));
lean_inc(v___x_1028_);
v___x_1034_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1028_);
lean_ctor_set(v___x_1034_, 1, v___x_1030_);
lean_ctor_set(v___x_1034_, 2, v___x_1032_);
lean_ctor_set(v___x_1034_, 3, v___x_1033_);
v___x_1035_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1028_);
v___x_1036_ = l_Lean_Syntax_node2(v___x_1028_, v___x_1035_, v___x_1024_, v___x_1026_);
v___x_1037_ = l_Lean_Syntax_node2(v___x_1028_, v___x_1029_, v___x_1034_, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v_a_1015_);
return v___x_1038_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasEquiv__Equiv__1(lean_object* v_x_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1039_);
v___x_1043_ = l_Lean_Syntax_isOfKind(v_x_1039_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec(v_x_1039_);
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_a_1041_);
return v___x_1045_;
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1046_ = lean_unsigned_to_nat(0u);
v___x_1047_ = l_Lean_Syntax_getArg(v_x_1039_, v___x_1046_);
v___x_1048_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1047_);
v___x_1049_ = l_Lean_Syntax_isOfKind(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec(v___x_1047_);
lean_dec(v_x_1039_);
v___x_1050_ = lean_box(0);
v___x_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v_a_1041_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1052_ = lean_unsigned_to_nat(1u);
v___x_1053_ = l_Lean_Syntax_getArg(v_x_1039_, v___x_1052_);
lean_dec(v_x_1039_);
v___x_1054_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1053_);
v___x_1055_ = l_Lean_Syntax_matchesNull(v___x_1053_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_dec(v___x_1053_);
lean_dec(v___x_1047_);
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v_a_1041_);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v_ref_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1058_ = l_Lean_Syntax_getArg(v___x_1053_, v___x_1046_);
v___x_1059_ = l_Lean_Syntax_getArg(v___x_1053_, v___x_1052_);
lean_dec(v___x_1053_);
v_ref_1060_ = l_Lean_replaceRef(v___x_1047_, v_a_1040_);
lean_dec(v___x_1047_);
v___x_1061_ = 0;
v___x_1062_ = l_Lean_SourceInfo_fromRef(v_ref_1060_, v___x_1061_);
lean_dec(v_ref_1060_);
v___x_1063_ = ((lean_object*)(l_term___u2248___00__closed__1));
v___x_1064_ = ((lean_object*)(l_term___u2248___00__closed__2));
lean_inc(v___x_1062_);
v___x_1065_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1062_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_Syntax_node3(v___x_1062_, v___x_1063_, v___x_1058_, v___x_1065_, v___x_1059_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v_a_1041_);
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasEquiv__Equiv__1___boxed(lean_object* v_x_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___aux__Init__Core______unexpand__HasEquiv__Equiv__1(v_x_1068_, v_a_1069_, v_a_1070_);
lean_dec(v_a_1069_);
return v_res_1071_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2286____1___closed__1(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2286____1___closed__0));
v___x_1090_ = l_String_toRawSubstring_x27(v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2286____1(lean_object* v_x_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_term___u2286___00__closed__1));
lean_inc(v_x_1103_);
v___x_1107_ = l_Lean_Syntax_isOfKind(v_x_1103_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_dec_ref(v_a_1104_);
lean_dec(v_x_1103_);
v___x_1108_ = lean_box(1);
v___x_1109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_a_1105_);
return v___x_1109_;
}
else
{
lean_object* v_quotContext_1110_; lean_object* v_currMacroScope_1111_; lean_object* v_ref_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_quotContext_1110_ = lean_ctor_get(v_a_1104_, 1);
lean_inc(v_quotContext_1110_);
v_currMacroScope_1111_ = lean_ctor_get(v_a_1104_, 2);
lean_inc(v_currMacroScope_1111_);
v_ref_1112_ = lean_ctor_get(v_a_1104_, 5);
lean_inc(v_ref_1112_);
lean_dec_ref(v_a_1104_);
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = l_Lean_Syntax_getArg(v_x_1103_, v___x_1113_);
v___x_1115_ = lean_unsigned_to_nat(2u);
v___x_1116_ = l_Lean_Syntax_getArg(v_x_1103_, v___x_1115_);
lean_dec(v_x_1103_);
v___x_1117_ = 0;
v___x_1118_ = l_Lean_SourceInfo_fromRef(v_ref_1112_, v___x_1117_);
lean_dec(v_ref_1112_);
v___x_1119_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1120_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2286____1___closed__1, &l___aux__Init__Core______macroRules__term___u2286____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2286____1___closed__1);
v___x_1121_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2286____1___closed__2));
v___x_1122_ = l_Lean_addMacroScope(v_quotContext_1110_, v___x_1121_, v_currMacroScope_1111_);
v___x_1123_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2286____1___closed__6));
lean_inc(v___x_1118_);
v___x_1124_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1118_);
lean_ctor_set(v___x_1124_, 1, v___x_1120_);
lean_ctor_set(v___x_1124_, 2, v___x_1122_);
lean_ctor_set(v___x_1124_, 3, v___x_1123_);
v___x_1125_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1118_);
v___x_1126_ = l_Lean_Syntax_node2(v___x_1118_, v___x_1125_, v___x_1114_, v___x_1116_);
v___x_1127_ = l_Lean_Syntax_node2(v___x_1118_, v___x_1119_, v___x_1124_, v___x_1126_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v_a_1105_);
return v___x_1128_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSubset__Subset__1(lean_object* v_x_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1129_);
v___x_1133_ = l_Lean_Syntax_isOfKind(v_x_1129_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec(v_x_1129_);
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v_a_1131_);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = l_Lean_Syntax_getArg(v_x_1129_, v___x_1136_);
v___x_1138_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1137_);
v___x_1139_ = l_Lean_Syntax_isOfKind(v___x_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_dec(v___x_1137_);
lean_dec(v_x_1129_);
v___x_1140_ = lean_box(0);
v___x_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v_a_1131_);
return v___x_1141_;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1142_ = lean_unsigned_to_nat(1u);
v___x_1143_ = l_Lean_Syntax_getArg(v_x_1129_, v___x_1142_);
lean_dec(v_x_1129_);
v___x_1144_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1143_);
v___x_1145_ = l_Lean_Syntax_matchesNull(v___x_1143_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec(v___x_1143_);
lean_dec(v___x_1137_);
v___x_1146_ = lean_box(0);
v___x_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_a_1131_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_ref_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1148_ = l_Lean_Syntax_getArg(v___x_1143_, v___x_1136_);
v___x_1149_ = l_Lean_Syntax_getArg(v___x_1143_, v___x_1142_);
lean_dec(v___x_1143_);
v_ref_1150_ = l_Lean_replaceRef(v___x_1137_, v_a_1130_);
lean_dec(v___x_1137_);
v___x_1151_ = 0;
v___x_1152_ = l_Lean_SourceInfo_fromRef(v_ref_1150_, v___x_1151_);
lean_dec(v_ref_1150_);
v___x_1153_ = ((lean_object*)(l_term___u2286___00__closed__1));
v___x_1154_ = ((lean_object*)(l_term___u2286___00__closed__2));
lean_inc(v___x_1152_);
v___x_1155_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1152_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_Syntax_node3(v___x_1152_, v___x_1153_, v___x_1148_, v___x_1155_, v___x_1149_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v_a_1131_);
return v___x_1157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSubset__Subset__1___boxed(lean_object* v_x_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___aux__Init__Core______unexpand__HasSubset__Subset__1(v_x_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1159_);
return v_res_1161_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2282____1___closed__1(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2282____1___closed__0));
v___x_1180_ = l_String_toRawSubstring_x27(v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2282____1(lean_object* v_x_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = ((lean_object*)(l_term___u2282___00__closed__1));
lean_inc(v_x_1193_);
v___x_1197_ = l_Lean_Syntax_isOfKind(v_x_1193_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec_ref(v_a_1194_);
lean_dec(v_x_1193_);
v___x_1198_ = lean_box(1);
v___x_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v_a_1195_);
return v___x_1199_;
}
else
{
lean_object* v_quotContext_1200_; lean_object* v_currMacroScope_1201_; lean_object* v_ref_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_quotContext_1200_ = lean_ctor_get(v_a_1194_, 1);
lean_inc(v_quotContext_1200_);
v_currMacroScope_1201_ = lean_ctor_get(v_a_1194_, 2);
lean_inc(v_currMacroScope_1201_);
v_ref_1202_ = lean_ctor_get(v_a_1194_, 5);
lean_inc(v_ref_1202_);
lean_dec_ref(v_a_1194_);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = l_Lean_Syntax_getArg(v_x_1193_, v___x_1203_);
v___x_1205_ = lean_unsigned_to_nat(2u);
v___x_1206_ = l_Lean_Syntax_getArg(v_x_1193_, v___x_1205_);
lean_dec(v_x_1193_);
v___x_1207_ = 0;
v___x_1208_ = l_Lean_SourceInfo_fromRef(v_ref_1202_, v___x_1207_);
lean_dec(v_ref_1202_);
v___x_1209_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1210_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2282____1___closed__1, &l___aux__Init__Core______macroRules__term___u2282____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2282____1___closed__1);
v___x_1211_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2282____1___closed__2));
v___x_1212_ = l_Lean_addMacroScope(v_quotContext_1200_, v___x_1211_, v_currMacroScope_1201_);
v___x_1213_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2282____1___closed__6));
lean_inc(v___x_1208_);
v___x_1214_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1208_);
lean_ctor_set(v___x_1214_, 1, v___x_1210_);
lean_ctor_set(v___x_1214_, 2, v___x_1212_);
lean_ctor_set(v___x_1214_, 3, v___x_1213_);
v___x_1215_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1208_);
v___x_1216_ = l_Lean_Syntax_node2(v___x_1208_, v___x_1215_, v___x_1204_, v___x_1206_);
v___x_1217_ = l_Lean_Syntax_node2(v___x_1208_, v___x_1209_, v___x_1214_, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v_a_1195_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSSubset__SSubset__1(lean_object* v_x_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1219_);
v___x_1223_ = l_Lean_Syntax_isOfKind(v_x_1219_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_dec(v_x_1219_);
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v_a_1221_);
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = l_Lean_Syntax_getArg(v_x_1219_, v___x_1226_);
v___x_1228_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1227_);
v___x_1229_ = l_Lean_Syntax_isOfKind(v___x_1227_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec(v___x_1227_);
lean_dec(v_x_1219_);
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v_a_1221_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = l_Lean_Syntax_getArg(v_x_1219_, v___x_1232_);
lean_dec(v_x_1219_);
v___x_1234_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1233_);
v___x_1235_ = l_Lean_Syntax_matchesNull(v___x_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_dec(v___x_1233_);
lean_dec(v___x_1227_);
v___x_1236_ = lean_box(0);
v___x_1237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v_a_1221_);
return v___x_1237_;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_ref_1240_; uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1238_ = l_Lean_Syntax_getArg(v___x_1233_, v___x_1226_);
v___x_1239_ = l_Lean_Syntax_getArg(v___x_1233_, v___x_1232_);
lean_dec(v___x_1233_);
v_ref_1240_ = l_Lean_replaceRef(v___x_1227_, v_a_1220_);
lean_dec(v___x_1227_);
v___x_1241_ = 0;
v___x_1242_ = l_Lean_SourceInfo_fromRef(v_ref_1240_, v___x_1241_);
lean_dec(v_ref_1240_);
v___x_1243_ = ((lean_object*)(l_term___u2282___00__closed__1));
v___x_1244_ = ((lean_object*)(l_term___u2282___00__closed__2));
lean_inc(v___x_1242_);
v___x_1245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1242_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = l_Lean_Syntax_node3(v___x_1242_, v___x_1243_, v___x_1238_, v___x_1245_, v___x_1239_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
lean_ctor_set(v___x_1247_, 1, v_a_1221_);
return v___x_1247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSSubset__SSubset__1___boxed(lean_object* v_x_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___aux__Init__Core______unexpand__HasSSubset__SSubset__1(v_x_1248_, v_a_1249_, v_a_1250_);
lean_dec(v_a_1249_);
return v_res_1251_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2287____1___closed__1(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2287____1___closed__0));
v___x_1270_ = l_String_toRawSubstring_x27(v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2287____1(lean_object* v_x_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_term___u2287___00__closed__1));
lean_inc(v_x_1279_);
v___x_1283_ = l_Lean_Syntax_isOfKind(v_x_1279_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec_ref(v_a_1280_);
lean_dec(v_x_1279_);
v___x_1284_ = lean_box(1);
v___x_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v_a_1281_);
return v___x_1285_;
}
else
{
lean_object* v_quotContext_1286_; lean_object* v_currMacroScope_1287_; lean_object* v_ref_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_quotContext_1286_ = lean_ctor_get(v_a_1280_, 1);
lean_inc(v_quotContext_1286_);
v_currMacroScope_1287_ = lean_ctor_get(v_a_1280_, 2);
lean_inc(v_currMacroScope_1287_);
v_ref_1288_ = lean_ctor_get(v_a_1280_, 5);
lean_inc(v_ref_1288_);
lean_dec_ref(v_a_1280_);
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = l_Lean_Syntax_getArg(v_x_1279_, v___x_1289_);
v___x_1291_ = lean_unsigned_to_nat(2u);
v___x_1292_ = l_Lean_Syntax_getArg(v_x_1279_, v___x_1291_);
lean_dec(v_x_1279_);
v___x_1293_ = 0;
v___x_1294_ = l_Lean_SourceInfo_fromRef(v_ref_1288_, v___x_1293_);
lean_dec(v_ref_1288_);
v___x_1295_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1296_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2287____1___closed__1, &l___aux__Init__Core______macroRules__term___u2287____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2287____1___closed__1);
v___x_1297_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2287____1___closed__2));
v___x_1298_ = l_Lean_addMacroScope(v_quotContext_1286_, v___x_1297_, v_currMacroScope_1287_);
v___x_1299_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2287____1___closed__4));
lean_inc(v___x_1294_);
v___x_1300_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1294_);
lean_ctor_set(v___x_1300_, 1, v___x_1296_);
lean_ctor_set(v___x_1300_, 2, v___x_1298_);
lean_ctor_set(v___x_1300_, 3, v___x_1299_);
v___x_1301_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1294_);
v___x_1302_ = l_Lean_Syntax_node2(v___x_1294_, v___x_1301_, v___x_1290_, v___x_1292_);
v___x_1303_ = l_Lean_Syntax_node2(v___x_1294_, v___x_1295_, v___x_1300_, v___x_1302_);
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v_a_1281_);
return v___x_1304_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Superset__1(lean_object* v_x_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1305_);
v___x_1309_ = l_Lean_Syntax_isOfKind(v_x_1305_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec(v_x_1305_);
v___x_1310_ = lean_box(0);
v___x_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_a_1307_);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = l_Lean_Syntax_getArg(v_x_1305_, v___x_1312_);
v___x_1314_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1313_);
v___x_1315_ = l_Lean_Syntax_isOfKind(v___x_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec(v___x_1313_);
lean_dec(v_x_1305_);
v___x_1316_ = lean_box(0);
v___x_1317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v_a_1307_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1318_ = lean_unsigned_to_nat(1u);
v___x_1319_ = l_Lean_Syntax_getArg(v_x_1305_, v___x_1318_);
lean_dec(v_x_1305_);
v___x_1320_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1319_);
v___x_1321_ = l_Lean_Syntax_matchesNull(v___x_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec(v___x_1319_);
lean_dec(v___x_1313_);
v___x_1322_ = lean_box(0);
v___x_1323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
lean_ctor_set(v___x_1323_, 1, v_a_1307_);
return v___x_1323_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v_ref_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1324_ = l_Lean_Syntax_getArg(v___x_1319_, v___x_1312_);
v___x_1325_ = l_Lean_Syntax_getArg(v___x_1319_, v___x_1318_);
lean_dec(v___x_1319_);
v_ref_1326_ = l_Lean_replaceRef(v___x_1313_, v_a_1306_);
lean_dec(v___x_1313_);
v___x_1327_ = 0;
v___x_1328_ = l_Lean_SourceInfo_fromRef(v_ref_1326_, v___x_1327_);
lean_dec(v_ref_1326_);
v___x_1329_ = ((lean_object*)(l_term___u2287___00__closed__1));
v___x_1330_ = ((lean_object*)(l_term___u2287___00__closed__2));
lean_inc(v___x_1328_);
v___x_1331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1328_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_Syntax_node3(v___x_1328_, v___x_1329_, v___x_1324_, v___x_1331_, v___x_1325_);
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v_a_1307_);
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Superset__1___boxed(lean_object* v_x_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l___aux__Init__Core______unexpand__Superset__1(v_x_1334_, v_a_1335_, v_a_1336_);
lean_dec(v_a_1335_);
return v_res_1337_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2283____1___closed__1(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2283____1___closed__0));
v___x_1356_ = l_String_toRawSubstring_x27(v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2283____1(lean_object* v_x_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = ((lean_object*)(l_term___u2283___00__closed__1));
lean_inc(v_x_1365_);
v___x_1369_ = l_Lean_Syntax_isOfKind(v_x_1365_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec_ref(v_a_1366_);
lean_dec(v_x_1365_);
v___x_1370_ = lean_box(1);
v___x_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v_a_1367_);
return v___x_1371_;
}
else
{
lean_object* v_quotContext_1372_; lean_object* v_currMacroScope_1373_; lean_object* v_ref_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_quotContext_1372_ = lean_ctor_get(v_a_1366_, 1);
lean_inc(v_quotContext_1372_);
v_currMacroScope_1373_ = lean_ctor_get(v_a_1366_, 2);
lean_inc(v_currMacroScope_1373_);
v_ref_1374_ = lean_ctor_get(v_a_1366_, 5);
lean_inc(v_ref_1374_);
lean_dec_ref(v_a_1366_);
v___x_1375_ = lean_unsigned_to_nat(0u);
v___x_1376_ = l_Lean_Syntax_getArg(v_x_1365_, v___x_1375_);
v___x_1377_ = lean_unsigned_to_nat(2u);
v___x_1378_ = l_Lean_Syntax_getArg(v_x_1365_, v___x_1377_);
lean_dec(v_x_1365_);
v___x_1379_ = 0;
v___x_1380_ = l_Lean_SourceInfo_fromRef(v_ref_1374_, v___x_1379_);
lean_dec(v_ref_1374_);
v___x_1381_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1382_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2283____1___closed__1, &l___aux__Init__Core______macroRules__term___u2283____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2283____1___closed__1);
v___x_1383_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2283____1___closed__2));
v___x_1384_ = l_Lean_addMacroScope(v_quotContext_1372_, v___x_1383_, v_currMacroScope_1373_);
v___x_1385_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2283____1___closed__4));
lean_inc(v___x_1380_);
v___x_1386_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1380_);
lean_ctor_set(v___x_1386_, 1, v___x_1382_);
lean_ctor_set(v___x_1386_, 2, v___x_1384_);
lean_ctor_set(v___x_1386_, 3, v___x_1385_);
v___x_1387_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1380_);
v___x_1388_ = l_Lean_Syntax_node2(v___x_1380_, v___x_1387_, v___x_1376_, v___x_1378_);
v___x_1389_ = l_Lean_Syntax_node2(v___x_1380_, v___x_1381_, v___x_1386_, v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v_a_1367_);
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SSuperset__1(lean_object* v_x_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1391_);
v___x_1395_ = l_Lean_Syntax_isOfKind(v_x_1391_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec(v_x_1391_);
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v_a_1393_);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = l_Lean_Syntax_getArg(v_x_1391_, v___x_1398_);
v___x_1400_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1399_);
v___x_1401_ = l_Lean_Syntax_isOfKind(v___x_1399_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_dec(v___x_1399_);
lean_dec(v_x_1391_);
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
lean_ctor_set(v___x_1403_, 1, v_a_1393_);
return v___x_1403_;
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1404_ = lean_unsigned_to_nat(1u);
v___x_1405_ = l_Lean_Syntax_getArg(v_x_1391_, v___x_1404_);
lean_dec(v_x_1391_);
v___x_1406_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1405_);
v___x_1407_ = l_Lean_Syntax_matchesNull(v___x_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_dec(v___x_1405_);
lean_dec(v___x_1399_);
v___x_1408_ = lean_box(0);
v___x_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
lean_ctor_set(v___x_1409_, 1, v_a_1393_);
return v___x_1409_;
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v_ref_1412_; uint8_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1410_ = l_Lean_Syntax_getArg(v___x_1405_, v___x_1398_);
v___x_1411_ = l_Lean_Syntax_getArg(v___x_1405_, v___x_1404_);
lean_dec(v___x_1405_);
v_ref_1412_ = l_Lean_replaceRef(v___x_1399_, v_a_1392_);
lean_dec(v___x_1399_);
v___x_1413_ = 0;
v___x_1414_ = l_Lean_SourceInfo_fromRef(v_ref_1412_, v___x_1413_);
lean_dec(v_ref_1412_);
v___x_1415_ = ((lean_object*)(l_term___u2283___00__closed__1));
v___x_1416_ = ((lean_object*)(l_term___u2283___00__closed__2));
lean_inc(v___x_1414_);
v___x_1417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1414_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = l_Lean_Syntax_node3(v___x_1414_, v___x_1415_, v___x_1410_, v___x_1417_, v___x_1411_);
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
lean_ctor_set(v___x_1419_, 1, v_a_1393_);
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SSuperset__1___boxed(lean_object* v_x_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___aux__Init__Core______unexpand__SSuperset__1(v_x_1420_, v_a_1421_, v_a_1422_);
lean_dec(v_a_1421_);
return v_res_1423_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u222a____1___closed__1(void){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u222a____1___closed__0));
v___x_1444_ = l_String_toRawSubstring_x27(v___x_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u222a____1(lean_object* v_x_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_term___u222a___00__closed__1));
lean_inc(v_x_1456_);
v___x_1460_ = l_Lean_Syntax_isOfKind(v_x_1456_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref(v_a_1457_);
lean_dec(v_x_1456_);
v___x_1461_ = lean_box(1);
v___x_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v_a_1458_);
return v___x_1462_;
}
else
{
lean_object* v_quotContext_1463_; lean_object* v_currMacroScope_1464_; lean_object* v_ref_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_quotContext_1463_ = lean_ctor_get(v_a_1457_, 1);
lean_inc(v_quotContext_1463_);
v_currMacroScope_1464_ = lean_ctor_get(v_a_1457_, 2);
lean_inc(v_currMacroScope_1464_);
v_ref_1465_ = lean_ctor_get(v_a_1457_, 5);
lean_inc(v_ref_1465_);
lean_dec_ref(v_a_1457_);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = l_Lean_Syntax_getArg(v_x_1456_, v___x_1466_);
v___x_1468_ = lean_unsigned_to_nat(2u);
v___x_1469_ = l_Lean_Syntax_getArg(v_x_1456_, v___x_1468_);
lean_dec(v_x_1456_);
v___x_1470_ = 0;
v___x_1471_ = l_Lean_SourceInfo_fromRef(v_ref_1465_, v___x_1470_);
lean_dec(v_ref_1465_);
v___x_1472_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1473_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u222a____1___closed__1, &l___aux__Init__Core______macroRules__term___u222a____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u222a____1___closed__1);
v___x_1474_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u222a____1___closed__4));
v___x_1475_ = l_Lean_addMacroScope(v_quotContext_1463_, v___x_1474_, v_currMacroScope_1464_);
v___x_1476_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u222a____1___closed__6));
lean_inc(v___x_1471_);
v___x_1477_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1471_);
lean_ctor_set(v___x_1477_, 1, v___x_1473_);
lean_ctor_set(v___x_1477_, 2, v___x_1475_);
lean_ctor_set(v___x_1477_, 3, v___x_1476_);
v___x_1478_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1471_);
v___x_1479_ = l_Lean_Syntax_node2(v___x_1471_, v___x_1478_, v___x_1467_, v___x_1469_);
v___x_1480_ = l_Lean_Syntax_node2(v___x_1471_, v___x_1472_, v___x_1477_, v___x_1479_);
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v_a_1458_);
return v___x_1481_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Union__union__1(lean_object* v_x_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1482_);
v___x_1486_ = l_Lean_Syntax_isOfKind(v_x_1482_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec(v_x_1482_);
v___x_1487_ = lean_box(0);
v___x_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v_a_1484_);
return v___x_1488_;
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = l_Lean_Syntax_getArg(v_x_1482_, v___x_1489_);
v___x_1491_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1490_);
v___x_1492_ = l_Lean_Syntax_isOfKind(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_dec(v___x_1490_);
lean_dec(v_x_1482_);
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v_a_1484_);
return v___x_1494_;
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1495_ = lean_unsigned_to_nat(1u);
v___x_1496_ = l_Lean_Syntax_getArg(v_x_1482_, v___x_1495_);
lean_dec(v_x_1482_);
v___x_1497_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1496_);
v___x_1498_ = l_Lean_Syntax_matchesNull(v___x_1496_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec(v___x_1496_);
lean_dec(v___x_1490_);
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
lean_ctor_set(v___x_1500_, 1, v_a_1484_);
return v___x_1500_;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v_ref_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1501_ = l_Lean_Syntax_getArg(v___x_1496_, v___x_1489_);
v___x_1502_ = l_Lean_Syntax_getArg(v___x_1496_, v___x_1495_);
lean_dec(v___x_1496_);
v_ref_1503_ = l_Lean_replaceRef(v___x_1490_, v_a_1483_);
lean_dec(v___x_1490_);
v___x_1504_ = 0;
v___x_1505_ = l_Lean_SourceInfo_fromRef(v_ref_1503_, v___x_1504_);
lean_dec(v_ref_1503_);
v___x_1506_ = ((lean_object*)(l_term___u222a___00__closed__1));
v___x_1507_ = ((lean_object*)(l_term___u222a___00__closed__2));
lean_inc(v___x_1505_);
v___x_1508_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1505_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = l_Lean_Syntax_node3(v___x_1505_, v___x_1506_, v___x_1501_, v___x_1508_, v___x_1502_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v_a_1484_);
return v___x_1510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Union__union__1___boxed(lean_object* v_x_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l___aux__Init__Core______unexpand__Union__union__1(v_x_1511_, v_a_1512_, v_a_1513_);
lean_dec(v_a_1512_);
return v_res_1514_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2229____1___closed__1(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2229____1___closed__0));
v___x_1535_ = l_String_toRawSubstring_x27(v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2229____1(lean_object* v_x_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_term___u2229___00__closed__1));
lean_inc(v_x_1547_);
v___x_1551_ = l_Lean_Syntax_isOfKind(v_x_1547_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec_ref(v_a_1548_);
lean_dec(v_x_1547_);
v___x_1552_ = lean_box(1);
v___x_1553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
lean_ctor_set(v___x_1553_, 1, v_a_1549_);
return v___x_1553_;
}
else
{
lean_object* v_quotContext_1554_; lean_object* v_currMacroScope_1555_; lean_object* v_ref_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_quotContext_1554_ = lean_ctor_get(v_a_1548_, 1);
lean_inc(v_quotContext_1554_);
v_currMacroScope_1555_ = lean_ctor_get(v_a_1548_, 2);
lean_inc(v_currMacroScope_1555_);
v_ref_1556_ = lean_ctor_get(v_a_1548_, 5);
lean_inc(v_ref_1556_);
lean_dec_ref(v_a_1548_);
v___x_1557_ = lean_unsigned_to_nat(0u);
v___x_1558_ = l_Lean_Syntax_getArg(v_x_1547_, v___x_1557_);
v___x_1559_ = lean_unsigned_to_nat(2u);
v___x_1560_ = l_Lean_Syntax_getArg(v_x_1547_, v___x_1559_);
lean_dec(v_x_1547_);
v___x_1561_ = 0;
v___x_1562_ = l_Lean_SourceInfo_fromRef(v_ref_1556_, v___x_1561_);
lean_dec(v_ref_1556_);
v___x_1563_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1564_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2229____1___closed__1, &l___aux__Init__Core______macroRules__term___u2229____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2229____1___closed__1);
v___x_1565_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2229____1___closed__4));
v___x_1566_ = l_Lean_addMacroScope(v_quotContext_1554_, v___x_1565_, v_currMacroScope_1555_);
v___x_1567_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2229____1___closed__6));
lean_inc(v___x_1562_);
v___x_1568_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1562_);
lean_ctor_set(v___x_1568_, 1, v___x_1564_);
lean_ctor_set(v___x_1568_, 2, v___x_1566_);
lean_ctor_set(v___x_1568_, 3, v___x_1567_);
v___x_1569_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1562_);
v___x_1570_ = l_Lean_Syntax_node2(v___x_1562_, v___x_1569_, v___x_1558_, v___x_1560_);
v___x_1571_ = l_Lean_Syntax_node2(v___x_1562_, v___x_1563_, v___x_1568_, v___x_1570_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v_a_1549_);
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Inter__inter__1(lean_object* v_x_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1573_);
v___x_1577_ = l_Lean_Syntax_isOfKind(v_x_1573_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v_x_1573_);
v___x_1578_ = lean_box(0);
v___x_1579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v_a_1575_);
return v___x_1579_;
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1580_ = lean_unsigned_to_nat(0u);
v___x_1581_ = l_Lean_Syntax_getArg(v_x_1573_, v___x_1580_);
v___x_1582_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1581_);
v___x_1583_ = l_Lean_Syntax_isOfKind(v___x_1581_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec(v___x_1581_);
lean_dec(v_x_1573_);
v___x_1584_ = lean_box(0);
v___x_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v_a_1575_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1586_ = lean_unsigned_to_nat(1u);
v___x_1587_ = l_Lean_Syntax_getArg(v_x_1573_, v___x_1586_);
lean_dec(v_x_1573_);
v___x_1588_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1587_);
v___x_1589_ = l_Lean_Syntax_matchesNull(v___x_1587_, v___x_1588_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_dec(v___x_1587_);
lean_dec(v___x_1581_);
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set(v___x_1591_, 1, v_a_1575_);
return v___x_1591_;
}
else
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v_ref_1594_; uint8_t v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1592_ = l_Lean_Syntax_getArg(v___x_1587_, v___x_1580_);
v___x_1593_ = l_Lean_Syntax_getArg(v___x_1587_, v___x_1586_);
lean_dec(v___x_1587_);
v_ref_1594_ = l_Lean_replaceRef(v___x_1581_, v_a_1574_);
lean_dec(v___x_1581_);
v___x_1595_ = 0;
v___x_1596_ = l_Lean_SourceInfo_fromRef(v_ref_1594_, v___x_1595_);
lean_dec(v_ref_1594_);
v___x_1597_ = ((lean_object*)(l_term___u2229___00__closed__1));
v___x_1598_ = ((lean_object*)(l_term___u2229___00__closed__2));
lean_inc(v___x_1596_);
v___x_1599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1596_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = l_Lean_Syntax_node3(v___x_1596_, v___x_1597_, v___x_1592_, v___x_1599_, v___x_1593_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v_a_1575_);
return v___x_1601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Inter__inter__1___boxed(lean_object* v_x_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___aux__Init__Core______unexpand__Inter__inter__1(v_x_1602_, v_a_1603_, v_a_1604_);
lean_dec(v_a_1603_);
return v_res_1605_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x5c____1___closed__1(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x5c____1___closed__0));
v___x_1624_ = l_String_toRawSubstring_x27(v___x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x5c____1(lean_object* v_x_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_term___x5c___00__closed__1));
lean_inc(v_x_1636_);
v___x_1640_ = l_Lean_Syntax_isOfKind(v_x_1636_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_dec_ref(v_a_1637_);
lean_dec(v_x_1636_);
v___x_1641_ = lean_box(1);
v___x_1642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_a_1638_);
return v___x_1642_;
}
else
{
lean_object* v_quotContext_1643_; lean_object* v_currMacroScope_1644_; lean_object* v_ref_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_quotContext_1643_ = lean_ctor_get(v_a_1637_, 1);
lean_inc(v_quotContext_1643_);
v_currMacroScope_1644_ = lean_ctor_get(v_a_1637_, 2);
lean_inc(v_currMacroScope_1644_);
v_ref_1645_ = lean_ctor_get(v_a_1637_, 5);
lean_inc(v_ref_1645_);
lean_dec_ref(v_a_1637_);
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = l_Lean_Syntax_getArg(v_x_1636_, v___x_1646_);
v___x_1648_ = lean_unsigned_to_nat(2u);
v___x_1649_ = l_Lean_Syntax_getArg(v_x_1636_, v___x_1648_);
lean_dec(v_x_1636_);
v___x_1650_ = 0;
v___x_1651_ = l_Lean_SourceInfo_fromRef(v_ref_1645_, v___x_1650_);
lean_dec(v_ref_1645_);
v___x_1652_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1653_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x5c____1___closed__1, &l___aux__Init__Core______macroRules__term___x5c____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x5c____1___closed__1);
v___x_1654_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x5c____1___closed__4));
v___x_1655_ = l_Lean_addMacroScope(v_quotContext_1643_, v___x_1654_, v_currMacroScope_1644_);
v___x_1656_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x5c____1___closed__6));
lean_inc(v___x_1651_);
v___x_1657_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1651_);
lean_ctor_set(v___x_1657_, 1, v___x_1653_);
lean_ctor_set(v___x_1657_, 2, v___x_1655_);
lean_ctor_set(v___x_1657_, 3, v___x_1656_);
v___x_1658_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1651_);
v___x_1659_ = l_Lean_Syntax_node2(v___x_1651_, v___x_1658_, v___x_1647_, v___x_1649_);
v___x_1660_ = l_Lean_Syntax_node2(v___x_1651_, v___x_1652_, v___x_1657_, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v_a_1638_);
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SDiff__sdiff__1(lean_object* v_x_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1665_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1662_);
v___x_1666_ = l_Lean_Syntax_isOfKind(v_x_1662_, v___x_1665_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec(v_x_1662_);
v___x_1667_ = lean_box(0);
v___x_1668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v_a_1664_);
return v___x_1668_;
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = l_Lean_Syntax_getArg(v_x_1662_, v___x_1669_);
v___x_1671_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1670_);
v___x_1672_ = l_Lean_Syntax_isOfKind(v___x_1670_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec(v___x_1670_);
lean_dec(v_x_1662_);
v___x_1673_ = lean_box(0);
v___x_1674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v_a_1664_);
return v___x_1674_;
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = l_Lean_Syntax_getArg(v_x_1662_, v___x_1675_);
lean_dec(v_x_1662_);
v___x_1677_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1676_);
v___x_1678_ = l_Lean_Syntax_matchesNull(v___x_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec(v___x_1676_);
lean_dec(v___x_1670_);
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v_a_1664_);
return v___x_1680_;
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v_ref_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1681_ = l_Lean_Syntax_getArg(v___x_1676_, v___x_1669_);
v___x_1682_ = l_Lean_Syntax_getArg(v___x_1676_, v___x_1675_);
lean_dec(v___x_1676_);
v_ref_1683_ = l_Lean_replaceRef(v___x_1670_, v_a_1663_);
lean_dec(v___x_1670_);
v___x_1684_ = 0;
v___x_1685_ = l_Lean_SourceInfo_fromRef(v_ref_1683_, v___x_1684_);
lean_dec(v_ref_1683_);
v___x_1686_ = ((lean_object*)(l_term___x5c___00__closed__1));
v___x_1687_ = ((lean_object*)(l_term___x5c___00__closed__2));
lean_inc(v___x_1685_);
v___x_1688_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1685_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = l_Lean_Syntax_node3(v___x_1685_, v___x_1686_, v___x_1681_, v___x_1688_, v___x_1682_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
lean_ctor_set(v___x_1690_, 1, v_a_1664_);
return v___x_1690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SDiff__sdiff__1___boxed(lean_object* v_x_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l___aux__Init__Core______unexpand__SDiff__sdiff__1(v_x_1691_, v_a_1692_, v_a_1693_);
lean_dec(v_a_1692_);
return v_res_1694_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__0));
v___x_1715_ = l_String_toRawSubstring_x27(v___x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1(lean_object* v_x_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = ((lean_object*)(l_term_x7b_x7d___closed__1));
v___x_1731_ = l_Lean_Syntax_isOfKind(v_x_1727_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec_ref(v_a_1728_);
v___x_1732_ = lean_box(1);
v___x_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v_a_1729_);
return v___x_1733_;
}
else
{
lean_object* v_quotContext_1734_; lean_object* v_currMacroScope_1735_; lean_object* v_ref_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_quotContext_1734_ = lean_ctor_get(v_a_1728_, 1);
lean_inc(v_quotContext_1734_);
v_currMacroScope_1735_ = lean_ctor_get(v_a_1728_, 2);
lean_inc(v_currMacroScope_1735_);
v_ref_1736_ = lean_ctor_get(v_a_1728_, 5);
lean_inc(v_ref_1736_);
lean_dec_ref(v_a_1728_);
v___x_1737_ = 0;
v___x_1738_ = l_Lean_SourceInfo_fromRef(v_ref_1736_, v___x_1737_);
lean_dec(v_ref_1736_);
v___x_1739_ = lean_obj_once(&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1, &l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1_once, _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1);
v___x_1740_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4));
v___x_1741_ = l_Lean_addMacroScope(v_quotContext_1734_, v___x_1740_, v_currMacroScope_1735_);
v___x_1742_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6));
v___x_1743_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1738_);
lean_ctor_set(v___x_1743_, 1, v___x_1739_);
lean_ctor_set(v___x_1743_, 2, v___x_1741_);
lean_ctor_set(v___x_1743_, 3, v___x_1742_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v_a_1729_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1(lean_object* v_x_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v_x_1745_);
v___x_1749_ = l_Lean_Syntax_isOfKind(v_x_1745_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v_x_1745_);
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v_a_1747_);
return v___x_1751_;
}
else
{
lean_object* v_ref_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_ref_1752_ = l_Lean_replaceRef(v_x_1745_, v_a_1746_);
lean_dec(v_x_1745_);
v___x_1753_ = 0;
v___x_1754_ = l_Lean_SourceInfo_fromRef(v_ref_1752_, v___x_1753_);
lean_dec(v_ref_1752_);
v___x_1755_ = ((lean_object*)(l_term_x7b_x7d___closed__1));
v___x_1756_ = ((lean_object*)(l_term_x7b_x7d___closed__2));
lean_inc(v___x_1754_);
v___x_1757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1754_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = ((lean_object*)(l_term_x7b_x7d___closed__4));
lean_inc(v___x_1754_);
v___x_1759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1754_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = l_Lean_Syntax_node2(v___x_1754_, v___x_1755_, v___x_1757_, v___x_1759_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
lean_ctor_set(v___x_1761_, 1, v_a_1747_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1___boxed(lean_object* v_x_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1(v_x_1762_, v_a_1763_, v_a_1764_);
lean_dec(v_a_1763_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_u2205__1(lean_object* v_x_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = ((lean_object*)(l_term_u2205___closed__1));
v___x_1781_ = l_Lean_Syntax_isOfKind(v_x_1777_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_dec_ref(v_a_1778_);
v___x_1782_ = lean_box(1);
v___x_1783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v_a_1779_);
return v___x_1783_;
}
else
{
lean_object* v_quotContext_1784_; lean_object* v_currMacroScope_1785_; lean_object* v_ref_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v_quotContext_1784_ = lean_ctor_get(v_a_1778_, 1);
lean_inc(v_quotContext_1784_);
v_currMacroScope_1785_ = lean_ctor_get(v_a_1778_, 2);
lean_inc(v_currMacroScope_1785_);
v_ref_1786_ = lean_ctor_get(v_a_1778_, 5);
lean_inc(v_ref_1786_);
lean_dec_ref(v_a_1778_);
v___x_1787_ = 0;
v___x_1788_ = l_Lean_SourceInfo_fromRef(v_ref_1786_, v___x_1787_);
lean_dec(v_ref_1786_);
v___x_1789_ = lean_obj_once(&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1, &l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1_once, _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1);
v___x_1790_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4));
v___x_1791_ = l_Lean_addMacroScope(v_quotContext_1784_, v___x_1790_, v_currMacroScope_1785_);
v___x_1792_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6));
v___x_1793_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1788_);
lean_ctor_set(v___x_1793_, 1, v___x_1789_);
lean_ctor_set(v___x_1793_, 2, v___x_1791_);
lean_ctor_set(v___x_1793_, 3, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
lean_ctor_set(v___x_1794_, 1, v_a_1779_);
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2(lean_object* v_x_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v_x_1795_);
v___x_1799_ = l_Lean_Syntax_isOfKind(v_x_1795_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec(v_x_1795_);
v___x_1800_ = lean_box(0);
v___x_1801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v_a_1797_);
return v___x_1801_;
}
else
{
lean_object* v_ref_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v_ref_1802_ = l_Lean_replaceRef(v_x_1795_, v_a_1796_);
lean_dec(v_x_1795_);
v___x_1803_ = 0;
v___x_1804_ = l_Lean_SourceInfo_fromRef(v_ref_1802_, v___x_1803_);
lean_dec(v_ref_1802_);
v___x_1805_ = ((lean_object*)(l_term_u2205___closed__1));
v___x_1806_ = ((lean_object*)(l_term_u2205___closed__2));
lean_inc(v___x_1804_);
v___x_1807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1804_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = l_Lean_Syntax_node1(v___x_1804_, v___x_1805_, v___x_1807_);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v_a_1797_);
return v___x_1809_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2___boxed(lean_object* v_x_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2(v_x_1810_, v_a_1811_, v_a_1812_);
lean_dec(v_a_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask_default___redArg(lean_object* v_inst_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_inst_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask_default(lean_object* v_a_1816_, lean_object* v_inst_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v_inst_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask___redArg(lean_object* v_inst_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v_inst_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask(lean_object* v_a_1821_, lean_object* v_inst_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_inst_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Task_pure___boxed(lean_object* v_00_u03b1_1826_, lean_object* v_get_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = lean_task_pure(v_get_1827_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Task_get___boxed(lean_object* v_00_u03b1_1831_, lean_object* v_self_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = lean_task_get_own(v_self_1832_);
return v_res_1833_;
}
}
static lean_object* _init_l_Task_Priority_default(void){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_unsigned_to_nat(0u);
return v___x_1834_;
}
}
static lean_object* _init_l_Task_Priority_max(void){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_unsigned_to_nat(8u);
return v___x_1835_;
}
}
static lean_object* _init_l_Task_Priority_dedicated(void){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_unsigned_to_nat(9u);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Task_spawn___boxed(lean_object* v_00_u03b1_1840_, lean_object* v_fn_1841_, lean_object* v_prio_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = lean_task_spawn(v_fn_1841_, v_prio_1842_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Task_map___boxed(lean_object* v_00_u03b1_1850_, lean_object* v_00_u03b2_1851_, lean_object* v_f_1852_, lean_object* v_x_1853_, lean_object* v_prio_1854_, lean_object* v_sync_1855_){
_start:
{
uint8_t v_sync_boxed_1856_; lean_object* v_res_1857_; 
v_sync_boxed_1856_ = lean_unbox(v_sync_1855_);
v_res_1857_ = lean_task_map(v_f_1852_, v_x_1853_, v_prio_1854_, v_sync_boxed_1856_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Task_bind___boxed(lean_object* v_00_u03b1_1864_, lean_object* v_00_u03b2_1865_, lean_object* v_x_1866_, lean_object* v_f_1867_, lean_object* v_prio_1868_, lean_object* v_sync_1869_){
_start:
{
uint8_t v_sync_boxed_1870_; lean_object* v_res_1871_; 
v_sync_boxed_1870_ = lean_unbox(v_sync_1869_);
v_res_1871_ = lean_task_bind(v_x_1866_, v_f_1867_, v_prio_1868_, v_sync_boxed_1870_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_strictOr___boxed(lean_object* v_b_u2081_1874_, lean_object* v_b_u2082_1875_){
_start:
{
uint8_t v_b_u2081_boxed_1876_; uint8_t v_b_u2082_boxed_1877_; uint8_t v_res_1878_; lean_object* v_r_1879_; 
v_b_u2081_boxed_1876_ = lean_unbox(v_b_u2081_1874_);
v_b_u2082_boxed_1877_ = lean_unbox(v_b_u2082_1875_);
v_res_1878_ = lean_strict_or(v_b_u2081_boxed_1876_, v_b_u2082_boxed_1877_);
v_r_1879_ = lean_box(v_res_1878_);
return v_r_1879_;
}
}
LEAN_EXPORT lean_object* l_strictAnd___boxed(lean_object* v_b_u2081_1882_, lean_object* v_b_u2082_1883_){
_start:
{
uint8_t v_b_u2081_boxed_1884_; uint8_t v_b_u2082_boxed_1885_; uint8_t v_res_1886_; lean_object* v_r_1887_; 
v_b_u2081_boxed_1884_ = lean_unbox(v_b_u2081_1882_);
v_b_u2082_boxed_1885_ = lean_unbox(v_b_u2082_1883_);
v_res_1886_ = lean_strict_and(v_b_u2081_boxed_1884_, v_b_u2082_boxed_1885_);
v_r_1887_ = lean_box(v_res_1886_);
return v_r_1887_;
}
}
LEAN_EXPORT uint8_t l_bne___redArg(lean_object* v_inst_1888_, lean_object* v_a_1889_, lean_object* v_b_1890_){
_start:
{
lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = lean_apply_2(v_inst_1888_, v_a_1889_, v_b_1890_);
v___x_1892_ = lean_unbox(v___x_1891_);
if (v___x_1892_ == 0)
{
uint8_t v___x_1893_; 
v___x_1893_ = 1;
return v___x_1893_;
}
else
{
uint8_t v___x_1894_; 
v___x_1894_ = 0;
return v___x_1894_;
}
}
}
LEAN_EXPORT lean_object* l_bne___redArg___boxed(lean_object* v_inst_1895_, lean_object* v_a_1896_, lean_object* v_b_1897_){
_start:
{
uint8_t v_res_1898_; lean_object* v_r_1899_; 
v_res_1898_ = l_bne___redArg(v_inst_1895_, v_a_1896_, v_b_1897_);
v_r_1899_ = lean_box(v_res_1898_);
return v_r_1899_;
}
}
LEAN_EXPORT uint8_t l_bne(lean_object* v_00_u03b1_1900_, lean_object* v_inst_1901_, lean_object* v_a_1902_, lean_object* v_b_1903_){
_start:
{
lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = lean_apply_2(v_inst_1901_, v_a_1902_, v_b_1903_);
v___x_1905_ = lean_unbox(v___x_1904_);
if (v___x_1905_ == 0)
{
uint8_t v___x_1906_; 
v___x_1906_ = 1;
return v___x_1906_;
}
else
{
uint8_t v___x_1907_; 
v___x_1907_ = 0;
return v___x_1907_;
}
}
}
LEAN_EXPORT lean_object* l_bne___boxed(lean_object* v_00_u03b1_1908_, lean_object* v_inst_1909_, lean_object* v_a_1910_, lean_object* v_b_1911_){
_start:
{
uint8_t v_res_1912_; lean_object* v_r_1913_; 
v_res_1912_ = l_bne(v_00_u03b1_1908_, v_inst_1909_, v_a_1910_, v_b_1911_);
v_r_1913_ = lean_box(v_res_1912_);
return v_r_1913_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0));
v___x_1932_ = l_String_toRawSubstring_x27(v___x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1(lean_object* v_x_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1944_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
lean_inc(v_x_1941_);
v___x_1945_ = l_Lean_Syntax_isOfKind(v_x_1941_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_dec_ref(v_a_1942_);
lean_dec(v_x_1941_);
v___x_1946_ = lean_box(1);
v___x_1947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v_a_1943_);
return v___x_1947_;
}
else
{
lean_object* v_quotContext_1948_; lean_object* v_currMacroScope_1949_; lean_object* v_ref_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v_quotContext_1948_ = lean_ctor_get(v_a_1942_, 1);
lean_inc(v_quotContext_1948_);
v_currMacroScope_1949_ = lean_ctor_get(v_a_1942_, 2);
lean_inc(v_currMacroScope_1949_);
v_ref_1950_ = lean_ctor_get(v_a_1942_, 5);
lean_inc(v_ref_1950_);
lean_dec_ref(v_a_1942_);
v___x_1951_ = lean_unsigned_to_nat(0u);
v___x_1952_ = l_Lean_Syntax_getArg(v_x_1941_, v___x_1951_);
v___x_1953_ = lean_unsigned_to_nat(2u);
v___x_1954_ = l_Lean_Syntax_getArg(v_x_1941_, v___x_1953_);
lean_dec(v_x_1941_);
v___x_1955_ = 0;
v___x_1956_ = l_Lean_SourceInfo_fromRef(v_ref_1950_, v___x_1955_);
lean_dec(v_ref_1950_);
v___x_1957_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1958_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1, &l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1);
v___x_1959_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2));
v___x_1960_ = l_Lean_addMacroScope(v_quotContext_1948_, v___x_1959_, v_currMacroScope_1949_);
v___x_1961_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4));
lean_inc(v___x_1956_);
v___x_1962_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1956_);
lean_ctor_set(v___x_1962_, 1, v___x_1958_);
lean_ctor_set(v___x_1962_, 2, v___x_1960_);
lean_ctor_set(v___x_1962_, 3, v___x_1961_);
v___x_1963_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1956_);
v___x_1964_ = l_Lean_Syntax_node2(v___x_1956_, v___x_1963_, v___x_1952_, v___x_1954_);
v___x_1965_ = l_Lean_Syntax_node2(v___x_1956_, v___x_1957_, v___x_1962_, v___x_1964_);
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
lean_ctor_set(v___x_1966_, 1, v_a_1943_);
return v___x_1966_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__bne__1(lean_object* v_x_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1970_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1967_);
v___x_1971_ = l_Lean_Syntax_isOfKind(v_x_1967_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec(v_x_1967_);
v___x_1972_ = lean_box(0);
v___x_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
lean_ctor_set(v___x_1973_, 1, v_a_1969_);
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = l_Lean_Syntax_getArg(v_x_1967_, v___x_1974_);
v___x_1976_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1975_);
v___x_1977_ = l_Lean_Syntax_isOfKind(v___x_1975_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_dec(v___x_1975_);
lean_dec(v_x_1967_);
v___x_1978_ = lean_box(0);
v___x_1979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v_a_1969_);
return v___x_1979_;
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1980_ = lean_unsigned_to_nat(1u);
v___x_1981_ = l_Lean_Syntax_getArg(v_x_1967_, v___x_1980_);
lean_dec(v_x_1967_);
v___x_1982_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1981_);
v___x_1983_ = l_Lean_Syntax_matchesNull(v___x_1981_, v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec(v___x_1981_);
lean_dec(v___x_1975_);
v___x_1984_ = lean_box(0);
v___x_1985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
lean_ctor_set(v___x_1985_, 1, v_a_1969_);
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v_ref_1988_; uint8_t v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1986_ = l_Lean_Syntax_getArg(v___x_1981_, v___x_1974_);
v___x_1987_ = l_Lean_Syntax_getArg(v___x_1981_, v___x_1980_);
lean_dec(v___x_1981_);
v_ref_1988_ = l_Lean_replaceRef(v___x_1975_, v_a_1968_);
lean_dec(v___x_1975_);
v___x_1989_ = 0;
v___x_1990_ = l_Lean_SourceInfo_fromRef(v_ref_1988_, v___x_1989_);
lean_dec(v_ref_1988_);
v___x_1991_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
v___x_1992_ = ((lean_object*)(l_term___x21_x3d___00__closed__2));
lean_inc(v___x_1990_);
v___x_1993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1990_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = l_Lean_Syntax_node3(v___x_1990_, v___x_1991_, v___x_1986_, v___x_1993_, v___x_1987_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
lean_ctor_set(v___x_1995_, 1, v_a_1969_);
return v___x_1995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__bne__1___boxed(lean_object* v_x_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l___aux__Init__Core______unexpand__bne__1(v_x_1996_, v_a_1997_, v_a_1998_);
lean_dec(v_a_1997_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2(lean_object* v_x_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
lean_inc(v_x_2007_);
v___x_2011_ = l_Lean_Syntax_isOfKind(v_x_2007_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec_ref(v_a_2008_);
lean_dec(v_x_2007_);
v___x_2012_ = lean_box(1);
v___x_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
lean_ctor_set(v___x_2013_, 1, v_a_2009_);
return v___x_2013_;
}
else
{
lean_object* v_quotContext_2014_; lean_object* v_currMacroScope_2015_; lean_object* v_ref_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_quotContext_2014_ = lean_ctor_get(v_a_2008_, 1);
lean_inc(v_quotContext_2014_);
v_currMacroScope_2015_ = lean_ctor_get(v_a_2008_, 2);
lean_inc(v_currMacroScope_2015_);
v_ref_2016_ = lean_ctor_get(v_a_2008_, 5);
lean_inc(v_ref_2016_);
lean_dec_ref(v_a_2008_);
v___x_2017_ = lean_unsigned_to_nat(0u);
v___x_2018_ = l_Lean_Syntax_getArg(v_x_2007_, v___x_2017_);
v___x_2019_ = lean_unsigned_to_nat(2u);
v___x_2020_ = l_Lean_Syntax_getArg(v_x_2007_, v___x_2019_);
lean_dec(v_x_2007_);
v___x_2021_ = 0;
v___x_2022_ = l_Lean_SourceInfo_fromRef(v_ref_2016_, v___x_2021_);
lean_dec(v_ref_2016_);
v___x_2023_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1));
v___x_2024_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__2));
lean_inc(v___x_2022_);
v___x_2025_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2022_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1, &l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1);
v___x_2027_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2));
v___x_2028_ = l_Lean_addMacroScope(v_quotContext_2014_, v___x_2027_, v_currMacroScope_2015_);
v___x_2029_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4));
lean_inc(v___x_2022_);
v___x_2030_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2022_);
lean_ctor_set(v___x_2030_, 1, v___x_2026_);
lean_ctor_set(v___x_2030_, 2, v___x_2028_);
lean_ctor_set(v___x_2030_, 3, v___x_2029_);
v___x_2031_ = l_Lean_Syntax_node4(v___x_2022_, v___x_2023_, v___x_2025_, v___x_2030_, v___x_2018_, v___x_2020_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v_a_2009_);
return v___x_2032_;
}
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_2033_, lean_object* v_x_2034_, lean_object* v_y_2035_){
_start:
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = lean_apply_2(v_inst_2033_, v_x_2034_, v_y_2035_);
v___x_2037_ = lean_unbox(v___x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_2038_, lean_object* v_x_2039_, lean_object* v_y_2040_){
_start:
{
uint8_t v_res_2041_; lean_object* v_r_2042_; 
v_res_2041_ = l_instDecidableEqOfLawfulBEq___redArg(v_inst_2038_, v_x_2039_, v_y_2040_);
v_r_2042_ = lean_box(v_res_2041_);
return v_r_2042_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_2043_, lean_object* v_inst_2044_, lean_object* v_inst_2045_, lean_object* v_x_2046_, lean_object* v_y_2047_){
_start:
{
lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2048_ = lean_apply_2(v_inst_2044_, v_x_2046_, v_y_2047_);
v___x_2049_ = lean_unbox(v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_x_2053_, lean_object* v_y_2054_){
_start:
{
uint8_t v_res_2055_; lean_object* v_r_2056_; 
v_res_2055_ = l_instDecidableEqOfLawfulBEq(v_00_u03b1_2050_, v_inst_2051_, v_inst_2052_, v_x_2053_, v_y_2054_);
v_r_2056_ = lean_box(v_res_2055_);
return v_r_2056_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__0));
v___x_2075_ = l_String_toRawSubstring_x27(v___x_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____1(lean_object* v_x_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_term___u2260___00__closed__1));
lean_inc(v_x_2084_);
v___x_2088_ = l_Lean_Syntax_isOfKind(v_x_2084_, v___x_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec_ref(v_a_2085_);
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
lean_inc(v_quotContext_2091_);
v_currMacroScope_2092_ = lean_ctor_get(v_a_2085_, 2);
lean_inc(v_currMacroScope_2092_);
v_ref_2093_ = lean_ctor_get(v_a_2085_, 5);
lean_inc(v_ref_2093_);
lean_dec_ref(v_a_2085_);
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = l_Lean_Syntax_getArg(v_x_2084_, v___x_2094_);
v___x_2096_ = lean_unsigned_to_nat(2u);
v___x_2097_ = l_Lean_Syntax_getArg(v_x_2084_, v___x_2096_);
lean_dec(v_x_2084_);
v___x_2098_ = 0;
v___x_2099_ = l_Lean_SourceInfo_fromRef(v_ref_2093_, v___x_2098_);
lean_dec(v_ref_2093_);
v___x_2100_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_2101_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2260____1___closed__1, &l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1);
v___x_2102_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__2));
v___x_2103_ = l_Lean_addMacroScope(v_quotContext_2091_, v___x_2102_, v_currMacroScope_2092_);
v___x_2104_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__4));
lean_inc(v___x_2099_);
v___x_2105_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2099_);
lean_ctor_set(v___x_2105_, 1, v___x_2101_);
lean_ctor_set(v___x_2105_, 2, v___x_2103_);
lean_ctor_set(v___x_2105_, 3, v___x_2104_);
v___x_2106_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_2099_);
v___x_2107_ = l_Lean_Syntax_node2(v___x_2099_, v___x_2106_, v___x_2095_, v___x_2097_);
v___x_2108_ = l_Lean_Syntax_node2(v___x_2099_, v___x_2100_, v___x_2105_, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v_a_2086_);
return v___x_2109_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Ne__1(lean_object* v_x_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_2110_);
v___x_2114_ = l_Lean_Syntax_isOfKind(v_x_2110_, v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec(v_x_2110_);
v___x_2115_ = lean_box(0);
v___x_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v_a_2112_);
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2118_ = l_Lean_Syntax_getArg(v_x_2110_, v___x_2117_);
v___x_2119_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_2118_);
v___x_2120_ = l_Lean_Syntax_isOfKind(v___x_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_dec(v___x_2118_);
lean_dec(v_x_2110_);
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v_a_2112_);
return v___x_2122_;
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2123_ = lean_unsigned_to_nat(1u);
v___x_2124_ = l_Lean_Syntax_getArg(v_x_2110_, v___x_2123_);
lean_dec(v_x_2110_);
v___x_2125_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2124_);
v___x_2126_ = l_Lean_Syntax_matchesNull(v___x_2124_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec(v___x_2124_);
lean_dec(v___x_2118_);
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v_a_2112_);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v_ref_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2129_ = l_Lean_Syntax_getArg(v___x_2124_, v___x_2117_);
v___x_2130_ = l_Lean_Syntax_getArg(v___x_2124_, v___x_2123_);
lean_dec(v___x_2124_);
v_ref_2131_ = l_Lean_replaceRef(v___x_2118_, v_a_2111_);
lean_dec(v___x_2118_);
v___x_2132_ = 0;
v___x_2133_ = l_Lean_SourceInfo_fromRef(v_ref_2131_, v___x_2132_);
lean_dec(v_ref_2131_);
v___x_2134_ = ((lean_object*)(l_term___u2260___00__closed__1));
v___x_2135_ = ((lean_object*)(l_term___u2260___00__closed__2));
lean_inc(v___x_2133_);
v___x_2136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2133_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = l_Lean_Syntax_node3(v___x_2133_, v___x_2134_, v___x_2129_, v___x_2136_, v___x_2130_);
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
lean_ctor_set(v___x_2138_, 1, v_a_2112_);
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Ne__1___boxed(lean_object* v_x_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l___aux__Init__Core______unexpand__Ne__1(v_x_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_a_2140_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____2(lean_object* v_x_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_term___u2260___00__closed__1));
lean_inc(v_x_2150_);
v___x_2154_ = l_Lean_Syntax_isOfKind(v_x_2150_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_dec_ref(v_a_2151_);
lean_dec(v_x_2150_);
v___x_2155_ = lean_box(1);
v___x_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
lean_ctor_set(v___x_2156_, 1, v_a_2152_);
return v___x_2156_;
}
else
{
lean_object* v_quotContext_2157_; lean_object* v_currMacroScope_2158_; lean_object* v_ref_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_quotContext_2157_ = lean_ctor_get(v_a_2151_, 1);
lean_inc(v_quotContext_2157_);
v_currMacroScope_2158_ = lean_ctor_get(v_a_2151_, 2);
lean_inc(v_currMacroScope_2158_);
v_ref_2159_ = lean_ctor_get(v_a_2151_, 5);
lean_inc(v_ref_2159_);
lean_dec_ref(v_a_2151_);
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = l_Lean_Syntax_getArg(v_x_2150_, v___x_2160_);
v___x_2162_ = lean_unsigned_to_nat(2u);
v___x_2163_ = l_Lean_Syntax_getArg(v_x_2150_, v___x_2162_);
lean_dec(v_x_2150_);
v___x_2164_ = 0;
v___x_2165_ = l_Lean_SourceInfo_fromRef(v_ref_2159_, v___x_2164_);
lean_dec(v_ref_2159_);
v___x_2166_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____2___closed__1));
v___x_2167_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____2___closed__2));
lean_inc(v___x_2165_);
v___x_2168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2165_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2260____1___closed__1, &l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1);
v___x_2170_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__2));
v___x_2171_ = l_Lean_addMacroScope(v_quotContext_2157_, v___x_2170_, v_currMacroScope_2158_);
v___x_2172_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__4));
lean_inc(v___x_2165_);
v___x_2173_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2165_);
lean_ctor_set(v___x_2173_, 1, v___x_2169_);
lean_ctor_set(v___x_2173_, 2, v___x_2171_);
lean_ctor_set(v___x_2173_, 3, v___x_2172_);
v___x_2174_ = l_Lean_Syntax_node4(v___x_2165_, v___x_2166_, v___x_2168_, v___x_2173_, v___x_2161_, v___x_2163_);
v___x_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
lean_ctor_set(v___x_2175_, 1, v_a_2152_);
return v___x_2175_;
}
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__5));
v___x_2191_ = l_String_toRawSubstring_x27(v___x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1(lean_object* v_x_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2205_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2));
v___x_2206_ = l_Lean_Syntax_isOfKind(v_x_2202_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec_ref(v_a_2203_);
v___x_2207_ = lean_box(1);
v___x_2208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v_a_2204_);
return v___x_2208_;
}
else
{
lean_object* v_quotContext_2209_; lean_object* v_currMacroScope_2210_; lean_object* v_ref_2211_; uint8_t v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_quotContext_2209_ = lean_ctor_get(v_a_2203_, 1);
lean_inc(v_quotContext_2209_);
v_currMacroScope_2210_ = lean_ctor_get(v_a_2203_, 2);
lean_inc(v_currMacroScope_2210_);
v_ref_2211_ = lean_ctor_get(v_a_2203_, 5);
lean_inc(v_ref_2211_);
lean_dec_ref(v_a_2203_);
v___x_2212_ = 0;
v___x_2213_ = l_Lean_SourceInfo_fromRef(v_ref_2211_, v___x_2212_);
lean_dec(v_ref_2211_);
v___x_2214_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3));
v___x_2215_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4));
lean_inc(v___x_2213_);
v___x_2216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2213_);
lean_ctor_set(v___x_2216_, 1, v___x_2214_);
v___x_2217_ = lean_obj_once(&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6, &l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6_once, _init_l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6);
v___x_2218_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8));
v___x_2219_ = l_Lean_addMacroScope(v_quotContext_2209_, v___x_2218_, v_currMacroScope_2210_);
v___x_2220_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__10));
lean_inc(v___x_2213_);
v___x_2221_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2213_);
lean_ctor_set(v___x_2221_, 1, v___x_2217_);
lean_ctor_set(v___x_2221_, 2, v___x_2219_);
lean_ctor_set(v___x_2221_, 3, v___x_2220_);
v___x_2222_ = l_Lean_Syntax_node2(v___x_2213_, v___x_2215_, v___x_2216_, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v_a_2204_);
return v___x_2223_;
}
}
}
static lean_object* _init_l_instTransIff(void){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_box(0);
return v___x_2224_;
}
}
LEAN_EXPORT uint8_t l_toBoolUsing___redArg(uint8_t v_d_2225_){
_start:
{
return v_d_2225_;
}
}
LEAN_EXPORT lean_object* l_toBoolUsing___redArg___boxed(lean_object* v_d_2226_){
_start:
{
uint8_t v_d_boxed_2227_; uint8_t v_res_2228_; lean_object* v_r_2229_; 
v_d_boxed_2227_ = lean_unbox(v_d_2226_);
v_res_2228_ = l_toBoolUsing___redArg(v_d_boxed_2227_);
v_r_2229_ = lean_box(v_res_2228_);
return v_r_2229_;
}
}
LEAN_EXPORT uint8_t l_toBoolUsing(lean_object* v_p_2230_, uint8_t v_d_2231_){
_start:
{
return v_d_2231_;
}
}
LEAN_EXPORT lean_object* l_toBoolUsing___boxed(lean_object* v_p_2232_, lean_object* v_d_2233_){
_start:
{
uint8_t v_d_boxed_2234_; uint8_t v_res_2235_; lean_object* v_r_2236_; 
v_d_boxed_2234_ = lean_unbox(v_d_2233_);
v_res_2235_ = l_toBoolUsing(v_p_2232_, v_d_boxed_2234_);
v_r_2236_ = lean_box(v_res_2235_);
return v_r_2236_;
}
}
static uint8_t _init_l_instDecidableTrue(void){
_start:
{
uint8_t v___x_2237_; 
v___x_2237_ = 1;
return v___x_2237_;
}
}
static uint8_t _init_l_instDecidableFalse(void){
_start:
{
uint8_t v___x_2238_; 
v___x_2238_ = 0;
return v___x_2238_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__iff___redArg(uint8_t v_inst_2239_){
_start:
{
return v_inst_2239_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__iff___redArg___boxed(lean_object* v_inst_2240_){
_start:
{
uint8_t v_inst_8__boxed_2241_; uint8_t v_res_2242_; lean_object* v_r_2243_; 
v_inst_8__boxed_2241_ = lean_unbox(v_inst_2240_);
v_res_2242_ = l_decidable__of__decidable__of__iff___redArg(v_inst_8__boxed_2241_);
v_r_2243_ = lean_box(v_res_2242_);
return v_r_2243_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__iff(lean_object* v_p_2244_, lean_object* v_q_2245_, uint8_t v_inst_2246_, lean_object* v_h_2247_){
_start:
{
return v_inst_2246_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__iff___boxed(lean_object* v_p_2248_, lean_object* v_q_2249_, lean_object* v_inst_2250_, lean_object* v_h_2251_){
_start:
{
uint8_t v_inst_11__boxed_2252_; uint8_t v_res_2253_; lean_object* v_r_2254_; 
v_inst_11__boxed_2252_ = lean_unbox(v_inst_2250_);
v_res_2253_ = l_decidable__of__decidable__of__iff(v_p_2248_, v_q_2249_, v_inst_11__boxed_2252_, v_h_2251_);
v_r_2254_ = lean_box(v_res_2253_);
return v_r_2254_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__eq___redArg(uint8_t v_inst_2255_){
_start:
{
return v_inst_2255_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__eq___redArg___boxed(lean_object* v_inst_2256_){
_start:
{
uint8_t v_inst_8__boxed_2257_; uint8_t v_res_2258_; lean_object* v_r_2259_; 
v_inst_8__boxed_2257_ = lean_unbox(v_inst_2256_);
v_res_2258_ = l_decidable__of__decidable__of__eq___redArg(v_inst_8__boxed_2257_);
v_r_2259_ = lean_box(v_res_2258_);
return v_r_2259_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__eq(lean_object* v_p_2260_, lean_object* v_q_2261_, uint8_t v_inst_2262_, lean_object* v_h_2263_){
_start:
{
return v_inst_2262_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__eq___boxed(lean_object* v_p_2264_, lean_object* v_q_2265_, lean_object* v_inst_2266_, lean_object* v_h_2267_){
_start:
{
uint8_t v_inst_11__boxed_2268_; uint8_t v_res_2269_; lean_object* v_r_2270_; 
v_inst_11__boxed_2268_ = lean_unbox(v_inst_2266_);
v_res_2269_ = l_decidable__of__decidable__of__eq(v_p_2264_, v_q_2265_, v_inst_11__boxed_2268_, v_h_2267_);
v_r_2270_ = lean_box(v_res_2269_);
return v_r_2270_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIff___redArg(uint8_t v_inst_2271_, uint8_t v_inst_2272_){
_start:
{
if (v_inst_2271_ == 0)
{
if (v_inst_2272_ == 0)
{
uint8_t v___x_2273_; 
v___x_2273_ = 1;
return v___x_2273_;
}
else
{
return v_inst_2271_;
}
}
else
{
return v_inst_2272_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableIff___redArg___boxed(lean_object* v_inst_2274_, lean_object* v_inst_2275_){
_start:
{
uint8_t v_inst_15__boxed_2276_; uint8_t v_inst_16__boxed_2277_; uint8_t v_res_2278_; lean_object* v_r_2279_; 
v_inst_15__boxed_2276_ = lean_unbox(v_inst_2274_);
v_inst_16__boxed_2277_ = lean_unbox(v_inst_2275_);
v_res_2278_ = l_instDecidableIff___redArg(v_inst_15__boxed_2276_, v_inst_16__boxed_2277_);
v_r_2279_ = lean_box(v_res_2278_);
return v_r_2279_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIff(lean_object* v_p_2280_, lean_object* v_q_2281_, uint8_t v_inst_2282_, uint8_t v_inst_2283_){
_start:
{
if (v_inst_2282_ == 0)
{
if (v_inst_2283_ == 0)
{
uint8_t v___x_2284_; 
v___x_2284_ = 1;
return v___x_2284_;
}
else
{
return v_inst_2282_;
}
}
else
{
return v_inst_2283_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableIff___boxed(lean_object* v_p_2285_, lean_object* v_q_2286_, lean_object* v_inst_2287_, lean_object* v_inst_2288_){
_start:
{
uint8_t v_inst_23__boxed_2289_; uint8_t v_inst_24__boxed_2290_; uint8_t v_res_2291_; lean_object* v_r_2292_; 
v_inst_23__boxed_2289_ = lean_unbox(v_inst_2287_);
v_inst_24__boxed_2290_ = lean_unbox(v_inst_2288_);
v_res_2291_ = l_instDecidableIff(v_p_2285_, v_q_2286_, v_inst_23__boxed_2289_, v_inst_24__boxed_2290_);
v_r_2292_ = lean_box(v_res_2291_);
return v_r_2292_;
}
}
LEAN_EXPORT lean_object* l_iteInduction___redArg(uint8_t v_inst_2293_, lean_object* v_hpos_2294_, lean_object* v_hneg_2295_){
_start:
{
if (v_inst_2293_ == 0)
{
lean_object* v___x_2296_; 
lean_dec(v_hpos_2294_);
v___x_2296_ = lean_apply_1(v_hneg_2295_, lean_box(0));
return v___x_2296_;
}
else
{
lean_object* v___x_2297_; 
lean_dec(v_hneg_2295_);
v___x_2297_ = lean_apply_1(v_hpos_2294_, lean_box(0));
return v___x_2297_;
}
}
}
LEAN_EXPORT lean_object* l_iteInduction___redArg___boxed(lean_object* v_inst_2298_, lean_object* v_hpos_2299_, lean_object* v_hneg_2300_){
_start:
{
uint8_t v_inst_boxed_2301_; lean_object* v_res_2302_; 
v_inst_boxed_2301_ = lean_unbox(v_inst_2298_);
v_res_2302_ = l_iteInduction___redArg(v_inst_boxed_2301_, v_hpos_2299_, v_hneg_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_iteInduction(lean_object* v_00_u03b1_2303_, lean_object* v_c_2304_, uint8_t v_inst_2305_, lean_object* v_motive_2306_, lean_object* v_t_2307_, lean_object* v_e_2308_, lean_object* v_hpos_2309_, lean_object* v_hneg_2310_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_iteInduction___redArg(v_inst_2305_, v_hpos_2309_, v_hneg_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_iteInduction___boxed(lean_object* v_00_u03b1_2312_, lean_object* v_c_2313_, lean_object* v_inst_2314_, lean_object* v_motive_2315_, lean_object* v_t_2316_, lean_object* v_e_2317_, lean_object* v_hpos_2318_, lean_object* v_hneg_2319_){
_start:
{
uint8_t v_inst_boxed_2320_; lean_object* v_res_2321_; 
v_inst_boxed_2320_ = lean_unbox(v_inst_2314_);
v_res_2321_ = l_iteInduction(v_00_u03b1_2312_, v_c_2313_, v_inst_boxed_2320_, v_motive_2315_, v_t_2316_, v_e_2317_, v_hpos_2318_, v_hneg_2319_);
lean_dec(v_e_2317_);
lean_dec(v_t_2316_);
return v_res_2321_;
}
}
LEAN_EXPORT uint8_t l_instDecidableDite___redArg(uint8_t v_dC_2322_, lean_object* v_dT_2323_, lean_object* v_dE_2324_){
_start:
{
if (v_dC_2322_ == 0)
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
lean_dec_ref(v_dT_2323_);
v___x_2325_ = lean_apply_1(v_dE_2324_, lean_box(0));
v___x_2326_ = lean_unbox(v___x_2325_);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; uint8_t v___x_2328_; 
lean_dec_ref(v_dE_2324_);
v___x_2327_ = lean_apply_1(v_dT_2323_, lean_box(0));
v___x_2328_ = lean_unbox(v___x_2327_);
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableDite___redArg___boxed(lean_object* v_dC_2329_, lean_object* v_dT_2330_, lean_object* v_dE_2331_){
_start:
{
uint8_t v_dC_boxed_2332_; uint8_t v_res_2333_; lean_object* v_r_2334_; 
v_dC_boxed_2332_ = lean_unbox(v_dC_2329_);
v_res_2333_ = l_instDecidableDite___redArg(v_dC_boxed_2332_, v_dT_2330_, v_dE_2331_);
v_r_2334_ = lean_box(v_res_2333_);
return v_r_2334_;
}
}
LEAN_EXPORT uint8_t l_instDecidableDite(lean_object* v_c_2335_, lean_object* v_t_2336_, lean_object* v_e_2337_, uint8_t v_dC_2338_, lean_object* v_dT_2339_, lean_object* v_dE_2340_){
_start:
{
if (v_dC_2338_ == 0)
{
lean_object* v___x_2341_; uint8_t v___x_2342_; 
lean_dec_ref(v_dT_2339_);
v___x_2341_ = lean_apply_1(v_dE_2340_, lean_box(0));
v___x_2342_ = lean_unbox(v___x_2341_);
return v___x_2342_;
}
else
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
lean_dec_ref(v_dE_2340_);
v___x_2343_ = lean_apply_1(v_dT_2339_, lean_box(0));
v___x_2344_ = lean_unbox(v___x_2343_);
return v___x_2344_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableDite___boxed(lean_object* v_c_2345_, lean_object* v_t_2346_, lean_object* v_e_2347_, lean_object* v_dC_2348_, lean_object* v_dT_2349_, lean_object* v_dE_2350_){
_start:
{
uint8_t v_dC_boxed_2351_; uint8_t v_res_2352_; lean_object* v_r_2353_; 
v_dC_boxed_2351_ = lean_unbox(v_dC_2348_);
v_res_2352_ = l_instDecidableDite(v_c_2345_, v_t_2346_, v_e_2347_, v_dC_boxed_2351_, v_dT_2349_, v_dE_2350_);
v_r_2353_ = lean_box(v_res_2352_);
return v_r_2353_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg___lam__0(lean_object* v_x_2354_){
_start:
{
lean_inc(v_x_2354_);
return v_x_2354_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg___lam__0___boxed(lean_object* v_x_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_noConfusionEnum___redArg___lam__0(v_x_2355_);
lean_dec(v_x_2355_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg(lean_object* v_inst_2358_, lean_object* v_f_2359_, lean_object* v_x_2360_, lean_object* v_y_2361_){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___f_2365_; 
lean_inc(v_f_2359_);
v___x_2362_ = lean_apply_1(v_f_2359_, v_x_2360_);
v___x_2363_ = lean_apply_1(v_f_2359_, v_y_2361_);
v___x_2364_ = lean_apply_2(v_inst_2358_, v___x_2362_, v___x_2363_);
v___f_2365_ = ((lean_object*)(l_noConfusionEnum___redArg___closed__0));
return v___f_2365_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum(lean_object* v_00_u03b1_2366_, lean_object* v_00_u03b2_2367_, lean_object* v_inst_2368_, lean_object* v_f_2369_, lean_object* v_P_2370_, lean_object* v_x_2371_, lean_object* v_y_2372_, lean_object* v_h_2373_){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___f_2377_; 
lean_inc(v_f_2369_);
v___x_2374_ = lean_apply_1(v_f_2369_, v_x_2371_);
v___x_2375_ = lean_apply_1(v_f_2369_, v_y_2372_);
v___x_2376_ = lean_apply_2(v_inst_2368_, v___x_2374_, v___x_2375_);
v___f_2377_ = ((lean_object*)(l_noConfusionEnum___redArg___closed__0));
return v___f_2377_;
}
}
static lean_object* _init_l_instInhabitedProp(void){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_box(0);
return v___x_2378_;
}
}
static lean_object* _init_l_instInhabitedNonScalar_default(void){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_unsigned_to_nat(0u);
return v___x_2379_;
}
}
static lean_object* _init_l_instInhabitedNonScalar(void){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_unsigned_to_nat(0u);
return v___x_2380_;
}
}
static lean_object* _init_l_instInhabitedPNonScalar_default(void){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_unsigned_to_nat(0u);
return v___x_2381_;
}
}
static lean_object* _init_l_instInhabitedPNonScalar(void){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_unsigned_to_nat(0u);
return v___x_2382_;
}
}
static lean_object* _init_l_instInhabitedTrue(void){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_box(0);
return v___x_2383_;
}
}
LEAN_EXPORT uint8_t l_Subtype_instBEq___redArg___lam__0(lean_object* v_inst_2384_, lean_object* v_x_2385_, lean_object* v_y_2386_){
_start:
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = lean_apply_2(v_inst_2384_, v_x_2385_, v_y_2386_);
v___x_2388_ = lean_unbox(v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq___redArg___lam__0___boxed(lean_object* v_inst_2389_, lean_object* v_x_2390_, lean_object* v_y_2391_){
_start:
{
uint8_t v_res_2392_; lean_object* v_r_2393_; 
v_res_2392_ = l_Subtype_instBEq___redArg___lam__0(v_inst_2389_, v_x_2390_, v_y_2391_);
v_r_2393_ = lean_box(v_res_2392_);
return v_r_2393_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq___redArg(lean_object* v_inst_2394_){
_start:
{
lean_object* v___f_2395_; 
v___f_2395_ = lean_alloc_closure((void*)(l_Subtype_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2395_, 0, v_inst_2394_);
return v___f_2395_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq(lean_object* v_00_u03b1_2396_, lean_object* v_p_2397_, lean_object* v_inst_2398_){
_start:
{
lean_object* v___f_2399_; 
v___f_2399_ = lean_alloc_closure((void*)(l_Subtype_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2399_, 0, v_inst_2398_);
return v___f_2399_;
}
}
LEAN_EXPORT uint8_t l_Subtype_instDecidableEq___redArg(lean_object* v_inst_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_){
_start:
{
lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2403_ = lean_apply_2(v_inst_2400_, v_x_2401_, v_x_2402_);
v___x_2404_ = lean_unbox(v___x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instDecidableEq___redArg___boxed(lean_object* v_inst_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_res_2408_ = l_Subtype_instDecidableEq___redArg(v_inst_2405_, v_x_2406_, v_x_2407_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT uint8_t l_Subtype_instDecidableEq(lean_object* v_00_u03b1_2410_, lean_object* v_p_2411_, lean_object* v_inst_2412_, lean_object* v_x_2413_, lean_object* v_x_2414_){
_start:
{
lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2415_ = lean_apply_2(v_inst_2412_, v_x_2413_, v_x_2414_);
v___x_2416_ = lean_unbox(v___x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instDecidableEq___boxed(lean_object* v_00_u03b1_2417_, lean_object* v_p_2418_, lean_object* v_inst_2419_, lean_object* v_x_2420_, lean_object* v_x_2421_){
_start:
{
uint8_t v_res_2422_; lean_object* v_r_2423_; 
v_res_2422_ = l_Subtype_instDecidableEq(v_00_u03b1_2417_, v_p_2418_, v_inst_2419_, v_x_2420_, v_x_2421_);
v_r_2423_ = lean_box(v_res_2422_);
return v_r_2423_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedLeft___redArg(lean_object* v_inst_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v_inst_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedLeft(lean_object* v_00_u03b1_2426_, lean_object* v_00_u03b2_2427_, lean_object* v_inst_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v_inst_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedRight___redArg(lean_object* v_inst_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2431_, 0, v_inst_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedRight(lean_object* v_00_u03b1_2432_, lean_object* v_00_u03b2_2433_, lean_object* v_inst_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2435_, 0, v_inst_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum_decEq___redArg(lean_object* v_inst_2436_, lean_object* v_inst_2437_, lean_object* v_x_2438_, lean_object* v_x_2439_){
_start:
{
if (lean_obj_tag(v_x_2438_) == 0)
{
lean_dec_ref(v_inst_2437_);
if (lean_obj_tag(v_x_2439_) == 0)
{
lean_object* v_val_2440_; lean_object* v_val_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
v_val_2440_ = lean_ctor_get(v_x_2438_, 0);
lean_inc(v_val_2440_);
lean_dec_ref(v_x_2438_);
v_val_2441_ = lean_ctor_get(v_x_2439_, 0);
lean_inc(v_val_2441_);
lean_dec_ref(v_x_2439_);
v___x_2442_ = lean_apply_2(v_inst_2436_, v_val_2440_, v_val_2441_);
v___x_2443_ = lean_unbox(v___x_2442_);
return v___x_2443_;
}
else
{
uint8_t v___x_2444_; 
lean_dec_ref(v_x_2439_);
lean_dec_ref(v_x_2438_);
lean_dec_ref(v_inst_2436_);
v___x_2444_ = 0;
return v___x_2444_;
}
}
else
{
lean_dec_ref(v_inst_2436_);
if (lean_obj_tag(v_x_2439_) == 0)
{
uint8_t v___x_2445_; 
lean_dec_ref(v_x_2439_);
lean_dec_ref(v_x_2438_);
lean_dec_ref(v_inst_2437_);
v___x_2445_ = 0;
return v___x_2445_;
}
else
{
lean_object* v_val_2446_; lean_object* v_val_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; 
v_val_2446_ = lean_ctor_get(v_x_2438_, 0);
lean_inc(v_val_2446_);
lean_dec_ref(v_x_2438_);
v_val_2447_ = lean_ctor_get(v_x_2439_, 0);
lean_inc(v_val_2447_);
lean_dec_ref(v_x_2439_);
v___x_2448_ = lean_apply_2(v_inst_2437_, v_val_2446_, v_val_2447_);
v___x_2449_ = lean_unbox(v___x_2448_);
return v___x_2449_;
}
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum_decEq___redArg___boxed(lean_object* v_inst_2450_, lean_object* v_inst_2451_, lean_object* v_x_2452_, lean_object* v_x_2453_){
_start:
{
uint8_t v_res_2454_; lean_object* v_r_2455_; 
v_res_2454_ = l_instDecidableEqSum_decEq___redArg(v_inst_2450_, v_inst_2451_, v_x_2452_, v_x_2453_);
v_r_2455_ = lean_box(v_res_2454_);
return v_r_2455_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum_decEq(lean_object* v_00_u03b1_2456_, lean_object* v_00_u03b2_2457_, lean_object* v_inst_2458_, lean_object* v_inst_2459_, lean_object* v_x_2460_, lean_object* v_x_2461_){
_start:
{
uint8_t v___x_2462_; 
v___x_2462_ = l_instDecidableEqSum_decEq___redArg(v_inst_2458_, v_inst_2459_, v_x_2460_, v_x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum_decEq___boxed(lean_object* v_00_u03b1_2463_, lean_object* v_00_u03b2_2464_, lean_object* v_inst_2465_, lean_object* v_inst_2466_, lean_object* v_x_2467_, lean_object* v_x_2468_){
_start:
{
uint8_t v_res_2469_; lean_object* v_r_2470_; 
v_res_2469_ = l_instDecidableEqSum_decEq(v_00_u03b1_2463_, v_00_u03b2_2464_, v_inst_2465_, v_inst_2466_, v_x_2467_, v_x_2468_);
v_r_2470_ = lean_box(v_res_2469_);
return v_r_2470_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum___redArg(lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_x_2473_, lean_object* v_x_2474_){
_start:
{
uint8_t v___x_2475_; 
v___x_2475_ = l_instDecidableEqSum_decEq___redArg(v_inst_2471_, v_inst_2472_, v_x_2473_, v_x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum___redArg___boxed(lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_x_2478_, lean_object* v_x_2479_){
_start:
{
uint8_t v_res_2480_; lean_object* v_r_2481_; 
v_res_2480_ = l_instDecidableEqSum___redArg(v_inst_2476_, v_inst_2477_, v_x_2478_, v_x_2479_);
v_r_2481_ = lean_box(v_res_2480_);
return v_r_2481_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum(lean_object* v_00_u03b1_2482_, lean_object* v_00_u03b2_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_x_2486_, lean_object* v_x_2487_){
_start:
{
uint8_t v___x_2488_; 
v___x_2488_ = l_instDecidableEqSum_decEq___redArg(v_inst_2484_, v_inst_2485_, v_x_2486_, v_x_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum___boxed(lean_object* v_00_u03b1_2489_, lean_object* v_00_u03b2_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_x_2493_, lean_object* v_x_2494_){
_start:
{
uint8_t v_res_2495_; lean_object* v_r_2496_; 
v_res_2495_ = l_instDecidableEqSum(v_00_u03b1_2489_, v_00_u03b2_2490_, v_inst_2491_, v_inst_2492_, v_x_2493_, v_x_2494_);
v_r_2496_ = lean_box(v_res_2495_);
return v_r_2496_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedProd___redArg(lean_object* v_inst_2497_, lean_object* v_inst_2498_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v_inst_2497_);
lean_ctor_set(v___x_2499_, 1, v_inst_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedProd(lean_object* v_00_u03b1_2500_, lean_object* v_00_u03b2_2501_, lean_object* v_inst_2502_, lean_object* v_inst_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2504_, 0, v_inst_2502_);
lean_ctor_set(v___x_2504_, 1, v_inst_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedMProd___redArg(lean_object* v_inst_2505_, lean_object* v_inst_2506_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2507_, 0, v_inst_2505_);
lean_ctor_set(v___x_2507_, 1, v_inst_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedMProd(lean_object* v_00_u03b1_2508_, lean_object* v_00_u03b2_2509_, lean_object* v_inst_2510_, lean_object* v_inst_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v_inst_2510_);
lean_ctor_set(v___x_2512_, 1, v_inst_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedPProd___redArg(lean_object* v_inst_2513_, lean_object* v_inst_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v_inst_2513_);
lean_ctor_set(v___x_2515_, 1, v_inst_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedPProd(lean_object* v_00_u03b1_2516_, lean_object* v_00_u03b2_2517_, lean_object* v_inst_2518_, lean_object* v_inst_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v_inst_2518_);
lean_ctor_set(v___x_2520_, 1, v_inst_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqProd___redArg(lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_x_2523_, lean_object* v_x_2524_){
_start:
{
lean_object* v_fst_2525_; lean_object* v_snd_2526_; lean_object* v_fst_2527_; lean_object* v_snd_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v_fst_2525_ = lean_ctor_get(v_x_2523_, 0);
lean_inc(v_fst_2525_);
v_snd_2526_ = lean_ctor_get(v_x_2523_, 1);
lean_inc(v_snd_2526_);
lean_dec_ref(v_x_2523_);
v_fst_2527_ = lean_ctor_get(v_x_2524_, 0);
lean_inc(v_fst_2527_);
v_snd_2528_ = lean_ctor_get(v_x_2524_, 1);
lean_inc(v_snd_2528_);
lean_dec_ref(v_x_2524_);
v___x_2529_ = lean_apply_2(v_inst_2521_, v_fst_2525_, v_fst_2527_);
v___x_2530_ = lean_unbox(v___x_2529_);
if (v___x_2530_ == 0)
{
uint8_t v___x_2531_; 
lean_dec(v_snd_2528_);
lean_dec(v_snd_2526_);
lean_dec_ref(v_inst_2522_);
v___x_2531_ = lean_unbox(v___x_2529_);
return v___x_2531_;
}
else
{
lean_object* v___x_2532_; uint8_t v___x_2533_; 
v___x_2532_ = lean_apply_2(v_inst_2522_, v_snd_2526_, v_snd_2528_);
v___x_2533_ = lean_unbox(v___x_2532_);
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqProd___redArg___boxed(lean_object* v_inst_2534_, lean_object* v_inst_2535_, lean_object* v_x_2536_, lean_object* v_x_2537_){
_start:
{
uint8_t v_res_2538_; lean_object* v_r_2539_; 
v_res_2538_ = l_instDecidableEqProd___redArg(v_inst_2534_, v_inst_2535_, v_x_2536_, v_x_2537_);
v_r_2539_ = lean_box(v_res_2538_);
return v_r_2539_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqProd(lean_object* v_00_u03b1_2540_, lean_object* v_00_u03b2_2541_, lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_x_2544_, lean_object* v_x_2545_){
_start:
{
uint8_t v___x_2546_; 
v___x_2546_ = l_instDecidableEqProd___redArg(v_inst_2542_, v_inst_2543_, v_x_2544_, v_x_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqProd___boxed(lean_object* v_00_u03b1_2547_, lean_object* v_00_u03b2_2548_, lean_object* v_inst_2549_, lean_object* v_inst_2550_, lean_object* v_x_2551_, lean_object* v_x_2552_){
_start:
{
uint8_t v_res_2553_; lean_object* v_r_2554_; 
v_res_2553_ = l_instDecidableEqProd(v_00_u03b1_2547_, v_00_u03b2_2548_, v_inst_2549_, v_inst_2550_, v_x_2551_, v_x_2552_);
v_r_2554_ = lean_box(v_res_2553_);
return v_r_2554_;
}
}
LEAN_EXPORT uint8_t l_instBEqProd___redArg___lam__0(lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_x_2557_, lean_object* v_x_2558_){
_start:
{
lean_object* v_fst_2559_; lean_object* v_snd_2560_; lean_object* v_fst_2561_; lean_object* v_snd_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v_fst_2559_ = lean_ctor_get(v_x_2557_, 0);
lean_inc(v_fst_2559_);
v_snd_2560_ = lean_ctor_get(v_x_2557_, 1);
lean_inc(v_snd_2560_);
lean_dec_ref(v_x_2557_);
v_fst_2561_ = lean_ctor_get(v_x_2558_, 0);
lean_inc(v_fst_2561_);
v_snd_2562_ = lean_ctor_get(v_x_2558_, 1);
lean_inc(v_snd_2562_);
lean_dec_ref(v_x_2558_);
v___x_2563_ = lean_apply_2(v_inst_2555_, v_fst_2559_, v_fst_2561_);
v___x_2564_ = lean_unbox(v___x_2563_);
if (v___x_2564_ == 0)
{
uint8_t v___x_2565_; 
lean_dec(v_snd_2562_);
lean_dec(v_snd_2560_);
lean_dec_ref(v_inst_2556_);
v___x_2565_ = lean_unbox(v___x_2563_);
return v___x_2565_;
}
else
{
lean_object* v___x_2566_; uint8_t v___x_2567_; 
v___x_2566_ = lean_apply_2(v_inst_2556_, v_snd_2560_, v_snd_2562_);
v___x_2567_ = lean_unbox(v___x_2566_);
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object* v_inst_2568_, lean_object* v_inst_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_){
_start:
{
uint8_t v_res_2572_; lean_object* v_r_2573_; 
v_res_2572_ = l_instBEqProd___redArg___lam__0(v_inst_2568_, v_inst_2569_, v_x_2570_, v_x_2571_);
v_r_2573_ = lean_box(v_res_2572_);
return v_r_2573_;
}
}
LEAN_EXPORT lean_object* l_instBEqProd___redArg(lean_object* v_inst_2574_, lean_object* v_inst_2575_){
_start:
{
lean_object* v___f_2576_; 
v___f_2576_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2576_, 0, v_inst_2574_);
lean_closure_set(v___f_2576_, 1, v_inst_2575_);
return v___f_2576_;
}
}
LEAN_EXPORT lean_object* l_instBEqProd(lean_object* v_00_u03b1_2577_, lean_object* v_00_u03b2_2578_, lean_object* v_inst_2579_, lean_object* v_inst_2580_){
_start:
{
lean_object* v___f_2581_; 
v___f_2581_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2581_, 0, v_inst_2579_);
lean_closure_set(v___f_2581_, 1, v_inst_2580_);
return v___f_2581_;
}
}
LEAN_EXPORT uint8_t l_Prod_lexLtDec___redArg(lean_object* v_inst_2582_, lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_){
_start:
{
lean_object* v_fst_2587_; lean_object* v_snd_2588_; lean_object* v_fst_2589_; lean_object* v_snd_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v_fst_2587_ = lean_ctor_get(v_x_2585_, 0);
lean_inc(v_fst_2587_);
v_snd_2588_ = lean_ctor_get(v_x_2585_, 1);
lean_inc(v_snd_2588_);
lean_dec_ref(v_x_2585_);
v_fst_2589_ = lean_ctor_get(v_x_2586_, 0);
lean_inc(v_fst_2589_);
v_snd_2590_ = lean_ctor_get(v_x_2586_, 1);
lean_inc(v_snd_2590_);
lean_dec_ref(v_x_2586_);
lean_inc(v_fst_2589_);
lean_inc(v_fst_2587_);
v___x_2591_ = lean_apply_2(v_inst_2583_, v_fst_2587_, v_fst_2589_);
v___x_2592_ = lean_unbox(v___x_2591_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2593_ = lean_apply_2(v_inst_2582_, v_fst_2587_, v_fst_2589_);
v___x_2594_ = lean_unbox(v___x_2593_);
if (v___x_2594_ == 0)
{
uint8_t v___x_2595_; 
lean_dec(v_snd_2590_);
lean_dec(v_snd_2588_);
lean_dec_ref(v_inst_2584_);
v___x_2595_ = lean_unbox(v___x_2593_);
return v___x_2595_;
}
else
{
lean_object* v___x_2596_; uint8_t v___x_2597_; 
v___x_2596_ = lean_apply_2(v_inst_2584_, v_snd_2588_, v_snd_2590_);
v___x_2597_ = lean_unbox(v___x_2596_);
return v___x_2597_;
}
}
else
{
uint8_t v___x_2598_; 
lean_dec(v_snd_2590_);
lean_dec(v_fst_2589_);
lean_dec(v_snd_2588_);
lean_dec(v_fst_2587_);
lean_dec_ref(v_inst_2584_);
lean_dec_ref(v_inst_2582_);
v___x_2598_ = lean_unbox(v___x_2591_);
return v___x_2598_;
}
}
}
LEAN_EXPORT lean_object* l_Prod_lexLtDec___redArg___boxed(lean_object* v_inst_2599_, lean_object* v_inst_2600_, lean_object* v_inst_2601_, lean_object* v_x_2602_, lean_object* v_x_2603_){
_start:
{
uint8_t v_res_2604_; lean_object* v_r_2605_; 
v_res_2604_ = l_Prod_lexLtDec___redArg(v_inst_2599_, v_inst_2600_, v_inst_2601_, v_x_2602_, v_x_2603_);
v_r_2605_ = lean_box(v_res_2604_);
return v_r_2605_;
}
}
LEAN_EXPORT uint8_t l_Prod_lexLtDec(lean_object* v_00_u03b1_2606_, lean_object* v_00_u03b2_2607_, lean_object* v_inst_2608_, lean_object* v_inst_2609_, lean_object* v_inst_2610_, lean_object* v_inst_2611_, lean_object* v_inst_2612_, lean_object* v_x_2613_, lean_object* v_x_2614_){
_start:
{
uint8_t v___x_2615_; 
v___x_2615_ = l_Prod_lexLtDec___redArg(v_inst_2610_, v_inst_2611_, v_inst_2612_, v_x_2613_, v_x_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Prod_lexLtDec___boxed(lean_object* v_00_u03b1_2616_, lean_object* v_00_u03b2_2617_, lean_object* v_inst_2618_, lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_inst_2622_, lean_object* v_x_2623_, lean_object* v_x_2624_){
_start:
{
uint8_t v_res_2625_; lean_object* v_r_2626_; 
v_res_2625_ = l_Prod_lexLtDec(v_00_u03b1_2616_, v_00_u03b2_2617_, v_inst_2618_, v_inst_2619_, v_inst_2620_, v_inst_2621_, v_inst_2622_, v_x_2623_, v_x_2624_);
v_r_2626_ = lean_box(v_res_2625_);
return v_r_2626_;
}
}
LEAN_EXPORT lean_object* l_Prod_map___redArg(lean_object* v_f_2627_, lean_object* v_g_2628_, lean_object* v_x_2629_){
_start:
{
lean_object* v_fst_2630_; lean_object* v_snd_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2640_; 
v_fst_2630_ = lean_ctor_get(v_x_2629_, 0);
v_snd_2631_ = lean_ctor_get(v_x_2629_, 1);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_x_2629_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2633_ = v_x_2629_;
v_isShared_2634_ = v_isSharedCheck_2640_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_snd_2631_);
lean_inc(v_fst_2630_);
lean_dec(v_x_2629_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2640_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
v___x_2635_ = lean_apply_1(v_f_2627_, v_fst_2630_);
v___x_2636_ = lean_apply_1(v_g_2628_, v_snd_2631_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 1, v___x_2636_);
lean_ctor_set(v___x_2633_, 0, v___x_2635_);
v___x_2638_ = v___x_2633_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2639_, 1, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_map(lean_object* v_00_u03b1_u2081_2641_, lean_object* v_00_u03b1_u2082_2642_, lean_object* v_00_u03b2_u2081_2643_, lean_object* v_00_u03b2_u2082_2644_, lean_object* v_f_2645_, lean_object* v_g_2646_, lean_object* v_x_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Prod_map___redArg(v_f_2645_, v_g_2646_, v_x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSigma___redArg(lean_object* v_h_u2081_2649_, lean_object* v_h_u2082_2650_, lean_object* v_x_2651_, lean_object* v_x_2652_){
_start:
{
lean_object* v_fst_2653_; lean_object* v_snd_2654_; lean_object* v_fst_2655_; lean_object* v_snd_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v_fst_2653_ = lean_ctor_get(v_x_2651_, 0);
lean_inc(v_fst_2653_);
v_snd_2654_ = lean_ctor_get(v_x_2651_, 1);
lean_inc(v_snd_2654_);
lean_dec_ref(v_x_2651_);
v_fst_2655_ = lean_ctor_get(v_x_2652_, 0);
lean_inc(v_fst_2655_);
v_snd_2656_ = lean_ctor_get(v_x_2652_, 1);
lean_inc(v_snd_2656_);
lean_dec_ref(v_x_2652_);
lean_inc(v_fst_2653_);
v___x_2657_ = lean_apply_2(v_h_u2081_2649_, v_fst_2653_, v_fst_2655_);
v___x_2658_ = lean_unbox(v___x_2657_);
if (v___x_2658_ == 0)
{
uint8_t v___x_2659_; 
lean_dec(v_snd_2656_);
lean_dec(v_snd_2654_);
lean_dec(v_fst_2653_);
lean_dec_ref(v_h_u2082_2650_);
v___x_2659_ = lean_unbox(v___x_2657_);
return v___x_2659_;
}
else
{
lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2660_ = lean_apply_3(v_h_u2082_2650_, v_fst_2653_, v_snd_2654_, v_snd_2656_);
v___x_2661_ = lean_unbox(v___x_2660_);
return v___x_2661_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSigma___redArg___boxed(lean_object* v_h_u2081_2662_, lean_object* v_h_u2082_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_){
_start:
{
uint8_t v_res_2666_; lean_object* v_r_2667_; 
v_res_2666_ = l_instDecidableEqSigma___redArg(v_h_u2081_2662_, v_h_u2082_2663_, v_x_2664_, v_x_2665_);
v_r_2667_ = lean_box(v_res_2666_);
return v_r_2667_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSigma(lean_object* v_00_u03b1_2668_, lean_object* v_00_u03b2_2669_, lean_object* v_h_u2081_2670_, lean_object* v_h_u2082_2671_, lean_object* v_x_2672_, lean_object* v_x_2673_){
_start:
{
uint8_t v___x_2674_; 
v___x_2674_ = l_instDecidableEqSigma___redArg(v_h_u2081_2670_, v_h_u2082_2671_, v_x_2672_, v_x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSigma___boxed(lean_object* v_00_u03b1_2675_, lean_object* v_00_u03b2_2676_, lean_object* v_h_u2081_2677_, lean_object* v_h_u2082_2678_, lean_object* v_x_2679_, lean_object* v_x_2680_){
_start:
{
uint8_t v_res_2681_; lean_object* v_r_2682_; 
v_res_2681_ = l_instDecidableEqSigma(v_00_u03b1_2675_, v_00_u03b2_2676_, v_h_u2081_2677_, v_h_u2082_2678_, v_x_2679_, v_x_2680_);
v_r_2682_ = lean_box(v_res_2681_);
return v_r_2682_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPSigma___redArg(lean_object* v_h_u2081_2683_, lean_object* v_h_u2082_2684_, lean_object* v_x_2685_, lean_object* v_x_2686_){
_start:
{
lean_object* v_fst_2687_; lean_object* v_snd_2688_; lean_object* v_fst_2689_; lean_object* v_snd_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
v_fst_2687_ = lean_ctor_get(v_x_2685_, 0);
lean_inc(v_fst_2687_);
v_snd_2688_ = lean_ctor_get(v_x_2685_, 1);
lean_inc(v_snd_2688_);
lean_dec_ref(v_x_2685_);
v_fst_2689_ = lean_ctor_get(v_x_2686_, 0);
lean_inc(v_fst_2689_);
v_snd_2690_ = lean_ctor_get(v_x_2686_, 1);
lean_inc(v_snd_2690_);
lean_dec_ref(v_x_2686_);
lean_inc(v_fst_2687_);
v___x_2691_ = lean_apply_2(v_h_u2081_2683_, v_fst_2687_, v_fst_2689_);
v___x_2692_ = lean_unbox(v___x_2691_);
if (v___x_2692_ == 0)
{
uint8_t v___x_2693_; 
lean_dec(v_snd_2690_);
lean_dec(v_snd_2688_);
lean_dec(v_fst_2687_);
lean_dec_ref(v_h_u2082_2684_);
v___x_2693_ = lean_unbox(v___x_2691_);
return v___x_2693_;
}
else
{
lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2694_ = lean_apply_3(v_h_u2082_2684_, v_fst_2687_, v_snd_2688_, v_snd_2690_);
v___x_2695_ = lean_unbox(v___x_2694_);
return v___x_2695_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPSigma___redArg___boxed(lean_object* v_h_u2081_2696_, lean_object* v_h_u2082_2697_, lean_object* v_x_2698_, lean_object* v_x_2699_){
_start:
{
uint8_t v_res_2700_; lean_object* v_r_2701_; 
v_res_2700_ = l_instDecidableEqPSigma___redArg(v_h_u2081_2696_, v_h_u2082_2697_, v_x_2698_, v_x_2699_);
v_r_2701_ = lean_box(v_res_2700_);
return v_r_2701_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPSigma(lean_object* v_00_u03b1_2702_, lean_object* v_00_u03b2_2703_, lean_object* v_h_u2081_2704_, lean_object* v_h_u2082_2705_, lean_object* v_x_2706_, lean_object* v_x_2707_){
_start:
{
uint8_t v___x_2708_; 
v___x_2708_ = l_instDecidableEqPSigma___redArg(v_h_u2081_2704_, v_h_u2082_2705_, v_x_2706_, v_x_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPSigma___boxed(lean_object* v_00_u03b1_2709_, lean_object* v_00_u03b2_2710_, lean_object* v_h_u2081_2711_, lean_object* v_h_u2082_2712_, lean_object* v_x_2713_, lean_object* v_x_2714_){
_start:
{
uint8_t v_res_2715_; lean_object* v_r_2716_; 
v_res_2715_ = l_instDecidableEqPSigma(v_00_u03b1_2709_, v_00_u03b2_2710_, v_h_u2081_2711_, v_h_u2082_2712_, v_x_2713_, v_x_2714_);
v_r_2716_ = lean_box(v_res_2715_);
return v_r_2716_;
}
}
static lean_object* _init_l_instInhabitedPUnit(void){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = lean_box(0);
return v___x_2717_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPUnit(lean_object* v_a_2718_, lean_object* v_b_2719_){
_start:
{
uint8_t v___x_2720_; 
v___x_2720_ = 1;
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPUnit___boxed(lean_object* v_a_2721_, lean_object* v_b_2722_){
_start:
{
uint8_t v_res_2723_; lean_object* v_r_2724_; 
v_res_2723_ = l_instDecidableEqPUnit(v_a_2721_, v_b_2722_);
v_r_2724_ = lean_box(v_res_2723_);
return v_r_2724_;
}
}
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid(lean_object* v_00_u03b1_2725_, lean_object* v_inst_2726_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_box(0);
return v___x_2727_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfIff___redArg(uint8_t v_d_2728_){
_start:
{
return v_d_2728_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___redArg___boxed(lean_object* v_d_2729_){
_start:
{
uint8_t v_d_boxed_2730_; uint8_t v_res_2731_; lean_object* v_r_2732_; 
v_d_boxed_2730_ = lean_unbox(v_d_2729_);
v_res_2731_ = l_instDecidableEqOfIff___redArg(v_d_boxed_2730_);
v_r_2732_ = lean_box(v_res_2731_);
return v_r_2732_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfIff(lean_object* v_p_2733_, lean_object* v_q_2734_, uint8_t v_d_2735_){
_start:
{
return v_d_2735_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___boxed(lean_object* v_p_2736_, lean_object* v_q_2737_, lean_object* v_d_2738_){
_start:
{
uint8_t v_d_boxed_2739_; uint8_t v_res_2740_; lean_object* v_r_2741_; 
v_d_boxed_2739_ = lean_unbox(v_d_2738_);
v_res_2740_ = l_instDecidableEqOfIff(v_p_2736_, v_q_2737_, v_d_boxed_2739_);
v_r_2741_ = lean_box(v_res_2740_);
return v_r_2741_;
}
}
LEAN_EXPORT lean_object* l_Not_elim(lean_object* v_a_2742_, lean_object* v_00_u03b1_2743_, lean_object* v_H1_2744_, lean_object* v_H2_2745_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_And_elim___redArg(lean_object* v_f_2746_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = lean_apply_2(v_f_2746_, lean_box(0), lean_box(0));
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_And_elim(lean_object* v_a_2748_, lean_object* v_b_2749_, lean_object* v_00_u03b1_2750_, lean_object* v_f_2751_, lean_object* v_h_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = lean_apply_2(v_f_2751_, lean_box(0), lean_box(0));
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Iff_elim___redArg(lean_object* v_f_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_apply_2(v_f_2754_, lean_box(0), lean_box(0));
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Iff_elim(lean_object* v_a_2756_, lean_object* v_b_2757_, lean_object* v_00_u03b1_2758_, lean_object* v_f_2759_, lean_object* v_h_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_apply_2(v_f_2759_, lean_box(0), lean_box(0));
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Quot_liftOn___redArg(lean_object* v_q_2762_, lean_object* v_f_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_apply_1(v_f_2763_, v_q_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Quot_liftOn(lean_object* v_00_u03b1_2765_, lean_object* v_00_u03b2_2766_, lean_object* v_r_2767_, lean_object* v_q_2768_, lean_object* v_f_2769_, lean_object* v_c_2770_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_apply_1(v_f_2769_, v_q_2768_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Quot_rec___redArg(lean_object* v_f_2772_, lean_object* v_q_2773_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = lean_apply_1(v_f_2772_, v_q_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Quot_rec(lean_object* v_00_u03b1_2775_, lean_object* v_r_2776_, lean_object* v_motive_2777_, lean_object* v_f_2778_, lean_object* v_h_2779_, lean_object* v_q_2780_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_apply_1(v_f_2778_, v_q_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOn___redArg(lean_object* v_q_2782_, lean_object* v_f_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_apply_1(v_f_2783_, v_q_2782_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOn(lean_object* v_00_u03b1_2785_, lean_object* v_r_2786_, lean_object* v_motive_2787_, lean_object* v_q_2788_, lean_object* v_f_2789_, lean_object* v_h_2790_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_apply_1(v_f_2789_, v_q_2788_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOnSubsingleton___redArg(lean_object* v_q_2792_, lean_object* v_f_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_apply_1(v_f_2793_, v_q_2792_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOnSubsingleton(lean_object* v_00_u03b1_2795_, lean_object* v_r_2796_, lean_object* v_motive_2797_, lean_object* v_h_2798_, lean_object* v_q_2799_, lean_object* v_f_2800_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_apply_1(v_f_2800_, v_q_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Quot_hrecOn___redArg(lean_object* v_q_2802_, lean_object* v_f_2803_){
_start:
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_apply_1(v_f_2803_, v_q_2802_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Quot_hrecOn(lean_object* v_00_u03b1_2805_, lean_object* v_r_2806_, lean_object* v_motive_2807_, lean_object* v_q_2808_, lean_object* v_f_2809_, lean_object* v_c_2810_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_apply_1(v_f_2809_, v_q_2808_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___redArg(lean_object* v_a_2812_){
_start:
{
lean_inc(v_a_2812_);
return v_a_2812_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___redArg___boxed(lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Quotient_mk___redArg(v_a_2813_);
lean_dec(v_a_2813_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk(lean_object* v_00_u03b1_2815_, lean_object* v_s_2816_, lean_object* v_a_2817_){
_start:
{
lean_inc(v_a_2817_);
return v_a_2817_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___boxed(lean_object* v_00_u03b1_2818_, lean_object* v_s_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Quotient_mk(v_00_u03b1_2818_, v_s_2819_, v_a_2820_);
lean_dec(v_a_2820_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___redArg(lean_object* v_a_2822_){
_start:
{
lean_inc(v_a_2822_);
return v_a_2822_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___redArg___boxed(lean_object* v_a_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Quotient_mk_x27___redArg(v_a_2823_);
lean_dec(v_a_2823_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27(lean_object* v_00_u03b1_2825_, lean_object* v_s_2826_, lean_object* v_a_2827_){
_start:
{
lean_inc(v_a_2827_);
return v_a_2827_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___boxed(lean_object* v_00_u03b1_2828_, lean_object* v_s_2829_, lean_object* v_a_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Quotient_mk_x27(v_00_u03b1_2828_, v_s_2829_, v_a_2830_);
lean_dec(v_a_2830_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift___redArg(lean_object* v_f_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = lean_apply_1(v_f_2832_, v_a_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift(lean_object* v_00_u03b1_2835_, lean_object* v_00_u03b2_2836_, lean_object* v_s_2837_, lean_object* v_f_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = lean_apply_1(v_f_2838_, v_a_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn___redArg(lean_object* v_q_2842_, lean_object* v_f_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = lean_apply_1(v_f_2843_, v_q_2842_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn(lean_object* v_00_u03b1_2845_, lean_object* v_00_u03b2_2846_, lean_object* v_s_2847_, lean_object* v_q_2848_, lean_object* v_f_2849_, lean_object* v_c_2850_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_apply_1(v_f_2849_, v_q_2848_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Quotient_rec___redArg(lean_object* v_f_2852_, lean_object* v_q_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_apply_1(v_f_2852_, v_q_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Quotient_rec(lean_object* v_00_u03b1_2855_, lean_object* v_s_2856_, lean_object* v_motive_2857_, lean_object* v_f_2858_, lean_object* v_h_2859_, lean_object* v_q_2860_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = lean_apply_1(v_f_2858_, v_q_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOn___redArg(lean_object* v_q_2862_, lean_object* v_f_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = lean_apply_1(v_f_2863_, v_q_2862_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOn(lean_object* v_00_u03b1_2865_, lean_object* v_s_2866_, lean_object* v_motive_2867_, lean_object* v_q_2868_, lean_object* v_f_2869_, lean_object* v_h_2870_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = lean_apply_1(v_f_2869_, v_q_2868_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton___redArg(lean_object* v_q_2872_, lean_object* v_f_2873_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = lean_apply_1(v_f_2873_, v_q_2872_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton(lean_object* v_00_u03b1_2875_, lean_object* v_s_2876_, lean_object* v_motive_2877_, lean_object* v_h_2878_, lean_object* v_q_2879_, lean_object* v_f_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = lean_apply_1(v_f_2880_, v_q_2879_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Quotient_hrecOn___redArg(lean_object* v_q_2882_, lean_object* v_f_2883_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = lean_apply_1(v_f_2883_, v_q_2882_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Quotient_hrecOn(lean_object* v_00_u03b1_2885_, lean_object* v_s_2886_, lean_object* v_motive_2887_, lean_object* v_q_2888_, lean_object* v_f_2889_, lean_object* v_c_2890_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_apply_1(v_f_2889_, v_q_2888_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift_u2082___redArg(lean_object* v_f_2892_, lean_object* v_q_u2081_2893_, lean_object* v_q_u2082_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_apply_2(v_f_2892_, v_q_u2081_2893_, v_q_u2082_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift_u2082(lean_object* v_00_u03b1_2896_, lean_object* v_00_u03b2_2897_, lean_object* v_00_u03c6_2898_, lean_object* v_s_u2081_2899_, lean_object* v_s_u2082_2900_, lean_object* v_f_2901_, lean_object* v_c_2902_, lean_object* v_q_u2081_2903_, lean_object* v_q_u2082_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = lean_apply_2(v_f_2901_, v_q_u2081_2903_, v_q_u2082_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn_u2082___redArg(lean_object* v_q_u2081_2906_, lean_object* v_q_u2082_2907_, lean_object* v_f_2908_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = lean_apply_2(v_f_2908_, v_q_u2081_2906_, v_q_u2082_2907_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn_u2082(lean_object* v_00_u03b1_2910_, lean_object* v_00_u03b2_2911_, lean_object* v_00_u03c6_2912_, lean_object* v_s_u2081_2913_, lean_object* v_s_u2082_2914_, lean_object* v_q_u2081_2915_, lean_object* v_q_u2082_2916_, lean_object* v_f_2917_, lean_object* v_c_2918_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_apply_2(v_f_2917_, v_q_u2081_2915_, v_q_u2082_2916_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton_u2082___redArg(lean_object* v_q_u2081_2920_, lean_object* v_q_u2082_2921_, lean_object* v_g_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_apply_2(v_g_2922_, v_q_u2081_2920_, v_q_u2082_2921_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton_u2082(lean_object* v_00_u03b1_2924_, lean_object* v_00_u03b2_2925_, lean_object* v_s_u2081_2926_, lean_object* v_s_u2082_2927_, lean_object* v_motive_2928_, lean_object* v_s_2929_, lean_object* v_q_u2081_2930_, lean_object* v_q_u2082_2931_, lean_object* v_g_2932_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_apply_2(v_g_2932_, v_q_u2081_2930_, v_q_u2082_2931_);
return v___x_2933_;
}
}
LEAN_EXPORT uint8_t l_Quotient_decidableEq___redArg(lean_object* v_d_2934_, lean_object* v_q_u2081_2935_, lean_object* v_q_u2082_2936_){
_start:
{
lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2937_ = lean_apply_2(v_d_2934_, v_q_u2081_2935_, v_q_u2082_2936_);
v___x_2938_ = lean_unbox(v___x_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Quotient_decidableEq___redArg___boxed(lean_object* v_d_2939_, lean_object* v_q_u2081_2940_, lean_object* v_q_u2082_2941_){
_start:
{
uint8_t v_res_2942_; lean_object* v_r_2943_; 
v_res_2942_ = l_Quotient_decidableEq___redArg(v_d_2939_, v_q_u2081_2940_, v_q_u2082_2941_);
v_r_2943_ = lean_box(v_res_2942_);
return v_r_2943_;
}
}
LEAN_EXPORT uint8_t l_Quotient_decidableEq(lean_object* v_00_u03b1_2944_, lean_object* v_s_2945_, lean_object* v_d_2946_, lean_object* v_q_u2081_2947_, lean_object* v_q_u2082_2948_){
_start:
{
lean_object* v___x_2949_; uint8_t v___x_2950_; 
v___x_2949_ = lean_apply_2(v_d_2946_, v_q_u2081_2947_, v_q_u2082_2948_);
v___x_2950_ = lean_unbox(v___x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Quotient_decidableEq___boxed(lean_object* v_00_u03b1_2951_, lean_object* v_s_2952_, lean_object* v_d_2953_, lean_object* v_q_u2081_2954_, lean_object* v_q_u2082_2955_){
_start:
{
uint8_t v_res_2956_; lean_object* v_r_2957_; 
v_res_2956_ = l_Quotient_decidableEq(v_00_u03b1_2951_, v_s_2952_, v_d_2953_, v_q_u2081_2954_, v_q_u2082_2955_);
v_r_2957_ = lean_box(v_res_2956_);
return v_r_2957_;
}
}
LEAN_EXPORT lean_object* l_Quot_pliftOn___redArg(lean_object* v_q_2958_, lean_object* v_f_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_apply_2(v_f_2959_, v_q_2958_, lean_box(0));
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Quot_pliftOn(lean_object* v_00_u03b2_2961_, lean_object* v_00_u03b1_2962_, lean_object* v_r_2963_, lean_object* v_q_2964_, lean_object* v_f_2965_, lean_object* v_h_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_apply_2(v_f_2965_, v_q_2964_, lean_box(0));
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Quotient_pliftOn___redArg(lean_object* v_q_2968_, lean_object* v_f_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = lean_apply_2(v_f_2969_, v_q_2968_, lean_box(0));
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Quotient_pliftOn(lean_object* v_00_u03b2_2971_, lean_object* v_00_u03b1_2972_, lean_object* v_s_2973_, lean_object* v_q_2974_, lean_object* v_f_2975_, lean_object* v_h_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_apply_2(v_f_2975_, v_q_2974_, lean_box(0));
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Setoid_trivial(lean_object* v_00_u03b1_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_box(0);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___redArg(lean_object* v_x_2980_){
_start:
{
lean_inc(v_x_2980_);
return v_x_2980_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___redArg___boxed(lean_object* v_x_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Squash_mk___redArg(v_x_2981_);
lean_dec(v_x_2981_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk(lean_object* v_00_u03b1_2983_, lean_object* v_x_2984_){
_start:
{
lean_inc(v_x_2984_);
return v_x_2984_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___boxed(lean_object* v_00_u03b1_2985_, lean_object* v_x_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Squash_mk(v_00_u03b1_2985_, v_x_2986_);
lean_dec(v_x_2986_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Squash_lift___redArg(lean_object* v_s_2988_, lean_object* v_f_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_apply_1(v_f_2989_, v_s_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Squash_lift(lean_object* v_00_u03b1_2991_, lean_object* v_00_u03b2_2992_, lean_object* v_inst_2993_, lean_object* v_s_2994_, lean_object* v_f_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = lean_apply_1(v_f_2995_, v_s_2994_);
return v___x_2996_;
}
}
LEAN_EXPORT uint8_t l_Lean_reduceBool(uint8_t v_b_2997_){
_start:
{
return v_b_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_reduceBool___boxed(lean_object* v_b_2998_){
_start:
{
uint8_t v_b_boxed_2999_; uint8_t v_res_3000_; lean_object* v_r_3001_; 
v_b_boxed_2999_ = lean_unbox(v_b_2998_);
v_res_3000_ = l_Lean_reduceBool(v_b_boxed_2999_);
v_r_3001_ = lean_box(v_res_3000_);
return v_r_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_reduceNat(lean_object* v_n_3002_){
_start:
{
lean_inc(v_n_3002_);
return v_n_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_reduceNat___boxed(lean_object* v_n_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Lean_reduceNat(v_n_3003_);
lean_dec(v_n_3003_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___redArg(lean_object* v_x_3005_){
_start:
{
lean_inc(v_x_3005_);
return v_x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___redArg___boxed(lean_object* v_x_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_opaqueId___redArg(v_x_3006_);
lean_dec(v_x_3006_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId(lean_object* v_00_u03b1_3008_, lean_object* v_x_3009_){
_start:
{
lean_inc(v_x_3009_);
return v_x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___boxed(lean_object* v_00_u03b1_3010_, lean_object* v_x_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_opaqueId(v_00_u03b1_3010_, v_x_3011_);
lean_dec(v_x_3011_);
return v_res_3012_;
}
}
lean_object* runtime_initialize_Init_SizeOf(uint8_t builtin);
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Core(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
