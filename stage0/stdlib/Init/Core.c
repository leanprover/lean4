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
LEAN_EXPORT uint8_t l_Prod_lexLtDec___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_lexLtDec___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Prod_lexLtDec___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_lexLtDec___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_instInhabitedThunk___redArg(lean_object* v_inst_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_thunk_pure(v_inst_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedThunk(lean_object* v_00_u03b1_154_, lean_object* v_inst_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_thunk_pure(v_inst_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn___redArg(lean_object* v_m_157_){
_start:
{
lean_inc(v_m_157_);
return v_m_157_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn___redArg___boxed(lean_object* v_m_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Eq_ndrecOn___redArg(v_m_158_);
lean_dec(v_m_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn(lean_object* v_00_u03b1_160_, lean_object* v_a_161_, lean_object* v_motive_162_, lean_object* v_b_163_, lean_object* v_h_164_, lean_object* v_m_165_){
_start:
{
lean_inc(v_m_165_);
return v_m_165_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn___boxed(lean_object* v_00_u03b1_166_, lean_object* v_a_167_, lean_object* v_motive_168_, lean_object* v_b_169_, lean_object* v_h_170_, lean_object* v_m_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Eq_ndrecOn(v_00_u03b1_166_, v_a_167_, v_motive_168_, v_b_169_, v_h_170_, v_m_171_);
lean_dec(v_m_171_);
lean_dec(v_b_169_);
lean_dec(v_a_167_);
return v_res_172_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5));
v___x_209_ = l_String_toRawSubstring_x27(v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1(lean_object* v_x_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_229_ = ((lean_object*)(l_term___x3c_x2d_x3e___00__closed__1));
lean_inc(v_x_226_);
v___x_230_ = l_Lean_Syntax_isOfKind(v_x_226_, v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec_ref(v_a_227_);
lean_dec(v_x_226_);
v___x_231_ = lean_box(1);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v_a_228_);
return v___x_232_;
}
else
{
lean_object* v_quotContext_233_; lean_object* v_currMacroScope_234_; lean_object* v_ref_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_quotContext_233_ = lean_ctor_get(v_a_227_, 1);
lean_inc(v_quotContext_233_);
v_currMacroScope_234_ = lean_ctor_get(v_a_227_, 2);
lean_inc(v_currMacroScope_234_);
v_ref_235_ = lean_ctor_get(v_a_227_, 5);
lean_inc(v_ref_235_);
lean_dec_ref(v_a_227_);
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = l_Lean_Syntax_getArg(v_x_226_, v___x_236_);
v___x_238_ = lean_unsigned_to_nat(2u);
v___x_239_ = l_Lean_Syntax_getArg(v_x_226_, v___x_238_);
lean_dec(v_x_226_);
v___x_240_ = 0;
v___x_241_ = l_Lean_SourceInfo_fromRef(v_ref_235_, v___x_240_);
lean_dec(v_ref_235_);
v___x_242_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_243_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6, &l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6_once, _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6);
v___x_244_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7));
v___x_245_ = l_Lean_addMacroScope(v_quotContext_233_, v___x_244_, v_currMacroScope_234_);
v___x_246_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11));
lean_inc(v___x_241_);
v___x_247_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_247_, 0, v___x_241_);
lean_ctor_set(v___x_247_, 1, v___x_243_);
lean_ctor_set(v___x_247_, 2, v___x_245_);
lean_ctor_set(v___x_247_, 3, v___x_246_);
v___x_248_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_241_);
v___x_249_ = l_Lean_Syntax_node2(v___x_241_, v___x_248_, v___x_237_, v___x_239_);
v___x_250_ = l_Lean_Syntax_node2(v___x_241_, v___x_242_, v___x_247_, v___x_249_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v_a_228_);
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__1(lean_object* v_x_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_255_);
v___x_259_ = l_Lean_Syntax_isOfKind(v_x_255_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_x_255_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_a_257_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = l_Lean_Syntax_getArg(v_x_255_, v___x_262_);
v___x_264_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_263_);
v___x_265_ = l_Lean_Syntax_isOfKind(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec(v___x_263_);
lean_dec(v_x_255_);
v___x_266_ = lean_box(0);
v___x_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v_a_257_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = l_Lean_Syntax_getArg(v_x_255_, v___x_268_);
lean_dec(v_x_255_);
v___x_270_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_269_);
v___x_271_ = l_Lean_Syntax_matchesNull(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v___x_269_);
lean_dec(v___x_263_);
v___x_272_ = lean_box(0);
v___x_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_a_257_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_ref_276_; uint8_t v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_274_ = l_Lean_Syntax_getArg(v___x_269_, v___x_262_);
v___x_275_ = l_Lean_Syntax_getArg(v___x_269_, v___x_268_);
lean_dec(v___x_269_);
v_ref_276_ = l_Lean_replaceRef(v___x_263_, v_a_256_);
lean_dec(v___x_263_);
v___x_277_ = 0;
v___x_278_ = l_Lean_SourceInfo_fromRef(v_ref_276_, v___x_277_);
lean_dec(v_ref_276_);
v___x_279_ = ((lean_object*)(l_term___x3c_x2d_x3e___00__closed__1));
v___x_280_ = ((lean_object*)(l_term___x3c_x2d_x3e___00__closed__4));
lean_inc(v___x_278_);
v___x_281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_278_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = l_Lean_Syntax_node3(v___x_278_, v___x_279_, v___x_274_, v___x_281_, v___x_275_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_a_257_);
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__1___boxed(lean_object* v_x_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___aux__Init__Core______unexpand__Iff__1(v_x_284_, v_a_285_, v_a_286_);
lean_dec(v_a_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2194____1(lean_object* v_x_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = ((lean_object*)(l_term___u2194___00__closed__1));
lean_inc(v_x_304_);
v___x_308_ = l_Lean_Syntax_isOfKind(v_x_304_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec_ref(v_a_305_);
lean_dec(v_x_304_);
v___x_309_ = lean_box(1);
v___x_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v_a_306_);
return v___x_310_;
}
else
{
lean_object* v_quotContext_311_; lean_object* v_currMacroScope_312_; lean_object* v_ref_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_quotContext_311_ = lean_ctor_get(v_a_305_, 1);
lean_inc(v_quotContext_311_);
v_currMacroScope_312_ = lean_ctor_get(v_a_305_, 2);
lean_inc(v_currMacroScope_312_);
v_ref_313_ = lean_ctor_get(v_a_305_, 5);
lean_inc(v_ref_313_);
lean_dec_ref(v_a_305_);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = l_Lean_Syntax_getArg(v_x_304_, v___x_314_);
v___x_316_ = lean_unsigned_to_nat(2u);
v___x_317_ = l_Lean_Syntax_getArg(v_x_304_, v___x_316_);
lean_dec(v_x_304_);
v___x_318_ = 0;
v___x_319_ = l_Lean_SourceInfo_fromRef(v_ref_313_, v___x_318_);
lean_dec(v_ref_313_);
v___x_320_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_321_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6, &l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6_once, _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6);
v___x_322_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7));
v___x_323_ = l_Lean_addMacroScope(v_quotContext_311_, v___x_322_, v_currMacroScope_312_);
v___x_324_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11));
lean_inc(v___x_319_);
v___x_325_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_325_, 0, v___x_319_);
lean_ctor_set(v___x_325_, 1, v___x_321_);
lean_ctor_set(v___x_325_, 2, v___x_323_);
lean_ctor_set(v___x_325_, 3, v___x_324_);
v___x_326_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_319_);
v___x_327_ = l_Lean_Syntax_node2(v___x_319_, v___x_326_, v___x_315_, v___x_317_);
v___x_328_ = l_Lean_Syntax_node2(v___x_319_, v___x_320_, v___x_325_, v___x_327_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_a_306_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__2(lean_object* v_x_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_330_);
v___x_334_ = l_Lean_Syntax_isOfKind(v_x_330_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_x_330_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_a_332_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = l_Lean_Syntax_getArg(v_x_330_, v___x_337_);
v___x_339_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_338_);
v___x_340_ = l_Lean_Syntax_isOfKind(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec(v___x_338_);
lean_dec(v_x_330_);
v___x_341_ = lean_box(0);
v___x_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v_a_332_);
return v___x_342_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = l_Lean_Syntax_getArg(v_x_330_, v___x_343_);
lean_dec(v_x_330_);
v___x_345_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_344_);
v___x_346_ = l_Lean_Syntax_matchesNull(v___x_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v___x_344_);
lean_dec(v___x_338_);
v___x_347_ = lean_box(0);
v___x_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v_a_332_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_ref_351_; uint8_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_349_ = l_Lean_Syntax_getArg(v___x_344_, v___x_337_);
v___x_350_ = l_Lean_Syntax_getArg(v___x_344_, v___x_343_);
lean_dec(v___x_344_);
v_ref_351_ = l_Lean_replaceRef(v___x_338_, v_a_331_);
lean_dec(v___x_338_);
v___x_352_ = 0;
v___x_353_ = l_Lean_SourceInfo_fromRef(v_ref_351_, v___x_352_);
lean_dec(v_ref_351_);
v___x_354_ = ((lean_object*)(l_term___u2194___00__closed__1));
v___x_355_ = ((lean_object*)(l_term___u2194___00__closed__2));
lean_inc(v___x_353_);
v___x_356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_353_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = l_Lean_Syntax_node3(v___x_353_, v___x_354_, v___x_349_, v___x_356_, v___x_350_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_a_332_);
return v___x_358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__2___boxed(lean_object* v_x_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___aux__Init__Core______unexpand__Iff__2(v_x_359_, v_a_360_, v_a_361_);
lean_dec(v_a_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___redArg(lean_object* v_x_363_){
_start:
{
if (lean_obj_tag(v_x_363_) == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_unsigned_to_nat(0u);
return v___x_364_;
}
else
{
lean_object* v___x_365_; 
v___x_365_ = lean_unsigned_to_nat(1u);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___redArg___boxed(lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Sum_ctorIdx___redArg(v_x_366_);
lean_dec_ref(v_x_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_x_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Sum_ctorIdx___redArg(v_x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___boxed(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_x_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Sum_ctorIdx(v_00_u03b1_372_, v_00_u03b2_373_, v_x_374_);
lean_dec_ref(v_x_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim___redArg(lean_object* v_t_376_, lean_object* v_k_377_){
_start:
{
lean_object* v_val_378_; lean_object* v___x_379_; 
v_val_378_ = lean_ctor_get(v_t_376_, 0);
lean_inc(v_val_378_);
lean_dec_ref(v_t_376_);
v___x_379_ = lean_apply_1(v_k_377_, v_val_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim(lean_object* v_00_u03b1_380_, lean_object* v_00_u03b2_381_, lean_object* v_motive_382_, lean_object* v_ctorIdx_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_k_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Sum_ctorElim___redArg(v_t_384_, v_k_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim___boxed(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_motive_390_, lean_object* v_ctorIdx_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_k_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Sum_ctorElim(v_00_u03b1_388_, v_00_u03b2_389_, v_motive_390_, v_ctorIdx_391_, v_t_392_, v_h_393_, v_k_394_);
lean_dec(v_ctorIdx_391_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Sum_inl_elim___redArg(lean_object* v_t_396_, lean_object* v_inl_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Sum_ctorElim___redArg(v_t_396_, v_inl_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Sum_inl_elim(lean_object* v_00_u03b1_399_, lean_object* v_00_u03b2_400_, lean_object* v_motive_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_inl_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Sum_ctorElim___redArg(v_t_402_, v_inl_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Sum_inr_elim___redArg(lean_object* v_t_406_, lean_object* v_inr_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Sum_ctorElim___redArg(v_t_406_, v_inr_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Sum_inr_elim(lean_object* v_00_u03b1_409_, lean_object* v_00_u03b2_410_, lean_object* v_motive_411_, lean_object* v_t_412_, lean_object* v_h_413_, lean_object* v_inr_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Sum_ctorElim___redArg(v_t_412_, v_inr_414_);
return v___x_415_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2295____1___closed__1(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__0));
v___x_437_ = l_String_toRawSubstring_x27(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295____1(lean_object* v_x_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = ((lean_object*)(l_term___u2295___00__closed__1));
lean_inc(v_x_451_);
v___x_455_ = l_Lean_Syntax_isOfKind(v_x_451_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec_ref(v_a_452_);
lean_dec(v_x_451_);
v___x_456_ = lean_box(1);
v___x_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v_a_453_);
return v___x_457_;
}
else
{
lean_object* v_quotContext_458_; lean_object* v_currMacroScope_459_; lean_object* v_ref_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_quotContext_458_ = lean_ctor_get(v_a_452_, 1);
lean_inc(v_quotContext_458_);
v_currMacroScope_459_ = lean_ctor_get(v_a_452_, 2);
lean_inc(v_currMacroScope_459_);
v_ref_460_ = lean_ctor_get(v_a_452_, 5);
lean_inc(v_ref_460_);
lean_dec_ref(v_a_452_);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = l_Lean_Syntax_getArg(v_x_451_, v___x_461_);
v___x_463_ = lean_unsigned_to_nat(2u);
v___x_464_ = l_Lean_Syntax_getArg(v_x_451_, v___x_463_);
lean_dec(v_x_451_);
v___x_465_ = 0;
v___x_466_ = l_Lean_SourceInfo_fromRef(v_ref_460_, v___x_465_);
lean_dec(v_ref_460_);
v___x_467_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_468_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2295____1___closed__1, &l___aux__Init__Core______macroRules__term___u2295____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2295____1___closed__1);
v___x_469_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__2));
v___x_470_ = l_Lean_addMacroScope(v_quotContext_458_, v___x_469_, v_currMacroScope_459_);
v___x_471_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__6));
lean_inc(v___x_466_);
v___x_472_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_472_, 0, v___x_466_);
lean_ctor_set(v___x_472_, 1, v___x_468_);
lean_ctor_set(v___x_472_, 2, v___x_470_);
lean_ctor_set(v___x_472_, 3, v___x_471_);
v___x_473_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_466_);
v___x_474_ = l_Lean_Syntax_node2(v___x_466_, v___x_473_, v___x_462_, v___x_464_);
v___x_475_ = l_Lean_Syntax_node2(v___x_466_, v___x_467_, v___x_472_, v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v_a_453_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Sum__1(lean_object* v_x_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_477_);
v___x_481_ = l_Lean_Syntax_isOfKind(v_x_477_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v_x_477_);
v___x_482_ = lean_box(0);
v___x_483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v_a_479_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = l_Lean_Syntax_getArg(v_x_477_, v___x_484_);
v___x_486_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_485_);
v___x_487_ = l_Lean_Syntax_isOfKind(v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v___x_485_);
lean_dec(v_x_477_);
v___x_488_ = lean_box(0);
v___x_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v_a_479_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = l_Lean_Syntax_getArg(v_x_477_, v___x_490_);
lean_dec(v_x_477_);
v___x_492_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_491_);
v___x_493_ = l_Lean_Syntax_matchesNull(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v___x_491_);
lean_dec(v___x_485_);
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_a_479_);
return v___x_495_;
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v_ref_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_496_ = l_Lean_Syntax_getArg(v___x_491_, v___x_484_);
v___x_497_ = l_Lean_Syntax_getArg(v___x_491_, v___x_490_);
lean_dec(v___x_491_);
v_ref_498_ = l_Lean_replaceRef(v___x_485_, v_a_478_);
lean_dec(v___x_485_);
v___x_499_ = 0;
v___x_500_ = l_Lean_SourceInfo_fromRef(v_ref_498_, v___x_499_);
lean_dec(v_ref_498_);
v___x_501_ = ((lean_object*)(l_term___u2295___00__closed__1));
v___x_502_ = ((lean_object*)(l_term___u2295___00__closed__2));
lean_inc(v___x_500_);
v___x_503_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_500_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = l_Lean_Syntax_node3(v___x_500_, v___x_501_, v___x_496_, v___x_503_, v___x_497_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_a_479_);
return v___x_505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Sum__1___boxed(lean_object* v_x_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___aux__Init__Core______unexpand__Sum__1(v_x_506_, v_a_507_, v_a_508_);
lean_dec(v_a_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___redArg(lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
lean_object* v___x_511_; 
v___x_511_ = lean_unsigned_to_nat(0u);
return v___x_511_;
}
else
{
lean_object* v___x_512_; 
v___x_512_ = lean_unsigned_to_nat(1u);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___redArg___boxed(lean_object* v_x_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_PSum_ctorIdx___redArg(v_x_513_);
lean_dec_ref(v_x_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx(lean_object* v_00_u03b1_515_, lean_object* v_00_u03b2_516_, lean_object* v_x_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_PSum_ctorIdx___redArg(v_x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___boxed(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_x_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_PSum_ctorIdx(v_00_u03b1_519_, v_00_u03b2_520_, v_x_521_);
lean_dec_ref(v_x_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim___redArg(lean_object* v_t_523_, lean_object* v_k_524_){
_start:
{
lean_object* v_val_525_; lean_object* v___x_526_; 
v_val_525_ = lean_ctor_get(v_t_523_, 0);
lean_inc(v_val_525_);
lean_dec_ref(v_t_523_);
v___x_526_ = lean_apply_1(v_k_524_, v_val_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim(lean_object* v_00_u03b1_527_, lean_object* v_00_u03b2_528_, lean_object* v_motive_529_, lean_object* v_ctorIdx_530_, lean_object* v_t_531_, lean_object* v_h_532_, lean_object* v_k_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_PSum_ctorElim___redArg(v_t_531_, v_k_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim___boxed(lean_object* v_00_u03b1_535_, lean_object* v_00_u03b2_536_, lean_object* v_motive_537_, lean_object* v_ctorIdx_538_, lean_object* v_t_539_, lean_object* v_h_540_, lean_object* v_k_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_PSum_ctorElim(v_00_u03b1_535_, v_00_u03b2_536_, v_motive_537_, v_ctorIdx_538_, v_t_539_, v_h_540_, v_k_541_);
lean_dec(v_ctorIdx_538_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_PSum_inl_elim___redArg(lean_object* v_t_543_, lean_object* v_inl_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_PSum_ctorElim___redArg(v_t_543_, v_inl_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_PSum_inl_elim(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_motive_548_, lean_object* v_t_549_, lean_object* v_h_550_, lean_object* v_inl_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_PSum_ctorElim___redArg(v_t_549_, v_inl_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_PSum_inr_elim___redArg(lean_object* v_t_553_, lean_object* v_inr_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_PSum_ctorElim___redArg(v_t_553_, v_inr_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_PSum_inr_elim(lean_object* v_00_u03b1_556_, lean_object* v_00_u03b2_557_, lean_object* v_motive_558_, lean_object* v_t_559_, lean_object* v_h_560_, lean_object* v_inr_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_PSum_ctorElim___redArg(v_t_559_, v_inr_561_);
return v___x_562_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0));
v___x_581_ = l_String_toRawSubstring_x27(v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1(lean_object* v_x_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = ((lean_object*)(l_term___u2295_x27___00__closed__1));
lean_inc(v_x_595_);
v___x_599_ = l_Lean_Syntax_isOfKind(v_x_595_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec_ref(v_a_596_);
lean_dec(v_x_595_);
v___x_600_ = lean_box(1);
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v_a_597_);
return v___x_601_;
}
else
{
lean_object* v_quotContext_602_; lean_object* v_currMacroScope_603_; lean_object* v_ref_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_quotContext_602_ = lean_ctor_get(v_a_596_, 1);
lean_inc(v_quotContext_602_);
v_currMacroScope_603_ = lean_ctor_get(v_a_596_, 2);
lean_inc(v_currMacroScope_603_);
v_ref_604_ = lean_ctor_get(v_a_596_, 5);
lean_inc(v_ref_604_);
lean_dec_ref(v_a_596_);
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = l_Lean_Syntax_getArg(v_x_595_, v___x_605_);
v___x_607_ = lean_unsigned_to_nat(2u);
v___x_608_ = l_Lean_Syntax_getArg(v_x_595_, v___x_607_);
lean_dec(v_x_595_);
v___x_609_ = 0;
v___x_610_ = l_Lean_SourceInfo_fromRef(v_ref_604_, v___x_609_);
lean_dec(v_ref_604_);
v___x_611_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_612_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1, &l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1);
v___x_613_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2));
v___x_614_ = l_Lean_addMacroScope(v_quotContext_602_, v___x_613_, v_currMacroScope_603_);
v___x_615_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__6));
lean_inc(v___x_610_);
v___x_616_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_616_, 0, v___x_610_);
lean_ctor_set(v___x_616_, 1, v___x_612_);
lean_ctor_set(v___x_616_, 2, v___x_614_);
lean_ctor_set(v___x_616_, 3, v___x_615_);
v___x_617_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_610_);
v___x_618_ = l_Lean_Syntax_node2(v___x_610_, v___x_617_, v___x_606_, v___x_608_);
v___x_619_ = l_Lean_Syntax_node2(v___x_610_, v___x_611_, v___x_616_, v___x_618_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v_a_597_);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__PSum__1(lean_object* v_x_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_621_);
v___x_625_ = l_Lean_Syntax_isOfKind(v_x_621_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec(v_x_621_);
v___x_626_ = lean_box(0);
v___x_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v_a_623_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = l_Lean_Syntax_getArg(v_x_621_, v___x_628_);
v___x_630_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_629_);
v___x_631_ = l_Lean_Syntax_isOfKind(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v___x_629_);
lean_dec(v_x_621_);
v___x_632_ = lean_box(0);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v_a_623_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = l_Lean_Syntax_getArg(v_x_621_, v___x_634_);
lean_dec(v_x_621_);
v___x_636_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_635_);
v___x_637_ = l_Lean_Syntax_matchesNull(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v___x_635_);
lean_dec(v___x_629_);
v___x_638_ = lean_box(0);
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v_a_623_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v_ref_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_640_ = l_Lean_Syntax_getArg(v___x_635_, v___x_628_);
v___x_641_ = l_Lean_Syntax_getArg(v___x_635_, v___x_634_);
lean_dec(v___x_635_);
v_ref_642_ = l_Lean_replaceRef(v___x_629_, v_a_622_);
lean_dec(v___x_629_);
v___x_643_ = 0;
v___x_644_ = l_Lean_SourceInfo_fromRef(v_ref_642_, v___x_643_);
lean_dec(v_ref_642_);
v___x_645_ = ((lean_object*)(l_term___u2295_x27___00__closed__1));
v___x_646_ = ((lean_object*)(l_term___u2295_x27___00__closed__2));
lean_inc(v___x_644_);
v___x_647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_644_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = l_Lean_Syntax_node3(v___x_644_, v___x_645_, v___x_640_, v___x_647_, v___x_641_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v_a_623_);
return v___x_649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__PSum__1___boxed(lean_object* v_x_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___aux__Init__Core______unexpand__PSum__1(v_x_650_, v_a_651_, v_a_652_);
lean_dec(v_a_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedLeft___redArg(lean_object* v_inst_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_inst_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedLeft(lean_object* v_00_u03b1_656_, lean_object* v_00_u03b2_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v_inst_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedRight___redArg(lean_object* v_inst_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_661_, 0, v_inst_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedRight(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_inst_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v_inst_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___redArg(lean_object* v_x_666_){
_start:
{
if (lean_obj_tag(v_x_666_) == 0)
{
lean_object* v___x_667_; 
v___x_667_ = lean_unsigned_to_nat(0u);
return v___x_667_;
}
else
{
lean_object* v___x_668_; 
v___x_668_ = lean_unsigned_to_nat(1u);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___redArg___boxed(lean_object* v_x_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_ForInStep_ctorIdx___redArg(v_x_669_);
lean_dec_ref(v_x_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx(lean_object* v_00_u03b1_671_, lean_object* v_x_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_ForInStep_ctorIdx___redArg(v_x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___boxed(lean_object* v_00_u03b1_674_, lean_object* v_x_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_ForInStep_ctorIdx(v_00_u03b1_674_, v_x_675_);
lean_dec_ref(v_x_675_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim___redArg(lean_object* v_t_677_, lean_object* v_k_678_){
_start:
{
lean_object* v_a_679_; lean_object* v___x_680_; 
v_a_679_ = lean_ctor_get(v_t_677_, 0);
lean_inc(v_a_679_);
lean_dec_ref(v_t_677_);
v___x_680_ = lean_apply_1(v_k_678_, v_a_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim(lean_object* v_00_u03b1_681_, lean_object* v_motive_682_, lean_object* v_ctorIdx_683_, lean_object* v_t_684_, lean_object* v_h_685_, lean_object* v_k_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_ForInStep_ctorElim___redArg(v_t_684_, v_k_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim___boxed(lean_object* v_00_u03b1_688_, lean_object* v_motive_689_, lean_object* v_ctorIdx_690_, lean_object* v_t_691_, lean_object* v_h_692_, lean_object* v_k_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_ForInStep_ctorElim(v_00_u03b1_688_, v_motive_689_, v_ctorIdx_690_, v_t_691_, v_h_692_, v_k_693_);
lean_dec(v_ctorIdx_690_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_done_elim___redArg(lean_object* v_t_695_, lean_object* v_done_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_ForInStep_ctorElim___redArg(v_t_695_, v_done_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_done_elim(lean_object* v_00_u03b1_698_, lean_object* v_motive_699_, lean_object* v_t_700_, lean_object* v_h_701_, lean_object* v_done_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_ForInStep_ctorElim___redArg(v_t_700_, v_done_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_yield_elim___redArg(lean_object* v_t_704_, lean_object* v_yield_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_ForInStep_ctorElim___redArg(v_t_704_, v_yield_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_yield_elim(lean_object* v_00_u03b1_707_, lean_object* v_motive_708_, lean_object* v_t_709_, lean_object* v_h_710_, lean_object* v_yield_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_ForInStep_ctorElim___redArg(v_t_709_, v_yield_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep_default___redArg(lean_object* v_inst_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v_inst_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep_default(lean_object* v_a_715_, lean_object* v_inst_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_inst_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep___redArg(lean_object* v_inst_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v_inst_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep(lean_object* v_a_720_, lean_object* v_inst_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v_inst_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___redArg(lean_object* v_x_723_){
_start:
{
switch(lean_obj_tag(v_x_723_))
{
case 0:
{
lean_object* v___x_724_; 
v___x_724_ = lean_unsigned_to_nat(0u);
return v___x_724_;
}
case 1:
{
lean_object* v___x_725_; 
v___x_725_ = lean_unsigned_to_nat(1u);
return v___x_725_;
}
case 2:
{
lean_object* v___x_726_; 
v___x_726_ = lean_unsigned_to_nat(2u);
return v___x_726_;
}
default: 
{
lean_object* v___x_727_; 
v___x_727_ = lean_unsigned_to_nat(3u);
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___redArg___boxed(lean_object* v_x_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_DoResultPRBC_ctorIdx___redArg(v_x_728_);
lean_dec_ref(v_x_728_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx(lean_object* v_00_u03b1_730_, lean_object* v_00_u03b2_731_, lean_object* v_00_u03c3_732_, lean_object* v_x_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_DoResultPRBC_ctorIdx___redArg(v_x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___boxed(lean_object* v_00_u03b1_735_, lean_object* v_00_u03b2_736_, lean_object* v_00_u03c3_737_, lean_object* v_x_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_DoResultPRBC_ctorIdx(v_00_u03b1_735_, v_00_u03b2_736_, v_00_u03c3_737_, v_x_738_);
lean_dec_ref(v_x_738_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim___redArg(lean_object* v_t_740_, lean_object* v_k_741_){
_start:
{
switch(lean_obj_tag(v_t_740_))
{
case 2:
{
lean_object* v_a_742_; lean_object* v___x_743_; 
v_a_742_ = lean_ctor_get(v_t_740_, 0);
lean_inc(v_a_742_);
lean_dec_ref(v_t_740_);
v___x_743_ = lean_apply_1(v_k_741_, v_a_742_);
return v___x_743_;
}
case 3:
{
lean_object* v_a_744_; lean_object* v___x_745_; 
v_a_744_ = lean_ctor_get(v_t_740_, 0);
lean_inc(v_a_744_);
lean_dec_ref(v_t_740_);
v___x_745_ = lean_apply_1(v_k_741_, v_a_744_);
return v___x_745_;
}
default: 
{
lean_object* v_a_746_; lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_746_ = lean_ctor_get(v_t_740_, 0);
lean_inc(v_a_746_);
v_a_747_ = lean_ctor_get(v_t_740_, 1);
lean_inc(v_a_747_);
lean_dec_ref(v_t_740_);
v___x_748_ = lean_apply_2(v_k_741_, v_a_746_, v_a_747_);
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim(lean_object* v_00_u03b1_749_, lean_object* v_00_u03b2_750_, lean_object* v_00_u03c3_751_, lean_object* v_motive_752_, lean_object* v_ctorIdx_753_, lean_object* v_t_754_, lean_object* v_h_755_, lean_object* v_k_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_DoResultPRBC_ctorElim___redArg(v_t_754_, v_k_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim___boxed(lean_object* v_00_u03b1_758_, lean_object* v_00_u03b2_759_, lean_object* v_00_u03c3_760_, lean_object* v_motive_761_, lean_object* v_ctorIdx_762_, lean_object* v_t_763_, lean_object* v_h_764_, lean_object* v_k_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_DoResultPRBC_ctorElim(v_00_u03b1_758_, v_00_u03b2_759_, v_00_u03c3_760_, v_motive_761_, v_ctorIdx_762_, v_t_763_, v_h_764_, v_k_765_);
lean_dec(v_ctorIdx_762_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_pure_elim___redArg(lean_object* v_t_767_, lean_object* v_pure_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_DoResultPRBC_ctorElim___redArg(v_t_767_, v_pure_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_pure_elim(lean_object* v_00_u03b1_770_, lean_object* v_00_u03b2_771_, lean_object* v_00_u03c3_772_, lean_object* v_motive_773_, lean_object* v_t_774_, lean_object* v_h_775_, lean_object* v_pure_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_DoResultPRBC_ctorElim___redArg(v_t_774_, v_pure_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_return_elim___redArg(lean_object* v_t_778_, lean_object* v_return_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_DoResultPRBC_ctorElim___redArg(v_t_778_, v_return_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_return_elim(lean_object* v_00_u03b1_781_, lean_object* v_00_u03b2_782_, lean_object* v_00_u03c3_783_, lean_object* v_motive_784_, lean_object* v_t_785_, lean_object* v_h_786_, lean_object* v_return_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_DoResultPRBC_ctorElim___redArg(v_t_785_, v_return_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_break_elim___redArg(lean_object* v_t_789_, lean_object* v_break_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_DoResultPRBC_ctorElim___redArg(v_t_789_, v_break_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_break_elim(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_00_u03c3_794_, lean_object* v_motive_795_, lean_object* v_t_796_, lean_object* v_h_797_, lean_object* v_break_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_DoResultPRBC_ctorElim___redArg(v_t_796_, v_break_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_continue_elim___redArg(lean_object* v_t_800_, lean_object* v_continue_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_DoResultPRBC_ctorElim___redArg(v_t_800_, v_continue_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_continue_elim(lean_object* v_00_u03b1_803_, lean_object* v_00_u03b2_804_, lean_object* v_00_u03c3_805_, lean_object* v_motive_806_, lean_object* v_t_807_, lean_object* v_h_808_, lean_object* v_continue_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_DoResultPRBC_ctorElim___redArg(v_t_807_, v_continue_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___redArg(lean_object* v_x_811_){
_start:
{
if (lean_obj_tag(v_x_811_) == 0)
{
lean_object* v___x_812_; 
v___x_812_ = lean_unsigned_to_nat(0u);
return v___x_812_;
}
else
{
lean_object* v___x_813_; 
v___x_813_ = lean_unsigned_to_nat(1u);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___redArg___boxed(lean_object* v_x_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_DoResultPR_ctorIdx___redArg(v_x_814_);
lean_dec_ref(v_x_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_00_u03c3_818_, lean_object* v_x_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_DoResultPR_ctorIdx___redArg(v_x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___boxed(lean_object* v_00_u03b1_821_, lean_object* v_00_u03b2_822_, lean_object* v_00_u03c3_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_DoResultPR_ctorIdx(v_00_u03b1_821_, v_00_u03b2_822_, v_00_u03c3_823_, v_x_824_);
lean_dec_ref(v_x_824_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___redArg(lean_object* v_t_826_, lean_object* v_k_827_){
_start:
{
lean_object* v_a_828_; lean_object* v_a_829_; lean_object* v___x_830_; 
v_a_828_ = lean_ctor_get(v_t_826_, 0);
lean_inc(v_a_828_);
v_a_829_ = lean_ctor_get(v_t_826_, 1);
lean_inc(v_a_829_);
lean_dec_ref(v_t_826_);
v___x_830_ = lean_apply_2(v_k_827_, v_a_828_, v_a_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim(lean_object* v_00_u03b1_831_, lean_object* v_00_u03b2_832_, lean_object* v_00_u03c3_833_, lean_object* v_motive_834_, lean_object* v_ctorIdx_835_, lean_object* v_t_836_, lean_object* v_h_837_, lean_object* v_k_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_DoResultPR_ctorElim___redArg(v_t_836_, v_k_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___boxed(lean_object* v_00_u03b1_840_, lean_object* v_00_u03b2_841_, lean_object* v_00_u03c3_842_, lean_object* v_motive_843_, lean_object* v_ctorIdx_844_, lean_object* v_t_845_, lean_object* v_h_846_, lean_object* v_k_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_DoResultPR_ctorElim(v_00_u03b1_840_, v_00_u03b2_841_, v_00_u03c3_842_, v_motive_843_, v_ctorIdx_844_, v_t_845_, v_h_846_, v_k_847_);
lean_dec(v_ctorIdx_844_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim___redArg(lean_object* v_t_849_, lean_object* v_pure_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_DoResultPR_ctorElim___redArg(v_t_849_, v_pure_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim(lean_object* v_00_u03b1_852_, lean_object* v_00_u03b2_853_, lean_object* v_00_u03c3_854_, lean_object* v_motive_855_, lean_object* v_t_856_, lean_object* v_h_857_, lean_object* v_pure_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_DoResultPR_ctorElim___redArg(v_t_856_, v_pure_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_return_elim___redArg(lean_object* v_t_860_, lean_object* v_return_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_DoResultPR_ctorElim___redArg(v_t_860_, v_return_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_return_elim(lean_object* v_00_u03b1_863_, lean_object* v_00_u03b2_864_, lean_object* v_00_u03c3_865_, lean_object* v_motive_866_, lean_object* v_t_867_, lean_object* v_h_868_, lean_object* v_return_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_DoResultPR_ctorElim___redArg(v_t_867_, v_return_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___redArg(lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
lean_object* v___x_872_; 
v___x_872_ = lean_unsigned_to_nat(0u);
return v___x_872_;
}
else
{
lean_object* v___x_873_; 
v___x_873_ = lean_unsigned_to_nat(1u);
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___redArg___boxed(lean_object* v_x_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_DoResultBC_ctorIdx___redArg(v_x_874_);
lean_dec_ref(v_x_874_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx(lean_object* v_00_u03c3_876_, lean_object* v_x_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_DoResultBC_ctorIdx___redArg(v_x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___boxed(lean_object* v_00_u03c3_879_, lean_object* v_x_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_DoResultBC_ctorIdx(v_00_u03c3_879_, v_x_880_);
lean_dec_ref(v_x_880_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___redArg(lean_object* v_t_882_, lean_object* v_k_883_){
_start:
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v_t_882_, 0);
lean_inc(v_a_884_);
lean_dec_ref(v_t_882_);
v___x_885_ = lean_apply_1(v_k_883_, v_a_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim(lean_object* v_00_u03c3_886_, lean_object* v_motive_887_, lean_object* v_ctorIdx_888_, lean_object* v_t_889_, lean_object* v_h_890_, lean_object* v_k_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_DoResultBC_ctorElim___redArg(v_t_889_, v_k_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___boxed(lean_object* v_00_u03c3_893_, lean_object* v_motive_894_, lean_object* v_ctorIdx_895_, lean_object* v_t_896_, lean_object* v_h_897_, lean_object* v_k_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_DoResultBC_ctorElim(v_00_u03c3_893_, v_motive_894_, v_ctorIdx_895_, v_t_896_, v_h_897_, v_k_898_);
lean_dec(v_ctorIdx_895_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_break_elim___redArg(lean_object* v_t_900_, lean_object* v_break_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_DoResultBC_ctorElim___redArg(v_t_900_, v_break_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_break_elim(lean_object* v_00_u03c3_903_, lean_object* v_motive_904_, lean_object* v_t_905_, lean_object* v_h_906_, lean_object* v_break_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_DoResultBC_ctorElim___redArg(v_t_905_, v_break_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim___redArg(lean_object* v_t_909_, lean_object* v_continue_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_DoResultBC_ctorElim___redArg(v_t_909_, v_continue_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim(lean_object* v_00_u03c3_912_, lean_object* v_motive_913_, lean_object* v_t_914_, lean_object* v_h_915_, lean_object* v_continue_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_DoResultBC_ctorElim___redArg(v_t_914_, v_continue_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___redArg(lean_object* v_x_918_){
_start:
{
switch(lean_obj_tag(v_x_918_))
{
case 0:
{
lean_object* v___x_919_; 
v___x_919_ = lean_unsigned_to_nat(0u);
return v___x_919_;
}
case 1:
{
lean_object* v___x_920_; 
v___x_920_ = lean_unsigned_to_nat(1u);
return v___x_920_;
}
default: 
{
lean_object* v___x_921_; 
v___x_921_ = lean_unsigned_to_nat(2u);
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___redArg___boxed(lean_object* v_x_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_DoResultSBC_ctorIdx___redArg(v_x_922_);
lean_dec_ref(v_x_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx(lean_object* v_00_u03b1_924_, lean_object* v_00_u03c3_925_, lean_object* v_x_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_DoResultSBC_ctorIdx___redArg(v_x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___boxed(lean_object* v_00_u03b1_928_, lean_object* v_00_u03c3_929_, lean_object* v_x_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_DoResultSBC_ctorIdx(v_00_u03b1_928_, v_00_u03c3_929_, v_x_930_);
lean_dec_ref(v_x_930_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim___redArg(lean_object* v_t_932_, lean_object* v_k_933_){
_start:
{
if (lean_obj_tag(v_t_932_) == 0)
{
lean_object* v_a_934_; lean_object* v_a_935_; lean_object* v___x_936_; 
v_a_934_ = lean_ctor_get(v_t_932_, 0);
lean_inc(v_a_934_);
v_a_935_ = lean_ctor_get(v_t_932_, 1);
lean_inc(v_a_935_);
lean_dec_ref(v_t_932_);
v___x_936_ = lean_apply_2(v_k_933_, v_a_934_, v_a_935_);
return v___x_936_;
}
else
{
lean_object* v_a_937_; lean_object* v___x_938_; 
v_a_937_ = lean_ctor_get(v_t_932_, 0);
lean_inc(v_a_937_);
lean_dec_ref(v_t_932_);
v___x_938_ = lean_apply_1(v_k_933_, v_a_937_);
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim(lean_object* v_00_u03b1_939_, lean_object* v_00_u03c3_940_, lean_object* v_motive_941_, lean_object* v_ctorIdx_942_, lean_object* v_t_943_, lean_object* v_h_944_, lean_object* v_k_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_DoResultSBC_ctorElim___redArg(v_t_943_, v_k_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim___boxed(lean_object* v_00_u03b1_947_, lean_object* v_00_u03c3_948_, lean_object* v_motive_949_, lean_object* v_ctorIdx_950_, lean_object* v_t_951_, lean_object* v_h_952_, lean_object* v_k_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_DoResultSBC_ctorElim(v_00_u03b1_947_, v_00_u03c3_948_, v_motive_949_, v_ctorIdx_950_, v_t_951_, v_h_952_, v_k_953_);
lean_dec(v_ctorIdx_950_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_pureReturn_elim___redArg(lean_object* v_t_955_, lean_object* v_pureReturn_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_DoResultSBC_ctorElim___redArg(v_t_955_, v_pureReturn_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_pureReturn_elim(lean_object* v_00_u03b1_958_, lean_object* v_00_u03c3_959_, lean_object* v_motive_960_, lean_object* v_t_961_, lean_object* v_h_962_, lean_object* v_pureReturn_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_DoResultSBC_ctorElim___redArg(v_t_961_, v_pureReturn_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_break_elim___redArg(lean_object* v_t_965_, lean_object* v_break_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_DoResultSBC_ctorElim___redArg(v_t_965_, v_break_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_break_elim(lean_object* v_00_u03b1_968_, lean_object* v_00_u03c3_969_, lean_object* v_motive_970_, lean_object* v_t_971_, lean_object* v_h_972_, lean_object* v_break_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_DoResultSBC_ctorElim___redArg(v_t_971_, v_break_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_continue_elim___redArg(lean_object* v_t_975_, lean_object* v_continue_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_DoResultSBC_ctorElim___redArg(v_t_975_, v_continue_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_continue_elim(lean_object* v_00_u03b1_978_, lean_object* v_00_u03c3_979_, lean_object* v_motive_980_, lean_object* v_t_981_, lean_object* v_h_982_, lean_object* v_continue_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_DoResultSBC_ctorElim___redArg(v_t_981_, v_continue_983_);
return v___x_984_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2248____1___closed__1(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2248____1___closed__0));
v___x_1006_ = l_String_toRawSubstring_x27(v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2248____1(lean_object* v_x_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_term___u2248___00__closed__1));
lean_inc(v_x_1018_);
v___x_1022_ = l_Lean_Syntax_isOfKind(v_x_1018_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec_ref(v_a_1019_);
lean_dec(v_x_1018_);
v___x_1023_ = lean_box(1);
v___x_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_a_1020_);
return v___x_1024_;
}
else
{
lean_object* v_quotContext_1025_; lean_object* v_currMacroScope_1026_; lean_object* v_ref_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_quotContext_1025_ = lean_ctor_get(v_a_1019_, 1);
lean_inc(v_quotContext_1025_);
v_currMacroScope_1026_ = lean_ctor_get(v_a_1019_, 2);
lean_inc(v_currMacroScope_1026_);
v_ref_1027_ = lean_ctor_get(v_a_1019_, 5);
lean_inc(v_ref_1027_);
lean_dec_ref(v_a_1019_);
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = l_Lean_Syntax_getArg(v_x_1018_, v___x_1028_);
v___x_1030_ = lean_unsigned_to_nat(2u);
v___x_1031_ = l_Lean_Syntax_getArg(v_x_1018_, v___x_1030_);
lean_dec(v_x_1018_);
v___x_1032_ = 0;
v___x_1033_ = l_Lean_SourceInfo_fromRef(v_ref_1027_, v___x_1032_);
lean_dec(v_ref_1027_);
v___x_1034_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1035_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2248____1___closed__1, &l___aux__Init__Core______macroRules__term___u2248____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2248____1___closed__1);
v___x_1036_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2248____1___closed__4));
v___x_1037_ = l_Lean_addMacroScope(v_quotContext_1025_, v___x_1036_, v_currMacroScope_1026_);
v___x_1038_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2248____1___closed__6));
lean_inc(v___x_1033_);
v___x_1039_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1033_);
lean_ctor_set(v___x_1039_, 1, v___x_1035_);
lean_ctor_set(v___x_1039_, 2, v___x_1037_);
lean_ctor_set(v___x_1039_, 3, v___x_1038_);
v___x_1040_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1033_);
v___x_1041_ = l_Lean_Syntax_node2(v___x_1033_, v___x_1040_, v___x_1029_, v___x_1031_);
v___x_1042_ = l_Lean_Syntax_node2(v___x_1033_, v___x_1034_, v___x_1039_, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v_a_1020_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasEquiv__Equiv__1(lean_object* v_x_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1044_);
v___x_1048_ = l_Lean_Syntax_isOfKind(v_x_1044_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
lean_dec(v_x_1044_);
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_a_1046_);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = l_Lean_Syntax_getArg(v_x_1044_, v___x_1051_);
v___x_1053_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1052_);
v___x_1054_ = l_Lean_Syntax_isOfKind(v___x_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_dec(v___x_1052_);
lean_dec(v_x_1044_);
v___x_1055_ = lean_box(0);
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v_a_1046_);
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = l_Lean_Syntax_getArg(v_x_1044_, v___x_1057_);
lean_dec(v_x_1044_);
v___x_1059_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1058_);
v___x_1060_ = l_Lean_Syntax_matchesNull(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_dec(v___x_1058_);
lean_dec(v___x_1052_);
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v_a_1046_);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_ref_1065_; uint8_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1063_ = l_Lean_Syntax_getArg(v___x_1058_, v___x_1051_);
v___x_1064_ = l_Lean_Syntax_getArg(v___x_1058_, v___x_1057_);
lean_dec(v___x_1058_);
v_ref_1065_ = l_Lean_replaceRef(v___x_1052_, v_a_1045_);
lean_dec(v___x_1052_);
v___x_1066_ = 0;
v___x_1067_ = l_Lean_SourceInfo_fromRef(v_ref_1065_, v___x_1066_);
lean_dec(v_ref_1065_);
v___x_1068_ = ((lean_object*)(l_term___u2248___00__closed__1));
v___x_1069_ = ((lean_object*)(l_term___u2248___00__closed__2));
lean_inc(v___x_1067_);
v___x_1070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1067_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Lean_Syntax_node3(v___x_1067_, v___x_1068_, v___x_1063_, v___x_1070_, v___x_1064_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v_a_1046_);
return v___x_1072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasEquiv__Equiv__1___boxed(lean_object* v_x_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l___aux__Init__Core______unexpand__HasEquiv__Equiv__1(v_x_1073_, v_a_1074_, v_a_1075_);
lean_dec(v_a_1074_);
return v_res_1076_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2286____1___closed__1(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2286____1___closed__0));
v___x_1095_ = l_String_toRawSubstring_x27(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2286____1(lean_object* v_x_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_term___u2286___00__closed__1));
lean_inc(v_x_1108_);
v___x_1112_ = l_Lean_Syntax_isOfKind(v_x_1108_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec_ref(v_a_1109_);
lean_dec(v_x_1108_);
v___x_1113_ = lean_box(1);
v___x_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_a_1110_);
return v___x_1114_;
}
else
{
lean_object* v_quotContext_1115_; lean_object* v_currMacroScope_1116_; lean_object* v_ref_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_quotContext_1115_ = lean_ctor_get(v_a_1109_, 1);
lean_inc(v_quotContext_1115_);
v_currMacroScope_1116_ = lean_ctor_get(v_a_1109_, 2);
lean_inc(v_currMacroScope_1116_);
v_ref_1117_ = lean_ctor_get(v_a_1109_, 5);
lean_inc(v_ref_1117_);
lean_dec_ref(v_a_1109_);
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = l_Lean_Syntax_getArg(v_x_1108_, v___x_1118_);
v___x_1120_ = lean_unsigned_to_nat(2u);
v___x_1121_ = l_Lean_Syntax_getArg(v_x_1108_, v___x_1120_);
lean_dec(v_x_1108_);
v___x_1122_ = 0;
v___x_1123_ = l_Lean_SourceInfo_fromRef(v_ref_1117_, v___x_1122_);
lean_dec(v_ref_1117_);
v___x_1124_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1125_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2286____1___closed__1, &l___aux__Init__Core______macroRules__term___u2286____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2286____1___closed__1);
v___x_1126_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2286____1___closed__2));
v___x_1127_ = l_Lean_addMacroScope(v_quotContext_1115_, v___x_1126_, v_currMacroScope_1116_);
v___x_1128_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2286____1___closed__6));
lean_inc(v___x_1123_);
v___x_1129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1123_);
lean_ctor_set(v___x_1129_, 1, v___x_1125_);
lean_ctor_set(v___x_1129_, 2, v___x_1127_);
lean_ctor_set(v___x_1129_, 3, v___x_1128_);
v___x_1130_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1123_);
v___x_1131_ = l_Lean_Syntax_node2(v___x_1123_, v___x_1130_, v___x_1119_, v___x_1121_);
v___x_1132_ = l_Lean_Syntax_node2(v___x_1123_, v___x_1124_, v___x_1129_, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v_a_1110_);
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSubset__Subset__1(lean_object* v_x_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1134_);
v___x_1138_ = l_Lean_Syntax_isOfKind(v_x_1134_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec(v_x_1134_);
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v_a_1136_);
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = l_Lean_Syntax_getArg(v_x_1134_, v___x_1141_);
v___x_1143_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1142_);
v___x_1144_ = l_Lean_Syntax_isOfKind(v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec(v___x_1142_);
lean_dec(v_x_1134_);
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v_a_1136_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1147_ = lean_unsigned_to_nat(1u);
v___x_1148_ = l_Lean_Syntax_getArg(v_x_1134_, v___x_1147_);
lean_dec(v_x_1134_);
v___x_1149_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1148_);
v___x_1150_ = l_Lean_Syntax_matchesNull(v___x_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec(v___x_1148_);
lean_dec(v___x_1142_);
v___x_1151_ = lean_box(0);
v___x_1152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
lean_ctor_set(v___x_1152_, 1, v_a_1136_);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v_ref_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1153_ = l_Lean_Syntax_getArg(v___x_1148_, v___x_1141_);
v___x_1154_ = l_Lean_Syntax_getArg(v___x_1148_, v___x_1147_);
lean_dec(v___x_1148_);
v_ref_1155_ = l_Lean_replaceRef(v___x_1142_, v_a_1135_);
lean_dec(v___x_1142_);
v___x_1156_ = 0;
v___x_1157_ = l_Lean_SourceInfo_fromRef(v_ref_1155_, v___x_1156_);
lean_dec(v_ref_1155_);
v___x_1158_ = ((lean_object*)(l_term___u2286___00__closed__1));
v___x_1159_ = ((lean_object*)(l_term___u2286___00__closed__2));
lean_inc(v___x_1157_);
v___x_1160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1157_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_Syntax_node3(v___x_1157_, v___x_1158_, v___x_1153_, v___x_1160_, v___x_1154_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v_a_1136_);
return v___x_1162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSubset__Subset__1___boxed(lean_object* v_x_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___aux__Init__Core______unexpand__HasSubset__Subset__1(v_x_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1164_);
return v_res_1166_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2282____1___closed__1(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2282____1___closed__0));
v___x_1185_ = l_String_toRawSubstring_x27(v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2282____1(lean_object* v_x_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_term___u2282___00__closed__1));
lean_inc(v_x_1198_);
v___x_1202_ = l_Lean_Syntax_isOfKind(v_x_1198_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec_ref(v_a_1199_);
lean_dec(v_x_1198_);
v___x_1203_ = lean_box(1);
v___x_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v_a_1200_);
return v___x_1204_;
}
else
{
lean_object* v_quotContext_1205_; lean_object* v_currMacroScope_1206_; lean_object* v_ref_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_quotContext_1205_ = lean_ctor_get(v_a_1199_, 1);
lean_inc(v_quotContext_1205_);
v_currMacroScope_1206_ = lean_ctor_get(v_a_1199_, 2);
lean_inc(v_currMacroScope_1206_);
v_ref_1207_ = lean_ctor_get(v_a_1199_, 5);
lean_inc(v_ref_1207_);
lean_dec_ref(v_a_1199_);
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = l_Lean_Syntax_getArg(v_x_1198_, v___x_1208_);
v___x_1210_ = lean_unsigned_to_nat(2u);
v___x_1211_ = l_Lean_Syntax_getArg(v_x_1198_, v___x_1210_);
lean_dec(v_x_1198_);
v___x_1212_ = 0;
v___x_1213_ = l_Lean_SourceInfo_fromRef(v_ref_1207_, v___x_1212_);
lean_dec(v_ref_1207_);
v___x_1214_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1215_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2282____1___closed__1, &l___aux__Init__Core______macroRules__term___u2282____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2282____1___closed__1);
v___x_1216_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2282____1___closed__2));
v___x_1217_ = l_Lean_addMacroScope(v_quotContext_1205_, v___x_1216_, v_currMacroScope_1206_);
v___x_1218_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2282____1___closed__6));
lean_inc(v___x_1213_);
v___x_1219_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1213_);
lean_ctor_set(v___x_1219_, 1, v___x_1215_);
lean_ctor_set(v___x_1219_, 2, v___x_1217_);
lean_ctor_set(v___x_1219_, 3, v___x_1218_);
v___x_1220_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1213_);
v___x_1221_ = l_Lean_Syntax_node2(v___x_1213_, v___x_1220_, v___x_1209_, v___x_1211_);
v___x_1222_ = l_Lean_Syntax_node2(v___x_1213_, v___x_1214_, v___x_1219_, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set(v___x_1223_, 1, v_a_1200_);
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSSubset__SSubset__1(lean_object* v_x_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1224_);
v___x_1228_ = l_Lean_Syntax_isOfKind(v_x_1224_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec(v_x_1224_);
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v_a_1226_);
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = l_Lean_Syntax_getArg(v_x_1224_, v___x_1231_);
v___x_1233_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1232_);
v___x_1234_ = l_Lean_Syntax_isOfKind(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec(v___x_1232_);
lean_dec(v_x_1224_);
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v_a_1226_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = l_Lean_Syntax_getArg(v_x_1224_, v___x_1237_);
lean_dec(v_x_1224_);
v___x_1239_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1238_);
v___x_1240_ = l_Lean_Syntax_matchesNull(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec(v___x_1238_);
lean_dec(v___x_1232_);
v___x_1241_ = lean_box(0);
v___x_1242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v_a_1226_);
return v___x_1242_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_ref_1245_; uint8_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1243_ = l_Lean_Syntax_getArg(v___x_1238_, v___x_1231_);
v___x_1244_ = l_Lean_Syntax_getArg(v___x_1238_, v___x_1237_);
lean_dec(v___x_1238_);
v_ref_1245_ = l_Lean_replaceRef(v___x_1232_, v_a_1225_);
lean_dec(v___x_1232_);
v___x_1246_ = 0;
v___x_1247_ = l_Lean_SourceInfo_fromRef(v_ref_1245_, v___x_1246_);
lean_dec(v_ref_1245_);
v___x_1248_ = ((lean_object*)(l_term___u2282___00__closed__1));
v___x_1249_ = ((lean_object*)(l_term___u2282___00__closed__2));
lean_inc(v___x_1247_);
v___x_1250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1247_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = l_Lean_Syntax_node3(v___x_1247_, v___x_1248_, v___x_1243_, v___x_1250_, v___x_1244_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v_a_1226_);
return v___x_1252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSSubset__SSubset__1___boxed(lean_object* v_x_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l___aux__Init__Core______unexpand__HasSSubset__SSubset__1(v_x_1253_, v_a_1254_, v_a_1255_);
lean_dec(v_a_1254_);
return v_res_1256_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2287____1___closed__1(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2287____1___closed__0));
v___x_1275_ = l_String_toRawSubstring_x27(v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2287____1(lean_object* v_x_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_term___u2287___00__closed__1));
lean_inc(v_x_1284_);
v___x_1288_ = l_Lean_Syntax_isOfKind(v_x_1284_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec_ref(v_a_1285_);
lean_dec(v_x_1284_);
v___x_1289_ = lean_box(1);
v___x_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v_a_1286_);
return v___x_1290_;
}
else
{
lean_object* v_quotContext_1291_; lean_object* v_currMacroScope_1292_; lean_object* v_ref_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_quotContext_1291_ = lean_ctor_get(v_a_1285_, 1);
lean_inc(v_quotContext_1291_);
v_currMacroScope_1292_ = lean_ctor_get(v_a_1285_, 2);
lean_inc(v_currMacroScope_1292_);
v_ref_1293_ = lean_ctor_get(v_a_1285_, 5);
lean_inc(v_ref_1293_);
lean_dec_ref(v_a_1285_);
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = l_Lean_Syntax_getArg(v_x_1284_, v___x_1294_);
v___x_1296_ = lean_unsigned_to_nat(2u);
v___x_1297_ = l_Lean_Syntax_getArg(v_x_1284_, v___x_1296_);
lean_dec(v_x_1284_);
v___x_1298_ = 0;
v___x_1299_ = l_Lean_SourceInfo_fromRef(v_ref_1293_, v___x_1298_);
lean_dec(v_ref_1293_);
v___x_1300_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1301_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2287____1___closed__1, &l___aux__Init__Core______macroRules__term___u2287____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2287____1___closed__1);
v___x_1302_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2287____1___closed__2));
v___x_1303_ = l_Lean_addMacroScope(v_quotContext_1291_, v___x_1302_, v_currMacroScope_1292_);
v___x_1304_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2287____1___closed__4));
lean_inc(v___x_1299_);
v___x_1305_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1299_);
lean_ctor_set(v___x_1305_, 1, v___x_1301_);
lean_ctor_set(v___x_1305_, 2, v___x_1303_);
lean_ctor_set(v___x_1305_, 3, v___x_1304_);
v___x_1306_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1299_);
v___x_1307_ = l_Lean_Syntax_node2(v___x_1299_, v___x_1306_, v___x_1295_, v___x_1297_);
v___x_1308_ = l_Lean_Syntax_node2(v___x_1299_, v___x_1300_, v___x_1305_, v___x_1307_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v_a_1286_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Superset__1(lean_object* v_x_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1310_);
v___x_1314_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec(v_x_1310_);
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v_a_1312_);
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1317_);
v___x_1319_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1318_);
v___x_1320_ = l_Lean_Syntax_isOfKind(v___x_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v___x_1318_);
lean_dec(v_x_1310_);
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v_a_1312_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1323_);
lean_dec(v_x_1310_);
v___x_1325_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1324_);
v___x_1326_ = l_Lean_Syntax_matchesNull(v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec(v___x_1324_);
lean_dec(v___x_1318_);
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v_a_1312_);
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_ref_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1329_ = l_Lean_Syntax_getArg(v___x_1324_, v___x_1317_);
v___x_1330_ = l_Lean_Syntax_getArg(v___x_1324_, v___x_1323_);
lean_dec(v___x_1324_);
v_ref_1331_ = l_Lean_replaceRef(v___x_1318_, v_a_1311_);
lean_dec(v___x_1318_);
v___x_1332_ = 0;
v___x_1333_ = l_Lean_SourceInfo_fromRef(v_ref_1331_, v___x_1332_);
lean_dec(v_ref_1331_);
v___x_1334_ = ((lean_object*)(l_term___u2287___00__closed__1));
v___x_1335_ = ((lean_object*)(l_term___u2287___00__closed__2));
lean_inc(v___x_1333_);
v___x_1336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1333_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = l_Lean_Syntax_node3(v___x_1333_, v___x_1334_, v___x_1329_, v___x_1336_, v___x_1330_);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v_a_1312_);
return v___x_1338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Superset__1___boxed(lean_object* v_x_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l___aux__Init__Core______unexpand__Superset__1(v_x_1339_, v_a_1340_, v_a_1341_);
lean_dec(v_a_1340_);
return v_res_1342_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2283____1___closed__1(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2283____1___closed__0));
v___x_1361_ = l_String_toRawSubstring_x27(v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2283____1(lean_object* v_x_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = ((lean_object*)(l_term___u2283___00__closed__1));
lean_inc(v_x_1370_);
v___x_1374_ = l_Lean_Syntax_isOfKind(v_x_1370_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec_ref(v_a_1371_);
lean_dec(v_x_1370_);
v___x_1375_ = lean_box(1);
v___x_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v_a_1372_);
return v___x_1376_;
}
else
{
lean_object* v_quotContext_1377_; lean_object* v_currMacroScope_1378_; lean_object* v_ref_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v_quotContext_1377_ = lean_ctor_get(v_a_1371_, 1);
lean_inc(v_quotContext_1377_);
v_currMacroScope_1378_ = lean_ctor_get(v_a_1371_, 2);
lean_inc(v_currMacroScope_1378_);
v_ref_1379_ = lean_ctor_get(v_a_1371_, 5);
lean_inc(v_ref_1379_);
lean_dec_ref(v_a_1371_);
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = l_Lean_Syntax_getArg(v_x_1370_, v___x_1380_);
v___x_1382_ = lean_unsigned_to_nat(2u);
v___x_1383_ = l_Lean_Syntax_getArg(v_x_1370_, v___x_1382_);
lean_dec(v_x_1370_);
v___x_1384_ = 0;
v___x_1385_ = l_Lean_SourceInfo_fromRef(v_ref_1379_, v___x_1384_);
lean_dec(v_ref_1379_);
v___x_1386_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1387_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2283____1___closed__1, &l___aux__Init__Core______macroRules__term___u2283____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2283____1___closed__1);
v___x_1388_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2283____1___closed__2));
v___x_1389_ = l_Lean_addMacroScope(v_quotContext_1377_, v___x_1388_, v_currMacroScope_1378_);
v___x_1390_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2283____1___closed__4));
lean_inc(v___x_1385_);
v___x_1391_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1385_);
lean_ctor_set(v___x_1391_, 1, v___x_1387_);
lean_ctor_set(v___x_1391_, 2, v___x_1389_);
lean_ctor_set(v___x_1391_, 3, v___x_1390_);
v___x_1392_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1385_);
v___x_1393_ = l_Lean_Syntax_node2(v___x_1385_, v___x_1392_, v___x_1381_, v___x_1383_);
v___x_1394_ = l_Lean_Syntax_node2(v___x_1385_, v___x_1386_, v___x_1391_, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v_a_1372_);
return v___x_1395_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SSuperset__1(lean_object* v_x_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1396_);
v___x_1400_ = l_Lean_Syntax_isOfKind(v_x_1396_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec(v_x_1396_);
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
lean_ctor_set(v___x_1402_, 1, v_a_1398_);
return v___x_1402_;
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = l_Lean_Syntax_getArg(v_x_1396_, v___x_1403_);
v___x_1405_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1404_);
v___x_1406_ = l_Lean_Syntax_isOfKind(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec(v___x_1404_);
lean_dec(v_x_1396_);
v___x_1407_ = lean_box(0);
v___x_1408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
lean_ctor_set(v___x_1408_, 1, v_a_1398_);
return v___x_1408_;
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1409_ = lean_unsigned_to_nat(1u);
v___x_1410_ = l_Lean_Syntax_getArg(v_x_1396_, v___x_1409_);
lean_dec(v_x_1396_);
v___x_1411_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1410_);
v___x_1412_ = l_Lean_Syntax_matchesNull(v___x_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_dec(v___x_1410_);
lean_dec(v___x_1404_);
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v_a_1398_);
return v___x_1414_;
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_ref_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1415_ = l_Lean_Syntax_getArg(v___x_1410_, v___x_1403_);
v___x_1416_ = l_Lean_Syntax_getArg(v___x_1410_, v___x_1409_);
lean_dec(v___x_1410_);
v_ref_1417_ = l_Lean_replaceRef(v___x_1404_, v_a_1397_);
lean_dec(v___x_1404_);
v___x_1418_ = 0;
v___x_1419_ = l_Lean_SourceInfo_fromRef(v_ref_1417_, v___x_1418_);
lean_dec(v_ref_1417_);
v___x_1420_ = ((lean_object*)(l_term___u2283___00__closed__1));
v___x_1421_ = ((lean_object*)(l_term___u2283___00__closed__2));
lean_inc(v___x_1419_);
v___x_1422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1419_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = l_Lean_Syntax_node3(v___x_1419_, v___x_1420_, v___x_1415_, v___x_1422_, v___x_1416_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v_a_1398_);
return v___x_1424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SSuperset__1___boxed(lean_object* v_x_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___aux__Init__Core______unexpand__SSuperset__1(v_x_1425_, v_a_1426_, v_a_1427_);
lean_dec(v_a_1426_);
return v_res_1428_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u222a____1___closed__1(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u222a____1___closed__0));
v___x_1449_ = l_String_toRawSubstring_x27(v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u222a____1(lean_object* v_x_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = ((lean_object*)(l_term___u222a___00__closed__1));
lean_inc(v_x_1461_);
v___x_1465_ = l_Lean_Syntax_isOfKind(v_x_1461_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec_ref(v_a_1462_);
lean_dec(v_x_1461_);
v___x_1466_ = lean_box(1);
v___x_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v_a_1463_);
return v___x_1467_;
}
else
{
lean_object* v_quotContext_1468_; lean_object* v_currMacroScope_1469_; lean_object* v_ref_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v_quotContext_1468_ = lean_ctor_get(v_a_1462_, 1);
lean_inc(v_quotContext_1468_);
v_currMacroScope_1469_ = lean_ctor_get(v_a_1462_, 2);
lean_inc(v_currMacroScope_1469_);
v_ref_1470_ = lean_ctor_get(v_a_1462_, 5);
lean_inc(v_ref_1470_);
lean_dec_ref(v_a_1462_);
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = l_Lean_Syntax_getArg(v_x_1461_, v___x_1471_);
v___x_1473_ = lean_unsigned_to_nat(2u);
v___x_1474_ = l_Lean_Syntax_getArg(v_x_1461_, v___x_1473_);
lean_dec(v_x_1461_);
v___x_1475_ = 0;
v___x_1476_ = l_Lean_SourceInfo_fromRef(v_ref_1470_, v___x_1475_);
lean_dec(v_ref_1470_);
v___x_1477_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1478_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u222a____1___closed__1, &l___aux__Init__Core______macroRules__term___u222a____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u222a____1___closed__1);
v___x_1479_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u222a____1___closed__4));
v___x_1480_ = l_Lean_addMacroScope(v_quotContext_1468_, v___x_1479_, v_currMacroScope_1469_);
v___x_1481_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u222a____1___closed__6));
lean_inc(v___x_1476_);
v___x_1482_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1476_);
lean_ctor_set(v___x_1482_, 1, v___x_1478_);
lean_ctor_set(v___x_1482_, 2, v___x_1480_);
lean_ctor_set(v___x_1482_, 3, v___x_1481_);
v___x_1483_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1476_);
v___x_1484_ = l_Lean_Syntax_node2(v___x_1476_, v___x_1483_, v___x_1472_, v___x_1474_);
v___x_1485_ = l_Lean_Syntax_node2(v___x_1476_, v___x_1477_, v___x_1482_, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
lean_ctor_set(v___x_1486_, 1, v_a_1463_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Union__union__1(lean_object* v_x_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1487_);
v___x_1491_ = l_Lean_Syntax_isOfKind(v_x_1487_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec(v_x_1487_);
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
lean_ctor_set(v___x_1493_, 1, v_a_1489_);
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = l_Lean_Syntax_getArg(v_x_1487_, v___x_1494_);
v___x_1496_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1495_);
v___x_1497_ = l_Lean_Syntax_isOfKind(v___x_1495_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec(v___x_1495_);
lean_dec(v_x_1487_);
v___x_1498_ = lean_box(0);
v___x_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v_a_1489_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1500_ = lean_unsigned_to_nat(1u);
v___x_1501_ = l_Lean_Syntax_getArg(v_x_1487_, v___x_1500_);
lean_dec(v_x_1487_);
v___x_1502_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1501_);
v___x_1503_ = l_Lean_Syntax_matchesNull(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec(v___x_1501_);
lean_dec(v___x_1495_);
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v_a_1489_);
return v___x_1505_;
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v_ref_1508_; uint8_t v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1506_ = l_Lean_Syntax_getArg(v___x_1501_, v___x_1494_);
v___x_1507_ = l_Lean_Syntax_getArg(v___x_1501_, v___x_1500_);
lean_dec(v___x_1501_);
v_ref_1508_ = l_Lean_replaceRef(v___x_1495_, v_a_1488_);
lean_dec(v___x_1495_);
v___x_1509_ = 0;
v___x_1510_ = l_Lean_SourceInfo_fromRef(v_ref_1508_, v___x_1509_);
lean_dec(v_ref_1508_);
v___x_1511_ = ((lean_object*)(l_term___u222a___00__closed__1));
v___x_1512_ = ((lean_object*)(l_term___u222a___00__closed__2));
lean_inc(v___x_1510_);
v___x_1513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1510_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = l_Lean_Syntax_node3(v___x_1510_, v___x_1511_, v___x_1506_, v___x_1513_, v___x_1507_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v_a_1489_);
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Union__union__1___boxed(lean_object* v_x_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___aux__Init__Core______unexpand__Union__union__1(v_x_1516_, v_a_1517_, v_a_1518_);
lean_dec(v_a_1517_);
return v_res_1519_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2229____1___closed__1(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2229____1___closed__0));
v___x_1540_ = l_String_toRawSubstring_x27(v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2229____1(lean_object* v_x_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = ((lean_object*)(l_term___u2229___00__closed__1));
lean_inc(v_x_1552_);
v___x_1556_ = l_Lean_Syntax_isOfKind(v_x_1552_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec_ref(v_a_1553_);
lean_dec(v_x_1552_);
v___x_1557_ = lean_box(1);
v___x_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v_a_1554_);
return v___x_1558_;
}
else
{
lean_object* v_quotContext_1559_; lean_object* v_currMacroScope_1560_; lean_object* v_ref_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_quotContext_1559_ = lean_ctor_get(v_a_1553_, 1);
lean_inc(v_quotContext_1559_);
v_currMacroScope_1560_ = lean_ctor_get(v_a_1553_, 2);
lean_inc(v_currMacroScope_1560_);
v_ref_1561_ = lean_ctor_get(v_a_1553_, 5);
lean_inc(v_ref_1561_);
lean_dec_ref(v_a_1553_);
v___x_1562_ = lean_unsigned_to_nat(0u);
v___x_1563_ = l_Lean_Syntax_getArg(v_x_1552_, v___x_1562_);
v___x_1564_ = lean_unsigned_to_nat(2u);
v___x_1565_ = l_Lean_Syntax_getArg(v_x_1552_, v___x_1564_);
lean_dec(v_x_1552_);
v___x_1566_ = 0;
v___x_1567_ = l_Lean_SourceInfo_fromRef(v_ref_1561_, v___x_1566_);
lean_dec(v_ref_1561_);
v___x_1568_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1569_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2229____1___closed__1, &l___aux__Init__Core______macroRules__term___u2229____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2229____1___closed__1);
v___x_1570_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2229____1___closed__4));
v___x_1571_ = l_Lean_addMacroScope(v_quotContext_1559_, v___x_1570_, v_currMacroScope_1560_);
v___x_1572_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2229____1___closed__6));
lean_inc(v___x_1567_);
v___x_1573_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1567_);
lean_ctor_set(v___x_1573_, 1, v___x_1569_);
lean_ctor_set(v___x_1573_, 2, v___x_1571_);
lean_ctor_set(v___x_1573_, 3, v___x_1572_);
v___x_1574_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1567_);
v___x_1575_ = l_Lean_Syntax_node2(v___x_1567_, v___x_1574_, v___x_1563_, v___x_1565_);
v___x_1576_ = l_Lean_Syntax_node2(v___x_1567_, v___x_1568_, v___x_1573_, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
lean_ctor_set(v___x_1577_, 1, v_a_1554_);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Inter__inter__1(lean_object* v_x_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1578_);
v___x_1582_ = l_Lean_Syntax_isOfKind(v_x_1578_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec(v_x_1578_);
v___x_1583_ = lean_box(0);
v___x_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v_a_1580_);
return v___x_1584_;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1585_ = lean_unsigned_to_nat(0u);
v___x_1586_ = l_Lean_Syntax_getArg(v_x_1578_, v___x_1585_);
v___x_1587_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1586_);
v___x_1588_ = l_Lean_Syntax_isOfKind(v___x_1586_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v___x_1586_);
lean_dec(v_x_1578_);
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
lean_ctor_set(v___x_1590_, 1, v_a_1580_);
return v___x_1590_;
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1591_ = lean_unsigned_to_nat(1u);
v___x_1592_ = l_Lean_Syntax_getArg(v_x_1578_, v___x_1591_);
lean_dec(v_x_1578_);
v___x_1593_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1592_);
v___x_1594_ = l_Lean_Syntax_matchesNull(v___x_1592_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec(v___x_1592_);
lean_dec(v___x_1586_);
v___x_1595_ = lean_box(0);
v___x_1596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v_a_1580_);
return v___x_1596_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v_ref_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1597_ = l_Lean_Syntax_getArg(v___x_1592_, v___x_1585_);
v___x_1598_ = l_Lean_Syntax_getArg(v___x_1592_, v___x_1591_);
lean_dec(v___x_1592_);
v_ref_1599_ = l_Lean_replaceRef(v___x_1586_, v_a_1579_);
lean_dec(v___x_1586_);
v___x_1600_ = 0;
v___x_1601_ = l_Lean_SourceInfo_fromRef(v_ref_1599_, v___x_1600_);
lean_dec(v_ref_1599_);
v___x_1602_ = ((lean_object*)(l_term___u2229___00__closed__1));
v___x_1603_ = ((lean_object*)(l_term___u2229___00__closed__2));
lean_inc(v___x_1601_);
v___x_1604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1601_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = l_Lean_Syntax_node3(v___x_1601_, v___x_1602_, v___x_1597_, v___x_1604_, v___x_1598_);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
lean_ctor_set(v___x_1606_, 1, v_a_1580_);
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Inter__inter__1___boxed(lean_object* v_x_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___aux__Init__Core______unexpand__Inter__inter__1(v_x_1607_, v_a_1608_, v_a_1609_);
lean_dec(v_a_1608_);
return v_res_1610_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x5c____1___closed__1(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x5c____1___closed__0));
v___x_1629_ = l_String_toRawSubstring_x27(v___x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x5c____1(lean_object* v_x_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = ((lean_object*)(l_term___x5c___00__closed__1));
lean_inc(v_x_1641_);
v___x_1645_ = l_Lean_Syntax_isOfKind(v_x_1641_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec_ref(v_a_1642_);
lean_dec(v_x_1641_);
v___x_1646_ = lean_box(1);
v___x_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
lean_ctor_set(v___x_1647_, 1, v_a_1643_);
return v___x_1647_;
}
else
{
lean_object* v_quotContext_1648_; lean_object* v_currMacroScope_1649_; lean_object* v_ref_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_quotContext_1648_ = lean_ctor_get(v_a_1642_, 1);
lean_inc(v_quotContext_1648_);
v_currMacroScope_1649_ = lean_ctor_get(v_a_1642_, 2);
lean_inc(v_currMacroScope_1649_);
v_ref_1650_ = lean_ctor_get(v_a_1642_, 5);
lean_inc(v_ref_1650_);
lean_dec_ref(v_a_1642_);
v___x_1651_ = lean_unsigned_to_nat(0u);
v___x_1652_ = l_Lean_Syntax_getArg(v_x_1641_, v___x_1651_);
v___x_1653_ = lean_unsigned_to_nat(2u);
v___x_1654_ = l_Lean_Syntax_getArg(v_x_1641_, v___x_1653_);
lean_dec(v_x_1641_);
v___x_1655_ = 0;
v___x_1656_ = l_Lean_SourceInfo_fromRef(v_ref_1650_, v___x_1655_);
lean_dec(v_ref_1650_);
v___x_1657_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1658_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x5c____1___closed__1, &l___aux__Init__Core______macroRules__term___x5c____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x5c____1___closed__1);
v___x_1659_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x5c____1___closed__4));
v___x_1660_ = l_Lean_addMacroScope(v_quotContext_1648_, v___x_1659_, v_currMacroScope_1649_);
v___x_1661_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x5c____1___closed__6));
lean_inc(v___x_1656_);
v___x_1662_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1656_);
lean_ctor_set(v___x_1662_, 1, v___x_1658_);
lean_ctor_set(v___x_1662_, 2, v___x_1660_);
lean_ctor_set(v___x_1662_, 3, v___x_1661_);
v___x_1663_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1656_);
v___x_1664_ = l_Lean_Syntax_node2(v___x_1656_, v___x_1663_, v___x_1652_, v___x_1654_);
v___x_1665_ = l_Lean_Syntax_node2(v___x_1656_, v___x_1657_, v___x_1662_, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v_a_1643_);
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SDiff__sdiff__1(lean_object* v_x_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1670_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1667_);
v___x_1671_ = l_Lean_Syntax_isOfKind(v_x_1667_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec(v_x_1667_);
v___x_1672_ = lean_box(0);
v___x_1673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set(v___x_1673_, 1, v_a_1669_);
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = l_Lean_Syntax_getArg(v_x_1667_, v___x_1674_);
v___x_1676_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1675_);
v___x_1677_ = l_Lean_Syntax_isOfKind(v___x_1675_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v___x_1675_);
lean_dec(v_x_1667_);
v___x_1678_ = lean_box(0);
v___x_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
lean_ctor_set(v___x_1679_, 1, v_a_1669_);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1680_ = lean_unsigned_to_nat(1u);
v___x_1681_ = l_Lean_Syntax_getArg(v_x_1667_, v___x_1680_);
lean_dec(v_x_1667_);
v___x_1682_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1681_);
v___x_1683_ = l_Lean_Syntax_matchesNull(v___x_1681_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec(v___x_1681_);
lean_dec(v___x_1675_);
v___x_1684_ = lean_box(0);
v___x_1685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set(v___x_1685_, 1, v_a_1669_);
return v___x_1685_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v_ref_1688_; uint8_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1686_ = l_Lean_Syntax_getArg(v___x_1681_, v___x_1674_);
v___x_1687_ = l_Lean_Syntax_getArg(v___x_1681_, v___x_1680_);
lean_dec(v___x_1681_);
v_ref_1688_ = l_Lean_replaceRef(v___x_1675_, v_a_1668_);
lean_dec(v___x_1675_);
v___x_1689_ = 0;
v___x_1690_ = l_Lean_SourceInfo_fromRef(v_ref_1688_, v___x_1689_);
lean_dec(v_ref_1688_);
v___x_1691_ = ((lean_object*)(l_term___x5c___00__closed__1));
v___x_1692_ = ((lean_object*)(l_term___x5c___00__closed__2));
lean_inc(v___x_1690_);
v___x_1693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1690_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = l_Lean_Syntax_node3(v___x_1690_, v___x_1691_, v___x_1686_, v___x_1693_, v___x_1687_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v_a_1669_);
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SDiff__sdiff__1___boxed(lean_object* v_x_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l___aux__Init__Core______unexpand__SDiff__sdiff__1(v_x_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1697_);
return v_res_1699_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__0));
v___x_1720_ = l_String_toRawSubstring_x27(v___x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1(lean_object* v_x_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = ((lean_object*)(l_term_x7b_x7d___closed__1));
v___x_1736_ = l_Lean_Syntax_isOfKind(v_x_1732_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec_ref(v_a_1733_);
v___x_1737_ = lean_box(1);
v___x_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v_a_1734_);
return v___x_1738_;
}
else
{
lean_object* v_quotContext_1739_; lean_object* v_currMacroScope_1740_; lean_object* v_ref_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v_quotContext_1739_ = lean_ctor_get(v_a_1733_, 1);
lean_inc(v_quotContext_1739_);
v_currMacroScope_1740_ = lean_ctor_get(v_a_1733_, 2);
lean_inc(v_currMacroScope_1740_);
v_ref_1741_ = lean_ctor_get(v_a_1733_, 5);
lean_inc(v_ref_1741_);
lean_dec_ref(v_a_1733_);
v___x_1742_ = 0;
v___x_1743_ = l_Lean_SourceInfo_fromRef(v_ref_1741_, v___x_1742_);
lean_dec(v_ref_1741_);
v___x_1744_ = lean_obj_once(&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1, &l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1_once, _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1);
v___x_1745_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4));
v___x_1746_ = l_Lean_addMacroScope(v_quotContext_1739_, v___x_1745_, v_currMacroScope_1740_);
v___x_1747_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6));
v___x_1748_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1743_);
lean_ctor_set(v___x_1748_, 1, v___x_1744_);
lean_ctor_set(v___x_1748_, 2, v___x_1746_);
lean_ctor_set(v___x_1748_, 3, v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
lean_ctor_set(v___x_1749_, 1, v_a_1734_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1(lean_object* v_x_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v_x_1750_);
v___x_1754_ = l_Lean_Syntax_isOfKind(v_x_1750_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v_x_1750_);
v___x_1755_ = lean_box(0);
v___x_1756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v_a_1752_);
return v___x_1756_;
}
else
{
lean_object* v_ref_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_ref_1757_ = l_Lean_replaceRef(v_x_1750_, v_a_1751_);
lean_dec(v_x_1750_);
v___x_1758_ = 0;
v___x_1759_ = l_Lean_SourceInfo_fromRef(v_ref_1757_, v___x_1758_);
lean_dec(v_ref_1757_);
v___x_1760_ = ((lean_object*)(l_term_x7b_x7d___closed__1));
v___x_1761_ = ((lean_object*)(l_term_x7b_x7d___closed__2));
lean_inc(v___x_1759_);
v___x_1762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1759_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = ((lean_object*)(l_term_x7b_x7d___closed__4));
lean_inc(v___x_1759_);
v___x_1764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1759_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = l_Lean_Syntax_node2(v___x_1759_, v___x_1760_, v___x_1762_, v___x_1764_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
lean_ctor_set(v___x_1766_, 1, v_a_1752_);
return v___x_1766_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1___boxed(lean_object* v_x_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1(v_x_1767_, v_a_1768_, v_a_1769_);
lean_dec(v_a_1768_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_u2205__1(lean_object* v_x_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = ((lean_object*)(l_term_u2205___closed__1));
v___x_1786_ = l_Lean_Syntax_isOfKind(v_x_1782_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_dec_ref(v_a_1783_);
v___x_1787_ = lean_box(1);
v___x_1788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
lean_ctor_set(v___x_1788_, 1, v_a_1784_);
return v___x_1788_;
}
else
{
lean_object* v_quotContext_1789_; lean_object* v_currMacroScope_1790_; lean_object* v_ref_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_quotContext_1789_ = lean_ctor_get(v_a_1783_, 1);
lean_inc(v_quotContext_1789_);
v_currMacroScope_1790_ = lean_ctor_get(v_a_1783_, 2);
lean_inc(v_currMacroScope_1790_);
v_ref_1791_ = lean_ctor_get(v_a_1783_, 5);
lean_inc(v_ref_1791_);
lean_dec_ref(v_a_1783_);
v___x_1792_ = 0;
v___x_1793_ = l_Lean_SourceInfo_fromRef(v_ref_1791_, v___x_1792_);
lean_dec(v_ref_1791_);
v___x_1794_ = lean_obj_once(&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1, &l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1_once, _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1);
v___x_1795_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4));
v___x_1796_ = l_Lean_addMacroScope(v_quotContext_1789_, v___x_1795_, v_currMacroScope_1790_);
v___x_1797_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6));
v___x_1798_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1793_);
lean_ctor_set(v___x_1798_, 1, v___x_1794_);
lean_ctor_set(v___x_1798_, 2, v___x_1796_);
lean_ctor_set(v___x_1798_, 3, v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v_a_1784_);
return v___x_1799_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2(lean_object* v_x_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1803_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v_x_1800_);
v___x_1804_ = l_Lean_Syntax_isOfKind(v_x_1800_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec(v_x_1800_);
v___x_1805_ = lean_box(0);
v___x_1806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v_a_1802_);
return v___x_1806_;
}
else
{
lean_object* v_ref_1807_; uint8_t v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_ref_1807_ = l_Lean_replaceRef(v_x_1800_, v_a_1801_);
lean_dec(v_x_1800_);
v___x_1808_ = 0;
v___x_1809_ = l_Lean_SourceInfo_fromRef(v_ref_1807_, v___x_1808_);
lean_dec(v_ref_1807_);
v___x_1810_ = ((lean_object*)(l_term_u2205___closed__1));
v___x_1811_ = ((lean_object*)(l_term_u2205___closed__2));
lean_inc(v___x_1809_);
v___x_1812_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1809_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Lean_Syntax_node1(v___x_1809_, v___x_1810_, v___x_1812_);
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
lean_ctor_set(v___x_1814_, 1, v_a_1802_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2___boxed(lean_object* v_x_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2(v_x_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_a_1816_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask_default___redArg(lean_object* v_inst_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v_inst_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask_default(lean_object* v_a_1821_, lean_object* v_inst_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_inst_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask___redArg(lean_object* v_inst_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_inst_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask(lean_object* v_a_1826_, lean_object* v_inst_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v_inst_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Task_pure___boxed(lean_object* v_00_u03b1_1831_, lean_object* v_get_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = lean_task_pure(v_get_1832_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Task_get___boxed(lean_object* v_00_u03b1_1836_, lean_object* v_self_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = lean_task_get_own(v_self_1837_);
return v_res_1838_;
}
}
static lean_object* _init_l_Task_Priority_default(void){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_unsigned_to_nat(0u);
return v___x_1839_;
}
}
static lean_object* _init_l_Task_Priority_max(void){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_unsigned_to_nat(8u);
return v___x_1840_;
}
}
static lean_object* _init_l_Task_Priority_dedicated(void){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_unsigned_to_nat(9u);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Task_spawn___boxed(lean_object* v_00_u03b1_1845_, lean_object* v_fn_1846_, lean_object* v_prio_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = lean_task_spawn(v_fn_1846_, v_prio_1847_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Task_map___boxed(lean_object* v_00_u03b1_1855_, lean_object* v_00_u03b2_1856_, lean_object* v_f_1857_, lean_object* v_x_1858_, lean_object* v_prio_1859_, lean_object* v_sync_1860_){
_start:
{
uint8_t v_sync_boxed_1861_; lean_object* v_res_1862_; 
v_sync_boxed_1861_ = lean_unbox(v_sync_1860_);
v_res_1862_ = lean_task_map(v_f_1857_, v_x_1858_, v_prio_1859_, v_sync_boxed_1861_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Task_bind___boxed(lean_object* v_00_u03b1_1869_, lean_object* v_00_u03b2_1870_, lean_object* v_x_1871_, lean_object* v_f_1872_, lean_object* v_prio_1873_, lean_object* v_sync_1874_){
_start:
{
uint8_t v_sync_boxed_1875_; lean_object* v_res_1876_; 
v_sync_boxed_1875_ = lean_unbox(v_sync_1874_);
v_res_1876_ = lean_task_bind(v_x_1871_, v_f_1872_, v_prio_1873_, v_sync_boxed_1875_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_strictOr___boxed(lean_object* v_b_u2081_1879_, lean_object* v_b_u2082_1880_){
_start:
{
uint8_t v_b_u2081_boxed_1881_; uint8_t v_b_u2082_boxed_1882_; uint8_t v_res_1883_; lean_object* v_r_1884_; 
v_b_u2081_boxed_1881_ = lean_unbox(v_b_u2081_1879_);
v_b_u2082_boxed_1882_ = lean_unbox(v_b_u2082_1880_);
v_res_1883_ = lean_strict_or(v_b_u2081_boxed_1881_, v_b_u2082_boxed_1882_);
v_r_1884_ = lean_box(v_res_1883_);
return v_r_1884_;
}
}
LEAN_EXPORT lean_object* l_strictAnd___boxed(lean_object* v_b_u2081_1887_, lean_object* v_b_u2082_1888_){
_start:
{
uint8_t v_b_u2081_boxed_1889_; uint8_t v_b_u2082_boxed_1890_; uint8_t v_res_1891_; lean_object* v_r_1892_; 
v_b_u2081_boxed_1889_ = lean_unbox(v_b_u2081_1887_);
v_b_u2082_boxed_1890_ = lean_unbox(v_b_u2082_1888_);
v_res_1891_ = lean_strict_and(v_b_u2081_boxed_1889_, v_b_u2082_boxed_1890_);
v_r_1892_ = lean_box(v_res_1891_);
return v_r_1892_;
}
}
LEAN_EXPORT uint8_t l_bne___redArg(lean_object* v_inst_1893_, lean_object* v_a_1894_, lean_object* v_b_1895_){
_start:
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = lean_apply_2(v_inst_1893_, v_a_1894_, v_b_1895_);
v___x_1897_ = lean_unbox(v___x_1896_);
if (v___x_1897_ == 0)
{
uint8_t v___x_1898_; 
v___x_1898_ = 1;
return v___x_1898_;
}
else
{
uint8_t v___x_1899_; 
v___x_1899_ = 0;
return v___x_1899_;
}
}
}
LEAN_EXPORT lean_object* l_bne___redArg___boxed(lean_object* v_inst_1900_, lean_object* v_a_1901_, lean_object* v_b_1902_){
_start:
{
uint8_t v_res_1903_; lean_object* v_r_1904_; 
v_res_1903_ = l_bne___redArg(v_inst_1900_, v_a_1901_, v_b_1902_);
v_r_1904_ = lean_box(v_res_1903_);
return v_r_1904_;
}
}
LEAN_EXPORT uint8_t l_bne(lean_object* v_00_u03b1_1905_, lean_object* v_inst_1906_, lean_object* v_a_1907_, lean_object* v_b_1908_){
_start:
{
lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = lean_apply_2(v_inst_1906_, v_a_1907_, v_b_1908_);
v___x_1910_ = lean_unbox(v___x_1909_);
if (v___x_1910_ == 0)
{
uint8_t v___x_1911_; 
v___x_1911_ = 1;
return v___x_1911_;
}
else
{
uint8_t v___x_1912_; 
v___x_1912_ = 0;
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l_bne___boxed(lean_object* v_00_u03b1_1913_, lean_object* v_inst_1914_, lean_object* v_a_1915_, lean_object* v_b_1916_){
_start:
{
uint8_t v_res_1917_; lean_object* v_r_1918_; 
v_res_1917_ = l_bne(v_00_u03b1_1913_, v_inst_1914_, v_a_1915_, v_b_1916_);
v_r_1918_ = lean_box(v_res_1917_);
return v_r_1918_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0));
v___x_1937_ = l_String_toRawSubstring_x27(v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1(lean_object* v_x_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
lean_inc(v_x_1946_);
v___x_1950_ = l_Lean_Syntax_isOfKind(v_x_1946_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec_ref(v_a_1947_);
lean_dec(v_x_1946_);
v___x_1951_ = lean_box(1);
v___x_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v_a_1948_);
return v___x_1952_;
}
else
{
lean_object* v_quotContext_1953_; lean_object* v_currMacroScope_1954_; lean_object* v_ref_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v_quotContext_1953_ = lean_ctor_get(v_a_1947_, 1);
lean_inc(v_quotContext_1953_);
v_currMacroScope_1954_ = lean_ctor_get(v_a_1947_, 2);
lean_inc(v_currMacroScope_1954_);
v_ref_1955_ = lean_ctor_get(v_a_1947_, 5);
lean_inc(v_ref_1955_);
lean_dec_ref(v_a_1947_);
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = l_Lean_Syntax_getArg(v_x_1946_, v___x_1956_);
v___x_1958_ = lean_unsigned_to_nat(2u);
v___x_1959_ = l_Lean_Syntax_getArg(v_x_1946_, v___x_1958_);
lean_dec(v_x_1946_);
v___x_1960_ = 0;
v___x_1961_ = l_Lean_SourceInfo_fromRef(v_ref_1955_, v___x_1960_);
lean_dec(v_ref_1955_);
v___x_1962_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1963_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1, &l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1);
v___x_1964_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2));
v___x_1965_ = l_Lean_addMacroScope(v_quotContext_1953_, v___x_1964_, v_currMacroScope_1954_);
v___x_1966_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4));
lean_inc(v___x_1961_);
v___x_1967_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1961_);
lean_ctor_set(v___x_1967_, 1, v___x_1963_);
lean_ctor_set(v___x_1967_, 2, v___x_1965_);
lean_ctor_set(v___x_1967_, 3, v___x_1966_);
v___x_1968_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_1961_);
v___x_1969_ = l_Lean_Syntax_node2(v___x_1961_, v___x_1968_, v___x_1957_, v___x_1959_);
v___x_1970_ = l_Lean_Syntax_node2(v___x_1961_, v___x_1962_, v___x_1967_, v___x_1969_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v_a_1948_);
return v___x_1971_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__bne__1(lean_object* v_x_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1975_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1972_);
v___x_1976_ = l_Lean_Syntax_isOfKind(v_x_1972_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_dec(v_x_1972_);
v___x_1977_ = lean_box(0);
v___x_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v_a_1974_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1979_ = lean_unsigned_to_nat(0u);
v___x_1980_ = l_Lean_Syntax_getArg(v_x_1972_, v___x_1979_);
v___x_1981_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1980_);
v___x_1982_ = l_Lean_Syntax_isOfKind(v___x_1980_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_dec(v___x_1980_);
lean_dec(v_x_1972_);
v___x_1983_ = lean_box(0);
v___x_1984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
lean_ctor_set(v___x_1984_, 1, v_a_1974_);
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1985_ = lean_unsigned_to_nat(1u);
v___x_1986_ = l_Lean_Syntax_getArg(v_x_1972_, v___x_1985_);
lean_dec(v_x_1972_);
v___x_1987_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1986_);
v___x_1988_ = l_Lean_Syntax_matchesNull(v___x_1986_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_dec(v___x_1986_);
lean_dec(v___x_1980_);
v___x_1989_ = lean_box(0);
v___x_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v_a_1974_);
return v___x_1990_;
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v_ref_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1991_ = l_Lean_Syntax_getArg(v___x_1986_, v___x_1979_);
v___x_1992_ = l_Lean_Syntax_getArg(v___x_1986_, v___x_1985_);
lean_dec(v___x_1986_);
v_ref_1993_ = l_Lean_replaceRef(v___x_1980_, v_a_1973_);
lean_dec(v___x_1980_);
v___x_1994_ = 0;
v___x_1995_ = l_Lean_SourceInfo_fromRef(v_ref_1993_, v___x_1994_);
lean_dec(v_ref_1993_);
v___x_1996_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
v___x_1997_ = ((lean_object*)(l_term___x21_x3d___00__closed__2));
lean_inc(v___x_1995_);
v___x_1998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1995_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = l_Lean_Syntax_node3(v___x_1995_, v___x_1996_, v___x_1991_, v___x_1998_, v___x_1992_);
v___x_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set(v___x_2000_, 1, v_a_1974_);
return v___x_2000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__bne__1___boxed(lean_object* v_x_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___aux__Init__Core______unexpand__bne__1(v_x_2001_, v_a_2002_, v_a_2003_);
lean_dec(v_a_2002_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2(lean_object* v_x_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
lean_inc(v_x_2012_);
v___x_2016_ = l_Lean_Syntax_isOfKind(v_x_2012_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec_ref(v_a_2013_);
lean_dec(v_x_2012_);
v___x_2017_ = lean_box(1);
v___x_2018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
lean_ctor_set(v___x_2018_, 1, v_a_2014_);
return v___x_2018_;
}
else
{
lean_object* v_quotContext_2019_; lean_object* v_currMacroScope_2020_; lean_object* v_ref_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_quotContext_2019_ = lean_ctor_get(v_a_2013_, 1);
lean_inc(v_quotContext_2019_);
v_currMacroScope_2020_ = lean_ctor_get(v_a_2013_, 2);
lean_inc(v_currMacroScope_2020_);
v_ref_2021_ = lean_ctor_get(v_a_2013_, 5);
lean_inc(v_ref_2021_);
lean_dec_ref(v_a_2013_);
v___x_2022_ = lean_unsigned_to_nat(0u);
v___x_2023_ = l_Lean_Syntax_getArg(v_x_2012_, v___x_2022_);
v___x_2024_ = lean_unsigned_to_nat(2u);
v___x_2025_ = l_Lean_Syntax_getArg(v_x_2012_, v___x_2024_);
lean_dec(v_x_2012_);
v___x_2026_ = 0;
v___x_2027_ = l_Lean_SourceInfo_fromRef(v_ref_2021_, v___x_2026_);
lean_dec(v_ref_2021_);
v___x_2028_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1));
v___x_2029_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__2));
lean_inc(v___x_2027_);
v___x_2030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2027_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1, &l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1);
v___x_2032_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2));
v___x_2033_ = l_Lean_addMacroScope(v_quotContext_2019_, v___x_2032_, v_currMacroScope_2020_);
v___x_2034_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4));
lean_inc(v___x_2027_);
v___x_2035_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2027_);
lean_ctor_set(v___x_2035_, 1, v___x_2031_);
lean_ctor_set(v___x_2035_, 2, v___x_2033_);
lean_ctor_set(v___x_2035_, 3, v___x_2034_);
v___x_2036_ = l_Lean_Syntax_node4(v___x_2027_, v___x_2028_, v___x_2030_, v___x_2035_, v___x_2023_, v___x_2025_);
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
lean_ctor_set(v___x_2037_, 1, v_a_2014_);
return v___x_2037_;
}
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_2038_, lean_object* v_x_2039_, lean_object* v_y_2040_){
_start:
{
lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = lean_apply_2(v_inst_2038_, v_x_2039_, v_y_2040_);
v___x_2042_ = lean_unbox(v___x_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_2043_, lean_object* v_x_2044_, lean_object* v_y_2045_){
_start:
{
uint8_t v_res_2046_; lean_object* v_r_2047_; 
v_res_2046_ = l_instDecidableEqOfLawfulBEq___redArg(v_inst_2043_, v_x_2044_, v_y_2045_);
v_r_2047_ = lean_box(v_res_2046_);
return v_r_2047_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_2048_, lean_object* v_inst_2049_, lean_object* v_inst_2050_, lean_object* v_x_2051_, lean_object* v_y_2052_){
_start:
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = lean_apply_2(v_inst_2049_, v_x_2051_, v_y_2052_);
v___x_2054_ = lean_unbox(v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_2055_, lean_object* v_inst_2056_, lean_object* v_inst_2057_, lean_object* v_x_2058_, lean_object* v_y_2059_){
_start:
{
uint8_t v_res_2060_; lean_object* v_r_2061_; 
v_res_2060_ = l_instDecidableEqOfLawfulBEq(v_00_u03b1_2055_, v_inst_2056_, v_inst_2057_, v_x_2058_, v_y_2059_);
v_r_2061_ = lean_box(v_res_2060_);
return v_r_2061_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__0));
v___x_2080_ = l_String_toRawSubstring_x27(v___x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____1(lean_object* v_x_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = ((lean_object*)(l_term___u2260___00__closed__1));
lean_inc(v_x_2089_);
v___x_2093_ = l_Lean_Syntax_isOfKind(v_x_2089_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec_ref(v_a_2090_);
lean_dec(v_x_2089_);
v___x_2094_ = lean_box(1);
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set(v___x_2095_, 1, v_a_2091_);
return v___x_2095_;
}
else
{
lean_object* v_quotContext_2096_; lean_object* v_currMacroScope_2097_; lean_object* v_ref_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_quotContext_2096_ = lean_ctor_get(v_a_2090_, 1);
lean_inc(v_quotContext_2096_);
v_currMacroScope_2097_ = lean_ctor_get(v_a_2090_, 2);
lean_inc(v_currMacroScope_2097_);
v_ref_2098_ = lean_ctor_get(v_a_2090_, 5);
lean_inc(v_ref_2098_);
lean_dec_ref(v_a_2090_);
v___x_2099_ = lean_unsigned_to_nat(0u);
v___x_2100_ = l_Lean_Syntax_getArg(v_x_2089_, v___x_2099_);
v___x_2101_ = lean_unsigned_to_nat(2u);
v___x_2102_ = l_Lean_Syntax_getArg(v_x_2089_, v___x_2101_);
lean_dec(v_x_2089_);
v___x_2103_ = 0;
v___x_2104_ = l_Lean_SourceInfo_fromRef(v_ref_2098_, v___x_2103_);
lean_dec(v_ref_2098_);
v___x_2105_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_2106_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2260____1___closed__1, &l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1);
v___x_2107_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__2));
v___x_2108_ = l_Lean_addMacroScope(v_quotContext_2096_, v___x_2107_, v_currMacroScope_2097_);
v___x_2109_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__4));
lean_inc(v___x_2104_);
v___x_2110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2104_);
lean_ctor_set(v___x_2110_, 1, v___x_2106_);
lean_ctor_set(v___x_2110_, 2, v___x_2108_);
lean_ctor_set(v___x_2110_, 3, v___x_2109_);
v___x_2111_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
lean_inc(v___x_2104_);
v___x_2112_ = l_Lean_Syntax_node2(v___x_2104_, v___x_2111_, v___x_2100_, v___x_2102_);
v___x_2113_ = l_Lean_Syntax_node2(v___x_2104_, v___x_2105_, v___x_2110_, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v_a_2091_);
return v___x_2114_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Ne__1(lean_object* v_x_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_2115_);
v___x_2119_ = l_Lean_Syntax_isOfKind(v_x_2115_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec(v_x_2115_);
v___x_2120_ = lean_box(0);
v___x_2121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
lean_ctor_set(v___x_2121_, 1, v_a_2117_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = l_Lean_Syntax_getArg(v_x_2115_, v___x_2122_);
v___x_2124_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_2123_);
v___x_2125_ = l_Lean_Syntax_isOfKind(v___x_2123_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
lean_dec(v___x_2123_);
lean_dec(v_x_2115_);
v___x_2126_ = lean_box(0);
v___x_2127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v_a_2117_);
return v___x_2127_;
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2128_ = lean_unsigned_to_nat(1u);
v___x_2129_ = l_Lean_Syntax_getArg(v_x_2115_, v___x_2128_);
lean_dec(v_x_2115_);
v___x_2130_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2129_);
v___x_2131_ = l_Lean_Syntax_matchesNull(v___x_2129_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec(v___x_2129_);
lean_dec(v___x_2123_);
v___x_2132_ = lean_box(0);
v___x_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v_a_2117_);
return v___x_2133_;
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v_ref_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2134_ = l_Lean_Syntax_getArg(v___x_2129_, v___x_2122_);
v___x_2135_ = l_Lean_Syntax_getArg(v___x_2129_, v___x_2128_);
lean_dec(v___x_2129_);
v_ref_2136_ = l_Lean_replaceRef(v___x_2123_, v_a_2116_);
lean_dec(v___x_2123_);
v___x_2137_ = 0;
v___x_2138_ = l_Lean_SourceInfo_fromRef(v_ref_2136_, v___x_2137_);
lean_dec(v_ref_2136_);
v___x_2139_ = ((lean_object*)(l_term___u2260___00__closed__1));
v___x_2140_ = ((lean_object*)(l_term___u2260___00__closed__2));
lean_inc(v___x_2138_);
v___x_2141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2138_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = l_Lean_Syntax_node3(v___x_2138_, v___x_2139_, v___x_2134_, v___x_2141_, v___x_2135_);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v_a_2117_);
return v___x_2143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Ne__1___boxed(lean_object* v_x_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l___aux__Init__Core______unexpand__Ne__1(v_x_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_a_2145_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____2(lean_object* v_x_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2158_ = ((lean_object*)(l_term___u2260___00__closed__1));
lean_inc(v_x_2155_);
v___x_2159_ = l_Lean_Syntax_isOfKind(v_x_2155_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec_ref(v_a_2156_);
lean_dec(v_x_2155_);
v___x_2160_ = lean_box(1);
v___x_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v_a_2157_);
return v___x_2161_;
}
else
{
lean_object* v_quotContext_2162_; lean_object* v_currMacroScope_2163_; lean_object* v_ref_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v_quotContext_2162_ = lean_ctor_get(v_a_2156_, 1);
lean_inc(v_quotContext_2162_);
v_currMacroScope_2163_ = lean_ctor_get(v_a_2156_, 2);
lean_inc(v_currMacroScope_2163_);
v_ref_2164_ = lean_ctor_get(v_a_2156_, 5);
lean_inc(v_ref_2164_);
lean_dec_ref(v_a_2156_);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = l_Lean_Syntax_getArg(v_x_2155_, v___x_2165_);
v___x_2167_ = lean_unsigned_to_nat(2u);
v___x_2168_ = l_Lean_Syntax_getArg(v_x_2155_, v___x_2167_);
lean_dec(v_x_2155_);
v___x_2169_ = 0;
v___x_2170_ = l_Lean_SourceInfo_fromRef(v_ref_2164_, v___x_2169_);
lean_dec(v_ref_2164_);
v___x_2171_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____2___closed__1));
v___x_2172_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____2___closed__2));
lean_inc(v___x_2170_);
v___x_2173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2170_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
v___x_2174_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2260____1___closed__1, &l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1);
v___x_2175_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__2));
v___x_2176_ = l_Lean_addMacroScope(v_quotContext_2162_, v___x_2175_, v_currMacroScope_2163_);
v___x_2177_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__4));
lean_inc(v___x_2170_);
v___x_2178_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2170_);
lean_ctor_set(v___x_2178_, 1, v___x_2174_);
lean_ctor_set(v___x_2178_, 2, v___x_2176_);
lean_ctor_set(v___x_2178_, 3, v___x_2177_);
v___x_2179_ = l_Lean_Syntax_node4(v___x_2170_, v___x_2171_, v___x_2173_, v___x_2178_, v___x_2166_, v___x_2168_);
v___x_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set(v___x_2180_, 1, v_a_2157_);
return v___x_2180_;
}
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__5));
v___x_2196_ = l_String_toRawSubstring_x27(v___x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1(lean_object* v_x_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2210_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2));
v___x_2211_ = l_Lean_Syntax_isOfKind(v_x_2207_, v___x_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec_ref(v_a_2208_);
v___x_2212_ = lean_box(1);
v___x_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v_a_2209_);
return v___x_2213_;
}
else
{
lean_object* v_quotContext_2214_; lean_object* v_currMacroScope_2215_; lean_object* v_ref_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v_quotContext_2214_ = lean_ctor_get(v_a_2208_, 1);
lean_inc(v_quotContext_2214_);
v_currMacroScope_2215_ = lean_ctor_get(v_a_2208_, 2);
lean_inc(v_currMacroScope_2215_);
v_ref_2216_ = lean_ctor_get(v_a_2208_, 5);
lean_inc(v_ref_2216_);
lean_dec_ref(v_a_2208_);
v___x_2217_ = 0;
v___x_2218_ = l_Lean_SourceInfo_fromRef(v_ref_2216_, v___x_2217_);
lean_dec(v_ref_2216_);
v___x_2219_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3));
v___x_2220_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4));
lean_inc(v___x_2218_);
v___x_2221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2218_);
lean_ctor_set(v___x_2221_, 1, v___x_2219_);
v___x_2222_ = lean_obj_once(&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6, &l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6_once, _init_l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6);
v___x_2223_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8));
v___x_2224_ = l_Lean_addMacroScope(v_quotContext_2214_, v___x_2223_, v_currMacroScope_2215_);
v___x_2225_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__10));
lean_inc(v___x_2218_);
v___x_2226_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2218_);
lean_ctor_set(v___x_2226_, 1, v___x_2222_);
lean_ctor_set(v___x_2226_, 2, v___x_2224_);
lean_ctor_set(v___x_2226_, 3, v___x_2225_);
v___x_2227_ = l_Lean_Syntax_node2(v___x_2218_, v___x_2220_, v___x_2221_, v___x_2226_);
v___x_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v_a_2209_);
return v___x_2228_;
}
}
}
static lean_object* _init_l_instTransIff(void){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_box(0);
return v___x_2229_;
}
}
LEAN_EXPORT uint8_t l_toBoolUsing___redArg(uint8_t v_d_2230_){
_start:
{
return v_d_2230_;
}
}
LEAN_EXPORT lean_object* l_toBoolUsing___redArg___boxed(lean_object* v_d_2231_){
_start:
{
uint8_t v_d_boxed_2232_; uint8_t v_res_2233_; lean_object* v_r_2234_; 
v_d_boxed_2232_ = lean_unbox(v_d_2231_);
v_res_2233_ = l_toBoolUsing___redArg(v_d_boxed_2232_);
v_r_2234_ = lean_box(v_res_2233_);
return v_r_2234_;
}
}
LEAN_EXPORT uint8_t l_toBoolUsing(lean_object* v_p_2235_, uint8_t v_d_2236_){
_start:
{
return v_d_2236_;
}
}
LEAN_EXPORT lean_object* l_toBoolUsing___boxed(lean_object* v_p_2237_, lean_object* v_d_2238_){
_start:
{
uint8_t v_d_boxed_2239_; uint8_t v_res_2240_; lean_object* v_r_2241_; 
v_d_boxed_2239_ = lean_unbox(v_d_2238_);
v_res_2240_ = l_toBoolUsing(v_p_2237_, v_d_boxed_2239_);
v_r_2241_ = lean_box(v_res_2240_);
return v_r_2241_;
}
}
static uint8_t _init_l_instDecidableTrue(void){
_start:
{
uint8_t v___x_2242_; 
v___x_2242_ = 1;
return v___x_2242_;
}
}
static uint8_t _init_l_instDecidableFalse(void){
_start:
{
uint8_t v___x_2243_; 
v___x_2243_ = 0;
return v___x_2243_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__iff___redArg(uint8_t v_inst_2244_){
_start:
{
return v_inst_2244_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__iff___redArg___boxed(lean_object* v_inst_2245_){
_start:
{
uint8_t v_inst_8__boxed_2246_; uint8_t v_res_2247_; lean_object* v_r_2248_; 
v_inst_8__boxed_2246_ = lean_unbox(v_inst_2245_);
v_res_2247_ = l_decidable__of__decidable__of__iff___redArg(v_inst_8__boxed_2246_);
v_r_2248_ = lean_box(v_res_2247_);
return v_r_2248_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__iff(lean_object* v_p_2249_, lean_object* v_q_2250_, uint8_t v_inst_2251_, lean_object* v_h_2252_){
_start:
{
return v_inst_2251_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__iff___boxed(lean_object* v_p_2253_, lean_object* v_q_2254_, lean_object* v_inst_2255_, lean_object* v_h_2256_){
_start:
{
uint8_t v_inst_11__boxed_2257_; uint8_t v_res_2258_; lean_object* v_r_2259_; 
v_inst_11__boxed_2257_ = lean_unbox(v_inst_2255_);
v_res_2258_ = l_decidable__of__decidable__of__iff(v_p_2253_, v_q_2254_, v_inst_11__boxed_2257_, v_h_2256_);
v_r_2259_ = lean_box(v_res_2258_);
return v_r_2259_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__eq___redArg(uint8_t v_inst_2260_){
_start:
{
return v_inst_2260_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__eq___redArg___boxed(lean_object* v_inst_2261_){
_start:
{
uint8_t v_inst_8__boxed_2262_; uint8_t v_res_2263_; lean_object* v_r_2264_; 
v_inst_8__boxed_2262_ = lean_unbox(v_inst_2261_);
v_res_2263_ = l_decidable__of__decidable__of__eq___redArg(v_inst_8__boxed_2262_);
v_r_2264_ = lean_box(v_res_2263_);
return v_r_2264_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__eq(lean_object* v_p_2265_, lean_object* v_q_2266_, uint8_t v_inst_2267_, lean_object* v_h_2268_){
_start:
{
return v_inst_2267_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__eq___boxed(lean_object* v_p_2269_, lean_object* v_q_2270_, lean_object* v_inst_2271_, lean_object* v_h_2272_){
_start:
{
uint8_t v_inst_11__boxed_2273_; uint8_t v_res_2274_; lean_object* v_r_2275_; 
v_inst_11__boxed_2273_ = lean_unbox(v_inst_2271_);
v_res_2274_ = l_decidable__of__decidable__of__eq(v_p_2269_, v_q_2270_, v_inst_11__boxed_2273_, v_h_2272_);
v_r_2275_ = lean_box(v_res_2274_);
return v_r_2275_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIff___redArg(uint8_t v_inst_2276_, uint8_t v_inst_2277_){
_start:
{
if (v_inst_2276_ == 0)
{
if (v_inst_2277_ == 0)
{
uint8_t v___x_2278_; 
v___x_2278_ = 1;
return v___x_2278_;
}
else
{
return v_inst_2276_;
}
}
else
{
return v_inst_2277_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableIff___redArg___boxed(lean_object* v_inst_2279_, lean_object* v_inst_2280_){
_start:
{
uint8_t v_inst_15__boxed_2281_; uint8_t v_inst_16__boxed_2282_; uint8_t v_res_2283_; lean_object* v_r_2284_; 
v_inst_15__boxed_2281_ = lean_unbox(v_inst_2279_);
v_inst_16__boxed_2282_ = lean_unbox(v_inst_2280_);
v_res_2283_ = l_instDecidableIff___redArg(v_inst_15__boxed_2281_, v_inst_16__boxed_2282_);
v_r_2284_ = lean_box(v_res_2283_);
return v_r_2284_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIff(lean_object* v_p_2285_, lean_object* v_q_2286_, uint8_t v_inst_2287_, uint8_t v_inst_2288_){
_start:
{
if (v_inst_2287_ == 0)
{
if (v_inst_2288_ == 0)
{
uint8_t v___x_2289_; 
v___x_2289_ = 1;
return v___x_2289_;
}
else
{
return v_inst_2287_;
}
}
else
{
return v_inst_2288_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableIff___boxed(lean_object* v_p_2290_, lean_object* v_q_2291_, lean_object* v_inst_2292_, lean_object* v_inst_2293_){
_start:
{
uint8_t v_inst_23__boxed_2294_; uint8_t v_inst_24__boxed_2295_; uint8_t v_res_2296_; lean_object* v_r_2297_; 
v_inst_23__boxed_2294_ = lean_unbox(v_inst_2292_);
v_inst_24__boxed_2295_ = lean_unbox(v_inst_2293_);
v_res_2296_ = l_instDecidableIff(v_p_2290_, v_q_2291_, v_inst_23__boxed_2294_, v_inst_24__boxed_2295_);
v_r_2297_ = lean_box(v_res_2296_);
return v_r_2297_;
}
}
LEAN_EXPORT lean_object* l_iteInduction___redArg(uint8_t v_inst_2298_, lean_object* v_hpos_2299_, lean_object* v_hneg_2300_){
_start:
{
if (v_inst_2298_ == 0)
{
lean_object* v___x_2301_; 
lean_dec(v_hpos_2299_);
v___x_2301_ = lean_apply_1(v_hneg_2300_, lean_box(0));
return v___x_2301_;
}
else
{
lean_object* v___x_2302_; 
lean_dec(v_hneg_2300_);
v___x_2302_ = lean_apply_1(v_hpos_2299_, lean_box(0));
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l_iteInduction___redArg___boxed(lean_object* v_inst_2303_, lean_object* v_hpos_2304_, lean_object* v_hneg_2305_){
_start:
{
uint8_t v_inst_boxed_2306_; lean_object* v_res_2307_; 
v_inst_boxed_2306_ = lean_unbox(v_inst_2303_);
v_res_2307_ = l_iteInduction___redArg(v_inst_boxed_2306_, v_hpos_2304_, v_hneg_2305_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_iteInduction(lean_object* v_00_u03b1_2308_, lean_object* v_c_2309_, uint8_t v_inst_2310_, lean_object* v_motive_2311_, lean_object* v_t_2312_, lean_object* v_e_2313_, lean_object* v_hpos_2314_, lean_object* v_hneg_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_iteInduction___redArg(v_inst_2310_, v_hpos_2314_, v_hneg_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_iteInduction___boxed(lean_object* v_00_u03b1_2317_, lean_object* v_c_2318_, lean_object* v_inst_2319_, lean_object* v_motive_2320_, lean_object* v_t_2321_, lean_object* v_e_2322_, lean_object* v_hpos_2323_, lean_object* v_hneg_2324_){
_start:
{
uint8_t v_inst_boxed_2325_; lean_object* v_res_2326_; 
v_inst_boxed_2325_ = lean_unbox(v_inst_2319_);
v_res_2326_ = l_iteInduction(v_00_u03b1_2317_, v_c_2318_, v_inst_boxed_2325_, v_motive_2320_, v_t_2321_, v_e_2322_, v_hpos_2323_, v_hneg_2324_);
lean_dec(v_e_2322_);
lean_dec(v_t_2321_);
return v_res_2326_;
}
}
LEAN_EXPORT uint8_t l_instDecidableDite___redArg(uint8_t v_dC_2327_, lean_object* v_dT_2328_, lean_object* v_dE_2329_){
_start:
{
if (v_dC_2327_ == 0)
{
lean_object* v___x_2330_; uint8_t v___x_2331_; 
lean_dec_ref(v_dT_2328_);
v___x_2330_ = lean_apply_1(v_dE_2329_, lean_box(0));
v___x_2331_ = lean_unbox(v___x_2330_);
return v___x_2331_;
}
else
{
lean_object* v___x_2332_; uint8_t v___x_2333_; 
lean_dec_ref(v_dE_2329_);
v___x_2332_ = lean_apply_1(v_dT_2328_, lean_box(0));
v___x_2333_ = lean_unbox(v___x_2332_);
return v___x_2333_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableDite___redArg___boxed(lean_object* v_dC_2334_, lean_object* v_dT_2335_, lean_object* v_dE_2336_){
_start:
{
uint8_t v_dC_boxed_2337_; uint8_t v_res_2338_; lean_object* v_r_2339_; 
v_dC_boxed_2337_ = lean_unbox(v_dC_2334_);
v_res_2338_ = l_instDecidableDite___redArg(v_dC_boxed_2337_, v_dT_2335_, v_dE_2336_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
LEAN_EXPORT uint8_t l_instDecidableDite(lean_object* v_c_2340_, lean_object* v_t_2341_, lean_object* v_e_2342_, uint8_t v_dC_2343_, lean_object* v_dT_2344_, lean_object* v_dE_2345_){
_start:
{
if (v_dC_2343_ == 0)
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
lean_dec_ref(v_dT_2344_);
v___x_2346_ = lean_apply_1(v_dE_2345_, lean_box(0));
v___x_2347_ = lean_unbox(v___x_2346_);
return v___x_2347_;
}
else
{
lean_object* v___x_2348_; uint8_t v___x_2349_; 
lean_dec_ref(v_dE_2345_);
v___x_2348_ = lean_apply_1(v_dT_2344_, lean_box(0));
v___x_2349_ = lean_unbox(v___x_2348_);
return v___x_2349_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableDite___boxed(lean_object* v_c_2350_, lean_object* v_t_2351_, lean_object* v_e_2352_, lean_object* v_dC_2353_, lean_object* v_dT_2354_, lean_object* v_dE_2355_){
_start:
{
uint8_t v_dC_boxed_2356_; uint8_t v_res_2357_; lean_object* v_r_2358_; 
v_dC_boxed_2356_ = lean_unbox(v_dC_2353_);
v_res_2357_ = l_instDecidableDite(v_c_2350_, v_t_2351_, v_e_2352_, v_dC_boxed_2356_, v_dT_2354_, v_dE_2355_);
v_r_2358_ = lean_box(v_res_2357_);
return v_r_2358_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg___lam__0(lean_object* v_x_2359_){
_start:
{
lean_inc(v_x_2359_);
return v_x_2359_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg___lam__0___boxed(lean_object* v_x_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_noConfusionEnum___redArg___lam__0(v_x_2360_);
lean_dec(v_x_2360_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg(lean_object* v_inst_2363_, lean_object* v_f_2364_, lean_object* v_x_2365_, lean_object* v_y_2366_){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___f_2370_; 
lean_inc(v_f_2364_);
v___x_2367_ = lean_apply_1(v_f_2364_, v_x_2365_);
v___x_2368_ = lean_apply_1(v_f_2364_, v_y_2366_);
v___x_2369_ = lean_apply_2(v_inst_2363_, v___x_2367_, v___x_2368_);
v___f_2370_ = ((lean_object*)(l_noConfusionEnum___redArg___closed__0));
return v___f_2370_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum(lean_object* v_00_u03b1_2371_, lean_object* v_00_u03b2_2372_, lean_object* v_inst_2373_, lean_object* v_f_2374_, lean_object* v_P_2375_, lean_object* v_x_2376_, lean_object* v_y_2377_, lean_object* v_h_2378_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___f_2382_; 
lean_inc(v_f_2374_);
v___x_2379_ = lean_apply_1(v_f_2374_, v_x_2376_);
v___x_2380_ = lean_apply_1(v_f_2374_, v_y_2377_);
v___x_2381_ = lean_apply_2(v_inst_2373_, v___x_2379_, v___x_2380_);
v___f_2382_ = ((lean_object*)(l_noConfusionEnum___redArg___closed__0));
return v___f_2382_;
}
}
static lean_object* _init_l_instInhabitedProp(void){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_box(0);
return v___x_2383_;
}
}
static lean_object* _init_l_instInhabitedNonScalar_default(void){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = lean_unsigned_to_nat(0u);
return v___x_2384_;
}
}
static lean_object* _init_l_instInhabitedNonScalar(void){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = lean_unsigned_to_nat(0u);
return v___x_2385_;
}
}
static lean_object* _init_l_instInhabitedPNonScalar_default(void){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_unsigned_to_nat(0u);
return v___x_2386_;
}
}
static lean_object* _init_l_instInhabitedPNonScalar(void){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_unsigned_to_nat(0u);
return v___x_2387_;
}
}
static lean_object* _init_l_instInhabitedTrue(void){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_box(0);
return v___x_2388_;
}
}
LEAN_EXPORT uint8_t l_Subtype_instBEq___redArg___lam__0(lean_object* v_inst_2389_, lean_object* v_x_2390_, lean_object* v_y_2391_){
_start:
{
lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2392_ = lean_apply_2(v_inst_2389_, v_x_2390_, v_y_2391_);
v___x_2393_ = lean_unbox(v___x_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq___redArg___lam__0___boxed(lean_object* v_inst_2394_, lean_object* v_x_2395_, lean_object* v_y_2396_){
_start:
{
uint8_t v_res_2397_; lean_object* v_r_2398_; 
v_res_2397_ = l_Subtype_instBEq___redArg___lam__0(v_inst_2394_, v_x_2395_, v_y_2396_);
v_r_2398_ = lean_box(v_res_2397_);
return v_r_2398_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq___redArg(lean_object* v_inst_2399_){
_start:
{
lean_object* v___f_2400_; 
v___f_2400_ = lean_alloc_closure((void*)(l_Subtype_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2400_, 0, v_inst_2399_);
return v___f_2400_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq(lean_object* v_00_u03b1_2401_, lean_object* v_p_2402_, lean_object* v_inst_2403_){
_start:
{
lean_object* v___f_2404_; 
v___f_2404_ = lean_alloc_closure((void*)(l_Subtype_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2404_, 0, v_inst_2403_);
return v___f_2404_;
}
}
LEAN_EXPORT uint8_t l_Subtype_instDecidableEq___redArg(lean_object* v_inst_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = lean_apply_2(v_inst_2405_, v_x_2406_, v_x_2407_);
v___x_2409_ = lean_unbox(v___x_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instDecidableEq___redArg___boxed(lean_object* v_inst_2410_, lean_object* v_x_2411_, lean_object* v_x_2412_){
_start:
{
uint8_t v_res_2413_; lean_object* v_r_2414_; 
v_res_2413_ = l_Subtype_instDecidableEq___redArg(v_inst_2410_, v_x_2411_, v_x_2412_);
v_r_2414_ = lean_box(v_res_2413_);
return v_r_2414_;
}
}
LEAN_EXPORT uint8_t l_Subtype_instDecidableEq(lean_object* v_00_u03b1_2415_, lean_object* v_p_2416_, lean_object* v_inst_2417_, lean_object* v_x_2418_, lean_object* v_x_2419_){
_start:
{
lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = lean_apply_2(v_inst_2417_, v_x_2418_, v_x_2419_);
v___x_2421_ = lean_unbox(v___x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instDecidableEq___boxed(lean_object* v_00_u03b1_2422_, lean_object* v_p_2423_, lean_object* v_inst_2424_, lean_object* v_x_2425_, lean_object* v_x_2426_){
_start:
{
uint8_t v_res_2427_; lean_object* v_r_2428_; 
v_res_2427_ = l_Subtype_instDecidableEq(v_00_u03b1_2422_, v_p_2423_, v_inst_2424_, v_x_2425_, v_x_2426_);
v_r_2428_ = lean_box(v_res_2427_);
return v_r_2428_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedLeft___redArg(lean_object* v_inst_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_inst_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedLeft(lean_object* v_00_u03b1_2431_, lean_object* v_00_u03b2_2432_, lean_object* v_inst_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_inst_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedRight___redArg(lean_object* v_inst_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2436_, 0, v_inst_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedRight(lean_object* v_00_u03b1_2437_, lean_object* v_00_u03b2_2438_, lean_object* v_inst_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2440_, 0, v_inst_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum_decEq___redArg(lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_x_2443_, lean_object* v_x_2444_){
_start:
{
if (lean_obj_tag(v_x_2443_) == 0)
{
lean_dec_ref(v_inst_2442_);
if (lean_obj_tag(v_x_2444_) == 0)
{
lean_object* v_val_2445_; lean_object* v_val_2446_; lean_object* v___x_2447_; uint8_t v___x_2448_; 
v_val_2445_ = lean_ctor_get(v_x_2443_, 0);
lean_inc(v_val_2445_);
lean_dec_ref(v_x_2443_);
v_val_2446_ = lean_ctor_get(v_x_2444_, 0);
lean_inc(v_val_2446_);
lean_dec_ref(v_x_2444_);
v___x_2447_ = lean_apply_2(v_inst_2441_, v_val_2445_, v_val_2446_);
v___x_2448_ = lean_unbox(v___x_2447_);
return v___x_2448_;
}
else
{
uint8_t v___x_2449_; 
lean_dec_ref(v_x_2444_);
lean_dec_ref(v_x_2443_);
lean_dec_ref(v_inst_2441_);
v___x_2449_ = 0;
return v___x_2449_;
}
}
else
{
lean_dec_ref(v_inst_2441_);
if (lean_obj_tag(v_x_2444_) == 0)
{
uint8_t v___x_2450_; 
lean_dec_ref(v_x_2444_);
lean_dec_ref(v_x_2443_);
lean_dec_ref(v_inst_2442_);
v___x_2450_ = 0;
return v___x_2450_;
}
else
{
lean_object* v_val_2451_; lean_object* v_val_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v_val_2451_ = lean_ctor_get(v_x_2443_, 0);
lean_inc(v_val_2451_);
lean_dec_ref(v_x_2443_);
v_val_2452_ = lean_ctor_get(v_x_2444_, 0);
lean_inc(v_val_2452_);
lean_dec_ref(v_x_2444_);
v___x_2453_ = lean_apply_2(v_inst_2442_, v_val_2451_, v_val_2452_);
v___x_2454_ = lean_unbox(v___x_2453_);
return v___x_2454_;
}
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum_decEq___redArg___boxed(lean_object* v_inst_2455_, lean_object* v_inst_2456_, lean_object* v_x_2457_, lean_object* v_x_2458_){
_start:
{
uint8_t v_res_2459_; lean_object* v_r_2460_; 
v_res_2459_ = l_instDecidableEqSum_decEq___redArg(v_inst_2455_, v_inst_2456_, v_x_2457_, v_x_2458_);
v_r_2460_ = lean_box(v_res_2459_);
return v_r_2460_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum_decEq(lean_object* v_00_u03b1_2461_, lean_object* v_00_u03b2_2462_, lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_x_2465_, lean_object* v_x_2466_){
_start:
{
uint8_t v___x_2467_; 
v___x_2467_ = l_instDecidableEqSum_decEq___redArg(v_inst_2463_, v_inst_2464_, v_x_2465_, v_x_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum_decEq___boxed(lean_object* v_00_u03b1_2468_, lean_object* v_00_u03b2_2469_, lean_object* v_inst_2470_, lean_object* v_inst_2471_, lean_object* v_x_2472_, lean_object* v_x_2473_){
_start:
{
uint8_t v_res_2474_; lean_object* v_r_2475_; 
v_res_2474_ = l_instDecidableEqSum_decEq(v_00_u03b1_2468_, v_00_u03b2_2469_, v_inst_2470_, v_inst_2471_, v_x_2472_, v_x_2473_);
v_r_2475_ = lean_box(v_res_2474_);
return v_r_2475_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum___redArg(lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_x_2478_, lean_object* v_x_2479_){
_start:
{
uint8_t v___x_2480_; 
v___x_2480_ = l_instDecidableEqSum_decEq___redArg(v_inst_2476_, v_inst_2477_, v_x_2478_, v_x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum___redArg___boxed(lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_x_2483_, lean_object* v_x_2484_){
_start:
{
uint8_t v_res_2485_; lean_object* v_r_2486_; 
v_res_2485_ = l_instDecidableEqSum___redArg(v_inst_2481_, v_inst_2482_, v_x_2483_, v_x_2484_);
v_r_2486_ = lean_box(v_res_2485_);
return v_r_2486_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum(lean_object* v_00_u03b1_2487_, lean_object* v_00_u03b2_2488_, lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_x_2491_, lean_object* v_x_2492_){
_start:
{
uint8_t v___x_2493_; 
v___x_2493_ = l_instDecidableEqSum_decEq___redArg(v_inst_2489_, v_inst_2490_, v_x_2491_, v_x_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum___boxed(lean_object* v_00_u03b1_2494_, lean_object* v_00_u03b2_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_x_2498_, lean_object* v_x_2499_){
_start:
{
uint8_t v_res_2500_; lean_object* v_r_2501_; 
v_res_2500_ = l_instDecidableEqSum(v_00_u03b1_2494_, v_00_u03b2_2495_, v_inst_2496_, v_inst_2497_, v_x_2498_, v_x_2499_);
v_r_2501_ = lean_box(v_res_2500_);
return v_r_2501_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedProd___redArg(lean_object* v_inst_2502_, lean_object* v_inst_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2504_, 0, v_inst_2502_);
lean_ctor_set(v___x_2504_, 1, v_inst_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedProd(lean_object* v_00_u03b1_2505_, lean_object* v_00_u03b2_2506_, lean_object* v_inst_2507_, lean_object* v_inst_2508_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v_inst_2507_);
lean_ctor_set(v___x_2509_, 1, v_inst_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedMProd___redArg(lean_object* v_inst_2510_, lean_object* v_inst_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v_inst_2510_);
lean_ctor_set(v___x_2512_, 1, v_inst_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedMProd(lean_object* v_00_u03b1_2513_, lean_object* v_00_u03b2_2514_, lean_object* v_inst_2515_, lean_object* v_inst_2516_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_inst_2515_);
lean_ctor_set(v___x_2517_, 1, v_inst_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedPProd___redArg(lean_object* v_inst_2518_, lean_object* v_inst_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v_inst_2518_);
lean_ctor_set(v___x_2520_, 1, v_inst_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedPProd(lean_object* v_00_u03b1_2521_, lean_object* v_00_u03b2_2522_, lean_object* v_inst_2523_, lean_object* v_inst_2524_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2525_, 0, v_inst_2523_);
lean_ctor_set(v___x_2525_, 1, v_inst_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqProd___redArg(lean_object* v_inst_2526_, lean_object* v_inst_2527_, lean_object* v_x_2528_, lean_object* v_x_2529_){
_start:
{
lean_object* v_fst_2530_; lean_object* v_snd_2531_; lean_object* v_fst_2532_; lean_object* v_snd_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v_fst_2530_ = lean_ctor_get(v_x_2528_, 0);
lean_inc(v_fst_2530_);
v_snd_2531_ = lean_ctor_get(v_x_2528_, 1);
lean_inc(v_snd_2531_);
lean_dec_ref(v_x_2528_);
v_fst_2532_ = lean_ctor_get(v_x_2529_, 0);
lean_inc(v_fst_2532_);
v_snd_2533_ = lean_ctor_get(v_x_2529_, 1);
lean_inc(v_snd_2533_);
lean_dec_ref(v_x_2529_);
v___x_2534_ = lean_apply_2(v_inst_2526_, v_fst_2530_, v_fst_2532_);
v___x_2535_ = lean_unbox(v___x_2534_);
if (v___x_2535_ == 0)
{
uint8_t v___x_2536_; 
lean_dec(v_snd_2533_);
lean_dec(v_snd_2531_);
lean_dec_ref(v_inst_2527_);
v___x_2536_ = lean_unbox(v___x_2534_);
return v___x_2536_;
}
else
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = lean_apply_2(v_inst_2527_, v_snd_2531_, v_snd_2533_);
v___x_2538_ = lean_unbox(v___x_2537_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqProd___redArg___boxed(lean_object* v_inst_2539_, lean_object* v_inst_2540_, lean_object* v_x_2541_, lean_object* v_x_2542_){
_start:
{
uint8_t v_res_2543_; lean_object* v_r_2544_; 
v_res_2543_ = l_instDecidableEqProd___redArg(v_inst_2539_, v_inst_2540_, v_x_2541_, v_x_2542_);
v_r_2544_ = lean_box(v_res_2543_);
return v_r_2544_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqProd(lean_object* v_00_u03b1_2545_, lean_object* v_00_u03b2_2546_, lean_object* v_inst_2547_, lean_object* v_inst_2548_, lean_object* v_x_2549_, lean_object* v_x_2550_){
_start:
{
uint8_t v___x_2551_; 
v___x_2551_ = l_instDecidableEqProd___redArg(v_inst_2547_, v_inst_2548_, v_x_2549_, v_x_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqProd___boxed(lean_object* v_00_u03b1_2552_, lean_object* v_00_u03b2_2553_, lean_object* v_inst_2554_, lean_object* v_inst_2555_, lean_object* v_x_2556_, lean_object* v_x_2557_){
_start:
{
uint8_t v_res_2558_; lean_object* v_r_2559_; 
v_res_2558_ = l_instDecidableEqProd(v_00_u03b1_2552_, v_00_u03b2_2553_, v_inst_2554_, v_inst_2555_, v_x_2556_, v_x_2557_);
v_r_2559_ = lean_box(v_res_2558_);
return v_r_2559_;
}
}
LEAN_EXPORT uint8_t l_instBEqProd___redArg___lam__0(lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_x_2562_, lean_object* v_x_2563_){
_start:
{
lean_object* v_fst_2564_; lean_object* v_snd_2565_; lean_object* v_fst_2566_; lean_object* v_snd_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v_fst_2564_ = lean_ctor_get(v_x_2562_, 0);
lean_inc(v_fst_2564_);
v_snd_2565_ = lean_ctor_get(v_x_2562_, 1);
lean_inc(v_snd_2565_);
lean_dec_ref(v_x_2562_);
v_fst_2566_ = lean_ctor_get(v_x_2563_, 0);
lean_inc(v_fst_2566_);
v_snd_2567_ = lean_ctor_get(v_x_2563_, 1);
lean_inc(v_snd_2567_);
lean_dec_ref(v_x_2563_);
v___x_2568_ = lean_apply_2(v_inst_2560_, v_fst_2564_, v_fst_2566_);
v___x_2569_ = lean_unbox(v___x_2568_);
if (v___x_2569_ == 0)
{
uint8_t v___x_2570_; 
lean_dec(v_snd_2567_);
lean_dec(v_snd_2565_);
lean_dec_ref(v_inst_2561_);
v___x_2570_ = lean_unbox(v___x_2568_);
return v___x_2570_;
}
else
{
lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = lean_apply_2(v_inst_2561_, v_snd_2565_, v_snd_2567_);
v___x_2572_ = lean_unbox(v___x_2571_);
return v___x_2572_;
}
}
}
LEAN_EXPORT lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object* v_inst_2573_, lean_object* v_inst_2574_, lean_object* v_x_2575_, lean_object* v_x_2576_){
_start:
{
uint8_t v_res_2577_; lean_object* v_r_2578_; 
v_res_2577_ = l_instBEqProd___redArg___lam__0(v_inst_2573_, v_inst_2574_, v_x_2575_, v_x_2576_);
v_r_2578_ = lean_box(v_res_2577_);
return v_r_2578_;
}
}
LEAN_EXPORT lean_object* l_instBEqProd___redArg(lean_object* v_inst_2579_, lean_object* v_inst_2580_){
_start:
{
lean_object* v___f_2581_; 
v___f_2581_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2581_, 0, v_inst_2579_);
lean_closure_set(v___f_2581_, 1, v_inst_2580_);
return v___f_2581_;
}
}
LEAN_EXPORT lean_object* l_instBEqProd(lean_object* v_00_u03b1_2582_, lean_object* v_00_u03b2_2583_, lean_object* v_inst_2584_, lean_object* v_inst_2585_){
_start:
{
lean_object* v___f_2586_; 
v___f_2586_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2586_, 0, v_inst_2584_);
lean_closure_set(v___f_2586_, 1, v_inst_2585_);
return v___f_2586_;
}
}
LEAN_EXPORT uint8_t l_Prod_lexLtDec___aux__1___redArg(lean_object* v_inst_2587_, lean_object* v_inst_2588_, lean_object* v_inst_2589_, lean_object* v_x_2590_, lean_object* v_x_2591_){
_start:
{
lean_object* v_fst_2592_; lean_object* v_snd_2593_; lean_object* v_fst_2594_; lean_object* v_snd_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v_fst_2592_ = lean_ctor_get(v_x_2590_, 0);
lean_inc(v_fst_2592_);
v_snd_2593_ = lean_ctor_get(v_x_2590_, 1);
lean_inc(v_snd_2593_);
lean_dec_ref(v_x_2590_);
v_fst_2594_ = lean_ctor_get(v_x_2591_, 0);
lean_inc(v_fst_2594_);
v_snd_2595_ = lean_ctor_get(v_x_2591_, 1);
lean_inc(v_snd_2595_);
lean_dec_ref(v_x_2591_);
lean_inc(v_fst_2594_);
lean_inc(v_fst_2592_);
v___x_2596_ = lean_apply_2(v_inst_2588_, v_fst_2592_, v_fst_2594_);
v___x_2597_ = lean_unbox(v___x_2596_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = lean_apply_2(v_inst_2587_, v_fst_2592_, v_fst_2594_);
v___x_2599_ = lean_unbox(v___x_2598_);
if (v___x_2599_ == 0)
{
uint8_t v___x_2600_; 
lean_dec(v_snd_2595_);
lean_dec(v_snd_2593_);
lean_dec_ref(v_inst_2589_);
v___x_2600_ = lean_unbox(v___x_2598_);
return v___x_2600_;
}
else
{
lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2601_ = lean_apply_2(v_inst_2589_, v_snd_2593_, v_snd_2595_);
v___x_2602_ = lean_unbox(v___x_2601_);
return v___x_2602_;
}
}
else
{
uint8_t v___x_2603_; 
lean_dec(v_snd_2595_);
lean_dec(v_fst_2594_);
lean_dec(v_snd_2593_);
lean_dec(v_fst_2592_);
lean_dec_ref(v_inst_2589_);
lean_dec_ref(v_inst_2587_);
v___x_2603_ = lean_unbox(v___x_2596_);
return v___x_2603_;
}
}
}
LEAN_EXPORT lean_object* l_Prod_lexLtDec___aux__1___redArg___boxed(lean_object* v_inst_2604_, lean_object* v_inst_2605_, lean_object* v_inst_2606_, lean_object* v_x_2607_, lean_object* v_x_2608_){
_start:
{
uint8_t v_res_2609_; lean_object* v_r_2610_; 
v_res_2609_ = l_Prod_lexLtDec___aux__1___redArg(v_inst_2604_, v_inst_2605_, v_inst_2606_, v_x_2607_, v_x_2608_);
v_r_2610_ = lean_box(v_res_2609_);
return v_r_2610_;
}
}
LEAN_EXPORT uint8_t l_Prod_lexLtDec___aux__1(lean_object* v_00_u03b1_2611_, lean_object* v_00_u03b2_2612_, lean_object* v_inst_2613_, lean_object* v_inst_2614_, lean_object* v_inst_2615_, lean_object* v_inst_2616_, lean_object* v_inst_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_){
_start:
{
uint8_t v___x_2620_; 
v___x_2620_ = l_Prod_lexLtDec___aux__1___redArg(v_inst_2615_, v_inst_2616_, v_inst_2617_, v_x_2618_, v_x_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Prod_lexLtDec___aux__1___boxed(lean_object* v_00_u03b1_2621_, lean_object* v_00_u03b2_2622_, lean_object* v_inst_2623_, lean_object* v_inst_2624_, lean_object* v_inst_2625_, lean_object* v_inst_2626_, lean_object* v_inst_2627_, lean_object* v_x_2628_, lean_object* v_x_2629_){
_start:
{
uint8_t v_res_2630_; lean_object* v_r_2631_; 
v_res_2630_ = l_Prod_lexLtDec___aux__1(v_00_u03b1_2621_, v_00_u03b2_2622_, v_inst_2623_, v_inst_2624_, v_inst_2625_, v_inst_2626_, v_inst_2627_, v_x_2628_, v_x_2629_);
v_r_2631_ = lean_box(v_res_2630_);
return v_r_2631_;
}
}
LEAN_EXPORT uint8_t l_Prod_lexLtDec___redArg(lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_x_2635_, lean_object* v_x_2636_){
_start:
{
uint8_t v___x_2637_; 
v___x_2637_ = l_Prod_lexLtDec___aux__1___redArg(v_inst_2632_, v_inst_2633_, v_inst_2634_, v_x_2635_, v_x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Prod_lexLtDec___redArg___boxed(lean_object* v_inst_2638_, lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_x_2641_, lean_object* v_x_2642_){
_start:
{
uint8_t v_res_2643_; lean_object* v_r_2644_; 
v_res_2643_ = l_Prod_lexLtDec___redArg(v_inst_2638_, v_inst_2639_, v_inst_2640_, v_x_2641_, v_x_2642_);
v_r_2644_ = lean_box(v_res_2643_);
return v_r_2644_;
}
}
LEAN_EXPORT uint8_t l_Prod_lexLtDec(lean_object* v_00_u03b1_2645_, lean_object* v_00_u03b2_2646_, lean_object* v_inst_2647_, lean_object* v_inst_2648_, lean_object* v_inst_2649_, lean_object* v_inst_2650_, lean_object* v_inst_2651_, lean_object* v_x_2652_, lean_object* v_x_2653_){
_start:
{
uint8_t v___x_2654_; 
v___x_2654_ = l_Prod_lexLtDec___aux__1___redArg(v_inst_2649_, v_inst_2650_, v_inst_2651_, v_x_2652_, v_x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Prod_lexLtDec___boxed(lean_object* v_00_u03b1_2655_, lean_object* v_00_u03b2_2656_, lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_inst_2659_, lean_object* v_inst_2660_, lean_object* v_inst_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_){
_start:
{
uint8_t v_res_2664_; lean_object* v_r_2665_; 
v_res_2664_ = l_Prod_lexLtDec(v_00_u03b1_2655_, v_00_u03b2_2656_, v_inst_2657_, v_inst_2658_, v_inst_2659_, v_inst_2660_, v_inst_2661_, v_x_2662_, v_x_2663_);
v_r_2665_ = lean_box(v_res_2664_);
return v_r_2665_;
}
}
LEAN_EXPORT lean_object* l_Prod_map___redArg(lean_object* v_f_2666_, lean_object* v_g_2667_, lean_object* v_x_2668_){
_start:
{
lean_object* v_fst_2669_; lean_object* v_snd_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2679_; 
v_fst_2669_ = lean_ctor_get(v_x_2668_, 0);
v_snd_2670_ = lean_ctor_get(v_x_2668_, 1);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_x_2668_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2672_ = v_x_2668_;
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_snd_2670_);
lean_inc(v_fst_2669_);
lean_dec(v_x_2668_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2674_ = lean_apply_1(v_f_2666_, v_fst_2669_);
v___x_2675_ = lean_apply_1(v_g_2667_, v_snd_2670_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v___x_2675_);
lean_ctor_set(v___x_2672_, 0, v___x_2674_);
v___x_2677_ = v___x_2672_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_map(lean_object* v_00_u03b1_u2081_2680_, lean_object* v_00_u03b1_u2082_2681_, lean_object* v_00_u03b2_u2081_2682_, lean_object* v_00_u03b2_u2082_2683_, lean_object* v_f_2684_, lean_object* v_g_2685_, lean_object* v_x_2686_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = l_Prod_map___redArg(v_f_2684_, v_g_2685_, v_x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSigma___redArg(lean_object* v_h_u2081_2688_, lean_object* v_h_u2082_2689_, lean_object* v_x_2690_, lean_object* v_x_2691_){
_start:
{
lean_object* v_fst_2692_; lean_object* v_snd_2693_; lean_object* v_fst_2694_; lean_object* v_snd_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v_fst_2692_ = lean_ctor_get(v_x_2690_, 0);
lean_inc(v_fst_2692_);
v_snd_2693_ = lean_ctor_get(v_x_2690_, 1);
lean_inc(v_snd_2693_);
lean_dec_ref(v_x_2690_);
v_fst_2694_ = lean_ctor_get(v_x_2691_, 0);
lean_inc(v_fst_2694_);
v_snd_2695_ = lean_ctor_get(v_x_2691_, 1);
lean_inc(v_snd_2695_);
lean_dec_ref(v_x_2691_);
lean_inc(v_fst_2692_);
v___x_2696_ = lean_apply_2(v_h_u2081_2688_, v_fst_2692_, v_fst_2694_);
v___x_2697_ = lean_unbox(v___x_2696_);
if (v___x_2697_ == 0)
{
uint8_t v___x_2698_; 
lean_dec(v_snd_2695_);
lean_dec(v_snd_2693_);
lean_dec(v_fst_2692_);
lean_dec_ref(v_h_u2082_2689_);
v___x_2698_ = lean_unbox(v___x_2696_);
return v___x_2698_;
}
else
{
lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2699_ = lean_apply_3(v_h_u2082_2689_, v_fst_2692_, v_snd_2693_, v_snd_2695_);
v___x_2700_ = lean_unbox(v___x_2699_);
return v___x_2700_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSigma___redArg___boxed(lean_object* v_h_u2081_2701_, lean_object* v_h_u2082_2702_, lean_object* v_x_2703_, lean_object* v_x_2704_){
_start:
{
uint8_t v_res_2705_; lean_object* v_r_2706_; 
v_res_2705_ = l_instDecidableEqSigma___redArg(v_h_u2081_2701_, v_h_u2082_2702_, v_x_2703_, v_x_2704_);
v_r_2706_ = lean_box(v_res_2705_);
return v_r_2706_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSigma(lean_object* v_00_u03b1_2707_, lean_object* v_00_u03b2_2708_, lean_object* v_h_u2081_2709_, lean_object* v_h_u2082_2710_, lean_object* v_x_2711_, lean_object* v_x_2712_){
_start:
{
uint8_t v___x_2713_; 
v___x_2713_ = l_instDecidableEqSigma___redArg(v_h_u2081_2709_, v_h_u2082_2710_, v_x_2711_, v_x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSigma___boxed(lean_object* v_00_u03b1_2714_, lean_object* v_00_u03b2_2715_, lean_object* v_h_u2081_2716_, lean_object* v_h_u2082_2717_, lean_object* v_x_2718_, lean_object* v_x_2719_){
_start:
{
uint8_t v_res_2720_; lean_object* v_r_2721_; 
v_res_2720_ = l_instDecidableEqSigma(v_00_u03b1_2714_, v_00_u03b2_2715_, v_h_u2081_2716_, v_h_u2082_2717_, v_x_2718_, v_x_2719_);
v_r_2721_ = lean_box(v_res_2720_);
return v_r_2721_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPSigma___redArg(lean_object* v_h_u2081_2722_, lean_object* v_h_u2082_2723_, lean_object* v_x_2724_, lean_object* v_x_2725_){
_start:
{
lean_object* v_fst_2726_; lean_object* v_snd_2727_; lean_object* v_fst_2728_; lean_object* v_snd_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v_fst_2726_ = lean_ctor_get(v_x_2724_, 0);
lean_inc(v_fst_2726_);
v_snd_2727_ = lean_ctor_get(v_x_2724_, 1);
lean_inc(v_snd_2727_);
lean_dec_ref(v_x_2724_);
v_fst_2728_ = lean_ctor_get(v_x_2725_, 0);
lean_inc(v_fst_2728_);
v_snd_2729_ = lean_ctor_get(v_x_2725_, 1);
lean_inc(v_snd_2729_);
lean_dec_ref(v_x_2725_);
lean_inc(v_fst_2726_);
v___x_2730_ = lean_apply_2(v_h_u2081_2722_, v_fst_2726_, v_fst_2728_);
v___x_2731_ = lean_unbox(v___x_2730_);
if (v___x_2731_ == 0)
{
uint8_t v___x_2732_; 
lean_dec(v_snd_2729_);
lean_dec(v_snd_2727_);
lean_dec(v_fst_2726_);
lean_dec_ref(v_h_u2082_2723_);
v___x_2732_ = lean_unbox(v___x_2730_);
return v___x_2732_;
}
else
{
lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2733_ = lean_apply_3(v_h_u2082_2723_, v_fst_2726_, v_snd_2727_, v_snd_2729_);
v___x_2734_ = lean_unbox(v___x_2733_);
return v___x_2734_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPSigma___redArg___boxed(lean_object* v_h_u2081_2735_, lean_object* v_h_u2082_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_){
_start:
{
uint8_t v_res_2739_; lean_object* v_r_2740_; 
v_res_2739_ = l_instDecidableEqPSigma___redArg(v_h_u2081_2735_, v_h_u2082_2736_, v_x_2737_, v_x_2738_);
v_r_2740_ = lean_box(v_res_2739_);
return v_r_2740_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPSigma(lean_object* v_00_u03b1_2741_, lean_object* v_00_u03b2_2742_, lean_object* v_h_u2081_2743_, lean_object* v_h_u2082_2744_, lean_object* v_x_2745_, lean_object* v_x_2746_){
_start:
{
uint8_t v___x_2747_; 
v___x_2747_ = l_instDecidableEqPSigma___redArg(v_h_u2081_2743_, v_h_u2082_2744_, v_x_2745_, v_x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPSigma___boxed(lean_object* v_00_u03b1_2748_, lean_object* v_00_u03b2_2749_, lean_object* v_h_u2081_2750_, lean_object* v_h_u2082_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_){
_start:
{
uint8_t v_res_2754_; lean_object* v_r_2755_; 
v_res_2754_ = l_instDecidableEqPSigma(v_00_u03b1_2748_, v_00_u03b2_2749_, v_h_u2081_2750_, v_h_u2082_2751_, v_x_2752_, v_x_2753_);
v_r_2755_ = lean_box(v_res_2754_);
return v_r_2755_;
}
}
static lean_object* _init_l_instInhabitedPUnit(void){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_box(0);
return v___x_2756_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPUnit(lean_object* v_a_2757_, lean_object* v_b_2758_){
_start:
{
uint8_t v___x_2759_; 
v___x_2759_ = 1;
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPUnit___boxed(lean_object* v_a_2760_, lean_object* v_b_2761_){
_start:
{
uint8_t v_res_2762_; lean_object* v_r_2763_; 
v_res_2762_ = l_instDecidableEqPUnit(v_a_2760_, v_b_2761_);
v_r_2763_ = lean_box(v_res_2762_);
return v_r_2763_;
}
}
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid(lean_object* v_00_u03b1_2764_, lean_object* v_inst_2765_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_box(0);
return v___x_2766_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfIff___redArg(uint8_t v_d_2767_){
_start:
{
return v_d_2767_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___redArg___boxed(lean_object* v_d_2768_){
_start:
{
uint8_t v_d_boxed_2769_; uint8_t v_res_2770_; lean_object* v_r_2771_; 
v_d_boxed_2769_ = lean_unbox(v_d_2768_);
v_res_2770_ = l_instDecidableEqOfIff___redArg(v_d_boxed_2769_);
v_r_2771_ = lean_box(v_res_2770_);
return v_r_2771_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfIff(lean_object* v_p_2772_, lean_object* v_q_2773_, uint8_t v_d_2774_){
_start:
{
return v_d_2774_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___boxed(lean_object* v_p_2775_, lean_object* v_q_2776_, lean_object* v_d_2777_){
_start:
{
uint8_t v_d_boxed_2778_; uint8_t v_res_2779_; lean_object* v_r_2780_; 
v_d_boxed_2778_ = lean_unbox(v_d_2777_);
v_res_2779_ = l_instDecidableEqOfIff(v_p_2775_, v_q_2776_, v_d_boxed_2778_);
v_r_2780_ = lean_box(v_res_2779_);
return v_r_2780_;
}
}
LEAN_EXPORT lean_object* l_Not_elim(lean_object* v_a_2781_, lean_object* v_00_u03b1_2782_, lean_object* v_H1_2783_, lean_object* v_H2_2784_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_And_elim___redArg(lean_object* v_f_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_apply_2(v_f_2785_, lean_box(0), lean_box(0));
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_And_elim(lean_object* v_a_2787_, lean_object* v_b_2788_, lean_object* v_00_u03b1_2789_, lean_object* v_f_2790_, lean_object* v_h_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = lean_apply_2(v_f_2790_, lean_box(0), lean_box(0));
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Iff_elim___redArg(lean_object* v_f_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_apply_2(v_f_2793_, lean_box(0), lean_box(0));
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Iff_elim(lean_object* v_a_2795_, lean_object* v_b_2796_, lean_object* v_00_u03b1_2797_, lean_object* v_f_2798_, lean_object* v_h_2799_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_apply_2(v_f_2798_, lean_box(0), lean_box(0));
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Quot_liftOn___redArg(lean_object* v_q_2801_, lean_object* v_f_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_apply_1(v_f_2802_, v_q_2801_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Quot_liftOn(lean_object* v_00_u03b1_2804_, lean_object* v_00_u03b2_2805_, lean_object* v_r_2806_, lean_object* v_q_2807_, lean_object* v_f_2808_, lean_object* v_c_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_apply_1(v_f_2808_, v_q_2807_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Quot_rec___redArg(lean_object* v_f_2811_, lean_object* v_q_2812_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_apply_1(v_f_2811_, v_q_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Quot_rec(lean_object* v_00_u03b1_2814_, lean_object* v_r_2815_, lean_object* v_motive_2816_, lean_object* v_f_2817_, lean_object* v_h_2818_, lean_object* v_q_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = lean_apply_1(v_f_2817_, v_q_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOn___redArg(lean_object* v_q_2821_, lean_object* v_f_2822_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = lean_apply_1(v_f_2822_, v_q_2821_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOn(lean_object* v_00_u03b1_2824_, lean_object* v_r_2825_, lean_object* v_motive_2826_, lean_object* v_q_2827_, lean_object* v_f_2828_, lean_object* v_h_2829_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = lean_apply_1(v_f_2828_, v_q_2827_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOnSubsingleton___redArg(lean_object* v_q_2831_, lean_object* v_f_2832_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = lean_apply_1(v_f_2832_, v_q_2831_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOnSubsingleton(lean_object* v_00_u03b1_2834_, lean_object* v_r_2835_, lean_object* v_motive_2836_, lean_object* v_h_2837_, lean_object* v_q_2838_, lean_object* v_f_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_apply_1(v_f_2839_, v_q_2838_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Quot_hrecOn___redArg(lean_object* v_q_2841_, lean_object* v_f_2842_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_apply_1(v_f_2842_, v_q_2841_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Quot_hrecOn(lean_object* v_00_u03b1_2844_, lean_object* v_r_2845_, lean_object* v_motive_2846_, lean_object* v_q_2847_, lean_object* v_f_2848_, lean_object* v_c_2849_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = lean_apply_1(v_f_2848_, v_q_2847_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___redArg(lean_object* v_a_2851_){
_start:
{
lean_inc(v_a_2851_);
return v_a_2851_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___redArg___boxed(lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Quotient_mk___redArg(v_a_2852_);
lean_dec(v_a_2852_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk(lean_object* v_00_u03b1_2854_, lean_object* v_s_2855_, lean_object* v_a_2856_){
_start:
{
lean_inc(v_a_2856_);
return v_a_2856_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___boxed(lean_object* v_00_u03b1_2857_, lean_object* v_s_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Quotient_mk(v_00_u03b1_2857_, v_s_2858_, v_a_2859_);
lean_dec(v_a_2859_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___redArg(lean_object* v_a_2861_){
_start:
{
lean_inc(v_a_2861_);
return v_a_2861_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___redArg___boxed(lean_object* v_a_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Quotient_mk_x27___redArg(v_a_2862_);
lean_dec(v_a_2862_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27(lean_object* v_00_u03b1_2864_, lean_object* v_s_2865_, lean_object* v_a_2866_){
_start:
{
lean_inc(v_a_2866_);
return v_a_2866_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___boxed(lean_object* v_00_u03b1_2867_, lean_object* v_s_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Quotient_mk_x27(v_00_u03b1_2867_, v_s_2868_, v_a_2869_);
lean_dec(v_a_2869_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift___redArg(lean_object* v_f_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = lean_apply_1(v_f_2871_, v_a_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift(lean_object* v_00_u03b1_2874_, lean_object* v_00_u03b2_2875_, lean_object* v_s_2876_, lean_object* v_f_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = lean_apply_1(v_f_2877_, v_a_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn___redArg(lean_object* v_q_2881_, lean_object* v_f_2882_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_apply_1(v_f_2882_, v_q_2881_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn(lean_object* v_00_u03b1_2884_, lean_object* v_00_u03b2_2885_, lean_object* v_s_2886_, lean_object* v_q_2887_, lean_object* v_f_2888_, lean_object* v_c_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = lean_apply_1(v_f_2888_, v_q_2887_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Quotient_rec___redArg(lean_object* v_f_2891_, lean_object* v_q_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = lean_apply_1(v_f_2891_, v_q_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Quotient_rec(lean_object* v_00_u03b1_2894_, lean_object* v_s_2895_, lean_object* v_motive_2896_, lean_object* v_f_2897_, lean_object* v_h_2898_, lean_object* v_q_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_apply_1(v_f_2897_, v_q_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOn___redArg(lean_object* v_q_2901_, lean_object* v_f_2902_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_apply_1(v_f_2902_, v_q_2901_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOn(lean_object* v_00_u03b1_2904_, lean_object* v_s_2905_, lean_object* v_motive_2906_, lean_object* v_q_2907_, lean_object* v_f_2908_, lean_object* v_h_2909_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_apply_1(v_f_2908_, v_q_2907_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton___redArg(lean_object* v_q_2911_, lean_object* v_f_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_apply_1(v_f_2912_, v_q_2911_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton(lean_object* v_00_u03b1_2914_, lean_object* v_s_2915_, lean_object* v_motive_2916_, lean_object* v_h_2917_, lean_object* v_q_2918_, lean_object* v_f_2919_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_apply_1(v_f_2919_, v_q_2918_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Quotient_hrecOn___redArg(lean_object* v_q_2921_, lean_object* v_f_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_apply_1(v_f_2922_, v_q_2921_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Quotient_hrecOn(lean_object* v_00_u03b1_2924_, lean_object* v_s_2925_, lean_object* v_motive_2926_, lean_object* v_q_2927_, lean_object* v_f_2928_, lean_object* v_c_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_apply_1(v_f_2928_, v_q_2927_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift_u2082___redArg(lean_object* v_f_2931_, lean_object* v_q_u2081_2932_, lean_object* v_q_u2082_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_apply_2(v_f_2931_, v_q_u2081_2932_, v_q_u2082_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift_u2082(lean_object* v_00_u03b1_2935_, lean_object* v_00_u03b2_2936_, lean_object* v_00_u03c6_2937_, lean_object* v_s_u2081_2938_, lean_object* v_s_u2082_2939_, lean_object* v_f_2940_, lean_object* v_c_2941_, lean_object* v_q_u2081_2942_, lean_object* v_q_u2082_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = lean_apply_2(v_f_2940_, v_q_u2081_2942_, v_q_u2082_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn_u2082___redArg(lean_object* v_q_u2081_2945_, lean_object* v_q_u2082_2946_, lean_object* v_f_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = lean_apply_2(v_f_2947_, v_q_u2081_2945_, v_q_u2082_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn_u2082(lean_object* v_00_u03b1_2949_, lean_object* v_00_u03b2_2950_, lean_object* v_00_u03c6_2951_, lean_object* v_s_u2081_2952_, lean_object* v_s_u2082_2953_, lean_object* v_q_u2081_2954_, lean_object* v_q_u2082_2955_, lean_object* v_f_2956_, lean_object* v_c_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = lean_apply_2(v_f_2956_, v_q_u2081_2954_, v_q_u2082_2955_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton_u2082___redArg(lean_object* v_q_u2081_2959_, lean_object* v_q_u2082_2960_, lean_object* v_g_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_apply_2(v_g_2961_, v_q_u2081_2959_, v_q_u2082_2960_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton_u2082(lean_object* v_00_u03b1_2963_, lean_object* v_00_u03b2_2964_, lean_object* v_s_u2081_2965_, lean_object* v_s_u2082_2966_, lean_object* v_motive_2967_, lean_object* v_s_2968_, lean_object* v_q_u2081_2969_, lean_object* v_q_u2082_2970_, lean_object* v_g_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_apply_2(v_g_2971_, v_q_u2081_2969_, v_q_u2082_2970_);
return v___x_2972_;
}
}
LEAN_EXPORT uint8_t l_Quotient_decidableEq___redArg(lean_object* v_d_2973_, lean_object* v_q_u2081_2974_, lean_object* v_q_u2082_2975_){
_start:
{
lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2976_ = lean_apply_2(v_d_2973_, v_q_u2081_2974_, v_q_u2082_2975_);
v___x_2977_ = lean_unbox(v___x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Quotient_decidableEq___redArg___boxed(lean_object* v_d_2978_, lean_object* v_q_u2081_2979_, lean_object* v_q_u2082_2980_){
_start:
{
uint8_t v_res_2981_; lean_object* v_r_2982_; 
v_res_2981_ = l_Quotient_decidableEq___redArg(v_d_2978_, v_q_u2081_2979_, v_q_u2082_2980_);
v_r_2982_ = lean_box(v_res_2981_);
return v_r_2982_;
}
}
LEAN_EXPORT uint8_t l_Quotient_decidableEq(lean_object* v_00_u03b1_2983_, lean_object* v_s_2984_, lean_object* v_d_2985_, lean_object* v_q_u2081_2986_, lean_object* v_q_u2082_2987_){
_start:
{
lean_object* v___x_2988_; uint8_t v___x_2989_; 
v___x_2988_ = lean_apply_2(v_d_2985_, v_q_u2081_2986_, v_q_u2082_2987_);
v___x_2989_ = lean_unbox(v___x_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Quotient_decidableEq___boxed(lean_object* v_00_u03b1_2990_, lean_object* v_s_2991_, lean_object* v_d_2992_, lean_object* v_q_u2081_2993_, lean_object* v_q_u2082_2994_){
_start:
{
uint8_t v_res_2995_; lean_object* v_r_2996_; 
v_res_2995_ = l_Quotient_decidableEq(v_00_u03b1_2990_, v_s_2991_, v_d_2992_, v_q_u2081_2993_, v_q_u2082_2994_);
v_r_2996_ = lean_box(v_res_2995_);
return v_r_2996_;
}
}
LEAN_EXPORT lean_object* l_Quot_pliftOn___redArg(lean_object* v_q_2997_, lean_object* v_f_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_apply_2(v_f_2998_, v_q_2997_, lean_box(0));
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Quot_pliftOn(lean_object* v_00_u03b2_3000_, lean_object* v_00_u03b1_3001_, lean_object* v_r_3002_, lean_object* v_q_3003_, lean_object* v_f_3004_, lean_object* v_h_3005_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = lean_apply_2(v_f_3004_, v_q_3003_, lean_box(0));
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Quotient_pliftOn___redArg(lean_object* v_q_3007_, lean_object* v_f_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_apply_2(v_f_3008_, v_q_3007_, lean_box(0));
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Quotient_pliftOn(lean_object* v_00_u03b2_3010_, lean_object* v_00_u03b1_3011_, lean_object* v_s_3012_, lean_object* v_q_3013_, lean_object* v_f_3014_, lean_object* v_h_3015_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_apply_2(v_f_3014_, v_q_3013_, lean_box(0));
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Setoid_trivial(lean_object* v_00_u03b1_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_box(0);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___redArg(lean_object* v_x_3019_){
_start:
{
lean_inc(v_x_3019_);
return v_x_3019_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___redArg___boxed(lean_object* v_x_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Squash_mk___redArg(v_x_3020_);
lean_dec(v_x_3020_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk(lean_object* v_00_u03b1_3022_, lean_object* v_x_3023_){
_start:
{
lean_inc(v_x_3023_);
return v_x_3023_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___boxed(lean_object* v_00_u03b1_3024_, lean_object* v_x_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Squash_mk(v_00_u03b1_3024_, v_x_3025_);
lean_dec(v_x_3025_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Squash_lift___redArg(lean_object* v_s_3027_, lean_object* v_f_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_apply_1(v_f_3028_, v_s_3027_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Squash_lift(lean_object* v_00_u03b1_3030_, lean_object* v_00_u03b2_3031_, lean_object* v_inst_3032_, lean_object* v_s_3033_, lean_object* v_f_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_apply_1(v_f_3034_, v_s_3033_);
return v___x_3035_;
}
}
LEAN_EXPORT uint8_t l_Lean_reduceBool(uint8_t v_b_3036_){
_start:
{
return v_b_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_reduceBool___boxed(lean_object* v_b_3037_){
_start:
{
uint8_t v_b_boxed_3038_; uint8_t v_res_3039_; lean_object* v_r_3040_; 
v_b_boxed_3038_ = lean_unbox(v_b_3037_);
v_res_3039_ = l_Lean_reduceBool(v_b_boxed_3038_);
v_r_3040_ = lean_box(v_res_3039_);
return v_r_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_reduceNat(lean_object* v_n_3041_){
_start:
{
lean_inc(v_n_3041_);
return v_n_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_reduceNat___boxed(lean_object* v_n_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_reduceNat(v_n_3042_);
lean_dec(v_n_3042_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___redArg(lean_object* v_x_3044_){
_start:
{
lean_inc(v_x_3044_);
return v_x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___redArg___boxed(lean_object* v_x_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Lean_opaqueId___redArg(v_x_3045_);
lean_dec(v_x_3045_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId(lean_object* v_00_u03b1_3047_, lean_object* v_x_3048_){
_start:
{
lean_inc(v_x_3048_);
return v_x_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___boxed(lean_object* v_00_u03b1_3049_, lean_object* v_x_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_opaqueId(v_00_u03b1_3049_, v_x_3050_);
lean_dec(v_x_3050_);
return v_res_3051_;
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
