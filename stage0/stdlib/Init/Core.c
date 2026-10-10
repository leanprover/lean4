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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Sum_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Sum_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Sum_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Sum_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_PSum_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_PSum_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_PSum_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PSum_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___impl___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___impl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___impl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_return_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultPR_return_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_break_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_break_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
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
uint8_t l_instBEqOption_beq___redArg(lean_object* v_inst_1_, lean_object* v_x_2_, lean_object* v_x_3_){
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
LEAN_EXPORT void l_instBEqOption_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v_x_3_ = stack[2].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_instBEqOption_beq___redArg(v_inst_1_, v_x_2_, v_x_3_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___redArg___boxed(lean_object* v_inst_12_, lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_instBEqOption_beq___redArg(v_inst_12_, v_x_13_, v_x_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
uint8_t l_instBEqOption_beq(lean_object* v_00_u03b1_17_, lean_object* v_inst_18_, lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = l_instBEqOption_beq___redArg(v_inst_18_, v_x_19_, v_x_20_);
return v___x_21_;
}
}
LEAN_EXPORT void l_instBEqOption_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_18_ = stack[1].m_obj;
lean_object* v_x_19_ = stack[2].m_obj;
lean_object* v_x_20_ = stack[3].m_obj;
uint8_t v_res_22_;
v_res_22_ = l_instBEqOption_beq(lean_box(0), v_inst_18_, v_x_19_, v_x_20_);
stack->m_num = v_res_22_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___boxed(lean_object* v_00_u03b1_23_, lean_object* v_inst_24_, lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_instBEqOption_beq(v_00_u03b1_23_, v_inst_24_, v_x_25_, v_x_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l_instBEqOption___redArg(lean_object* v_inst_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_alloc_closure((void*)(l_instBEqOption_beq___boxed), 4, 2);
lean_closure_set(v___x_30_, 0, lean_box(0));
lean_closure_set(v___x_30_, 1, v_inst_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_instBEqOption(lean_object* v_00_u03b1_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_alloc_closure((void*)(l_instBEqOption_beq___boxed), 4, 2);
lean_closure_set(v___x_33_, 0, lean_box(0));
lean_closure_set(v___x_33_, 1, v_inst_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_inline___redArg(lean_object* v_a_34_){
_start:
{
lean_inc(v_a_34_);
return v_a_34_;
}
}
LEAN_EXPORT lean_object* l_inline___redArg___boxed(lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_inline___redArg(v_a_35_);
lean_dec(v_a_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_inline(lean_object* v_00_u03b1_37_, lean_object* v_a_38_){
_start:
{
lean_inc(v_a_38_);
return v_a_38_;
}
}
LEAN_EXPORT lean_object* l_inline___boxed(lean_object* v_00_u03b1_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_inline(v_00_u03b1_39_, v_a_40_);
lean_dec(v_a_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_eagerReduce___redArg(lean_object* v_a_42_){
_start:
{
lean_inc(v_a_42_);
return v_a_42_;
}
}
LEAN_EXPORT lean_object* l_eagerReduce___redArg___boxed(lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_eagerReduce___redArg(v_a_43_);
lean_dec(v_a_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_eagerReduce(lean_object* v_00_u03b1_45_, lean_object* v_a_46_){
_start:
{
lean_inc(v_a_46_);
return v_a_46_;
}
}
LEAN_EXPORT lean_object* l_eagerReduce___boxed(lean_object* v_00_u03b1_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_eagerReduce(v_00_u03b1_47_, v_a_48_);
lean_dec(v_a_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_flip___redArg(lean_object* v_f_50_, lean_object* v_b_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_apply_2(v_f_50_, v_a_52_, v_b_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_flip(lean_object* v_00_u03b1_54_, lean_object* v_00_u03b2_55_, lean_object* v_00_u03c6_56_, lean_object* v_f_57_, lean_object* v_b_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_apply_2(v_f_57_, v_a_59_, v_b_58_);
return v___x_60_;
}
}
uint8_t l_instDecidableEqEmpty___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_instDecidableEqEmpty___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_62_;
v_res_62_ = l_instDecidableEqEmpty___redArg();
stack->m_num = v_res_62_;
}
LEAN_EXPORT lean_object* l_instDecidableEqEmpty___redArg___boxed(lean_object* v___dummy_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_instDecidableEqEmpty___redArg();
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
uint8_t l_instDecidableEqEmpty(uint8_t v_a_66_, uint8_t v_b_67_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_instDecidableEqEmpty_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_66_ = stack[0].m_num;
uint8_t v_b_67_ = stack[1].m_num;
uint8_t v_res_68_;
v_res_68_ = l_instDecidableEqEmpty(v_a_66_, v_b_67_);
stack->m_num = v_res_68_;
}
LEAN_EXPORT lean_object* l_instDecidableEqEmpty___boxed(lean_object* v_a_69_, lean_object* v_b_70_){
_start:
{
uint8_t v_a_boxed_71_; uint8_t v_b_boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_a_boxed_71_ = lean_unbox(v_a_69_);
v_b_boxed_72_ = lean_unbox(v_b_70_);
v_res_73_ = l_instDecidableEqEmpty(v_a_boxed_71_, v_b_boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
uint8_t l_instDecidableEqPEmpty___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_instDecidableEqPEmpty___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_76_;
v_res_76_ = l_instDecidableEqPEmpty___redArg();
stack->m_num = v_res_76_;
}
LEAN_EXPORT lean_object* l_instDecidableEqPEmpty___redArg___boxed(lean_object* v___dummy_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_instDecidableEqPEmpty___redArg();
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
uint8_t l_instDecidableEqPEmpty(uint8_t v_a_80_, uint8_t v_b_81_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_instDecidableEqPEmpty_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_80_ = stack[0].m_num;
uint8_t v_b_81_ = stack[1].m_num;
uint8_t v_res_82_;
v_res_82_ = l_instDecidableEqPEmpty(v_a_80_, v_b_81_);
stack->m_num = v_res_82_;
}
LEAN_EXPORT lean_object* l_instDecidableEqPEmpty___boxed(lean_object* v_a_83_, lean_object* v_b_84_){
_start:
{
uint8_t v_a_boxed_85_; uint8_t v_b_boxed_86_; uint8_t v_res_87_; lean_object* v_r_88_; 
v_a_boxed_85_ = lean_unbox(v_a_83_);
v_b_boxed_86_ = lean_unbox(v_b_84_);
v_res_87_ = l_instDecidableEqPEmpty(v_a_boxed_85_, v_b_boxed_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT void l_Thunk_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_90_ = stack[1].m_obj;
lean_object* v_res_91_;
v_res_91_ = lean_mk_thunk(v_fn_90_);
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l_Thunk_mk___boxed(lean_object* v_00_u03b1_92_, lean_object* v_fn_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = lean_mk_thunk(v_fn_93_);
return v_res_94_;
}
}
LEAN_EXPORT void l_Thunk_pure_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_96_ = stack[1].m_obj;
lean_object* v_res_97_;
v_res_97_ = lean_thunk_pure(v_a_96_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Thunk_pure___boxed(lean_object* v_00_u03b1_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lean_thunk_pure(v_a_99_);
return v_res_100_;
}
}
LEAN_EXPORT void l_Thunk_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_102_ = stack[1].m_obj;
lean_object* v_res_103_;
v_res_103_ = lean_thunk_get_own(v_x_102_);
stack->m_obj
 = v_res_103_;
}
LEAN_EXPORT lean_object* l_Thunk_get___boxed(lean_object* v_00_u03b1_104_, lean_object* v_x_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lean_thunk_get_own(v_x_105_);
lean_dec_ref(v_x_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Thunk_fnImpl___redArg(lean_object* v_x_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_thunk_get_own(v_x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Thunk_fnImpl___redArg___boxed(lean_object* v_x_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Thunk_fnImpl___redArg(v_x_109_);
lean_dec_ref(v_x_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Thunk_fnImpl(lean_object* v_00_u03b1_111_, lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_thunk_get_own(v_x_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Thunk_fnImpl___boxed(lean_object* v_00_u03b1_115_, lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Thunk_fnImpl(v_00_u03b1_115_, v_x_116_, v_x_117_);
lean_dec_ref(v_x_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Thunk_map___redArg___lam__0(lean_object* v_x_119_, lean_object* v_f_120_, lean_object* v_x_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_thunk_get_own(v_x_119_);
v___x_123_ = lean_apply_1(v_f_120_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Thunk_map___redArg___lam__0___boxed(lean_object* v_x_124_, lean_object* v_f_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Thunk_map___redArg___lam__0(v_x_124_, v_f_125_, v_x_126_);
lean_dec_ref(v_x_124_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Thunk_map___redArg(lean_object* v_f_128_, lean_object* v_x_129_){
_start:
{
lean_object* v___f_130_; lean_object* v___x_131_; 
v___f_130_ = lean_alloc_closure((void*)(l_Thunk_map___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_130_, 0, v_x_129_);
lean_closure_set(v___f_130_, 1, v_f_128_);
v___x_131_ = lean_mk_thunk(v___f_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Thunk_map(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v_f_134_, lean_object* v_x_135_){
_start:
{
lean_object* v___f_136_; lean_object* v___x_137_; 
v___f_136_ = lean_alloc_closure((void*)(l_Thunk_map___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_136_, 0, v_x_135_);
lean_closure_set(v___f_136_, 1, v_f_134_);
v___x_137_ = lean_mk_thunk(v___f_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Thunk_bind___redArg___lam__0(lean_object* v_x_138_, lean_object* v_f_139_, lean_object* v_x_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = lean_thunk_get_own(v_x_138_);
v___x_142_ = lean_apply_1(v_f_139_, v___x_141_);
v___x_143_ = lean_thunk_get_own(v___x_142_);
lean_dec_ref(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Thunk_bind___redArg___lam__0___boxed(lean_object* v_x_144_, lean_object* v_f_145_, lean_object* v_x_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Thunk_bind___redArg___lam__0(v_x_144_, v_f_145_, v_x_146_);
lean_dec_ref(v_x_144_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Thunk_bind___redArg(lean_object* v_x_148_, lean_object* v_f_149_){
_start:
{
lean_object* v___f_150_; lean_object* v___x_151_; 
v___f_150_ = lean_alloc_closure((void*)(l_Thunk_bind___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_150_, 0, v_x_148_);
lean_closure_set(v___f_150_, 1, v_f_149_);
v___x_151_ = lean_mk_thunk(v___f_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Thunk_bind(lean_object* v_00_u03b1_152_, lean_object* v_00_u03b2_153_, lean_object* v_x_154_, lean_object* v_f_155_){
_start:
{
lean_object* v___f_156_; lean_object* v___x_157_; 
v___f_156_ = lean_alloc_closure((void*)(l_Thunk_bind___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_156_, 0, v_x_154_);
lean_closure_set(v___f_156_, 1, v_f_155_);
v___x_157_ = lean_mk_thunk(v___f_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe___redArg___lam__0(lean_object* v_a_158_, lean_object* v_x_159_){
_start:
{
lean_inc(v_a_158_);
return v_a_158_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe___redArg___lam__0___boxed(lean_object* v_a_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_thunkCoe___redArg___lam__0(v_a_160_, v_x_161_);
lean_dec(v_a_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe___redArg___lam__1(lean_object* v_a_163_){
_start:
{
lean_object* v___f_164_; lean_object* v___x_165_; 
v___f_164_ = lean_alloc_closure((void*)(l_thunkCoe___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_164_, 0, v_a_163_);
v___x_165_ = lean_mk_thunk(v___f_164_);
return v___x_165_;
}
}
lean_object* l_thunkCoe___redArg(){
_start:
{
lean_object* v___f_168_; 
v___f_168_ = ((lean_object*)(l_thunkCoe___redArg___closed__0));
return v___f_168_;
}
}
LEAN_EXPORT void l_thunkCoe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_169_;
v_res_169_ = l_thunkCoe___redArg();
stack->m_obj
 = v_res_169_;
}
LEAN_EXPORT lean_object* l_thunkCoe___redArg___boxed(lean_object* v___dummy_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_thunkCoe___redArg();
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_thunkCoe(lean_object* v_00_u03b1_172_){
_start:
{
lean_object* v___f_173_; 
v___f_173_ = ((lean_object*)(l_thunkCoe___redArg___closed__0));
return v___f_173_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedThunk___redArg(lean_object* v_inst_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_thunk_pure(v_inst_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedThunk(lean_object* v_00_u03b1_176_, lean_object* v_inst_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_thunk_pure(v_inst_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn___redArg(lean_object* v_m_179_){
_start:
{
lean_inc(v_m_179_);
return v_m_179_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn___redArg___boxed(lean_object* v_m_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Eq_ndrecOn___redArg(v_m_180_);
lean_dec(v_m_180_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn(lean_object* v_00_u03b1_182_, lean_object* v_a_183_, lean_object* v_motive_184_, lean_object* v_b_185_, lean_object* v_h_186_, lean_object* v_m_187_){
_start:
{
lean_inc(v_m_187_);
return v_m_187_;
}
}
LEAN_EXPORT lean_object* l_Eq_ndrecOn___boxed(lean_object* v_00_u03b1_188_, lean_object* v_a_189_, lean_object* v_motive_190_, lean_object* v_b_191_, lean_object* v_h_192_, lean_object* v_m_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Eq_ndrecOn(v_00_u03b1_188_, v_a_189_, v_motive_190_, v_b_191_, v_h_192_, v_m_193_);
lean_dec(v_m_193_);
lean_dec(v_b_191_);
lean_dec(v_a_189_);
return v_res_194_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__5));
v___x_231_ = l_String_toRawSubstring_x27(v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1(lean_object* v_x_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_term___x3c_x2d_x3e___00__closed__1));
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
lean_object* v_quotContext_255_; lean_object* v_currMacroScope_256_; lean_object* v_ref_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_quotContext_255_ = lean_ctor_get(v_a_249_, 1);
v_currMacroScope_256_ = lean_ctor_get(v_a_249_, 2);
v_ref_257_ = lean_ctor_get(v_a_249_, 5);
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = l_Lean_Syntax_getArg(v_x_248_, v___x_258_);
v___x_260_ = lean_unsigned_to_nat(2u);
v___x_261_ = l_Lean_Syntax_getArg(v_x_248_, v___x_260_);
lean_dec(v_x_248_);
v___x_262_ = 0;
v___x_263_ = l_Lean_SourceInfo_fromRef(v_ref_257_, v___x_262_);
v___x_264_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_265_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6, &l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6_once, _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6);
v___x_266_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7));
lean_inc(v_currMacroScope_256_);
lean_inc(v_quotContext_255_);
v___x_267_ = l_Lean_addMacroScope(v_quotContext_255_, v___x_266_, v_currMacroScope_256_);
v___x_268_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11));
lean_inc_n(v___x_263_, 2);
v___x_269_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_269_, 0, v___x_263_);
lean_ctor_set(v___x_269_, 1, v___x_265_);
lean_ctor_set(v___x_269_, 2, v___x_267_);
lean_ctor_set(v___x_269_, 3, v___x_268_);
v___x_270_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_271_ = l_Lean_Syntax_node2(v___x_263_, v___x_270_, v___x_259_, v___x_261_);
v___x_272_ = l_Lean_Syntax_node2(v___x_263_, v___x_264_, v___x_269_, v___x_271_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_a_250_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___boxed(lean_object* v_x_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1(v_x_274_, v_a_275_, v_a_276_);
lean_dec_ref(v_a_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__1(lean_object* v_x_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_281_);
v___x_285_ = l_Lean_Syntax_isOfKind(v_x_281_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v_x_281_);
v___x_286_ = lean_box(0);
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v_a_283_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l_Lean_Syntax_getArg(v_x_281_, v___x_288_);
v___x_290_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_289_);
v___x_291_ = l_Lean_Syntax_isOfKind(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec(v___x_289_);
lean_dec(v_x_281_);
v___x_292_ = lean_box(0);
v___x_293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_a_283_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = l_Lean_Syntax_getArg(v_x_281_, v___x_294_);
lean_dec(v_x_281_);
v___x_296_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_295_);
v___x_297_ = l_Lean_Syntax_matchesNull(v___x_295_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v___x_295_);
lean_dec(v___x_289_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_a_283_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_ref_302_; uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_300_ = l_Lean_Syntax_getArg(v___x_295_, v___x_288_);
v___x_301_ = l_Lean_Syntax_getArg(v___x_295_, v___x_294_);
lean_dec(v___x_295_);
v_ref_302_ = l_Lean_replaceRef(v___x_289_, v_a_282_);
lean_dec(v___x_289_);
v___x_303_ = 0;
v___x_304_ = l_Lean_SourceInfo_fromRef(v_ref_302_, v___x_303_);
lean_dec(v_ref_302_);
v___x_305_ = ((lean_object*)(l_term___x3c_x2d_x3e___00__closed__1));
v___x_306_ = ((lean_object*)(l_term___x3c_x2d_x3e___00__closed__4));
lean_inc(v___x_304_);
v___x_307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_304_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = l_Lean_Syntax_node3(v___x_304_, v___x_305_, v___x_300_, v___x_307_, v___x_301_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_a_283_);
return v___x_309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__1___boxed(lean_object* v_x_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___aux__Init__Core______unexpand__Iff__1(v_x_310_, v_a_311_, v_a_312_);
lean_dec(v_a_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2194____1(lean_object* v_x_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = ((lean_object*)(l_term___u2194___00__closed__1));
lean_inc(v_x_330_);
v___x_334_ = l_Lean_Syntax_isOfKind(v_x_330_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_x_330_);
v___x_335_ = lean_box(1);
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_a_332_);
return v___x_336_;
}
else
{
lean_object* v_quotContext_337_; lean_object* v_currMacroScope_338_; lean_object* v_ref_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_quotContext_337_ = lean_ctor_get(v_a_331_, 1);
v_currMacroScope_338_ = lean_ctor_get(v_a_331_, 2);
v_ref_339_ = lean_ctor_get(v_a_331_, 5);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = l_Lean_Syntax_getArg(v_x_330_, v___x_340_);
v___x_342_ = lean_unsigned_to_nat(2u);
v___x_343_ = l_Lean_Syntax_getArg(v_x_330_, v___x_342_);
lean_dec(v_x_330_);
v___x_344_ = 0;
v___x_345_ = l_Lean_SourceInfo_fromRef(v_ref_339_, v___x_344_);
v___x_346_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_347_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6, &l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6_once, _init_l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__6);
v___x_348_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__7));
lean_inc(v_currMacroScope_338_);
lean_inc(v_quotContext_337_);
v___x_349_ = l_Lean_addMacroScope(v_quotContext_337_, v___x_348_, v_currMacroScope_338_);
v___x_350_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__11));
lean_inc_n(v___x_345_, 2);
v___x_351_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_351_, 0, v___x_345_);
lean_ctor_set(v___x_351_, 1, v___x_347_);
lean_ctor_set(v___x_351_, 2, v___x_349_);
lean_ctor_set(v___x_351_, 3, v___x_350_);
v___x_352_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_353_ = l_Lean_Syntax_node2(v___x_345_, v___x_352_, v___x_341_, v___x_343_);
v___x_354_ = l_Lean_Syntax_node2(v___x_345_, v___x_346_, v___x_351_, v___x_353_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v_a_332_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2194____1___boxed(lean_object* v_x_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___aux__Init__Core______macroRules__term___u2194____1(v_x_356_, v_a_357_, v_a_358_);
lean_dec_ref(v_a_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__2(lean_object* v_x_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
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
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = l_Lean_Syntax_getArg(v_x_360_, v___x_367_);
v___x_369_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_368_);
v___x_370_ = l_Lean_Syntax_isOfKind(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v___x_368_);
lean_dec(v_x_360_);
v___x_371_ = lean_box(0);
v___x_372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_a_362_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = l_Lean_Syntax_getArg(v_x_360_, v___x_373_);
lean_dec(v_x_360_);
v___x_375_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_374_);
v___x_376_ = l_Lean_Syntax_matchesNull(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v___x_374_);
lean_dec(v___x_368_);
v___x_377_ = lean_box(0);
v___x_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v_a_362_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_ref_381_; uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_379_ = l_Lean_Syntax_getArg(v___x_374_, v___x_367_);
v___x_380_ = l_Lean_Syntax_getArg(v___x_374_, v___x_373_);
lean_dec(v___x_374_);
v_ref_381_ = l_Lean_replaceRef(v___x_368_, v_a_361_);
lean_dec(v___x_368_);
v___x_382_ = 0;
v___x_383_ = l_Lean_SourceInfo_fromRef(v_ref_381_, v___x_382_);
lean_dec(v_ref_381_);
v___x_384_ = ((lean_object*)(l_term___u2194___00__closed__1));
v___x_385_ = ((lean_object*)(l_term___u2194___00__closed__2));
lean_inc(v___x_383_);
v___x_386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_383_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = l_Lean_Syntax_node3(v___x_383_, v___x_384_, v___x_379_, v___x_386_, v___x_380_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_a_362_);
return v___x_388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Iff__2___boxed(lean_object* v_x_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___aux__Init__Core______unexpand__Iff__2(v_x_389_, v_a_390_, v_a_391_);
lean_dec(v_a_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___impl___redArg(lean_object* v_x_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = lean_obj_tag_nat(v_x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___impl___redArg___boxed(lean_object* v_x_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Sum_ctorIdx___impl___redArg(v_x_395_);
lean_dec_ref(v_x_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___impl(lean_object* v_00_u03b1_397_, lean_object* v_00_u03b2_398_, lean_object* v_x_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_obj_tag_nat(v_x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___impl___boxed(lean_object* v_00_u03b1_401_, lean_object* v_00_u03b2_402_, lean_object* v_x_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Sum_ctorIdx___impl(v_00_u03b1_401_, v_00_u03b2_402_, v_x_403_);
lean_dec_ref(v_x_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim___redArg(lean_object* v_t_405_, lean_object* v_k_406_){
_start:
{
lean_object* v_val_407_; lean_object* v___x_408_; 
v_val_407_ = lean_ctor_get(v_t_405_, 0);
lean_inc(v_val_407_);
lean_dec_ref(v_t_405_);
v___x_408_ = lean_apply_1(v_k_406_, v_val_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim(lean_object* v_00_u03b1_409_, lean_object* v_00_u03b2_410_, lean_object* v_motive_411_, lean_object* v_ctorIdx_412_, lean_object* v_t_413_, lean_object* v_h_414_, lean_object* v_k_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Sum_ctorElim___redArg(v_t_413_, v_k_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim___boxed(lean_object* v_00_u03b1_417_, lean_object* v_00_u03b2_418_, lean_object* v_motive_419_, lean_object* v_ctorIdx_420_, lean_object* v_t_421_, lean_object* v_h_422_, lean_object* v_k_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Sum_ctorElim(v_00_u03b1_417_, v_00_u03b2_418_, v_motive_419_, v_ctorIdx_420_, v_t_421_, v_h_422_, v_k_423_);
lean_dec(v_ctorIdx_420_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Sum_inl_elim___redArg(lean_object* v_t_425_, lean_object* v_inl_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Sum_ctorElim___redArg(v_t_425_, v_inl_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Sum_inl_elim(lean_object* v_00_u03b1_428_, lean_object* v_00_u03b2_429_, lean_object* v_motive_430_, lean_object* v_t_431_, lean_object* v_h_432_, lean_object* v_inl_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Sum_ctorElim___redArg(v_t_431_, v_inl_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Sum_inr_elim___redArg(lean_object* v_t_435_, lean_object* v_inr_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Sum_ctorElim___redArg(v_t_435_, v_inr_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Sum_inr_elim(lean_object* v_00_u03b1_438_, lean_object* v_00_u03b2_439_, lean_object* v_motive_440_, lean_object* v_t_441_, lean_object* v_h_442_, lean_object* v_inr_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Sum_ctorElim___redArg(v_t_441_, v_inr_443_);
return v___x_444_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2295____1___closed__1(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__0));
v___x_466_ = l_String_toRawSubstring_x27(v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295____1(lean_object* v_x_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l_term___u2295___00__closed__1));
lean_inc(v_x_480_);
v___x_484_ = l_Lean_Syntax_isOfKind(v_x_480_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v_x_480_);
v___x_485_ = lean_box(1);
v___x_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_a_482_);
return v___x_486_;
}
else
{
lean_object* v_quotContext_487_; lean_object* v_currMacroScope_488_; lean_object* v_ref_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_quotContext_487_ = lean_ctor_get(v_a_481_, 1);
v_currMacroScope_488_ = lean_ctor_get(v_a_481_, 2);
v_ref_489_ = lean_ctor_get(v_a_481_, 5);
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = l_Lean_Syntax_getArg(v_x_480_, v___x_490_);
v___x_492_ = lean_unsigned_to_nat(2u);
v___x_493_ = l_Lean_Syntax_getArg(v_x_480_, v___x_492_);
lean_dec(v_x_480_);
v___x_494_ = 0;
v___x_495_ = l_Lean_SourceInfo_fromRef(v_ref_489_, v___x_494_);
v___x_496_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_497_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2295____1___closed__1, &l___aux__Init__Core______macroRules__term___u2295____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2295____1___closed__1);
v___x_498_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__2));
lean_inc(v_currMacroScope_488_);
lean_inc(v_quotContext_487_);
v___x_499_ = l_Lean_addMacroScope(v_quotContext_487_, v___x_498_, v_currMacroScope_488_);
v___x_500_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__6));
lean_inc_n(v___x_495_, 2);
v___x_501_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_501_, 0, v___x_495_);
lean_ctor_set(v___x_501_, 1, v___x_497_);
lean_ctor_set(v___x_501_, 2, v___x_499_);
lean_ctor_set(v___x_501_, 3, v___x_500_);
v___x_502_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_503_ = l_Lean_Syntax_node2(v___x_495_, v___x_502_, v___x_491_, v___x_493_);
v___x_504_ = l_Lean_Syntax_node2(v___x_495_, v___x_496_, v___x_501_, v___x_503_);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_a_482_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295____1___boxed(lean_object* v_x_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___aux__Init__Core______macroRules__term___u2295____1(v_x_506_, v_a_507_, v_a_508_);
lean_dec_ref(v_a_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Sum__1(lean_object* v_x_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_510_);
v___x_514_ = l_Lean_Syntax_isOfKind(v_x_510_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_x_510_);
v___x_515_ = lean_box(0);
v___x_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v_a_512_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l_Lean_Syntax_getArg(v_x_510_, v___x_517_);
v___x_519_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_518_);
v___x_520_ = l_Lean_Syntax_isOfKind(v___x_518_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v___x_518_);
lean_dec(v_x_510_);
v___x_521_ = lean_box(0);
v___x_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v_a_512_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = l_Lean_Syntax_getArg(v_x_510_, v___x_523_);
lean_dec(v_x_510_);
v___x_525_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_524_);
v___x_526_ = l_Lean_Syntax_matchesNull(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v___x_524_);
lean_dec(v___x_518_);
v___x_527_ = lean_box(0);
v___x_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v_a_512_);
return v___x_528_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_ref_531_; uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_529_ = l_Lean_Syntax_getArg(v___x_524_, v___x_517_);
v___x_530_ = l_Lean_Syntax_getArg(v___x_524_, v___x_523_);
lean_dec(v___x_524_);
v_ref_531_ = l_Lean_replaceRef(v___x_518_, v_a_511_);
lean_dec(v___x_518_);
v___x_532_ = 0;
v___x_533_ = l_Lean_SourceInfo_fromRef(v_ref_531_, v___x_532_);
lean_dec(v_ref_531_);
v___x_534_ = ((lean_object*)(l_term___u2295___00__closed__1));
v___x_535_ = ((lean_object*)(l_term___u2295___00__closed__2));
lean_inc(v___x_533_);
v___x_536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_533_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = l_Lean_Syntax_node3(v___x_533_, v___x_534_, v___x_529_, v___x_536_, v___x_530_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v_a_512_);
return v___x_538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Sum__1___boxed(lean_object* v_x_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___aux__Init__Core______unexpand__Sum__1(v_x_539_, v_a_540_, v_a_541_);
lean_dec(v_a_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___impl___redArg(lean_object* v_x_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_tag_nat(v_x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___impl___redArg___boxed(lean_object* v_x_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_PSum_ctorIdx___impl___redArg(v_x_545_);
lean_dec_ref(v_x_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___impl(lean_object* v_00_u03b1_547_, lean_object* v_00_u03b2_548_, lean_object* v_x_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_tag_nat(v_x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___impl___boxed(lean_object* v_00_u03b1_551_, lean_object* v_00_u03b2_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_PSum_ctorIdx___impl(v_00_u03b1_551_, v_00_u03b2_552_, v_x_553_);
lean_dec_ref(v_x_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim___redArg(lean_object* v_t_555_, lean_object* v_k_556_){
_start:
{
lean_object* v_val_557_; lean_object* v___x_558_; 
v_val_557_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_val_557_);
lean_dec_ref(v_t_555_);
v___x_558_ = lean_apply_1(v_k_556_, v_val_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim(lean_object* v_00_u03b1_559_, lean_object* v_00_u03b2_560_, lean_object* v_motive_561_, lean_object* v_ctorIdx_562_, lean_object* v_t_563_, lean_object* v_h_564_, lean_object* v_k_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_PSum_ctorElim___redArg(v_t_563_, v_k_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim___boxed(lean_object* v_00_u03b1_567_, lean_object* v_00_u03b2_568_, lean_object* v_motive_569_, lean_object* v_ctorIdx_570_, lean_object* v_t_571_, lean_object* v_h_572_, lean_object* v_k_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_PSum_ctorElim(v_00_u03b1_567_, v_00_u03b2_568_, v_motive_569_, v_ctorIdx_570_, v_t_571_, v_h_572_, v_k_573_);
lean_dec(v_ctorIdx_570_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_PSum_inl_elim___redArg(lean_object* v_t_575_, lean_object* v_inl_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_PSum_ctorElim___redArg(v_t_575_, v_inl_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_PSum_inl_elim(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_motive_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_inl_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_PSum_ctorElim___redArg(v_t_581_, v_inl_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_PSum_inr_elim___redArg(lean_object* v_t_585_, lean_object* v_inr_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_PSum_ctorElim___redArg(v_t_585_, v_inr_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_PSum_inr_elim(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_motive_590_, lean_object* v_t_591_, lean_object* v_h_592_, lean_object* v_inr_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_PSum_ctorElim___redArg(v_t_591_, v_inr_593_);
return v___x_594_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0));
v___x_613_ = l_String_toRawSubstring_x27(v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1(lean_object* v_x_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = ((lean_object*)(l_term___u2295_x27___00__closed__1));
lean_inc(v_x_627_);
v___x_631_ = l_Lean_Syntax_isOfKind(v_x_627_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v_x_627_);
v___x_632_ = lean_box(1);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v_a_629_);
return v___x_633_;
}
else
{
lean_object* v_quotContext_634_; lean_object* v_currMacroScope_635_; lean_object* v_ref_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_quotContext_634_ = lean_ctor_get(v_a_628_, 1);
v_currMacroScope_635_ = lean_ctor_get(v_a_628_, 2);
v_ref_636_ = lean_ctor_get(v_a_628_, 5);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = l_Lean_Syntax_getArg(v_x_627_, v___x_637_);
v___x_639_ = lean_unsigned_to_nat(2u);
v___x_640_ = l_Lean_Syntax_getArg(v_x_627_, v___x_639_);
lean_dec(v_x_627_);
v___x_641_ = 0;
v___x_642_ = l_Lean_SourceInfo_fromRef(v_ref_636_, v___x_641_);
v___x_643_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_644_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1, &l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1);
v___x_645_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2));
lean_inc(v_currMacroScope_635_);
lean_inc(v_quotContext_634_);
v___x_646_ = l_Lean_addMacroScope(v_quotContext_634_, v___x_645_, v_currMacroScope_635_);
v___x_647_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__6));
lean_inc_n(v___x_642_, 2);
v___x_648_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_648_, 0, v___x_642_);
lean_ctor_set(v___x_648_, 1, v___x_644_);
lean_ctor_set(v___x_648_, 2, v___x_646_);
lean_ctor_set(v___x_648_, 3, v___x_647_);
v___x_649_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_650_ = l_Lean_Syntax_node2(v___x_642_, v___x_649_, v___x_638_, v___x_640_);
v___x_651_ = l_Lean_Syntax_node2(v___x_642_, v___x_643_, v___x_648_, v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v_a_629_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1___boxed(lean_object* v_x_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___aux__Init__Core______macroRules__term___u2295_x27____1(v_x_653_, v_a_654_, v_a_655_);
lean_dec_ref(v_a_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__PSum__1(lean_object* v_x_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_657_);
v___x_661_ = l_Lean_Syntax_isOfKind(v_x_657_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec(v_x_657_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v_a_659_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = l_Lean_Syntax_getArg(v_x_657_, v___x_664_);
v___x_666_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_665_);
v___x_667_ = l_Lean_Syntax_isOfKind(v___x_665_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
lean_dec(v___x_665_);
lean_dec(v_x_657_);
v___x_668_ = lean_box(0);
v___x_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v_a_659_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = l_Lean_Syntax_getArg(v_x_657_, v___x_670_);
lean_dec(v_x_657_);
v___x_672_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_671_);
v___x_673_ = l_Lean_Syntax_matchesNull(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; 
lean_dec(v___x_671_);
lean_dec(v___x_665_);
v___x_674_ = lean_box(0);
v___x_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v_a_659_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_ref_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_676_ = l_Lean_Syntax_getArg(v___x_671_, v___x_664_);
v___x_677_ = l_Lean_Syntax_getArg(v___x_671_, v___x_670_);
lean_dec(v___x_671_);
v_ref_678_ = l_Lean_replaceRef(v___x_665_, v_a_658_);
lean_dec(v___x_665_);
v___x_679_ = 0;
v___x_680_ = l_Lean_SourceInfo_fromRef(v_ref_678_, v___x_679_);
lean_dec(v_ref_678_);
v___x_681_ = ((lean_object*)(l_term___u2295_x27___00__closed__1));
v___x_682_ = ((lean_object*)(l_term___u2295_x27___00__closed__2));
lean_inc(v___x_680_);
v___x_683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_680_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = l_Lean_Syntax_node3(v___x_680_, v___x_681_, v___x_676_, v___x_683_, v___x_677_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v_a_659_);
return v___x_685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__PSum__1___boxed(lean_object* v_x_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___aux__Init__Core______unexpand__PSum__1(v_x_686_, v_a_687_, v_a_688_);
lean_dec(v_a_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedLeft___redArg(lean_object* v_inst_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v_inst_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedLeft(lean_object* v_00_u03b1_692_, lean_object* v_00_u03b2_693_, lean_object* v_inst_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v_inst_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedRight___redArg(lean_object* v_inst_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v_inst_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedRight(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_inst_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v_inst_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___impl___redArg(lean_object* v_x_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = lean_obj_tag_nat(v_x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___impl___redArg___boxed(lean_object* v_x_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_ForInStep_ctorIdx___impl___redArg(v_x_704_);
lean_dec_ref(v_x_704_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___impl(lean_object* v_00_u03b1_706_, lean_object* v_x_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_tag_nat(v_x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___impl___boxed(lean_object* v_00_u03b1_709_, lean_object* v_x_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_ForInStep_ctorIdx___impl(v_00_u03b1_709_, v_x_710_);
lean_dec_ref(v_x_710_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim___redArg(lean_object* v_t_712_, lean_object* v_k_713_){
_start:
{
lean_object* v_a_714_; lean_object* v___x_715_; 
v_a_714_ = lean_ctor_get(v_t_712_, 0);
lean_inc(v_a_714_);
lean_dec_ref(v_t_712_);
v___x_715_ = lean_apply_1(v_k_713_, v_a_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim(lean_object* v_00_u03b1_716_, lean_object* v_motive_717_, lean_object* v_ctorIdx_718_, lean_object* v_t_719_, lean_object* v_h_720_, lean_object* v_k_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_ForInStep_ctorElim___redArg(v_t_719_, v_k_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim___boxed(lean_object* v_00_u03b1_723_, lean_object* v_motive_724_, lean_object* v_ctorIdx_725_, lean_object* v_t_726_, lean_object* v_h_727_, lean_object* v_k_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_ForInStep_ctorElim(v_00_u03b1_723_, v_motive_724_, v_ctorIdx_725_, v_t_726_, v_h_727_, v_k_728_);
lean_dec(v_ctorIdx_725_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_done_elim___redArg(lean_object* v_t_730_, lean_object* v_done_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_ForInStep_ctorElim___redArg(v_t_730_, v_done_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_done_elim(lean_object* v_00_u03b1_733_, lean_object* v_motive_734_, lean_object* v_t_735_, lean_object* v_h_736_, lean_object* v_done_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_ForInStep_ctorElim___redArg(v_t_735_, v_done_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_yield_elim___redArg(lean_object* v_t_739_, lean_object* v_yield_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_ForInStep_ctorElim___redArg(v_t_739_, v_yield_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_yield_elim(lean_object* v_00_u03b1_742_, lean_object* v_motive_743_, lean_object* v_t_744_, lean_object* v_h_745_, lean_object* v_yield_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_ForInStep_ctorElim___redArg(v_t_744_, v_yield_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep_default___redArg(lean_object* v_inst_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v_inst_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep_default(lean_object* v_00_u03b1_750_, lean_object* v_inst_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v_inst_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep___redArg(lean_object* v_inst_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v_inst_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep(lean_object* v_a_755_, lean_object* v_inst_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v_inst_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___impl___redArg(lean_object* v_x_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = lean_obj_tag_nat(v_x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___impl___redArg___boxed(lean_object* v_x_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_DoResultPRBC_ctorIdx___impl___redArg(v_x_760_);
lean_dec_ref(v_x_760_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___impl(lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_00_u03c3_764_, lean_object* v_x_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_tag_nat(v_x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___impl___boxed(lean_object* v_00_u03b1_767_, lean_object* v_00_u03b2_768_, lean_object* v_00_u03c3_769_, lean_object* v_x_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_DoResultPRBC_ctorIdx___impl(v_00_u03b1_767_, v_00_u03b2_768_, v_00_u03c3_769_, v_x_770_);
lean_dec_ref(v_x_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim___redArg(lean_object* v_t_772_, lean_object* v_k_773_){
_start:
{
switch(lean_obj_tag(v_t_772_))
{
case 2:
{
lean_object* v_a_774_; lean_object* v___x_775_; 
v_a_774_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v_t_772_, 1);
v___x_775_ = lean_apply_1(v_k_773_, v_a_774_);
return v___x_775_;
}
case 3:
{
lean_object* v_a_776_; lean_object* v___x_777_; 
v_a_776_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v_t_772_, 1);
v___x_777_ = lean_apply_1(v_k_773_, v_a_776_);
return v___x_777_;
}
default: 
{
lean_object* v_a_778_; lean_object* v_a_779_; lean_object* v___x_780_; 
v_a_778_ = lean_ctor_get(v_t_772_, 0);
lean_inc(v_a_778_);
v_a_779_ = lean_ctor_get(v_t_772_, 1);
lean_inc(v_a_779_);
lean_dec_ref(v_t_772_);
v___x_780_ = lean_apply_2(v_k_773_, v_a_778_, v_a_779_);
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim(lean_object* v_00_u03b1_781_, lean_object* v_00_u03b2_782_, lean_object* v_00_u03c3_783_, lean_object* v_motive_784_, lean_object* v_ctorIdx_785_, lean_object* v_t_786_, lean_object* v_h_787_, lean_object* v_k_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_DoResultPRBC_ctorElim___redArg(v_t_786_, v_k_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim___boxed(lean_object* v_00_u03b1_790_, lean_object* v_00_u03b2_791_, lean_object* v_00_u03c3_792_, lean_object* v_motive_793_, lean_object* v_ctorIdx_794_, lean_object* v_t_795_, lean_object* v_h_796_, lean_object* v_k_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_DoResultPRBC_ctorElim(v_00_u03b1_790_, v_00_u03b2_791_, v_00_u03c3_792_, v_motive_793_, v_ctorIdx_794_, v_t_795_, v_h_796_, v_k_797_);
lean_dec(v_ctorIdx_794_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_pure_elim___redArg(lean_object* v_t_799_, lean_object* v_pure_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_DoResultPRBC_ctorElim___redArg(v_t_799_, v_pure_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_pure_elim(lean_object* v_00_u03b1_802_, lean_object* v_00_u03b2_803_, lean_object* v_00_u03c3_804_, lean_object* v_motive_805_, lean_object* v_t_806_, lean_object* v_h_807_, lean_object* v_pure_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_DoResultPRBC_ctorElim___redArg(v_t_806_, v_pure_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_return_elim___redArg(lean_object* v_t_810_, lean_object* v_return_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_DoResultPRBC_ctorElim___redArg(v_t_810_, v_return_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_return_elim(lean_object* v_00_u03b1_813_, lean_object* v_00_u03b2_814_, lean_object* v_00_u03c3_815_, lean_object* v_motive_816_, lean_object* v_t_817_, lean_object* v_h_818_, lean_object* v_return_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_DoResultPRBC_ctorElim___redArg(v_t_817_, v_return_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_break_elim___redArg(lean_object* v_t_821_, lean_object* v_break_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_DoResultPRBC_ctorElim___redArg(v_t_821_, v_break_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_break_elim(lean_object* v_00_u03b1_824_, lean_object* v_00_u03b2_825_, lean_object* v_00_u03c3_826_, lean_object* v_motive_827_, lean_object* v_t_828_, lean_object* v_h_829_, lean_object* v_break_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_DoResultPRBC_ctorElim___redArg(v_t_828_, v_break_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_continue_elim___redArg(lean_object* v_t_832_, lean_object* v_continue_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_DoResultPRBC_ctorElim___redArg(v_t_832_, v_continue_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_continue_elim(lean_object* v_00_u03b1_835_, lean_object* v_00_u03b2_836_, lean_object* v_00_u03c3_837_, lean_object* v_motive_838_, lean_object* v_t_839_, lean_object* v_h_840_, lean_object* v_continue_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_DoResultPRBC_ctorElim___redArg(v_t_839_, v_continue_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___impl___redArg(lean_object* v_x_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = lean_obj_tag_nat(v_x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___impl___redArg___boxed(lean_object* v_x_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_DoResultPR_ctorIdx___impl___redArg(v_x_845_);
lean_dec_ref(v_x_845_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___impl(lean_object* v_00_u03b1_847_, lean_object* v_00_u03b2_848_, lean_object* v_00_u03c3_849_, lean_object* v_x_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = lean_obj_tag_nat(v_x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___impl___boxed(lean_object* v_00_u03b1_852_, lean_object* v_00_u03b2_853_, lean_object* v_00_u03c3_854_, lean_object* v_x_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_DoResultPR_ctorIdx___impl(v_00_u03b1_852_, v_00_u03b2_853_, v_00_u03c3_854_, v_x_855_);
lean_dec_ref(v_x_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___redArg(lean_object* v_t_857_, lean_object* v_k_858_){
_start:
{
lean_object* v_a_859_; lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_859_ = lean_ctor_get(v_t_857_, 0);
lean_inc(v_a_859_);
v_a_860_ = lean_ctor_get(v_t_857_, 1);
lean_inc(v_a_860_);
lean_dec_ref(v_t_857_);
v___x_861_ = lean_apply_2(v_k_858_, v_a_859_, v_a_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim(lean_object* v_00_u03b1_862_, lean_object* v_00_u03b2_863_, lean_object* v_00_u03c3_864_, lean_object* v_motive_865_, lean_object* v_ctorIdx_866_, lean_object* v_t_867_, lean_object* v_h_868_, lean_object* v_k_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_DoResultPR_ctorElim___redArg(v_t_867_, v_k_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___boxed(lean_object* v_00_u03b1_871_, lean_object* v_00_u03b2_872_, lean_object* v_00_u03c3_873_, lean_object* v_motive_874_, lean_object* v_ctorIdx_875_, lean_object* v_t_876_, lean_object* v_h_877_, lean_object* v_k_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_DoResultPR_ctorElim(v_00_u03b1_871_, v_00_u03b2_872_, v_00_u03c3_873_, v_motive_874_, v_ctorIdx_875_, v_t_876_, v_h_877_, v_k_878_);
lean_dec(v_ctorIdx_875_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim___redArg(lean_object* v_t_880_, lean_object* v_pure_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_DoResultPR_ctorElim___redArg(v_t_880_, v_pure_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim(lean_object* v_00_u03b1_883_, lean_object* v_00_u03b2_884_, lean_object* v_00_u03c3_885_, lean_object* v_motive_886_, lean_object* v_t_887_, lean_object* v_h_888_, lean_object* v_pure_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_DoResultPR_ctorElim___redArg(v_t_887_, v_pure_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_return_elim___redArg(lean_object* v_t_891_, lean_object* v_return_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_DoResultPR_ctorElim___redArg(v_t_891_, v_return_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_return_elim(lean_object* v_00_u03b1_894_, lean_object* v_00_u03b2_895_, lean_object* v_00_u03c3_896_, lean_object* v_motive_897_, lean_object* v_t_898_, lean_object* v_h_899_, lean_object* v_return_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_DoResultPR_ctorElim___redArg(v_t_898_, v_return_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___impl___redArg(lean_object* v_x_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = lean_obj_tag_nat(v_x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___impl___redArg___boxed(lean_object* v_x_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_DoResultBC_ctorIdx___impl___redArg(v_x_904_);
lean_dec_ref(v_x_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___impl(lean_object* v_00_u03c3_906_, lean_object* v_x_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_obj_tag_nat(v_x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___impl___boxed(lean_object* v_00_u03c3_909_, lean_object* v_x_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_DoResultBC_ctorIdx___impl(v_00_u03c3_909_, v_x_910_);
lean_dec_ref(v_x_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___redArg(lean_object* v_t_912_, lean_object* v_k_913_){
_start:
{
lean_object* v_a_914_; lean_object* v___x_915_; 
v_a_914_ = lean_ctor_get(v_t_912_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v_t_912_);
v___x_915_ = lean_apply_1(v_k_913_, v_a_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim(lean_object* v_00_u03c3_916_, lean_object* v_motive_917_, lean_object* v_ctorIdx_918_, lean_object* v_t_919_, lean_object* v_h_920_, lean_object* v_k_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_DoResultBC_ctorElim___redArg(v_t_919_, v_k_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___boxed(lean_object* v_00_u03c3_923_, lean_object* v_motive_924_, lean_object* v_ctorIdx_925_, lean_object* v_t_926_, lean_object* v_h_927_, lean_object* v_k_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_DoResultBC_ctorElim(v_00_u03c3_923_, v_motive_924_, v_ctorIdx_925_, v_t_926_, v_h_927_, v_k_928_);
lean_dec(v_ctorIdx_925_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_break_elim___redArg(lean_object* v_t_930_, lean_object* v_break_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_DoResultBC_ctorElim___redArg(v_t_930_, v_break_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_break_elim(lean_object* v_00_u03c3_933_, lean_object* v_motive_934_, lean_object* v_t_935_, lean_object* v_h_936_, lean_object* v_break_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_DoResultBC_ctorElim___redArg(v_t_935_, v_break_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim___redArg(lean_object* v_t_939_, lean_object* v_continue_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_DoResultBC_ctorElim___redArg(v_t_939_, v_continue_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim(lean_object* v_00_u03c3_942_, lean_object* v_motive_943_, lean_object* v_t_944_, lean_object* v_h_945_, lean_object* v_continue_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_DoResultBC_ctorElim___redArg(v_t_944_, v_continue_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___impl___redArg(lean_object* v_x_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = lean_obj_tag_nat(v_x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___impl___redArg___boxed(lean_object* v_x_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_DoResultSBC_ctorIdx___impl___redArg(v_x_950_);
lean_dec_ref(v_x_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___impl(lean_object* v_00_u03b1_952_, lean_object* v_00_u03c3_953_, lean_object* v_x_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = lean_obj_tag_nat(v_x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___impl___boxed(lean_object* v_00_u03b1_956_, lean_object* v_00_u03c3_957_, lean_object* v_x_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_DoResultSBC_ctorIdx___impl(v_00_u03b1_956_, v_00_u03c3_957_, v_x_958_);
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
LEAN_EXPORT void l_Task_pure_0interp(lean_interpreter_value* stack)
{
lean_object* v_get_1898_ = stack[1].m_obj;
lean_object* v_res_1899_;
v_res_1899_ = lean_task_pure(v_get_1898_);
stack->m_obj
 = v_res_1899_;
}
LEAN_EXPORT lean_object* l_Task_pure___boxed(lean_object* v_00_u03b1_1900_, lean_object* v_get_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = lean_task_pure(v_get_1901_);
return v_res_1902_;
}
}
LEAN_EXPORT void l_Task_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1904_ = stack[1].m_obj;
lean_object* v_res_1905_;
v_res_1905_ = lean_task_get_own(v_self_1904_);
stack->m_obj
 = v_res_1905_;
}
LEAN_EXPORT lean_object* l_Task_get___boxed(lean_object* v_00_u03b1_1906_, lean_object* v_self_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = lean_task_get_own(v_self_1907_);
return v_res_1908_;
}
}
static lean_object* _init_l_Task_Priority_default(void){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_unsigned_to_nat(0u);
return v___x_1909_;
}
}
static lean_object* _init_l_Task_Priority_max(void){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_unsigned_to_nat(8u);
return v___x_1910_;
}
}
static lean_object* _init_l_Task_Priority_dedicated(void){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_unsigned_to_nat(9u);
return v___x_1911_;
}
}
LEAN_EXPORT void l_Task_spawn_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_1913_ = stack[1].m_obj;
lean_object* v_prio_1914_ = stack[2].m_obj;
lean_object* v_res_1915_;
v_res_1915_ = lean_task_spawn(v_fn_1913_, v_prio_1914_);
stack->m_obj
 = v_res_1915_;
}
LEAN_EXPORT lean_object* l_Task_spawn___boxed(lean_object* v_00_u03b1_1916_, lean_object* v_fn_1917_, lean_object* v_prio_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = lean_task_spawn(v_fn_1917_, v_prio_1918_);
return v_res_1919_;
}
}
LEAN_EXPORT void l_Task_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1922_ = stack[2].m_obj;
lean_object* v_x_1923_ = stack[3].m_obj;
lean_object* v_prio_1924_ = stack[4].m_obj;
uint8_t v_sync_1925_ = stack[5].m_num;
lean_object* v_res_1926_;
v_res_1926_ = lean_task_map(v_f_1922_, v_x_1923_, v_prio_1924_, v_sync_1925_);
stack->m_obj
 = v_res_1926_;
}
LEAN_EXPORT lean_object* l_Task_map___boxed(lean_object* v_00_u03b1_1927_, lean_object* v_00_u03b2_1928_, lean_object* v_f_1929_, lean_object* v_x_1930_, lean_object* v_prio_1931_, lean_object* v_sync_1932_){
_start:
{
uint8_t v_sync_boxed_1933_; lean_object* v_res_1934_; 
v_sync_boxed_1933_ = lean_unbox(v_sync_1932_);
v_res_1934_ = lean_task_map(v_f_1929_, v_x_1930_, v_prio_1931_, v_sync_boxed_1933_);
return v_res_1934_;
}
}
LEAN_EXPORT void l_Task_bind_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1937_ = stack[2].m_obj;
lean_object* v_f_1938_ = stack[3].m_obj;
lean_object* v_prio_1939_ = stack[4].m_obj;
uint8_t v_sync_1940_ = stack[5].m_num;
lean_object* v_res_1941_;
v_res_1941_ = lean_task_bind(v_x_1937_, v_f_1938_, v_prio_1939_, v_sync_1940_);
stack->m_obj
 = v_res_1941_;
}
LEAN_EXPORT lean_object* l_Task_bind___boxed(lean_object* v_00_u03b1_1942_, lean_object* v_00_u03b2_1943_, lean_object* v_x_1944_, lean_object* v_f_1945_, lean_object* v_prio_1946_, lean_object* v_sync_1947_){
_start:
{
uint8_t v_sync_boxed_1948_; lean_object* v_res_1949_; 
v_sync_boxed_1948_ = lean_unbox(v_sync_1947_);
v_res_1949_ = lean_task_bind(v_x_1944_, v_f_1945_, v_prio_1946_, v_sync_boxed_1948_);
return v_res_1949_;
}
}
LEAN_EXPORT void l_strictOr_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_u2081_1950_ = stack[0].m_num;
uint8_t v_b_u2082_1951_ = stack[1].m_num;
uint8_t v_res_1952_;
v_res_1952_ = lean_strict_or(v_b_u2081_1950_, v_b_u2082_1951_);
stack->m_num = v_res_1952_;
}
LEAN_EXPORT lean_object* l_strictOr___boxed(lean_object* v_b_u2081_1953_, lean_object* v_b_u2082_1954_){
_start:
{
uint8_t v_b_u2081_boxed_1955_; uint8_t v_b_u2082_boxed_1956_; uint8_t v_res_1957_; lean_object* v_r_1958_; 
v_b_u2081_boxed_1955_ = lean_unbox(v_b_u2081_1953_);
v_b_u2082_boxed_1956_ = lean_unbox(v_b_u2082_1954_);
v_res_1957_ = lean_strict_or(v_b_u2081_boxed_1955_, v_b_u2082_boxed_1956_);
v_r_1958_ = lean_box(v_res_1957_);
return v_r_1958_;
}
}
LEAN_EXPORT void l_strictAnd_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_u2081_1959_ = stack[0].m_num;
uint8_t v_b_u2082_1960_ = stack[1].m_num;
uint8_t v_res_1961_;
v_res_1961_ = lean_strict_and(v_b_u2081_1959_, v_b_u2082_1960_);
stack->m_num = v_res_1961_;
}
LEAN_EXPORT lean_object* l_strictAnd___boxed(lean_object* v_b_u2081_1962_, lean_object* v_b_u2082_1963_){
_start:
{
uint8_t v_b_u2081_boxed_1964_; uint8_t v_b_u2082_boxed_1965_; uint8_t v_res_1966_; lean_object* v_r_1967_; 
v_b_u2081_boxed_1964_ = lean_unbox(v_b_u2081_1962_);
v_b_u2082_boxed_1965_ = lean_unbox(v_b_u2082_1963_);
v_res_1966_ = lean_strict_and(v_b_u2081_boxed_1964_, v_b_u2082_boxed_1965_);
v_r_1967_ = lean_box(v_res_1966_);
return v_r_1967_;
}
}
uint8_t l_bne___redArg(lean_object* v_inst_1968_, lean_object* v_a_1969_, lean_object* v_b_1970_){
_start:
{
lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1971_ = lean_apply_2(v_inst_1968_, v_a_1969_, v_b_1970_);
v___x_1972_ = lean_unbox(v___x_1971_);
if (v___x_1972_ == 0)
{
uint8_t v___x_1973_; 
v___x_1973_ = 1;
return v___x_1973_;
}
else
{
uint8_t v___x_1974_; 
v___x_1974_ = 0;
return v___x_1974_;
}
}
}
LEAN_EXPORT void l_bne___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1968_ = stack[0].m_obj;
lean_object* v_a_1969_ = stack[1].m_obj;
lean_object* v_b_1970_ = stack[2].m_obj;
uint8_t v_res_1975_;
v_res_1975_ = l_bne___redArg(v_inst_1968_, v_a_1969_, v_b_1970_);
stack->m_num = v_res_1975_;
}
LEAN_EXPORT lean_object* l_bne___redArg___boxed(lean_object* v_inst_1976_, lean_object* v_a_1977_, lean_object* v_b_1978_){
_start:
{
uint8_t v_res_1979_; lean_object* v_r_1980_; 
v_res_1979_ = l_bne___redArg(v_inst_1976_, v_a_1977_, v_b_1978_);
v_r_1980_ = lean_box(v_res_1979_);
return v_r_1980_;
}
}
uint8_t l_bne(lean_object* v_00_u03b1_1981_, lean_object* v_inst_1982_, lean_object* v_a_1983_, lean_object* v_b_1984_){
_start:
{
lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1985_ = lean_apply_2(v_inst_1982_, v_a_1983_, v_b_1984_);
v___x_1986_ = lean_unbox(v___x_1985_);
if (v___x_1986_ == 0)
{
uint8_t v___x_1987_; 
v___x_1987_ = 1;
return v___x_1987_;
}
else
{
uint8_t v___x_1988_; 
v___x_1988_ = 0;
return v___x_1988_;
}
}
}
LEAN_EXPORT void l_bne_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1982_ = stack[1].m_obj;
lean_object* v_a_1983_ = stack[2].m_obj;
lean_object* v_b_1984_ = stack[3].m_obj;
uint8_t v_res_1989_;
v_res_1989_ = l_bne(lean_box(0), v_inst_1982_, v_a_1983_, v_b_1984_);
stack->m_num = v_res_1989_;
}
LEAN_EXPORT lean_object* l_bne___boxed(lean_object* v_00_u03b1_1990_, lean_object* v_inst_1991_, lean_object* v_a_1992_, lean_object* v_b_1993_){
_start:
{
uint8_t v_res_1994_; lean_object* v_r_1995_; 
v_res_1994_ = l_bne(v_00_u03b1_1990_, v_inst_1991_, v_a_1992_, v_b_1993_);
v_r_1995_ = lean_box(v_res_1994_);
return v_r_1995_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0));
v___x_2014_ = l_String_toRawSubstring_x27(v___x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1(lean_object* v_x_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
lean_inc(v_x_2023_);
v___x_2027_ = l_Lean_Syntax_isOfKind(v_x_2023_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_dec(v_x_2023_);
v___x_2028_ = lean_box(1);
v___x_2029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
lean_ctor_set(v___x_2029_, 1, v_a_2025_);
return v___x_2029_;
}
else
{
lean_object* v_quotContext_2030_; lean_object* v_currMacroScope_2031_; lean_object* v_ref_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_quotContext_2030_ = lean_ctor_get(v_a_2024_, 1);
v_currMacroScope_2031_ = lean_ctor_get(v_a_2024_, 2);
v_ref_2032_ = lean_ctor_get(v_a_2024_, 5);
v___x_2033_ = lean_unsigned_to_nat(0u);
v___x_2034_ = l_Lean_Syntax_getArg(v_x_2023_, v___x_2033_);
v___x_2035_ = lean_unsigned_to_nat(2u);
v___x_2036_ = l_Lean_Syntax_getArg(v_x_2023_, v___x_2035_);
lean_dec(v_x_2023_);
v___x_2037_ = 0;
v___x_2038_ = l_Lean_SourceInfo_fromRef(v_ref_2032_, v___x_2037_);
v___x_2039_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_2040_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1, &l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1);
v___x_2041_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2));
lean_inc(v_currMacroScope_2031_);
lean_inc(v_quotContext_2030_);
v___x_2042_ = l_Lean_addMacroScope(v_quotContext_2030_, v___x_2041_, v_currMacroScope_2031_);
v___x_2043_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4));
lean_inc_n(v___x_2038_, 2);
v___x_2044_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2038_);
lean_ctor_set(v___x_2044_, 1, v___x_2040_);
lean_ctor_set(v___x_2044_, 2, v___x_2042_);
lean_ctor_set(v___x_2044_, 3, v___x_2043_);
v___x_2045_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_2046_ = l_Lean_Syntax_node2(v___x_2038_, v___x_2045_, v___x_2034_, v___x_2036_);
v___x_2047_ = l_Lean_Syntax_node2(v___x_2038_, v___x_2039_, v___x_2044_, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
lean_ctor_set(v___x_2048_, 1, v_a_2025_);
return v___x_2048_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1___boxed(lean_object* v_x_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l___aux__Init__Core______macroRules__term___x21_x3d____1(v_x_2049_, v_a_2050_, v_a_2051_);
lean_dec_ref(v_a_2050_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__bne__1(lean_object* v_x_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2056_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_2053_);
v___x_2057_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec(v_x_2053_);
v___x_2058_ = lean_box(0);
v___x_2059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v_a_2055_);
return v___x_2059_;
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = l_Lean_Syntax_getArg(v_x_2053_, v___x_2060_);
v___x_2062_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_2061_);
v___x_2063_ = l_Lean_Syntax_isOfKind(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_dec(v___x_2061_);
lean_dec(v_x_2053_);
v___x_2064_ = lean_box(0);
v___x_2065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
lean_ctor_set(v___x_2065_, 1, v_a_2055_);
return v___x_2065_;
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2066_ = lean_unsigned_to_nat(1u);
v___x_2067_ = l_Lean_Syntax_getArg(v_x_2053_, v___x_2066_);
lean_dec(v_x_2053_);
v___x_2068_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2067_);
v___x_2069_ = l_Lean_Syntax_matchesNull(v___x_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
lean_dec(v___x_2067_);
lean_dec(v___x_2061_);
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v_a_2055_);
return v___x_2071_;
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v_ref_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2072_ = l_Lean_Syntax_getArg(v___x_2067_, v___x_2060_);
v___x_2073_ = l_Lean_Syntax_getArg(v___x_2067_, v___x_2066_);
lean_dec(v___x_2067_);
v_ref_2074_ = l_Lean_replaceRef(v___x_2061_, v_a_2054_);
lean_dec(v___x_2061_);
v___x_2075_ = 0;
v___x_2076_ = l_Lean_SourceInfo_fromRef(v_ref_2074_, v___x_2075_);
lean_dec(v_ref_2074_);
v___x_2077_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
v___x_2078_ = ((lean_object*)(l_term___x21_x3d___00__closed__2));
lean_inc(v___x_2076_);
v___x_2079_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2076_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = l_Lean_Syntax_node3(v___x_2076_, v___x_2077_, v___x_2072_, v___x_2079_, v___x_2073_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v_a_2055_);
return v___x_2081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__bne__1___boxed(lean_object* v_x_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l___aux__Init__Core______unexpand__bne__1(v_x_2082_, v_a_2083_, v_a_2084_);
lean_dec(v_a_2083_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2(lean_object* v_x_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
lean_inc(v_x_2093_);
v___x_2097_ = l_Lean_Syntax_isOfKind(v_x_2093_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec(v_x_2093_);
v___x_2098_ = lean_box(1);
v___x_2099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v_a_2095_);
return v___x_2099_;
}
else
{
lean_object* v_quotContext_2100_; lean_object* v_currMacroScope_2101_; lean_object* v_ref_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_quotContext_2100_ = lean_ctor_get(v_a_2094_, 1);
v_currMacroScope_2101_ = lean_ctor_get(v_a_2094_, 2);
v_ref_2102_ = lean_ctor_get(v_a_2094_, 5);
v___x_2103_ = lean_unsigned_to_nat(0u);
v___x_2104_ = l_Lean_Syntax_getArg(v_x_2093_, v___x_2103_);
v___x_2105_ = lean_unsigned_to_nat(2u);
v___x_2106_ = l_Lean_Syntax_getArg(v_x_2093_, v___x_2105_);
lean_dec(v_x_2093_);
v___x_2107_ = 0;
v___x_2108_ = l_Lean_SourceInfo_fromRef(v_ref_2102_, v___x_2107_);
v___x_2109_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1));
v___x_2110_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__2));
lean_inc_n(v___x_2108_, 2);
v___x_2111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2108_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1, &l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1);
v___x_2113_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2));
lean_inc(v_currMacroScope_2101_);
lean_inc(v_quotContext_2100_);
v___x_2114_ = l_Lean_addMacroScope(v_quotContext_2100_, v___x_2113_, v_currMacroScope_2101_);
v___x_2115_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4));
v___x_2116_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2108_);
lean_ctor_set(v___x_2116_, 1, v___x_2112_);
lean_ctor_set(v___x_2116_, 2, v___x_2114_);
lean_ctor_set(v___x_2116_, 3, v___x_2115_);
v___x_2117_ = l_Lean_Syntax_node4(v___x_2108_, v___x_2109_, v___x_2111_, v___x_2116_, v___x_2104_, v___x_2106_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v_a_2095_);
return v___x_2118_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2___boxed(lean_object* v_x_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l___aux__Init__Core______macroRules__term___x21_x3d____2(v_x_2119_, v_a_2120_, v_a_2121_);
lean_dec_ref(v_a_2120_);
return v_res_2122_;
}
}
uint8_t l_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_2123_, lean_object* v_x_2124_, lean_object* v_y_2125_){
_start:
{
lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = lean_apply_2(v_inst_2123_, v_x_2124_, v_y_2125_);
v___x_2127_ = lean_unbox(v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT void l_instDecidableEqOfLawfulBEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2123_ = stack[0].m_obj;
lean_object* v_x_2124_ = stack[1].m_obj;
lean_object* v_y_2125_ = stack[2].m_obj;
uint8_t v_res_2128_;
v_res_2128_ = l_instDecidableEqOfLawfulBEq___redArg(v_inst_2123_, v_x_2124_, v_y_2125_);
stack->m_num = v_res_2128_;
}
LEAN_EXPORT lean_object* l_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_2129_, lean_object* v_x_2130_, lean_object* v_y_2131_){
_start:
{
uint8_t v_res_2132_; lean_object* v_r_2133_; 
v_res_2132_ = l_instDecidableEqOfLawfulBEq___redArg(v_inst_2129_, v_x_2130_, v_y_2131_);
v_r_2133_ = lean_box(v_res_2132_);
return v_r_2133_;
}
}
uint8_t l_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_2134_, lean_object* v_inst_2135_, lean_object* v_inst_2136_, lean_object* v_x_2137_, lean_object* v_y_2138_){
_start:
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = lean_apply_2(v_inst_2135_, v_x_2137_, v_y_2138_);
v___x_2140_ = lean_unbox(v___x_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT void l_instDecidableEqOfLawfulBEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2135_ = stack[1].m_obj;
lean_object* v_x_2137_ = stack[3].m_obj;
lean_object* v_y_2138_ = stack[4].m_obj;
uint8_t v_res_2141_;
v_res_2141_ = l_instDecidableEqOfLawfulBEq(lean_box(0), v_inst_2135_, lean_box(0), v_x_2137_, v_y_2138_);
stack->m_num = v_res_2141_;
}
LEAN_EXPORT lean_object* l_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_x_2145_, lean_object* v_y_2146_){
_start:
{
uint8_t v_res_2147_; lean_object* v_r_2148_; 
v_res_2147_ = l_instDecidableEqOfLawfulBEq(v_00_u03b1_2142_, v_inst_2143_, v_inst_2144_, v_x_2145_, v_y_2146_);
v_r_2148_ = lean_box(v_res_2147_);
return v_r_2148_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__0));
v___x_2167_ = l_String_toRawSubstring_x27(v___x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____1(lean_object* v_x_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = ((lean_object*)(l_term___u2260___00__closed__1));
lean_inc(v_x_2176_);
v___x_2180_ = l_Lean_Syntax_isOfKind(v_x_2176_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec(v_x_2176_);
v___x_2181_ = lean_box(1);
v___x_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v_a_2178_);
return v___x_2182_;
}
else
{
lean_object* v_quotContext_2183_; lean_object* v_currMacroScope_2184_; lean_object* v_ref_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_quotContext_2183_ = lean_ctor_get(v_a_2177_, 1);
v_currMacroScope_2184_ = lean_ctor_get(v_a_2177_, 2);
v_ref_2185_ = lean_ctor_get(v_a_2177_, 5);
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = l_Lean_Syntax_getArg(v_x_2176_, v___x_2186_);
v___x_2188_ = lean_unsigned_to_nat(2u);
v___x_2189_ = l_Lean_Syntax_getArg(v_x_2176_, v___x_2188_);
lean_dec(v_x_2176_);
v___x_2190_ = 0;
v___x_2191_ = l_Lean_SourceInfo_fromRef(v_ref_2185_, v___x_2190_);
v___x_2192_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_2193_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2260____1___closed__1, &l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1);
v___x_2194_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__2));
lean_inc(v_currMacroScope_2184_);
lean_inc(v_quotContext_2183_);
v___x_2195_ = l_Lean_addMacroScope(v_quotContext_2183_, v___x_2194_, v_currMacroScope_2184_);
v___x_2196_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__4));
lean_inc_n(v___x_2191_, 2);
v___x_2197_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2191_);
lean_ctor_set(v___x_2197_, 1, v___x_2193_);
lean_ctor_set(v___x_2197_, 2, v___x_2195_);
lean_ctor_set(v___x_2197_, 3, v___x_2196_);
v___x_2198_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_2199_ = l_Lean_Syntax_node2(v___x_2191_, v___x_2198_, v___x_2187_, v___x_2189_);
v___x_2200_ = l_Lean_Syntax_node2(v___x_2191_, v___x_2192_, v___x_2197_, v___x_2199_);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v_a_2178_);
return v___x_2201_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____1___boxed(lean_object* v_x_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l___aux__Init__Core______macroRules__term___u2260____1(v_x_2202_, v_a_2203_, v_a_2204_);
lean_dec_ref(v_a_2203_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Ne__1(lean_object* v_x_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_2206_);
v___x_2210_ = l_Lean_Syntax_isOfKind(v_x_2206_, v___x_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_dec(v_x_2206_);
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v_a_2208_);
return v___x_2212_;
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2213_ = lean_unsigned_to_nat(0u);
v___x_2214_ = l_Lean_Syntax_getArg(v_x_2206_, v___x_2213_);
v___x_2215_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_2214_);
v___x_2216_ = l_Lean_Syntax_isOfKind(v___x_2214_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec(v___x_2214_);
lean_dec(v_x_2206_);
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v_a_2208_);
return v___x_2218_;
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2219_ = lean_unsigned_to_nat(1u);
v___x_2220_ = l_Lean_Syntax_getArg(v_x_2206_, v___x_2219_);
lean_dec(v_x_2206_);
v___x_2221_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2220_);
v___x_2222_ = l_Lean_Syntax_matchesNull(v___x_2220_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
lean_dec(v___x_2220_);
lean_dec(v___x_2214_);
v___x_2223_ = lean_box(0);
v___x_2224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set(v___x_2224_, 1, v_a_2208_);
return v___x_2224_;
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v_ref_2227_; uint8_t v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2225_ = l_Lean_Syntax_getArg(v___x_2220_, v___x_2213_);
v___x_2226_ = l_Lean_Syntax_getArg(v___x_2220_, v___x_2219_);
lean_dec(v___x_2220_);
v_ref_2227_ = l_Lean_replaceRef(v___x_2214_, v_a_2207_);
lean_dec(v___x_2214_);
v___x_2228_ = 0;
v___x_2229_ = l_Lean_SourceInfo_fromRef(v_ref_2227_, v___x_2228_);
lean_dec(v_ref_2227_);
v___x_2230_ = ((lean_object*)(l_term___u2260___00__closed__1));
v___x_2231_ = ((lean_object*)(l_term___u2260___00__closed__2));
lean_inc(v___x_2229_);
v___x_2232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2229_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = l_Lean_Syntax_node3(v___x_2229_, v___x_2230_, v___x_2225_, v___x_2232_, v___x_2226_);
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set(v___x_2234_, 1, v_a_2208_);
return v___x_2234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Ne__1___boxed(lean_object* v_x_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l___aux__Init__Core______unexpand__Ne__1(v_x_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____2(lean_object* v_x_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = ((lean_object*)(l_term___u2260___00__closed__1));
lean_inc(v_x_2246_);
v___x_2250_ = l_Lean_Syntax_isOfKind(v_x_2246_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec(v_x_2246_);
v___x_2251_ = lean_box(1);
v___x_2252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v_a_2248_);
return v___x_2252_;
}
else
{
lean_object* v_quotContext_2253_; lean_object* v_currMacroScope_2254_; lean_object* v_ref_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v_quotContext_2253_ = lean_ctor_get(v_a_2247_, 1);
v_currMacroScope_2254_ = lean_ctor_get(v_a_2247_, 2);
v_ref_2255_ = lean_ctor_get(v_a_2247_, 5);
v___x_2256_ = lean_unsigned_to_nat(0u);
v___x_2257_ = l_Lean_Syntax_getArg(v_x_2246_, v___x_2256_);
v___x_2258_ = lean_unsigned_to_nat(2u);
v___x_2259_ = l_Lean_Syntax_getArg(v_x_2246_, v___x_2258_);
lean_dec(v_x_2246_);
v___x_2260_ = 0;
v___x_2261_ = l_Lean_SourceInfo_fromRef(v_ref_2255_, v___x_2260_);
v___x_2262_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____2___closed__1));
v___x_2263_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____2___closed__2));
lean_inc_n(v___x_2261_, 2);
v___x_2264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2261_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2260____1___closed__1, &l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1);
v___x_2266_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__2));
lean_inc(v_currMacroScope_2254_);
lean_inc(v_quotContext_2253_);
v___x_2267_ = l_Lean_addMacroScope(v_quotContext_2253_, v___x_2266_, v_currMacroScope_2254_);
v___x_2268_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__4));
v___x_2269_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2261_);
lean_ctor_set(v___x_2269_, 1, v___x_2265_);
lean_ctor_set(v___x_2269_, 2, v___x_2267_);
lean_ctor_set(v___x_2269_, 3, v___x_2268_);
v___x_2270_ = l_Lean_Syntax_node4(v___x_2261_, v___x_2262_, v___x_2264_, v___x_2269_, v___x_2257_, v___x_2259_);
v___x_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
lean_ctor_set(v___x_2271_, 1, v_a_2248_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____2___boxed(lean_object* v_x_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l___aux__Init__Core______macroRules__term___u2260____2(v_x_2272_, v_a_2273_, v_a_2274_);
lean_dec_ref(v_a_2273_);
return v_res_2275_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__5));
v___x_2291_ = l_String_toRawSubstring_x27(v___x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1(lean_object* v_x_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v___x_2305_; uint8_t v___x_2306_; 
v___x_2305_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2));
v___x_2306_ = l_Lean_Syntax_isOfKind(v_x_2302_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = lean_box(1);
v___x_2308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v_a_2304_);
return v___x_2308_;
}
else
{
lean_object* v_quotContext_2309_; lean_object* v_currMacroScope_2310_; lean_object* v_ref_2311_; uint8_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_quotContext_2309_ = lean_ctor_get(v_a_2303_, 1);
v_currMacroScope_2310_ = lean_ctor_get(v_a_2303_, 2);
v_ref_2311_ = lean_ctor_get(v_a_2303_, 5);
v___x_2312_ = 0;
v___x_2313_ = l_Lean_SourceInfo_fromRef(v_ref_2311_, v___x_2312_);
v___x_2314_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3));
v___x_2315_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4));
lean_inc_n(v___x_2313_, 2);
v___x_2316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2313_);
lean_ctor_set(v___x_2316_, 1, v___x_2314_);
v___x_2317_ = lean_obj_once(&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6, &l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6_once, _init_l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6);
v___x_2318_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8));
lean_inc(v_currMacroScope_2310_);
lean_inc(v_quotContext_2309_);
v___x_2319_ = l_Lean_addMacroScope(v_quotContext_2309_, v___x_2318_, v_currMacroScope_2310_);
v___x_2320_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__10));
v___x_2321_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2313_);
lean_ctor_set(v___x_2321_, 1, v___x_2317_);
lean_ctor_set(v___x_2321_, 2, v___x_2319_);
lean_ctor_set(v___x_2321_, 3, v___x_2320_);
v___x_2322_ = l_Lean_Syntax_node2(v___x_2313_, v___x_2315_, v___x_2316_, v___x_2321_);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
lean_ctor_set(v___x_2323_, 1, v_a_2304_);
return v___x_2323_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___boxed(lean_object* v_x_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1(v_x_2324_, v_a_2325_, v_a_2326_);
lean_dec_ref(v_a_2325_);
return v_res_2327_;
}
}
static lean_object* _init_l_instTransIff(void){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_box(0);
return v___x_2328_;
}
}
uint8_t l_toBoolUsing___redArg(uint8_t v_d_2329_){
_start:
{
return v_d_2329_;
}
}
LEAN_EXPORT void l_toBoolUsing___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_d_2329_ = stack[0].m_num;
uint8_t v_res_2330_;
v_res_2330_ = l_toBoolUsing___redArg(v_d_2329_);
stack->m_num = v_res_2330_;
}
LEAN_EXPORT lean_object* l_toBoolUsing___redArg___boxed(lean_object* v_d_2331_){
_start:
{
uint8_t v_d_boxed_2332_; uint8_t v_res_2333_; lean_object* v_r_2334_; 
v_d_boxed_2332_ = lean_unbox(v_d_2331_);
v_res_2333_ = l_toBoolUsing___redArg(v_d_boxed_2332_);
v_r_2334_ = lean_box(v_res_2333_);
return v_r_2334_;
}
}
uint8_t l_toBoolUsing(lean_object* v_p_2335_, uint8_t v_d_2336_){
_start:
{
return v_d_2336_;
}
}
LEAN_EXPORT void l_toBoolUsing_0interp(lean_interpreter_value* stack)
{
uint8_t v_d_2336_ = stack[1].m_num;
uint8_t v_res_2337_;
v_res_2337_ = l_toBoolUsing(lean_box(0), v_d_2336_);
stack->m_num = v_res_2337_;
}
LEAN_EXPORT lean_object* l_toBoolUsing___boxed(lean_object* v_p_2338_, lean_object* v_d_2339_){
_start:
{
uint8_t v_d_boxed_2340_; uint8_t v_res_2341_; lean_object* v_r_2342_; 
v_d_boxed_2340_ = lean_unbox(v_d_2339_);
v_res_2341_ = l_toBoolUsing(v_p_2338_, v_d_boxed_2340_);
v_r_2342_ = lean_box(v_res_2341_);
return v_r_2342_;
}
}
static uint8_t _init_l_instDecidableTrue(void){
_start:
{
uint8_t v___x_2343_; 
v___x_2343_ = 1;
return v___x_2343_;
}
}
static uint8_t _init_l_instDecidableFalse(void){
_start:
{
uint8_t v___x_2344_; 
v___x_2344_ = 0;
return v___x_2344_;
}
}
uint8_t l_decidable__of__decidable__of__iff___redArg(uint8_t v_dp_2345_){
_start:
{
return v_dp_2345_;
}
}
LEAN_EXPORT void l_decidable__of__decidable__of__iff___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_dp_2345_ = stack[0].m_num;
uint8_t v_res_2346_;
v_res_2346_ = l_decidable__of__decidable__of__iff___redArg(v_dp_2345_);
stack->m_num = v_res_2346_;
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__iff___redArg___boxed(lean_object* v_dp_2347_){
_start:
{
uint8_t v_dp_boxed_2348_; uint8_t v_res_2349_; lean_object* v_r_2350_; 
v_dp_boxed_2348_ = lean_unbox(v_dp_2347_);
v_res_2349_ = l_decidable__of__decidable__of__iff___redArg(v_dp_boxed_2348_);
v_r_2350_ = lean_box(v_res_2349_);
return v_r_2350_;
}
}
uint8_t l_decidable__of__decidable__of__iff(lean_object* v_p_2351_, lean_object* v_q_2352_, uint8_t v_dp_2353_, lean_object* v_h_2354_){
_start:
{
return v_dp_2353_;
}
}
LEAN_EXPORT void l_decidable__of__decidable__of__iff_0interp(lean_interpreter_value* stack)
{
uint8_t v_dp_2353_ = stack[2].m_num;
uint8_t v_res_2355_;
v_res_2355_ = l_decidable__of__decidable__of__iff(lean_box(0), lean_box(0), v_dp_2353_, lean_box(0));
stack->m_num = v_res_2355_;
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__iff___boxed(lean_object* v_p_2356_, lean_object* v_q_2357_, lean_object* v_dp_2358_, lean_object* v_h_2359_){
_start:
{
uint8_t v_dp_boxed_2360_; uint8_t v_res_2361_; lean_object* v_r_2362_; 
v_dp_boxed_2360_ = lean_unbox(v_dp_2358_);
v_res_2361_ = l_decidable__of__decidable__of__iff(v_p_2356_, v_q_2357_, v_dp_boxed_2360_, v_h_2359_);
v_r_2362_ = lean_box(v_res_2361_);
return v_r_2362_;
}
}
uint8_t l_decidable__of__decidable__of__eq___redArg(uint8_t v_inst_2363_){
_start:
{
return v_inst_2363_;
}
}
LEAN_EXPORT void l_decidable__of__decidable__of__eq___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_2363_ = stack[0].m_num;
uint8_t v_res_2364_;
v_res_2364_ = l_decidable__of__decidable__of__eq___redArg(v_inst_2363_);
stack->m_num = v_res_2364_;
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__eq___redArg___boxed(lean_object* v_inst_2365_){
_start:
{
uint8_t v_inst_8__boxed_2366_; uint8_t v_res_2367_; lean_object* v_r_2368_; 
v_inst_8__boxed_2366_ = lean_unbox(v_inst_2365_);
v_res_2367_ = l_decidable__of__decidable__of__eq___redArg(v_inst_8__boxed_2366_);
v_r_2368_ = lean_box(v_res_2367_);
return v_r_2368_;
}
}
uint8_t l_decidable__of__decidable__of__eq(lean_object* v_p_2369_, lean_object* v_q_2370_, uint8_t v_inst_2371_, lean_object* v_h_2372_){
_start:
{
return v_inst_2371_;
}
}
LEAN_EXPORT void l_decidable__of__decidable__of__eq_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_2371_ = stack[2].m_num;
uint8_t v_res_2373_;
v_res_2373_ = l_decidable__of__decidable__of__eq(lean_box(0), lean_box(0), v_inst_2371_, lean_box(0));
stack->m_num = v_res_2373_;
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__eq___boxed(lean_object* v_p_2374_, lean_object* v_q_2375_, lean_object* v_inst_2376_, lean_object* v_h_2377_){
_start:
{
uint8_t v_inst_13__boxed_2378_; uint8_t v_res_2379_; lean_object* v_r_2380_; 
v_inst_13__boxed_2378_ = lean_unbox(v_inst_2376_);
v_res_2379_ = l_decidable__of__decidable__of__eq(v_p_2374_, v_q_2375_, v_inst_13__boxed_2378_, v_h_2377_);
v_r_2380_ = lean_box(v_res_2379_);
return v_r_2380_;
}
}
uint8_t l_instDecidableIff___redArg(uint8_t v_dp_2381_, uint8_t v_dq_2382_){
_start:
{
if (v_dq_2382_ == 0)
{
if (v_dp_2381_ == 0)
{
uint8_t v___x_2383_; 
v___x_2383_ = 1;
return v___x_2383_;
}
else
{
return v_dq_2382_;
}
}
else
{
return v_dp_2381_;
}
}
}
LEAN_EXPORT void l_instDecidableIff___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_dp_2381_ = stack[0].m_num;
uint8_t v_dq_2382_ = stack[1].m_num;
uint8_t v_res_2384_;
v_res_2384_ = l_instDecidableIff___redArg(v_dp_2381_, v_dq_2382_);
stack->m_num = v_res_2384_;
}
LEAN_EXPORT lean_object* l_instDecidableIff___redArg___boxed(lean_object* v_dp_2385_, lean_object* v_dq_2386_){
_start:
{
uint8_t v_dp_boxed_2387_; uint8_t v_dq_boxed_2388_; uint8_t v_res_2389_; lean_object* v_r_2390_; 
v_dp_boxed_2387_ = lean_unbox(v_dp_2385_);
v_dq_boxed_2388_ = lean_unbox(v_dq_2386_);
v_res_2389_ = l_instDecidableIff___redArg(v_dp_boxed_2387_, v_dq_boxed_2388_);
v_r_2390_ = lean_box(v_res_2389_);
return v_r_2390_;
}
}
uint8_t l_instDecidableIff(lean_object* v_p_2391_, lean_object* v_q_2392_, uint8_t v_dp_2393_, uint8_t v_dq_2394_){
_start:
{
if (v_dq_2394_ == 0)
{
if (v_dp_2393_ == 0)
{
uint8_t v___x_2395_; 
v___x_2395_ = 1;
return v___x_2395_;
}
else
{
return v_dq_2394_;
}
}
else
{
return v_dp_2393_;
}
}
}
LEAN_EXPORT void l_instDecidableIff_0interp(lean_interpreter_value* stack)
{
uint8_t v_dp_2393_ = stack[2].m_num;
uint8_t v_dq_2394_ = stack[3].m_num;
uint8_t v_res_2396_;
v_res_2396_ = l_instDecidableIff(lean_box(0), lean_box(0), v_dp_2393_, v_dq_2394_);
stack->m_num = v_res_2396_;
}
LEAN_EXPORT lean_object* l_instDecidableIff___boxed(lean_object* v_p_2397_, lean_object* v_q_2398_, lean_object* v_dp_2399_, lean_object* v_dq_2400_){
_start:
{
uint8_t v_dp_boxed_2401_; uint8_t v_dq_boxed_2402_; uint8_t v_res_2403_; lean_object* v_r_2404_; 
v_dp_boxed_2401_ = lean_unbox(v_dp_2399_);
v_dq_boxed_2402_ = lean_unbox(v_dq_2400_);
v_res_2403_ = l_instDecidableIff(v_p_2397_, v_q_2398_, v_dp_boxed_2401_, v_dq_boxed_2402_);
v_r_2404_ = lean_box(v_res_2403_);
return v_r_2404_;
}
}
lean_object* l_iteInduction___redArg(uint8_t v_inst_2405_, lean_object* v_hpos_2406_, lean_object* v_hneg_2407_){
_start:
{
if (v_inst_2405_ == 0)
{
lean_object* v___x_2408_; 
lean_dec(v_hpos_2406_);
v___x_2408_ = lean_apply_1(v_hneg_2407_, lean_box(0));
return v___x_2408_;
}
else
{
lean_object* v___x_2409_; 
lean_dec(v_hneg_2407_);
v___x_2409_ = lean_apply_1(v_hpos_2406_, lean_box(0));
return v___x_2409_;
}
}
}
LEAN_EXPORT void l_iteInduction___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_2405_ = stack[0].m_num;
lean_object* v_hpos_2406_ = stack[1].m_obj;
lean_object* v_hneg_2407_ = stack[2].m_obj;
lean_object* v_res_2410_;
v_res_2410_ = l_iteInduction___redArg(v_inst_2405_, v_hpos_2406_, v_hneg_2407_);
stack->m_obj
 = v_res_2410_;
}
LEAN_EXPORT lean_object* l_iteInduction___redArg___boxed(lean_object* v_inst_2411_, lean_object* v_hpos_2412_, lean_object* v_hneg_2413_){
_start:
{
uint8_t v_inst_boxed_2414_; lean_object* v_res_2415_; 
v_inst_boxed_2414_ = lean_unbox(v_inst_2411_);
v_res_2415_ = l_iteInduction___redArg(v_inst_boxed_2414_, v_hpos_2412_, v_hneg_2413_);
return v_res_2415_;
}
}
lean_object* l_iteInduction(lean_object* v_00_u03b1_2416_, lean_object* v_c_2417_, uint8_t v_inst_2418_, lean_object* v_motive_2419_, lean_object* v_t_2420_, lean_object* v_e_2421_, lean_object* v_hpos_2422_, lean_object* v_hneg_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_iteInduction___redArg(v_inst_2418_, v_hpos_2422_, v_hneg_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT void l_iteInduction_0interp(lean_interpreter_value* stack)
{
uint8_t v_inst_2418_ = stack[2].m_num;
lean_object* v_t_2420_ = stack[4].m_obj;
lean_object* v_e_2421_ = stack[5].m_obj;
lean_object* v_hpos_2422_ = stack[6].m_obj;
lean_object* v_hneg_2423_ = stack[7].m_obj;
lean_object* v_res_2425_;
v_res_2425_ = l_iteInduction(lean_box(0), lean_box(0), v_inst_2418_, lean_box(0), v_t_2420_, v_e_2421_, v_hpos_2422_, v_hneg_2423_);
stack->m_obj
 = v_res_2425_;
}
LEAN_EXPORT lean_object* l_iteInduction___boxed(lean_object* v_00_u03b1_2426_, lean_object* v_c_2427_, lean_object* v_inst_2428_, lean_object* v_motive_2429_, lean_object* v_t_2430_, lean_object* v_e_2431_, lean_object* v_hpos_2432_, lean_object* v_hneg_2433_){
_start:
{
uint8_t v_inst_boxed_2434_; lean_object* v_res_2435_; 
v_inst_boxed_2434_ = lean_unbox(v_inst_2428_);
v_res_2435_ = l_iteInduction(v_00_u03b1_2426_, v_c_2427_, v_inst_boxed_2434_, v_motive_2429_, v_t_2430_, v_e_2431_, v_hpos_2432_, v_hneg_2433_);
lean_dec(v_e_2431_);
lean_dec(v_t_2430_);
return v_res_2435_;
}
}
uint8_t l_instDecidableDite___redArg(uint8_t v_dC_2436_, lean_object* v_dT_2437_, lean_object* v_dE_2438_){
_start:
{
if (v_dC_2436_ == 0)
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
lean_dec_ref(v_dT_2437_);
v___x_2439_ = lean_apply_1(v_dE_2438_, lean_box(0));
v___x_2440_ = lean_unbox(v___x_2439_);
return v___x_2440_;
}
else
{
lean_object* v___x_2441_; uint8_t v___x_2442_; 
lean_dec_ref(v_dE_2438_);
v___x_2441_ = lean_apply_1(v_dT_2437_, lean_box(0));
v___x_2442_ = lean_unbox(v___x_2441_);
return v___x_2442_;
}
}
}
LEAN_EXPORT void l_instDecidableDite___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_dC_2436_ = stack[0].m_num;
lean_object* v_dT_2437_ = stack[1].m_obj;
lean_object* v_dE_2438_ = stack[2].m_obj;
uint8_t v_res_2443_;
v_res_2443_ = l_instDecidableDite___redArg(v_dC_2436_, v_dT_2437_, v_dE_2438_);
stack->m_num = v_res_2443_;
}
LEAN_EXPORT lean_object* l_instDecidableDite___redArg___boxed(lean_object* v_dC_2444_, lean_object* v_dT_2445_, lean_object* v_dE_2446_){
_start:
{
uint8_t v_dC_boxed_2447_; uint8_t v_res_2448_; lean_object* v_r_2449_; 
v_dC_boxed_2447_ = lean_unbox(v_dC_2444_);
v_res_2448_ = l_instDecidableDite___redArg(v_dC_boxed_2447_, v_dT_2445_, v_dE_2446_);
v_r_2449_ = lean_box(v_res_2448_);
return v_r_2449_;
}
}
uint8_t l_instDecidableDite(lean_object* v_c_2450_, lean_object* v_t_2451_, lean_object* v_e_2452_, uint8_t v_dC_2453_, lean_object* v_dT_2454_, lean_object* v_dE_2455_){
_start:
{
if (v_dC_2453_ == 0)
{
lean_object* v___x_2456_; uint8_t v___x_2457_; 
lean_dec_ref(v_dT_2454_);
v___x_2456_ = lean_apply_1(v_dE_2455_, lean_box(0));
v___x_2457_ = lean_unbox(v___x_2456_);
return v___x_2457_;
}
else
{
lean_object* v___x_2458_; uint8_t v___x_2459_; 
lean_dec_ref(v_dE_2455_);
v___x_2458_ = lean_apply_1(v_dT_2454_, lean_box(0));
v___x_2459_ = lean_unbox(v___x_2458_);
return v___x_2459_;
}
}
}
LEAN_EXPORT void l_instDecidableDite_0interp(lean_interpreter_value* stack)
{
uint8_t v_dC_2453_ = stack[3].m_num;
lean_object* v_dT_2454_ = stack[4].m_obj;
lean_object* v_dE_2455_ = stack[5].m_obj;
uint8_t v_res_2460_;
v_res_2460_ = l_instDecidableDite(lean_box(0), lean_box(0), lean_box(0), v_dC_2453_, v_dT_2454_, v_dE_2455_);
stack->m_num = v_res_2460_;
}
LEAN_EXPORT lean_object* l_instDecidableDite___boxed(lean_object* v_c_2461_, lean_object* v_t_2462_, lean_object* v_e_2463_, lean_object* v_dC_2464_, lean_object* v_dT_2465_, lean_object* v_dE_2466_){
_start:
{
uint8_t v_dC_boxed_2467_; uint8_t v_res_2468_; lean_object* v_r_2469_; 
v_dC_boxed_2467_ = lean_unbox(v_dC_2464_);
v_res_2468_ = l_instDecidableDite(v_c_2461_, v_t_2462_, v_e_2463_, v_dC_boxed_2467_, v_dT_2465_, v_dE_2466_);
v_r_2469_ = lean_box(v_res_2468_);
return v_r_2469_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg___lam__0(lean_object* v_a_2470_){
_start:
{
lean_inc(v_a_2470_);
return v_a_2470_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg___lam__0___boxed(lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_noConfusionEnum___redArg___lam__0(v_a_2471_);
lean_dec(v_a_2471_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg(lean_object* v_f_2474_, lean_object* v_x_2475_, lean_object* v_y_2476_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; lean_object* v___f_2480_; 
lean_inc_ref(v_f_2474_);
v___x_2477_ = lean_apply_1(v_f_2474_, v_x_2475_);
v___x_2478_ = lean_apply_1(v_f_2474_, v_y_2476_);
v___x_2479_ = lean_nat_dec_eq(v___x_2477_, v___x_2478_);
lean_dec(v___x_2478_);
lean_dec(v___x_2477_);
v___f_2480_ = ((lean_object*)(l_noConfusionEnum___redArg___closed__0));
return v___f_2480_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum(lean_object* v_00_u03b1_2481_, lean_object* v_f_2482_, lean_object* v_P_2483_, lean_object* v_x_2484_, lean_object* v_y_2485_, lean_object* v_h_2486_){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; lean_object* v___f_2490_; 
lean_inc_ref(v_f_2482_);
v___x_2487_ = lean_apply_1(v_f_2482_, v_x_2484_);
v___x_2488_ = lean_apply_1(v_f_2482_, v_y_2485_);
v___x_2489_ = lean_nat_dec_eq(v___x_2487_, v___x_2488_);
lean_dec(v___x_2488_);
lean_dec(v___x_2487_);
v___f_2490_ = ((lean_object*)(l_noConfusionEnum___redArg___closed__0));
return v___f_2490_;
}
}
static lean_object* _init_l_instInhabitedProp(void){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_box(0);
return v___x_2491_;
}
}
static lean_object* _init_l_instInhabitedNonScalar_default(void){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_unsigned_to_nat(0u);
return v___x_2492_;
}
}
static lean_object* _init_l_instInhabitedNonScalar(void){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = lean_unsigned_to_nat(0u);
return v___x_2493_;
}
}
static lean_object* _init_l_instInhabitedPNonScalar_default(void){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = lean_unsigned_to_nat(0u);
return v___x_2494_;
}
}
static lean_object* _init_l_instInhabitedPNonScalar(void){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = lean_unsigned_to_nat(0u);
return v___x_2495_;
}
}
static lean_object* _init_l_instInhabitedTrue(void){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = lean_box(0);
return v___x_2496_;
}
}
uint8_t l_Subtype_instBEq___redArg___lam__0(lean_object* v_inst_2497_, lean_object* v_x_2498_, lean_object* v_y_2499_){
_start:
{
lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2500_ = lean_apply_2(v_inst_2497_, v_x_2498_, v_y_2499_);
v___x_2501_ = lean_unbox(v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT void l_Subtype_instBEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2497_ = stack[0].m_obj;
lean_object* v_x_2498_ = stack[1].m_obj;
lean_object* v_y_2499_ = stack[2].m_obj;
uint8_t v_res_2502_;
v_res_2502_ = l_Subtype_instBEq___redArg___lam__0(v_inst_2497_, v_x_2498_, v_y_2499_);
stack->m_num = v_res_2502_;
}
LEAN_EXPORT lean_object* l_Subtype_instBEq___redArg___lam__0___boxed(lean_object* v_inst_2503_, lean_object* v_x_2504_, lean_object* v_y_2505_){
_start:
{
uint8_t v_res_2506_; lean_object* v_r_2507_; 
v_res_2506_ = l_Subtype_instBEq___redArg___lam__0(v_inst_2503_, v_x_2504_, v_y_2505_);
v_r_2507_ = lean_box(v_res_2506_);
return v_r_2507_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq___redArg(lean_object* v_inst_2508_){
_start:
{
lean_object* v___f_2509_; 
v___f_2509_ = lean_alloc_closure((void*)(l_Subtype_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2509_, 0, v_inst_2508_);
return v___f_2509_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq(lean_object* v_00_u03b1_2510_, lean_object* v_p_2511_, lean_object* v_inst_2512_){
_start:
{
lean_object* v___f_2513_; 
v___f_2513_ = lean_alloc_closure((void*)(l_Subtype_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2513_, 0, v_inst_2512_);
return v___f_2513_;
}
}
uint8_t l_Subtype_instDecidableEq___redArg(lean_object* v_inst_2514_, lean_object* v_x_2515_, lean_object* v_x_2516_){
_start:
{
lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = lean_apply_2(v_inst_2514_, v_x_2515_, v_x_2516_);
v___x_2518_ = lean_unbox(v___x_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT void l_Subtype_instDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2514_ = stack[0].m_obj;
lean_object* v_x_2515_ = stack[1].m_obj;
lean_object* v_x_2516_ = stack[2].m_obj;
uint8_t v_res_2519_;
v_res_2519_ = l_Subtype_instDecidableEq___redArg(v_inst_2514_, v_x_2515_, v_x_2516_);
stack->m_num = v_res_2519_;
}
LEAN_EXPORT lean_object* l_Subtype_instDecidableEq___redArg___boxed(lean_object* v_inst_2520_, lean_object* v_x_2521_, lean_object* v_x_2522_){
_start:
{
uint8_t v_res_2523_; lean_object* v_r_2524_; 
v_res_2523_ = l_Subtype_instDecidableEq___redArg(v_inst_2520_, v_x_2521_, v_x_2522_);
v_r_2524_ = lean_box(v_res_2523_);
return v_r_2524_;
}
}
uint8_t l_Subtype_instDecidableEq(lean_object* v_00_u03b1_2525_, lean_object* v_p_2526_, lean_object* v_inst_2527_, lean_object* v_x_2528_, lean_object* v_x_2529_){
_start:
{
lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = lean_apply_2(v_inst_2527_, v_x_2528_, v_x_2529_);
v___x_2531_ = lean_unbox(v___x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT void l_Subtype_instDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2527_ = stack[2].m_obj;
lean_object* v_x_2528_ = stack[3].m_obj;
lean_object* v_x_2529_ = stack[4].m_obj;
uint8_t v_res_2532_;
v_res_2532_ = l_Subtype_instDecidableEq(lean_box(0), lean_box(0), v_inst_2527_, v_x_2528_, v_x_2529_);
stack->m_num = v_res_2532_;
}
LEAN_EXPORT lean_object* l_Subtype_instDecidableEq___boxed(lean_object* v_00_u03b1_2533_, lean_object* v_p_2534_, lean_object* v_inst_2535_, lean_object* v_x_2536_, lean_object* v_x_2537_){
_start:
{
uint8_t v_res_2538_; lean_object* v_r_2539_; 
v_res_2538_ = l_Subtype_instDecidableEq(v_00_u03b1_2533_, v_p_2534_, v_inst_2535_, v_x_2536_, v_x_2537_);
v_r_2539_ = lean_box(v_res_2538_);
return v_r_2539_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedLeft___redArg(lean_object* v_inst_2540_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v_inst_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedLeft(lean_object* v_00_u03b1_2542_, lean_object* v_00_u03b2_2543_, lean_object* v_inst_2544_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_inst_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedRight___redArg(lean_object* v_inst_2546_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_inst_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedRight(lean_object* v_00_u03b1_2548_, lean_object* v_00_u03b2_2549_, lean_object* v_inst_2550_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_inst_2550_);
return v___x_2551_;
}
}
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object* v_inst_2552_, lean_object* v_inst_2553_, lean_object* v_x_2554_, lean_object* v_x_2555_){
_start:
{
if (lean_obj_tag(v_x_2554_) == 0)
{
lean_dec_ref(v_inst_2553_);
if (lean_obj_tag(v_x_2555_) == 0)
{
lean_object* v_val_2556_; lean_object* v_val_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v_val_2556_ = lean_ctor_get(v_x_2554_, 0);
lean_inc(v_val_2556_);
lean_dec_ref_known(v_x_2554_, 1);
v_val_2557_ = lean_ctor_get(v_x_2555_, 0);
lean_inc(v_val_2557_);
lean_dec_ref_known(v_x_2555_, 1);
v___x_2558_ = lean_apply_2(v_inst_2552_, v_val_2556_, v_val_2557_);
v___x_2559_ = lean_unbox(v___x_2558_);
return v___x_2559_;
}
else
{
uint8_t v___x_2560_; 
lean_dec_ref_known(v_x_2555_, 1);
lean_dec_ref_known(v_x_2554_, 1);
lean_dec_ref(v_inst_2552_);
v___x_2560_ = 0;
return v___x_2560_;
}
}
else
{
lean_dec_ref(v_inst_2552_);
if (lean_obj_tag(v_x_2555_) == 0)
{
uint8_t v___x_2561_; 
lean_dec_ref_known(v_x_2555_, 1);
lean_dec_ref_known(v_x_2554_, 1);
lean_dec_ref(v_inst_2553_);
v___x_2561_ = 0;
return v___x_2561_;
}
else
{
lean_object* v_val_2562_; lean_object* v_val_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v_val_2562_ = lean_ctor_get(v_x_2554_, 0);
lean_inc(v_val_2562_);
lean_dec_ref_known(v_x_2554_, 1);
v_val_2563_ = lean_ctor_get(v_x_2555_, 0);
lean_inc(v_val_2563_);
lean_dec_ref_known(v_x_2555_, 1);
v___x_2564_ = lean_apply_2(v_inst_2553_, v_val_2562_, v_val_2563_);
v___x_2565_ = lean_unbox(v___x_2564_);
return v___x_2565_;
}
}
}
}
LEAN_EXPORT void l_instDecidableEqSum_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2552_ = stack[0].m_obj;
lean_object* v_inst_2553_ = stack[1].m_obj;
lean_object* v_x_2554_ = stack[2].m_obj;
lean_object* v_x_2555_ = stack[3].m_obj;
uint8_t v_res_2566_;
v_res_2566_ = l_instDecidableEqSum_decEq___redArg(v_inst_2552_, v_inst_2553_, v_x_2554_, v_x_2555_);
stack->m_num = v_res_2566_;
}
LEAN_EXPORT lean_object* l_instDecidableEqSum_decEq___redArg___boxed(lean_object* v_inst_2567_, lean_object* v_inst_2568_, lean_object* v_x_2569_, lean_object* v_x_2570_){
_start:
{
uint8_t v_res_2571_; lean_object* v_r_2572_; 
v_res_2571_ = l_instDecidableEqSum_decEq___redArg(v_inst_2567_, v_inst_2568_, v_x_2569_, v_x_2570_);
v_r_2572_ = lean_box(v_res_2571_);
return v_r_2572_;
}
}
uint8_t l_instDecidableEqSum_decEq(lean_object* v_00_u03b1_2573_, lean_object* v_00_u03b2_2574_, lean_object* v_inst_2575_, lean_object* v_inst_2576_, lean_object* v_x_2577_, lean_object* v_x_2578_){
_start:
{
uint8_t v___x_2579_; 
v___x_2579_ = l_instDecidableEqSum_decEq___redArg(v_inst_2575_, v_inst_2576_, v_x_2577_, v_x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT void l_instDecidableEqSum_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2575_ = stack[2].m_obj;
lean_object* v_inst_2576_ = stack[3].m_obj;
lean_object* v_x_2577_ = stack[4].m_obj;
lean_object* v_x_2578_ = stack[5].m_obj;
uint8_t v_res_2580_;
v_res_2580_ = l_instDecidableEqSum_decEq(lean_box(0), lean_box(0), v_inst_2575_, v_inst_2576_, v_x_2577_, v_x_2578_);
stack->m_num = v_res_2580_;
}
LEAN_EXPORT lean_object* l_instDecidableEqSum_decEq___boxed(lean_object* v_00_u03b1_2581_, lean_object* v_00_u03b2_2582_, lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_){
_start:
{
uint8_t v_res_2587_; lean_object* v_r_2588_; 
v_res_2587_ = l_instDecidableEqSum_decEq(v_00_u03b1_2581_, v_00_u03b2_2582_, v_inst_2583_, v_inst_2584_, v_x_2585_, v_x_2586_);
v_r_2588_ = lean_box(v_res_2587_);
return v_r_2588_;
}
}
uint8_t l_instDecidableEqSum___redArg(lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_x_2591_, lean_object* v_x_2592_){
_start:
{
uint8_t v___x_2593_; 
v___x_2593_ = l_instDecidableEqSum_decEq___redArg(v_inst_2589_, v_inst_2590_, v_x_2591_, v_x_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT void l_instDecidableEqSum___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2589_ = stack[0].m_obj;
lean_object* v_inst_2590_ = stack[1].m_obj;
lean_object* v_x_2591_ = stack[2].m_obj;
lean_object* v_x_2592_ = stack[3].m_obj;
uint8_t v_res_2594_;
v_res_2594_ = l_instDecidableEqSum___redArg(v_inst_2589_, v_inst_2590_, v_x_2591_, v_x_2592_);
stack->m_num = v_res_2594_;
}
LEAN_EXPORT lean_object* l_instDecidableEqSum___redArg___boxed(lean_object* v_inst_2595_, lean_object* v_inst_2596_, lean_object* v_x_2597_, lean_object* v_x_2598_){
_start:
{
uint8_t v_res_2599_; lean_object* v_r_2600_; 
v_res_2599_ = l_instDecidableEqSum___redArg(v_inst_2595_, v_inst_2596_, v_x_2597_, v_x_2598_);
v_r_2600_ = lean_box(v_res_2599_);
return v_r_2600_;
}
}
uint8_t l_instDecidableEqSum(lean_object* v_00_u03b1_2601_, lean_object* v_00_u03b2_2602_, lean_object* v_inst_2603_, lean_object* v_inst_2604_, lean_object* v_x_2605_, lean_object* v_x_2606_){
_start:
{
uint8_t v___x_2607_; 
v___x_2607_ = l_instDecidableEqSum_decEq___redArg(v_inst_2603_, v_inst_2604_, v_x_2605_, v_x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT void l_instDecidableEqSum_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2603_ = stack[2].m_obj;
lean_object* v_inst_2604_ = stack[3].m_obj;
lean_object* v_x_2605_ = stack[4].m_obj;
lean_object* v_x_2606_ = stack[5].m_obj;
uint8_t v_res_2608_;
v_res_2608_ = l_instDecidableEqSum(lean_box(0), lean_box(0), v_inst_2603_, v_inst_2604_, v_x_2605_, v_x_2606_);
stack->m_num = v_res_2608_;
}
LEAN_EXPORT lean_object* l_instDecidableEqSum___boxed(lean_object* v_00_u03b1_2609_, lean_object* v_00_u03b2_2610_, lean_object* v_inst_2611_, lean_object* v_inst_2612_, lean_object* v_x_2613_, lean_object* v_x_2614_){
_start:
{
uint8_t v_res_2615_; lean_object* v_r_2616_; 
v_res_2615_ = l_instDecidableEqSum(v_00_u03b1_2609_, v_00_u03b2_2610_, v_inst_2611_, v_inst_2612_, v_x_2613_, v_x_2614_);
v_r_2616_ = lean_box(v_res_2615_);
return v_r_2616_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedProd___redArg(lean_object* v_inst_2617_, lean_object* v_inst_2618_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2619_, 0, v_inst_2617_);
lean_ctor_set(v___x_2619_, 1, v_inst_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedProd(lean_object* v_00_u03b1_2620_, lean_object* v_00_u03b2_2621_, lean_object* v_inst_2622_, lean_object* v_inst_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v_inst_2622_);
lean_ctor_set(v___x_2624_, 1, v_inst_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedMProd___redArg(lean_object* v_inst_2625_, lean_object* v_inst_2626_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v_inst_2625_);
lean_ctor_set(v___x_2627_, 1, v_inst_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedMProd(lean_object* v_00_u03b1_2628_, lean_object* v_00_u03b2_2629_, lean_object* v_inst_2630_, lean_object* v_inst_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2632_, 0, v_inst_2630_);
lean_ctor_set(v___x_2632_, 1, v_inst_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedPProd___redArg(lean_object* v_inst_2633_, lean_object* v_inst_2634_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2635_, 0, v_inst_2633_);
lean_ctor_set(v___x_2635_, 1, v_inst_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedPProd(lean_object* v_00_u03b1_2636_, lean_object* v_00_u03b2_2637_, lean_object* v_inst_2638_, lean_object* v_inst_2639_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2640_, 0, v_inst_2638_);
lean_ctor_set(v___x_2640_, 1, v_inst_2639_);
return v___x_2640_;
}
}
uint8_t l_instDecidableEqProd___redArg(lean_object* v_h_2641_, lean_object* v_h_x27_2642_, lean_object* v_x_2643_, lean_object* v_x_2644_){
_start:
{
lean_object* v_fst_2645_; lean_object* v_snd_2646_; lean_object* v_fst_2647_; lean_object* v_snd_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
v_fst_2645_ = lean_ctor_get(v_x_2643_, 0);
lean_inc(v_fst_2645_);
v_snd_2646_ = lean_ctor_get(v_x_2643_, 1);
lean_inc(v_snd_2646_);
lean_dec_ref(v_x_2643_);
v_fst_2647_ = lean_ctor_get(v_x_2644_, 0);
lean_inc(v_fst_2647_);
v_snd_2648_ = lean_ctor_get(v_x_2644_, 1);
lean_inc(v_snd_2648_);
lean_dec_ref(v_x_2644_);
v___x_2649_ = lean_apply_2(v_h_2641_, v_fst_2645_, v_fst_2647_);
v___x_2650_ = lean_unbox(v___x_2649_);
if (v___x_2650_ == 0)
{
uint8_t v___x_2651_; 
lean_dec(v_snd_2648_);
lean_dec(v_snd_2646_);
lean_dec_ref(v_h_x27_2642_);
v___x_2651_ = lean_unbox(v___x_2649_);
return v___x_2651_;
}
else
{
lean_object* v___x_2652_; uint8_t v___x_2653_; 
v___x_2652_ = lean_apply_2(v_h_x27_2642_, v_snd_2646_, v_snd_2648_);
v___x_2653_ = lean_unbox(v___x_2652_);
return v___x_2653_;
}
}
}
LEAN_EXPORT void l_instDecidableEqProd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_2641_ = stack[0].m_obj;
lean_object* v_h_x27_2642_ = stack[1].m_obj;
lean_object* v_x_2643_ = stack[2].m_obj;
lean_object* v_x_2644_ = stack[3].m_obj;
uint8_t v_res_2654_;
v_res_2654_ = l_instDecidableEqProd___redArg(v_h_2641_, v_h_x27_2642_, v_x_2643_, v_x_2644_);
stack->m_num = v_res_2654_;
}
LEAN_EXPORT lean_object* l_instDecidableEqProd___redArg___boxed(lean_object* v_h_2655_, lean_object* v_h_x27_2656_, lean_object* v_x_2657_, lean_object* v_x_2658_){
_start:
{
uint8_t v_res_2659_; lean_object* v_r_2660_; 
v_res_2659_ = l_instDecidableEqProd___redArg(v_h_2655_, v_h_x27_2656_, v_x_2657_, v_x_2658_);
v_r_2660_ = lean_box(v_res_2659_);
return v_r_2660_;
}
}
uint8_t l_instDecidableEqProd(lean_object* v_00_u03b1_2661_, lean_object* v_00_u03b2_2662_, lean_object* v_h_2663_, lean_object* v_h_x27_2664_, lean_object* v_x_2665_, lean_object* v_x_2666_){
_start:
{
uint8_t v___x_2667_; 
v___x_2667_ = l_instDecidableEqProd___redArg(v_h_2663_, v_h_x27_2664_, v_x_2665_, v_x_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT void l_instDecidableEqProd_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_2663_ = stack[2].m_obj;
lean_object* v_h_x27_2664_ = stack[3].m_obj;
lean_object* v_x_2665_ = stack[4].m_obj;
lean_object* v_x_2666_ = stack[5].m_obj;
uint8_t v_res_2668_;
v_res_2668_ = l_instDecidableEqProd(lean_box(0), lean_box(0), v_h_2663_, v_h_x27_2664_, v_x_2665_, v_x_2666_);
stack->m_num = v_res_2668_;
}
LEAN_EXPORT lean_object* l_instDecidableEqProd___boxed(lean_object* v_00_u03b1_2669_, lean_object* v_00_u03b2_2670_, lean_object* v_h_2671_, lean_object* v_h_x27_2672_, lean_object* v_x_2673_, lean_object* v_x_2674_){
_start:
{
uint8_t v_res_2675_; lean_object* v_r_2676_; 
v_res_2675_ = l_instDecidableEqProd(v_00_u03b1_2669_, v_00_u03b2_2670_, v_h_2671_, v_h_x27_2672_, v_x_2673_, v_x_2674_);
v_r_2676_ = lean_box(v_res_2675_);
return v_r_2676_;
}
}
uint8_t l_instBEqProd___redArg___lam__0(lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_x_2679_, lean_object* v_x_2680_){
_start:
{
lean_object* v_fst_2681_; lean_object* v_snd_2682_; lean_object* v_fst_2683_; lean_object* v_snd_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v_fst_2681_ = lean_ctor_get(v_x_2679_, 0);
lean_inc(v_fst_2681_);
v_snd_2682_ = lean_ctor_get(v_x_2679_, 1);
lean_inc(v_snd_2682_);
lean_dec_ref(v_x_2679_);
v_fst_2683_ = lean_ctor_get(v_x_2680_, 0);
lean_inc(v_fst_2683_);
v_snd_2684_ = lean_ctor_get(v_x_2680_, 1);
lean_inc(v_snd_2684_);
lean_dec_ref(v_x_2680_);
v___x_2685_ = lean_apply_2(v_inst_2677_, v_fst_2681_, v_fst_2683_);
v___x_2686_ = lean_unbox(v___x_2685_);
if (v___x_2686_ == 0)
{
uint8_t v___x_2687_; 
lean_dec(v_snd_2684_);
lean_dec(v_snd_2682_);
lean_dec_ref(v_inst_2678_);
v___x_2687_ = lean_unbox(v___x_2685_);
return v___x_2687_;
}
else
{
lean_object* v___x_2688_; uint8_t v___x_2689_; 
v___x_2688_ = lean_apply_2(v_inst_2678_, v_snd_2682_, v_snd_2684_);
v___x_2689_ = lean_unbox(v___x_2688_);
return v___x_2689_;
}
}
}
LEAN_EXPORT void l_instBEqProd___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2677_ = stack[0].m_obj;
lean_object* v_inst_2678_ = stack[1].m_obj;
lean_object* v_x_2679_ = stack[2].m_obj;
lean_object* v_x_2680_ = stack[3].m_obj;
uint8_t v_res_2690_;
v_res_2690_ = l_instBEqProd___redArg___lam__0(v_inst_2677_, v_inst_2678_, v_x_2679_, v_x_2680_);
stack->m_num = v_res_2690_;
}
LEAN_EXPORT lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_x_2693_, lean_object* v_x_2694_){
_start:
{
uint8_t v_res_2695_; lean_object* v_r_2696_; 
v_res_2695_ = l_instBEqProd___redArg___lam__0(v_inst_2691_, v_inst_2692_, v_x_2693_, v_x_2694_);
v_r_2696_ = lean_box(v_res_2695_);
return v_r_2696_;
}
}
LEAN_EXPORT lean_object* l_instBEqProd___redArg(lean_object* v_inst_2697_, lean_object* v_inst_2698_){
_start:
{
lean_object* v___f_2699_; 
v___f_2699_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2699_, 0, v_inst_2697_);
lean_closure_set(v___f_2699_, 1, v_inst_2698_);
return v___f_2699_;
}
}
LEAN_EXPORT lean_object* l_instBEqProd(lean_object* v_00_u03b1_2700_, lean_object* v_00_u03b2_2701_, lean_object* v_inst_2702_, lean_object* v_inst_2703_){
_start:
{
lean_object* v___f_2704_; 
v___f_2704_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2704_, 0, v_inst_2702_);
lean_closure_set(v___f_2704_, 1, v_inst_2703_);
return v___f_2704_;
}
}
uint8_t l_Prod_lexLtDec___redArg(lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_x_2708_, lean_object* v_x_2709_){
_start:
{
lean_object* v_fst_2710_; lean_object* v_snd_2711_; lean_object* v_fst_2712_; lean_object* v_snd_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v_fst_2710_ = lean_ctor_get(v_x_2708_, 0);
lean_inc_n(v_fst_2710_, 2);
v_snd_2711_ = lean_ctor_get(v_x_2708_, 1);
lean_inc(v_snd_2711_);
lean_dec_ref(v_x_2708_);
v_fst_2712_ = lean_ctor_get(v_x_2709_, 0);
lean_inc_n(v_fst_2712_, 2);
v_snd_2713_ = lean_ctor_get(v_x_2709_, 1);
lean_inc(v_snd_2713_);
lean_dec_ref(v_x_2709_);
v___x_2714_ = lean_apply_2(v_inst_2706_, v_fst_2710_, v_fst_2712_);
v___x_2715_ = lean_unbox(v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; uint8_t v___x_2717_; 
v___x_2716_ = lean_apply_2(v_inst_2705_, v_fst_2710_, v_fst_2712_);
v___x_2717_ = lean_unbox(v___x_2716_);
if (v___x_2717_ == 0)
{
uint8_t v___x_2718_; 
lean_dec(v_snd_2713_);
lean_dec(v_snd_2711_);
lean_dec_ref(v_inst_2707_);
v___x_2718_ = lean_unbox(v___x_2716_);
return v___x_2718_;
}
else
{
lean_object* v___x_2719_; uint8_t v___x_2720_; 
v___x_2719_ = lean_apply_2(v_inst_2707_, v_snd_2711_, v_snd_2713_);
v___x_2720_ = lean_unbox(v___x_2719_);
return v___x_2720_;
}
}
else
{
uint8_t v___x_2721_; 
lean_dec(v_snd_2713_);
lean_dec(v_fst_2712_);
lean_dec(v_snd_2711_);
lean_dec(v_fst_2710_);
lean_dec_ref(v_inst_2707_);
lean_dec_ref(v_inst_2705_);
v___x_2721_ = lean_unbox(v___x_2714_);
return v___x_2721_;
}
}
}
LEAN_EXPORT void l_Prod_lexLtDec___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2705_ = stack[0].m_obj;
lean_object* v_inst_2706_ = stack[1].m_obj;
lean_object* v_inst_2707_ = stack[2].m_obj;
lean_object* v_x_2708_ = stack[3].m_obj;
lean_object* v_x_2709_ = stack[4].m_obj;
uint8_t v_res_2722_;
v_res_2722_ = l_Prod_lexLtDec___redArg(v_inst_2705_, v_inst_2706_, v_inst_2707_, v_x_2708_, v_x_2709_);
stack->m_num = v_res_2722_;
}
LEAN_EXPORT lean_object* l_Prod_lexLtDec___redArg___boxed(lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_x_2726_, lean_object* v_x_2727_){
_start:
{
uint8_t v_res_2728_; lean_object* v_r_2729_; 
v_res_2728_ = l_Prod_lexLtDec___redArg(v_inst_2723_, v_inst_2724_, v_inst_2725_, v_x_2726_, v_x_2727_);
v_r_2729_ = lean_box(v_res_2728_);
return v_r_2729_;
}
}
uint8_t l_Prod_lexLtDec(lean_object* v_00_u03b1_2730_, lean_object* v_00_u03b2_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_inst_2734_, lean_object* v_inst_2735_, lean_object* v_inst_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_){
_start:
{
uint8_t v___x_2739_; 
v___x_2739_ = l_Prod_lexLtDec___redArg(v_inst_2734_, v_inst_2735_, v_inst_2736_, v_x_2737_, v_x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT void l_Prod_lexLtDec_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2732_ = stack[2].m_obj;
lean_object* v_inst_2733_ = stack[3].m_obj;
lean_object* v_inst_2734_ = stack[4].m_obj;
lean_object* v_inst_2735_ = stack[5].m_obj;
lean_object* v_inst_2736_ = stack[6].m_obj;
lean_object* v_x_2737_ = stack[7].m_obj;
lean_object* v_x_2738_ = stack[8].m_obj;
uint8_t v_res_2740_;
v_res_2740_ = l_Prod_lexLtDec(lean_box(0), lean_box(0), v_inst_2732_, v_inst_2733_, v_inst_2734_, v_inst_2735_, v_inst_2736_, v_x_2737_, v_x_2738_);
stack->m_num = v_res_2740_;
}
LEAN_EXPORT lean_object* l_Prod_lexLtDec___boxed(lean_object* v_00_u03b1_2741_, lean_object* v_00_u03b2_2742_, lean_object* v_inst_2743_, lean_object* v_inst_2744_, lean_object* v_inst_2745_, lean_object* v_inst_2746_, lean_object* v_inst_2747_, lean_object* v_x_2748_, lean_object* v_x_2749_){
_start:
{
uint8_t v_res_2750_; lean_object* v_r_2751_; 
v_res_2750_ = l_Prod_lexLtDec(v_00_u03b1_2741_, v_00_u03b2_2742_, v_inst_2743_, v_inst_2744_, v_inst_2745_, v_inst_2746_, v_inst_2747_, v_x_2748_, v_x_2749_);
v_r_2751_ = lean_box(v_res_2750_);
return v_r_2751_;
}
}
LEAN_EXPORT lean_object* l_Prod_map___redArg(lean_object* v_f_2752_, lean_object* v_g_2753_, lean_object* v_x_2754_){
_start:
{
lean_object* v_fst_2755_; lean_object* v_snd_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2765_; 
v_fst_2755_ = lean_ctor_get(v_x_2754_, 0);
v_snd_2756_ = lean_ctor_get(v_x_2754_, 1);
v_isSharedCheck_2765_ = !lean_is_exclusive(v_x_2754_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2758_ = v_x_2754_;
v_isShared_2759_ = v_isSharedCheck_2765_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_snd_2756_);
lean_inc(v_fst_2755_);
lean_dec(v_x_2754_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2765_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2760_ = lean_apply_1(v_f_2752_, v_fst_2755_);
v___x_2761_ = lean_apply_1(v_g_2753_, v_snd_2756_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___x_2761_);
lean_ctor_set(v___x_2758_, 0, v___x_2760_);
v___x_2763_ = v___x_2758_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_map(lean_object* v_00_u03b1_u2081_2766_, lean_object* v_00_u03b1_u2082_2767_, lean_object* v_00_u03b2_u2081_2768_, lean_object* v_00_u03b2_u2082_2769_, lean_object* v_f_2770_, lean_object* v_g_2771_, lean_object* v_x_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Prod_map___redArg(v_f_2770_, v_g_2771_, v_x_2772_);
return v___x_2773_;
}
}
uint8_t l_instDecidableEqSigma___redArg(lean_object* v_h_u2081_2774_, lean_object* v_h_u2082_2775_, lean_object* v_x_2776_, lean_object* v_x_2777_){
_start:
{
lean_object* v_fst_2778_; lean_object* v_snd_2779_; lean_object* v_fst_2780_; lean_object* v_snd_2781_; lean_object* v_decide_2782_; uint8_t v___x_2783_; 
v_fst_2778_ = lean_ctor_get(v_x_2776_, 0);
lean_inc_n(v_fst_2778_, 2);
v_snd_2779_ = lean_ctor_get(v_x_2776_, 1);
lean_inc(v_snd_2779_);
lean_dec_ref(v_x_2776_);
v_fst_2780_ = lean_ctor_get(v_x_2777_, 0);
lean_inc(v_fst_2780_);
v_snd_2781_ = lean_ctor_get(v_x_2777_, 1);
lean_inc(v_snd_2781_);
lean_dec_ref(v_x_2777_);
v_decide_2782_ = lean_apply_2(v_h_u2081_2774_, v_fst_2778_, v_fst_2780_);
v___x_2783_ = lean_unbox(v_decide_2782_);
if (v___x_2783_ == 0)
{
uint8_t v___x_2784_; 
lean_dec(v_snd_2781_);
lean_dec(v_snd_2779_);
lean_dec(v_fst_2778_);
lean_dec_ref(v_h_u2082_2775_);
v___x_2784_ = lean_unbox(v_decide_2782_);
return v___x_2784_;
}
else
{
lean_object* v_decide_2785_; uint8_t v___x_2786_; 
v_decide_2785_ = lean_apply_3(v_h_u2082_2775_, v_fst_2778_, v_snd_2779_, v_snd_2781_);
v___x_2786_ = lean_unbox(v_decide_2785_);
return v___x_2786_;
}
}
}
LEAN_EXPORT void l_instDecidableEqSigma___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_u2081_2774_ = stack[0].m_obj;
lean_object* v_h_u2082_2775_ = stack[1].m_obj;
lean_object* v_x_2776_ = stack[2].m_obj;
lean_object* v_x_2777_ = stack[3].m_obj;
uint8_t v_res_2787_;
v_res_2787_ = l_instDecidableEqSigma___redArg(v_h_u2081_2774_, v_h_u2082_2775_, v_x_2776_, v_x_2777_);
stack->m_num = v_res_2787_;
}
LEAN_EXPORT lean_object* l_instDecidableEqSigma___redArg___boxed(lean_object* v_h_u2081_2788_, lean_object* v_h_u2082_2789_, lean_object* v_x_2790_, lean_object* v_x_2791_){
_start:
{
uint8_t v_res_2792_; lean_object* v_r_2793_; 
v_res_2792_ = l_instDecidableEqSigma___redArg(v_h_u2081_2788_, v_h_u2082_2789_, v_x_2790_, v_x_2791_);
v_r_2793_ = lean_box(v_res_2792_);
return v_r_2793_;
}
}
uint8_t l_instDecidableEqSigma(lean_object* v_00_u03b1_2794_, lean_object* v_00_u03b2_2795_, lean_object* v_h_u2081_2796_, lean_object* v_h_u2082_2797_, lean_object* v_x_2798_, lean_object* v_x_2799_){
_start:
{
uint8_t v___x_2800_; 
v___x_2800_ = l_instDecidableEqSigma___redArg(v_h_u2081_2796_, v_h_u2082_2797_, v_x_2798_, v_x_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT void l_instDecidableEqSigma_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_u2081_2796_ = stack[2].m_obj;
lean_object* v_h_u2082_2797_ = stack[3].m_obj;
lean_object* v_x_2798_ = stack[4].m_obj;
lean_object* v_x_2799_ = stack[5].m_obj;
uint8_t v_res_2801_;
v_res_2801_ = l_instDecidableEqSigma(lean_box(0), lean_box(0), v_h_u2081_2796_, v_h_u2082_2797_, v_x_2798_, v_x_2799_);
stack->m_num = v_res_2801_;
}
LEAN_EXPORT lean_object* l_instDecidableEqSigma___boxed(lean_object* v_00_u03b1_2802_, lean_object* v_00_u03b2_2803_, lean_object* v_h_u2081_2804_, lean_object* v_h_u2082_2805_, lean_object* v_x_2806_, lean_object* v_x_2807_){
_start:
{
uint8_t v_res_2808_; lean_object* v_r_2809_; 
v_res_2808_ = l_instDecidableEqSigma(v_00_u03b1_2802_, v_00_u03b2_2803_, v_h_u2081_2804_, v_h_u2082_2805_, v_x_2806_, v_x_2807_);
v_r_2809_ = lean_box(v_res_2808_);
return v_r_2809_;
}
}
uint8_t l_instDecidableEqPSigma___redArg(lean_object* v_h_u2081_2810_, lean_object* v_h_u2082_2811_, lean_object* v_x_2812_, lean_object* v_x_2813_){
_start:
{
lean_object* v_fst_2814_; lean_object* v_snd_2815_; lean_object* v_fst_2816_; lean_object* v_snd_2817_; lean_object* v_decide_2818_; uint8_t v___x_2819_; 
v_fst_2814_ = lean_ctor_get(v_x_2812_, 0);
lean_inc_n(v_fst_2814_, 2);
v_snd_2815_ = lean_ctor_get(v_x_2812_, 1);
lean_inc(v_snd_2815_);
lean_dec_ref(v_x_2812_);
v_fst_2816_ = lean_ctor_get(v_x_2813_, 0);
lean_inc(v_fst_2816_);
v_snd_2817_ = lean_ctor_get(v_x_2813_, 1);
lean_inc(v_snd_2817_);
lean_dec_ref(v_x_2813_);
v_decide_2818_ = lean_apply_2(v_h_u2081_2810_, v_fst_2814_, v_fst_2816_);
v___x_2819_ = lean_unbox(v_decide_2818_);
if (v___x_2819_ == 0)
{
uint8_t v___x_2820_; 
lean_dec(v_snd_2817_);
lean_dec(v_snd_2815_);
lean_dec(v_fst_2814_);
lean_dec_ref(v_h_u2082_2811_);
v___x_2820_ = lean_unbox(v_decide_2818_);
return v___x_2820_;
}
else
{
lean_object* v_decide_2821_; uint8_t v___x_2822_; 
v_decide_2821_ = lean_apply_3(v_h_u2082_2811_, v_fst_2814_, v_snd_2815_, v_snd_2817_);
v___x_2822_ = lean_unbox(v_decide_2821_);
return v___x_2822_;
}
}
}
LEAN_EXPORT void l_instDecidableEqPSigma___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_u2081_2810_ = stack[0].m_obj;
lean_object* v_h_u2082_2811_ = stack[1].m_obj;
lean_object* v_x_2812_ = stack[2].m_obj;
lean_object* v_x_2813_ = stack[3].m_obj;
uint8_t v_res_2823_;
v_res_2823_ = l_instDecidableEqPSigma___redArg(v_h_u2081_2810_, v_h_u2082_2811_, v_x_2812_, v_x_2813_);
stack->m_num = v_res_2823_;
}
LEAN_EXPORT lean_object* l_instDecidableEqPSigma___redArg___boxed(lean_object* v_h_u2081_2824_, lean_object* v_h_u2082_2825_, lean_object* v_x_2826_, lean_object* v_x_2827_){
_start:
{
uint8_t v_res_2828_; lean_object* v_r_2829_; 
v_res_2828_ = l_instDecidableEqPSigma___redArg(v_h_u2081_2824_, v_h_u2082_2825_, v_x_2826_, v_x_2827_);
v_r_2829_ = lean_box(v_res_2828_);
return v_r_2829_;
}
}
uint8_t l_instDecidableEqPSigma(lean_object* v_00_u03b1_2830_, lean_object* v_00_u03b2_2831_, lean_object* v_h_u2081_2832_, lean_object* v_h_u2082_2833_, lean_object* v_x_2834_, lean_object* v_x_2835_){
_start:
{
uint8_t v___x_2836_; 
v___x_2836_ = l_instDecidableEqPSigma___redArg(v_h_u2081_2832_, v_h_u2082_2833_, v_x_2834_, v_x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT void l_instDecidableEqPSigma_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_u2081_2832_ = stack[2].m_obj;
lean_object* v_h_u2082_2833_ = stack[3].m_obj;
lean_object* v_x_2834_ = stack[4].m_obj;
lean_object* v_x_2835_ = stack[5].m_obj;
uint8_t v_res_2837_;
v_res_2837_ = l_instDecidableEqPSigma(lean_box(0), lean_box(0), v_h_u2081_2832_, v_h_u2082_2833_, v_x_2834_, v_x_2835_);
stack->m_num = v_res_2837_;
}
LEAN_EXPORT lean_object* l_instDecidableEqPSigma___boxed(lean_object* v_00_u03b1_2838_, lean_object* v_00_u03b2_2839_, lean_object* v_h_u2081_2840_, lean_object* v_h_u2082_2841_, lean_object* v_x_2842_, lean_object* v_x_2843_){
_start:
{
uint8_t v_res_2844_; lean_object* v_r_2845_; 
v_res_2844_ = l_instDecidableEqPSigma(v_00_u03b1_2838_, v_00_u03b2_2839_, v_h_u2081_2840_, v_h_u2082_2841_, v_x_2842_, v_x_2843_);
v_r_2845_ = lean_box(v_res_2844_);
return v_r_2845_;
}
}
static lean_object* _init_l_instInhabitedPUnit(void){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = lean_box(0);
return v___x_2846_;
}
}
uint8_t l_instDecidableEqPUnit___redArg(){
_start:
{
uint8_t v___x_2848_; 
v___x_2848_ = 1;
return v___x_2848_;
}
}
LEAN_EXPORT void l_instDecidableEqPUnit___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_2849_;
v_res_2849_ = l_instDecidableEqPUnit___redArg();
stack->m_num = v_res_2849_;
}
LEAN_EXPORT lean_object* l_instDecidableEqPUnit___redArg___boxed(lean_object* v___dummy_2850_){
_start:
{
uint8_t v_res_2851_; lean_object* v_r_2852_; 
v_res_2851_ = l_instDecidableEqPUnit___redArg();
v_r_2852_ = lean_box(v_res_2851_);
return v_r_2852_;
}
}
uint8_t l_instDecidableEqPUnit(lean_object* v_a_2853_, lean_object* v_b_2854_){
_start:
{
uint8_t v___x_2855_; 
v___x_2855_ = 1;
return v___x_2855_;
}
}
LEAN_EXPORT void l_instDecidableEqPUnit_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2853_ = stack[0].m_obj;
lean_object* v_b_2854_ = stack[1].m_obj;
uint8_t v_res_2856_;
v_res_2856_ = l_instDecidableEqPUnit(v_a_2853_, v_b_2854_);
stack->m_num = v_res_2856_;
}
LEAN_EXPORT lean_object* l_instDecidableEqPUnit___boxed(lean_object* v_a_2857_, lean_object* v_b_2858_){
_start:
{
uint8_t v_res_2859_; lean_object* v_r_2860_; 
v_res_2859_ = l_instDecidableEqPUnit(v_a_2857_, v_b_2858_);
v_r_2860_ = lean_box(v_res_2859_);
return v_r_2860_;
}
}
lean_object* l_instHasEquivOfSetoid___redArg(){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = lean_box(0);
return v___x_2862_;
}
}
LEAN_EXPORT void l_instHasEquivOfSetoid___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2863_;
v_res_2863_ = l_instHasEquivOfSetoid___redArg();
stack->m_obj
 = v_res_2863_;
}
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid___redArg___boxed(lean_object* v___dummy_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_instHasEquivOfSetoid___redArg();
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid(lean_object* v_00_u03b1_2866_, lean_object* v_inst_2867_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = lean_box(0);
return v___x_2868_;
}
}
uint8_t l_instDecidableEqOfIff___redArg(uint8_t v_d_2869_){
_start:
{
return v_d_2869_;
}
}
LEAN_EXPORT void l_instDecidableEqOfIff___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_d_2869_ = stack[0].m_num;
uint8_t v_res_2870_;
v_res_2870_ = l_instDecidableEqOfIff___redArg(v_d_2869_);
stack->m_num = v_res_2870_;
}
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___redArg___boxed(lean_object* v_d_2871_){
_start:
{
uint8_t v_d_boxed_2872_; uint8_t v_res_2873_; lean_object* v_r_2874_; 
v_d_boxed_2872_ = lean_unbox(v_d_2871_);
v_res_2873_ = l_instDecidableEqOfIff___redArg(v_d_boxed_2872_);
v_r_2874_ = lean_box(v_res_2873_);
return v_r_2874_;
}
}
uint8_t l_instDecidableEqOfIff(lean_object* v_p_2875_, lean_object* v_q_2876_, uint8_t v_d_2877_){
_start:
{
return v_d_2877_;
}
}
LEAN_EXPORT void l_instDecidableEqOfIff_0interp(lean_interpreter_value* stack)
{
uint8_t v_d_2877_ = stack[2].m_num;
uint8_t v_res_2878_;
v_res_2878_ = l_instDecidableEqOfIff(lean_box(0), lean_box(0), v_d_2877_);
stack->m_num = v_res_2878_;
}
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___boxed(lean_object* v_p_2879_, lean_object* v_q_2880_, lean_object* v_d_2881_){
_start:
{
uint8_t v_d_boxed_2882_; uint8_t v_res_2883_; lean_object* v_r_2884_; 
v_d_boxed_2882_ = lean_unbox(v_d_2881_);
v_res_2883_ = l_instDecidableEqOfIff(v_p_2879_, v_q_2880_, v_d_boxed_2882_);
v_r_2884_ = lean_box(v_res_2883_);
return v_r_2884_;
}
}
lean_object* l_Not_elim___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_Not_elim___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2886_;
v_res_2886_ = l_Not_elim___redArg();
stack->m_obj
 = v_res_2886_;
}
LEAN_EXPORT lean_object* l_Not_elim___redArg___boxed(lean_object* v___dummy_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Not_elim___redArg();
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Not_elim(lean_object* v_a_2889_, lean_object* v_00_u03b1_2890_, lean_object* v_H1_2891_, lean_object* v_H2_2892_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_And_elim___redArg(lean_object* v_f_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = lean_apply_2(v_f_2893_, lean_box(0), lean_box(0));
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_And_elim(lean_object* v_a_2895_, lean_object* v_b_2896_, lean_object* v_00_u03b1_2897_, lean_object* v_f_2898_, lean_object* v_h_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_apply_2(v_f_2898_, lean_box(0), lean_box(0));
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Iff_elim___redArg(lean_object* v_f_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_apply_2(v_f_2901_, lean_box(0), lean_box(0));
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Iff_elim(lean_object* v_a_2903_, lean_object* v_b_2904_, lean_object* v_00_u03b1_2905_, lean_object* v_f_2906_, lean_object* v_h_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = lean_apply_2(v_f_2906_, lean_box(0), lean_box(0));
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Quot_rec___redArg(lean_object* v_f_2909_, lean_object* v_q_2910_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_apply_1(v_f_2909_, v_q_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Quot_rec(lean_object* v_00_u03b1_2912_, lean_object* v_r_2913_, lean_object* v_motive_2914_, lean_object* v_f_2915_, lean_object* v_h_2916_, lean_object* v_q_2917_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = lean_apply_1(v_f_2915_, v_q_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOn___redArg(lean_object* v_q_2919_, lean_object* v_f_2920_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_apply_1(v_f_2920_, v_q_2919_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOn(lean_object* v_00_u03b1_2922_, lean_object* v_r_2923_, lean_object* v_motive_2924_, lean_object* v_q_2925_, lean_object* v_f_2926_, lean_object* v_h_2927_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_apply_1(v_f_2926_, v_q_2925_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOnSubsingleton___redArg(lean_object* v_q_2929_, lean_object* v_f_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = lean_apply_1(v_f_2930_, v_q_2929_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOnSubsingleton(lean_object* v_00_u03b1_2932_, lean_object* v_r_2933_, lean_object* v_motive_2934_, lean_object* v_h_2935_, lean_object* v_q_2936_, lean_object* v_f_2937_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = lean_apply_1(v_f_2937_, v_q_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Quot_hrecOn___redArg(lean_object* v_q_2939_, lean_object* v_f_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = lean_apply_1(v_f_2940_, v_q_2939_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Quot_hrecOn(lean_object* v_00_u03b1_2942_, lean_object* v_r_2943_, lean_object* v_motive_2944_, lean_object* v_q_2945_, lean_object* v_f_2946_, lean_object* v_c_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = lean_apply_1(v_f_2946_, v_q_2945_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___redArg(lean_object* v_a_2949_){
_start:
{
lean_inc(v_a_2949_);
return v_a_2949_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___redArg___boxed(lean_object* v_a_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Quotient_mk___redArg(v_a_2950_);
lean_dec(v_a_2950_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk(lean_object* v_00_u03b1_2952_, lean_object* v_s_2953_, lean_object* v_a_2954_){
_start:
{
lean_inc(v_a_2954_);
return v_a_2954_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___boxed(lean_object* v_00_u03b1_2955_, lean_object* v_s_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Quotient_mk(v_00_u03b1_2955_, v_s_2956_, v_a_2957_);
lean_dec(v_a_2957_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___redArg(lean_object* v_a_2959_){
_start:
{
lean_inc(v_a_2959_);
return v_a_2959_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___redArg___boxed(lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Quotient_mk_x27___redArg(v_a_2960_);
lean_dec(v_a_2960_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27(lean_object* v_00_u03b1_2962_, lean_object* v_s_2963_, lean_object* v_a_2964_){
_start:
{
lean_inc(v_a_2964_);
return v_a_2964_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___boxed(lean_object* v_00_u03b1_2965_, lean_object* v_s_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Quotient_mk_x27(v_00_u03b1_2965_, v_s_2966_, v_a_2967_);
lean_dec(v_a_2967_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift___redArg(lean_object* v_f_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_apply_1(v_f_2969_, v_a_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift(lean_object* v_00_u03b1_2972_, lean_object* v_00_u03b2_2973_, lean_object* v_s_2974_, lean_object* v_f_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_apply_1(v_f_2975_, v_a_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn___redArg(lean_object* v_q_2979_, lean_object* v_f_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_apply_1(v_f_2980_, v_q_2979_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn(lean_object* v_00_u03b1_2982_, lean_object* v_00_u03b2_2983_, lean_object* v_s_2984_, lean_object* v_q_2985_, lean_object* v_f_2986_, lean_object* v_c_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_apply_1(v_f_2986_, v_q_2985_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Quotient_rec___redArg(lean_object* v_f_2989_, lean_object* v_q_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_apply_1(v_f_2989_, v_q_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Quotient_rec(lean_object* v_00_u03b1_2992_, lean_object* v_s_2993_, lean_object* v_motive_2994_, lean_object* v_f_2995_, lean_object* v_h_2996_, lean_object* v_q_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_apply_1(v_f_2995_, v_q_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOn___redArg(lean_object* v_q_2999_, lean_object* v_f_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_apply_1(v_f_3000_, v_q_2999_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOn(lean_object* v_00_u03b1_3002_, lean_object* v_s_3003_, lean_object* v_motive_3004_, lean_object* v_q_3005_, lean_object* v_f_3006_, lean_object* v_h_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_apply_1(v_f_3006_, v_q_3005_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton___redArg(lean_object* v_q_3009_, lean_object* v_f_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = lean_apply_1(v_f_3010_, v_q_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton(lean_object* v_00_u03b1_3012_, lean_object* v_s_3013_, lean_object* v_motive_3014_, lean_object* v_h_3015_, lean_object* v_q_3016_, lean_object* v_f_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_apply_1(v_f_3017_, v_q_3016_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Quotient_hrecOn___redArg(lean_object* v_q_3019_, lean_object* v_f_3020_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_apply_1(v_f_3020_, v_q_3019_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Quotient_hrecOn(lean_object* v_00_u03b1_3022_, lean_object* v_s_3023_, lean_object* v_motive_3024_, lean_object* v_q_3025_, lean_object* v_f_3026_, lean_object* v_c_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = lean_apply_1(v_f_3026_, v_q_3025_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift_u2082___redArg(lean_object* v_f_3029_, lean_object* v_q_u2081_3030_, lean_object* v_q_u2082_3031_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = lean_apply_2(v_f_3029_, v_q_u2081_3030_, v_q_u2082_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift_u2082(lean_object* v_00_u03b1_3033_, lean_object* v_00_u03b2_3034_, lean_object* v_00_u03c6_3035_, lean_object* v_s_u2081_3036_, lean_object* v_s_u2082_3037_, lean_object* v_f_3038_, lean_object* v_c_3039_, lean_object* v_q_u2081_3040_, lean_object* v_q_u2082_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_apply_2(v_f_3038_, v_q_u2081_3040_, v_q_u2082_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn_u2082___redArg(lean_object* v_q_u2081_3043_, lean_object* v_q_u2082_3044_, lean_object* v_f_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = lean_apply_2(v_f_3045_, v_q_u2081_3043_, v_q_u2082_3044_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn_u2082(lean_object* v_00_u03b1_3047_, lean_object* v_00_u03b2_3048_, lean_object* v_00_u03c6_3049_, lean_object* v_s_u2081_3050_, lean_object* v_s_u2082_3051_, lean_object* v_q_u2081_3052_, lean_object* v_q_u2082_3053_, lean_object* v_f_3054_, lean_object* v_c_3055_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_apply_2(v_f_3054_, v_q_u2081_3052_, v_q_u2082_3053_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton_u2082___redArg(lean_object* v_q_u2081_3057_, lean_object* v_q_u2082_3058_, lean_object* v_g_3059_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = lean_apply_2(v_g_3059_, v_q_u2081_3057_, v_q_u2082_3058_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton_u2082(lean_object* v_00_u03b1_3061_, lean_object* v_00_u03b2_3062_, lean_object* v_s_u2081_3063_, lean_object* v_s_u2082_3064_, lean_object* v_motive_3065_, lean_object* v_s_3066_, lean_object* v_q_u2081_3067_, lean_object* v_q_u2082_3068_, lean_object* v_g_3069_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_apply_2(v_g_3069_, v_q_u2081_3067_, v_q_u2082_3068_);
return v___x_3070_;
}
}
uint8_t l_Quotient_decidableEq___redArg(lean_object* v_d_3071_, lean_object* v_q_u2081_3072_, lean_object* v_q_u2082_3073_){
_start:
{
lean_object* v___x_3074_; uint8_t v___x_3075_; 
v___x_3074_ = lean_apply_2(v_d_3071_, v_q_u2081_3072_, v_q_u2082_3073_);
v___x_3075_ = lean_unbox(v___x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT void l_Quotient_decidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_3071_ = stack[0].m_obj;
lean_object* v_q_u2081_3072_ = stack[1].m_obj;
lean_object* v_q_u2082_3073_ = stack[2].m_obj;
uint8_t v_res_3076_;
v_res_3076_ = l_Quotient_decidableEq___redArg(v_d_3071_, v_q_u2081_3072_, v_q_u2082_3073_);
stack->m_num = v_res_3076_;
}
LEAN_EXPORT lean_object* l_Quotient_decidableEq___redArg___boxed(lean_object* v_d_3077_, lean_object* v_q_u2081_3078_, lean_object* v_q_u2082_3079_){
_start:
{
uint8_t v_res_3080_; lean_object* v_r_3081_; 
v_res_3080_ = l_Quotient_decidableEq___redArg(v_d_3077_, v_q_u2081_3078_, v_q_u2082_3079_);
v_r_3081_ = lean_box(v_res_3080_);
return v_r_3081_;
}
}
uint8_t l_Quotient_decidableEq(lean_object* v_00_u03b1_3082_, lean_object* v_s_3083_, lean_object* v_d_3084_, lean_object* v_q_u2081_3085_, lean_object* v_q_u2082_3086_){
_start:
{
lean_object* v___x_3087_; uint8_t v___x_3088_; 
v___x_3087_ = lean_apply_2(v_d_3084_, v_q_u2081_3085_, v_q_u2082_3086_);
v___x_3088_ = lean_unbox(v___x_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT void l_Quotient_decidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3083_ = stack[1].m_obj;
lean_object* v_d_3084_ = stack[2].m_obj;
lean_object* v_q_u2081_3085_ = stack[3].m_obj;
lean_object* v_q_u2082_3086_ = stack[4].m_obj;
uint8_t v_res_3089_;
v_res_3089_ = l_Quotient_decidableEq(lean_box(0), v_s_3083_, v_d_3084_, v_q_u2081_3085_, v_q_u2082_3086_);
stack->m_num = v_res_3089_;
}
LEAN_EXPORT lean_object* l_Quotient_decidableEq___boxed(lean_object* v_00_u03b1_3090_, lean_object* v_s_3091_, lean_object* v_d_3092_, lean_object* v_q_u2081_3093_, lean_object* v_q_u2082_3094_){
_start:
{
uint8_t v_res_3095_; lean_object* v_r_3096_; 
v_res_3095_ = l_Quotient_decidableEq(v_00_u03b1_3090_, v_s_3091_, v_d_3092_, v_q_u2081_3093_, v_q_u2082_3094_);
v_r_3096_ = lean_box(v_res_3095_);
return v_r_3096_;
}
}
LEAN_EXPORT lean_object* l_Quot_pliftOn___redArg(lean_object* v_q_3097_, lean_object* v_f_3098_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = lean_apply_2(v_f_3098_, v_q_3097_, lean_box(0));
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Quot_pliftOn(lean_object* v_00_u03b2_3100_, lean_object* v_00_u03b1_3101_, lean_object* v_r_3102_, lean_object* v_q_3103_, lean_object* v_f_3104_, lean_object* v_h_3105_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_apply_2(v_f_3104_, v_q_3103_, lean_box(0));
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Quotient_pliftOn___redArg(lean_object* v_q_3107_, lean_object* v_f_3108_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_apply_2(v_f_3108_, v_q_3107_, lean_box(0));
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Quotient_pliftOn(lean_object* v_00_u03b2_3110_, lean_object* v_00_u03b1_3111_, lean_object* v_s_3112_, lean_object* v_q_3113_, lean_object* v_f_3114_, lean_object* v_h_3115_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = lean_apply_2(v_f_3114_, v_q_3113_, lean_box(0));
return v___x_3116_;
}
}
lean_object* l_Setoid_trivial___redArg(){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_box(0);
return v___x_3118_;
}
}
LEAN_EXPORT void l_Setoid_trivial___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3119_;
v_res_3119_ = l_Setoid_trivial___redArg();
stack->m_obj
 = v_res_3119_;
}
LEAN_EXPORT lean_object* l_Setoid_trivial___redArg___boxed(lean_object* v___dummy_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Setoid_trivial___redArg();
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Setoid_trivial(lean_object* v_00_u03b1_3122_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_box(0);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___redArg(lean_object* v_x_3124_){
_start:
{
lean_inc(v_x_3124_);
return v_x_3124_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___redArg___boxed(lean_object* v_x_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Squash_mk___redArg(v_x_3125_);
lean_dec(v_x_3125_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk(lean_object* v_00_u03b1_3127_, lean_object* v_x_3128_){
_start:
{
lean_inc(v_x_3128_);
return v_x_3128_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___boxed(lean_object* v_00_u03b1_3129_, lean_object* v_x_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Squash_mk(v_00_u03b1_3129_, v_x_3130_);
lean_dec(v_x_3130_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Squash_lift___redArg(lean_object* v_s_3132_, lean_object* v_f_3133_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = lean_apply_1(v_f_3133_, v_s_3132_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Squash_lift(lean_object* v_00_u03b1_3135_, lean_object* v_00_u03b2_3136_, lean_object* v_inst_3137_, lean_object* v_s_3138_, lean_object* v_f_3139_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = lean_apply_1(v_f_3139_, v_s_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___redArg(lean_object* v_x_3141_){
_start:
{
lean_inc(v_x_3141_);
return v_x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___redArg___boxed(lean_object* v_x_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Lean_opaqueId___redArg(v_x_3142_);
lean_dec(v_x_3142_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId(lean_object* v_00_u03b1_3144_, lean_object* v_x_3145_){
_start:
{
lean_inc(v_x_3145_);
return v_x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___boxed(lean_object* v_00_u03b1_3146_, lean_object* v_x_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_opaqueId(v_00_u03b1_3146_, v_x_3147_);
lean_dec(v_x_3147_);
return v_res_3148_;
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
