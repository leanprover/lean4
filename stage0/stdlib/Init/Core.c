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
LEAN_EXPORT lean_object* l_Sum_ctorIdx___impl___redArg(lean_object* v_x_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_obj_tag_nat(v_x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___impl___redArg___boxed(lean_object* v_x_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Sum_ctorIdx___impl___redArg(v_x_385_);
lean_dec_ref(v_x_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___impl(lean_object* v_00_u03b1_387_, lean_object* v_00_u03b2_388_, lean_object* v_x_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lean_obj_tag_nat(v_x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorIdx___impl___boxed(lean_object* v_00_u03b1_391_, lean_object* v_00_u03b2_392_, lean_object* v_x_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Sum_ctorIdx___impl(v_00_u03b1_391_, v_00_u03b2_392_, v_x_393_);
lean_dec_ref(v_x_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim___redArg(lean_object* v_t_395_, lean_object* v_k_396_){
_start:
{
lean_object* v_val_397_; lean_object* v___x_398_; 
v_val_397_ = lean_ctor_get(v_t_395_, 0);
lean_inc(v_val_397_);
lean_dec_ref(v_t_395_);
v___x_398_ = lean_apply_1(v_k_396_, v_val_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim(lean_object* v_00_u03b1_399_, lean_object* v_00_u03b2_400_, lean_object* v_motive_401_, lean_object* v_ctorIdx_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_k_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Sum_ctorElim___redArg(v_t_403_, v_k_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Sum_ctorElim___boxed(lean_object* v_00_u03b1_407_, lean_object* v_00_u03b2_408_, lean_object* v_motive_409_, lean_object* v_ctorIdx_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_k_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Sum_ctorElim(v_00_u03b1_407_, v_00_u03b2_408_, v_motive_409_, v_ctorIdx_410_, v_t_411_, v_h_412_, v_k_413_);
lean_dec(v_ctorIdx_410_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Sum_inl_elim___redArg(lean_object* v_t_415_, lean_object* v_inl_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Sum_ctorElim___redArg(v_t_415_, v_inl_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Sum_inl_elim(lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_motive_420_, lean_object* v_t_421_, lean_object* v_h_422_, lean_object* v_inl_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Sum_ctorElim___redArg(v_t_421_, v_inl_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Sum_inr_elim___redArg(lean_object* v_t_425_, lean_object* v_inr_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Sum_ctorElim___redArg(v_t_425_, v_inr_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Sum_inr_elim(lean_object* v_00_u03b1_428_, lean_object* v_00_u03b2_429_, lean_object* v_motive_430_, lean_object* v_t_431_, lean_object* v_h_432_, lean_object* v_inr_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Sum_ctorElim___redArg(v_t_431_, v_inr_433_);
return v___x_434_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2295____1___closed__1(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__0));
v___x_456_ = l_String_toRawSubstring_x27(v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295____1(lean_object* v_x_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = ((lean_object*)(l_term___u2295___00__closed__1));
lean_inc(v_x_470_);
v___x_474_ = l_Lean_Syntax_isOfKind(v_x_470_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_x_470_);
v___x_475_ = lean_box(1);
v___x_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v_a_472_);
return v___x_476_;
}
else
{
lean_object* v_quotContext_477_; lean_object* v_currMacroScope_478_; lean_object* v_ref_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_quotContext_477_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_478_ = lean_ctor_get(v_a_471_, 2);
v_ref_479_ = lean_ctor_get(v_a_471_, 5);
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = l_Lean_Syntax_getArg(v_x_470_, v___x_480_);
v___x_482_ = lean_unsigned_to_nat(2u);
v___x_483_ = l_Lean_Syntax_getArg(v_x_470_, v___x_482_);
lean_dec(v_x_470_);
v___x_484_ = 0;
v___x_485_ = l_Lean_SourceInfo_fromRef(v_ref_479_, v___x_484_);
v___x_486_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_487_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2295____1___closed__1, &l___aux__Init__Core______macroRules__term___u2295____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2295____1___closed__1);
v___x_488_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__2));
lean_inc(v_currMacroScope_478_);
lean_inc(v_quotContext_477_);
v___x_489_ = l_Lean_addMacroScope(v_quotContext_477_, v___x_488_, v_currMacroScope_478_);
v___x_490_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295____1___closed__6));
lean_inc_n(v___x_485_, 2);
v___x_491_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_491_, 0, v___x_485_);
lean_ctor_set(v___x_491_, 1, v___x_487_);
lean_ctor_set(v___x_491_, 2, v___x_489_);
lean_ctor_set(v___x_491_, 3, v___x_490_);
v___x_492_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_493_ = l_Lean_Syntax_node2(v___x_485_, v___x_492_, v___x_481_, v___x_483_);
v___x_494_ = l_Lean_Syntax_node2(v___x_485_, v___x_486_, v___x_491_, v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_a_472_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295____1___boxed(lean_object* v_x_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___aux__Init__Core______macroRules__term___u2295____1(v_x_496_, v_a_497_, v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Sum__1(lean_object* v_x_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_500_);
v___x_504_ = l_Lean_Syntax_isOfKind(v_x_500_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v_x_500_);
v___x_505_ = lean_box(0);
v___x_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v_a_502_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = l_Lean_Syntax_getArg(v_x_500_, v___x_507_);
v___x_509_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_508_);
v___x_510_ = l_Lean_Syntax_isOfKind(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v___x_508_);
lean_dec(v_x_500_);
v___x_511_ = lean_box(0);
v___x_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v_a_502_);
return v___x_512_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = l_Lean_Syntax_getArg(v_x_500_, v___x_513_);
lean_dec(v_x_500_);
v___x_515_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_514_);
v___x_516_ = l_Lean_Syntax_matchesNull(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v___x_514_);
lean_dec(v___x_508_);
v___x_517_ = lean_box(0);
v___x_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v_a_502_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v_ref_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_519_ = l_Lean_Syntax_getArg(v___x_514_, v___x_507_);
v___x_520_ = l_Lean_Syntax_getArg(v___x_514_, v___x_513_);
lean_dec(v___x_514_);
v_ref_521_ = l_Lean_replaceRef(v___x_508_, v_a_501_);
lean_dec(v___x_508_);
v___x_522_ = 0;
v___x_523_ = l_Lean_SourceInfo_fromRef(v_ref_521_, v___x_522_);
lean_dec(v_ref_521_);
v___x_524_ = ((lean_object*)(l_term___u2295___00__closed__1));
v___x_525_ = ((lean_object*)(l_term___u2295___00__closed__2));
lean_inc(v___x_523_);
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_523_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_Syntax_node3(v___x_523_, v___x_524_, v___x_519_, v___x_526_, v___x_520_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v_a_502_);
return v___x_528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Sum__1___boxed(lean_object* v_x_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___aux__Init__Core______unexpand__Sum__1(v_x_529_, v_a_530_, v_a_531_);
lean_dec(v_a_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___impl___redArg(lean_object* v_x_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_obj_tag_nat(v_x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___impl___redArg___boxed(lean_object* v_x_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_PSum_ctorIdx___impl___redArg(v_x_535_);
lean_dec_ref(v_x_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___impl(lean_object* v_00_u03b1_537_, lean_object* v_00_u03b2_538_, lean_object* v_x_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = lean_obj_tag_nat(v_x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorIdx___impl___boxed(lean_object* v_00_u03b1_541_, lean_object* v_00_u03b2_542_, lean_object* v_x_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_PSum_ctorIdx___impl(v_00_u03b1_541_, v_00_u03b2_542_, v_x_543_);
lean_dec_ref(v_x_543_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim___redArg(lean_object* v_t_545_, lean_object* v_k_546_){
_start:
{
lean_object* v_val_547_; lean_object* v___x_548_; 
v_val_547_ = lean_ctor_get(v_t_545_, 0);
lean_inc(v_val_547_);
lean_dec_ref(v_t_545_);
v___x_548_ = lean_apply_1(v_k_546_, v_val_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim(lean_object* v_00_u03b1_549_, lean_object* v_00_u03b2_550_, lean_object* v_motive_551_, lean_object* v_ctorIdx_552_, lean_object* v_t_553_, lean_object* v_h_554_, lean_object* v_k_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_PSum_ctorElim___redArg(v_t_553_, v_k_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_PSum_ctorElim___boxed(lean_object* v_00_u03b1_557_, lean_object* v_00_u03b2_558_, lean_object* v_motive_559_, lean_object* v_ctorIdx_560_, lean_object* v_t_561_, lean_object* v_h_562_, lean_object* v_k_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_PSum_ctorElim(v_00_u03b1_557_, v_00_u03b2_558_, v_motive_559_, v_ctorIdx_560_, v_t_561_, v_h_562_, v_k_563_);
lean_dec(v_ctorIdx_560_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_PSum_inl_elim___redArg(lean_object* v_t_565_, lean_object* v_inl_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_PSum_ctorElim___redArg(v_t_565_, v_inl_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_PSum_inl_elim(lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_motive_570_, lean_object* v_t_571_, lean_object* v_h_572_, lean_object* v_inl_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_PSum_ctorElim___redArg(v_t_571_, v_inl_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_PSum_inr_elim___redArg(lean_object* v_t_575_, lean_object* v_inr_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_PSum_ctorElim___redArg(v_t_575_, v_inr_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_PSum_inr_elim(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_motive_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_inr_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_PSum_ctorElim___redArg(v_t_581_, v_inr_583_);
return v___x_584_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__0));
v___x_603_ = l_String_toRawSubstring_x27(v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1(lean_object* v_x_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = ((lean_object*)(l_term___u2295_x27___00__closed__1));
lean_inc(v_x_617_);
v___x_621_ = l_Lean_Syntax_isOfKind(v_x_617_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec(v_x_617_);
v___x_622_ = lean_box(1);
v___x_623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v_a_619_);
return v___x_623_;
}
else
{
lean_object* v_quotContext_624_; lean_object* v_currMacroScope_625_; lean_object* v_ref_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_quotContext_624_ = lean_ctor_get(v_a_618_, 1);
v_currMacroScope_625_ = lean_ctor_get(v_a_618_, 2);
v_ref_626_ = lean_ctor_get(v_a_618_, 5);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = l_Lean_Syntax_getArg(v_x_617_, v___x_627_);
v___x_629_ = lean_unsigned_to_nat(2u);
v___x_630_ = l_Lean_Syntax_getArg(v_x_617_, v___x_629_);
lean_dec(v_x_617_);
v___x_631_ = 0;
v___x_632_ = l_Lean_SourceInfo_fromRef(v_ref_626_, v___x_631_);
v___x_633_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_634_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1, &l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__1);
v___x_635_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__2));
lean_inc(v_currMacroScope_625_);
lean_inc(v_quotContext_624_);
v___x_636_ = l_Lean_addMacroScope(v_quotContext_624_, v___x_635_, v_currMacroScope_625_);
v___x_637_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2295_x27____1___closed__6));
lean_inc_n(v___x_632_, 2);
v___x_638_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_638_, 0, v___x_632_);
lean_ctor_set(v___x_638_, 1, v___x_634_);
lean_ctor_set(v___x_638_, 2, v___x_636_);
lean_ctor_set(v___x_638_, 3, v___x_637_);
v___x_639_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_640_ = l_Lean_Syntax_node2(v___x_632_, v___x_639_, v___x_628_, v___x_630_);
v___x_641_ = l_Lean_Syntax_node2(v___x_632_, v___x_633_, v___x_638_, v___x_640_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v_a_619_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2295_x27____1___boxed(lean_object* v_x_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l___aux__Init__Core______macroRules__term___u2295_x27____1(v_x_643_, v_a_644_, v_a_645_);
lean_dec_ref(v_a_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__PSum__1(lean_object* v_x_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_647_);
v___x_651_ = l_Lean_Syntax_isOfKind(v_x_647_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_x_647_);
v___x_652_ = lean_box(0);
v___x_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v_a_649_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = l_Lean_Syntax_getArg(v_x_647_, v___x_654_);
v___x_656_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_655_);
v___x_657_ = l_Lean_Syntax_isOfKind(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v___x_655_);
lean_dec(v_x_647_);
v___x_658_ = lean_box(0);
v___x_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v_a_649_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = l_Lean_Syntax_getArg(v_x_647_, v___x_660_);
lean_dec(v_x_647_);
v___x_662_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_661_);
v___x_663_ = l_Lean_Syntax_matchesNull(v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v___x_661_);
lean_dec(v___x_655_);
v___x_664_ = lean_box(0);
v___x_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v_a_649_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_ref_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_666_ = l_Lean_Syntax_getArg(v___x_661_, v___x_654_);
v___x_667_ = l_Lean_Syntax_getArg(v___x_661_, v___x_660_);
lean_dec(v___x_661_);
v_ref_668_ = l_Lean_replaceRef(v___x_655_, v_a_648_);
lean_dec(v___x_655_);
v___x_669_ = 0;
v___x_670_ = l_Lean_SourceInfo_fromRef(v_ref_668_, v___x_669_);
lean_dec(v_ref_668_);
v___x_671_ = ((lean_object*)(l_term___u2295_x27___00__closed__1));
v___x_672_ = ((lean_object*)(l_term___u2295_x27___00__closed__2));
lean_inc(v___x_670_);
v___x_673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_670_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = l_Lean_Syntax_node3(v___x_670_, v___x_671_, v___x_666_, v___x_673_, v___x_667_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v_a_649_);
return v___x_675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__PSum__1___boxed(lean_object* v_x_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___aux__Init__Core______unexpand__PSum__1(v_x_676_, v_a_677_, v_a_678_);
lean_dec(v_a_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedLeft___redArg(lean_object* v_inst_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v_inst_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedLeft(lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_inst_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_inst_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedRight___redArg(lean_object* v_inst_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v_inst_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_PSum_inhabitedRight(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_inst_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v_inst_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___impl___redArg(lean_object* v_x_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_tag_nat(v_x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___impl___redArg___boxed(lean_object* v_x_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_ForInStep_ctorIdx___impl___redArg(v_x_694_);
lean_dec_ref(v_x_694_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___impl(lean_object* v_00_u03b1_696_, lean_object* v_x_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = lean_obj_tag_nat(v_x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorIdx___impl___boxed(lean_object* v_00_u03b1_699_, lean_object* v_x_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_ForInStep_ctorIdx___impl(v_00_u03b1_699_, v_x_700_);
lean_dec_ref(v_x_700_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim___redArg(lean_object* v_t_702_, lean_object* v_k_703_){
_start:
{
lean_object* v_a_704_; lean_object* v___x_705_; 
v_a_704_ = lean_ctor_get(v_t_702_, 0);
lean_inc(v_a_704_);
lean_dec_ref(v_t_702_);
v___x_705_ = lean_apply_1(v_k_703_, v_a_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim(lean_object* v_00_u03b1_706_, lean_object* v_motive_707_, lean_object* v_ctorIdx_708_, lean_object* v_t_709_, lean_object* v_h_710_, lean_object* v_k_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_ForInStep_ctorElim___redArg(v_t_709_, v_k_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_ctorElim___boxed(lean_object* v_00_u03b1_713_, lean_object* v_motive_714_, lean_object* v_ctorIdx_715_, lean_object* v_t_716_, lean_object* v_h_717_, lean_object* v_k_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_ForInStep_ctorElim(v_00_u03b1_713_, v_motive_714_, v_ctorIdx_715_, v_t_716_, v_h_717_, v_k_718_);
lean_dec(v_ctorIdx_715_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_done_elim___redArg(lean_object* v_t_720_, lean_object* v_done_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_ForInStep_ctorElim___redArg(v_t_720_, v_done_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_done_elim(lean_object* v_00_u03b1_723_, lean_object* v_motive_724_, lean_object* v_t_725_, lean_object* v_h_726_, lean_object* v_done_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_ForInStep_ctorElim___redArg(v_t_725_, v_done_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_yield_elim___redArg(lean_object* v_t_729_, lean_object* v_yield_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_ForInStep_ctorElim___redArg(v_t_729_, v_yield_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_yield_elim(lean_object* v_00_u03b1_732_, lean_object* v_motive_733_, lean_object* v_t_734_, lean_object* v_h_735_, lean_object* v_yield_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_ForInStep_ctorElim___redArg(v_t_734_, v_yield_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep_default___redArg(lean_object* v_inst_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v_inst_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep_default(lean_object* v_00_u03b1_740_, lean_object* v_inst_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v_inst_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep___redArg(lean_object* v_inst_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v_inst_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedForInStep(lean_object* v_a_745_, lean_object* v_inst_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v_inst_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___impl___redArg(lean_object* v_x_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_obj_tag_nat(v_x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___impl___redArg___boxed(lean_object* v_x_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_DoResultPRBC_ctorIdx___impl___redArg(v_x_750_);
lean_dec_ref(v_x_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___impl(lean_object* v_00_u03b1_752_, lean_object* v_00_u03b2_753_, lean_object* v_00_u03c3_754_, lean_object* v_x_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_obj_tag_nat(v_x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorIdx___impl___boxed(lean_object* v_00_u03b1_757_, lean_object* v_00_u03b2_758_, lean_object* v_00_u03c3_759_, lean_object* v_x_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_DoResultPRBC_ctorIdx___impl(v_00_u03b1_757_, v_00_u03b2_758_, v_00_u03c3_759_, v_x_760_);
lean_dec_ref(v_x_760_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim___redArg(lean_object* v_t_762_, lean_object* v_k_763_){
_start:
{
switch(lean_obj_tag(v_t_762_))
{
case 2:
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v_t_762_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v_t_762_, 1);
v___x_765_ = lean_apply_1(v_k_763_, v_a_764_);
return v___x_765_;
}
case 3:
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v_t_762_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v_t_762_, 1);
v___x_767_ = lean_apply_1(v_k_763_, v_a_766_);
return v___x_767_;
}
default: 
{
lean_object* v_a_768_; lean_object* v_a_769_; lean_object* v___x_770_; 
v_a_768_ = lean_ctor_get(v_t_762_, 0);
lean_inc(v_a_768_);
v_a_769_ = lean_ctor_get(v_t_762_, 1);
lean_inc(v_a_769_);
lean_dec_ref(v_t_762_);
v___x_770_ = lean_apply_2(v_k_763_, v_a_768_, v_a_769_);
return v___x_770_;
}
}
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim(lean_object* v_00_u03b1_771_, lean_object* v_00_u03b2_772_, lean_object* v_00_u03c3_773_, lean_object* v_motive_774_, lean_object* v_ctorIdx_775_, lean_object* v_t_776_, lean_object* v_h_777_, lean_object* v_k_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_DoResultPRBC_ctorElim___redArg(v_t_776_, v_k_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_ctorElim___boxed(lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v_00_u03c3_782_, lean_object* v_motive_783_, lean_object* v_ctorIdx_784_, lean_object* v_t_785_, lean_object* v_h_786_, lean_object* v_k_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_DoResultPRBC_ctorElim(v_00_u03b1_780_, v_00_u03b2_781_, v_00_u03c3_782_, v_motive_783_, v_ctorIdx_784_, v_t_785_, v_h_786_, v_k_787_);
lean_dec(v_ctorIdx_784_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_pure_elim___redArg(lean_object* v_t_789_, lean_object* v_pure_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_DoResultPRBC_ctorElim___redArg(v_t_789_, v_pure_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_pure_elim(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_00_u03c3_794_, lean_object* v_motive_795_, lean_object* v_t_796_, lean_object* v_h_797_, lean_object* v_pure_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_DoResultPRBC_ctorElim___redArg(v_t_796_, v_pure_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_return_elim___redArg(lean_object* v_t_800_, lean_object* v_return_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_DoResultPRBC_ctorElim___redArg(v_t_800_, v_return_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_return_elim(lean_object* v_00_u03b1_803_, lean_object* v_00_u03b2_804_, lean_object* v_00_u03c3_805_, lean_object* v_motive_806_, lean_object* v_t_807_, lean_object* v_h_808_, lean_object* v_return_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_DoResultPRBC_ctorElim___redArg(v_t_807_, v_return_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_break_elim___redArg(lean_object* v_t_811_, lean_object* v_break_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_DoResultPRBC_ctorElim___redArg(v_t_811_, v_break_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_break_elim(lean_object* v_00_u03b1_814_, lean_object* v_00_u03b2_815_, lean_object* v_00_u03c3_816_, lean_object* v_motive_817_, lean_object* v_t_818_, lean_object* v_h_819_, lean_object* v_break_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_DoResultPRBC_ctorElim___redArg(v_t_818_, v_break_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_continue_elim___redArg(lean_object* v_t_822_, lean_object* v_continue_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_DoResultPRBC_ctorElim___redArg(v_t_822_, v_continue_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_DoResultPRBC_continue_elim(lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_00_u03c3_827_, lean_object* v_motive_828_, lean_object* v_t_829_, lean_object* v_h_830_, lean_object* v_continue_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_DoResultPRBC_ctorElim___redArg(v_t_829_, v_continue_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___impl___redArg(lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = lean_obj_tag_nat(v_x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___impl___redArg___boxed(lean_object* v_x_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_DoResultPR_ctorIdx___impl___redArg(v_x_835_);
lean_dec_ref(v_x_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___impl(lean_object* v_00_u03b1_837_, lean_object* v_00_u03b2_838_, lean_object* v_00_u03c3_839_, lean_object* v_x_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_obj_tag_nat(v_x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorIdx___impl___boxed(lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_00_u03c3_844_, lean_object* v_x_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_DoResultPR_ctorIdx___impl(v_00_u03b1_842_, v_00_u03b2_843_, v_00_u03c3_844_, v_x_845_);
lean_dec_ref(v_x_845_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___redArg(lean_object* v_t_847_, lean_object* v_k_848_){
_start:
{
lean_object* v_a_849_; lean_object* v_a_850_; lean_object* v___x_851_; 
v_a_849_ = lean_ctor_get(v_t_847_, 0);
lean_inc(v_a_849_);
v_a_850_ = lean_ctor_get(v_t_847_, 1);
lean_inc(v_a_850_);
lean_dec_ref(v_t_847_);
v___x_851_ = lean_apply_2(v_k_848_, v_a_849_, v_a_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim(lean_object* v_00_u03b1_852_, lean_object* v_00_u03b2_853_, lean_object* v_00_u03c3_854_, lean_object* v_motive_855_, lean_object* v_ctorIdx_856_, lean_object* v_t_857_, lean_object* v_h_858_, lean_object* v_k_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_DoResultPR_ctorElim___redArg(v_t_857_, v_k_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_ctorElim___boxed(lean_object* v_00_u03b1_861_, lean_object* v_00_u03b2_862_, lean_object* v_00_u03c3_863_, lean_object* v_motive_864_, lean_object* v_ctorIdx_865_, lean_object* v_t_866_, lean_object* v_h_867_, lean_object* v_k_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_DoResultPR_ctorElim(v_00_u03b1_861_, v_00_u03b2_862_, v_00_u03c3_863_, v_motive_864_, v_ctorIdx_865_, v_t_866_, v_h_867_, v_k_868_);
lean_dec(v_ctorIdx_865_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim___redArg(lean_object* v_t_870_, lean_object* v_pure_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_DoResultPR_ctorElim___redArg(v_t_870_, v_pure_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_pure_elim(lean_object* v_00_u03b1_873_, lean_object* v_00_u03b2_874_, lean_object* v_00_u03c3_875_, lean_object* v_motive_876_, lean_object* v_t_877_, lean_object* v_h_878_, lean_object* v_pure_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_DoResultPR_ctorElim___redArg(v_t_877_, v_pure_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_return_elim___redArg(lean_object* v_t_881_, lean_object* v_return_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_DoResultPR_ctorElim___redArg(v_t_881_, v_return_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_DoResultPR_return_elim(lean_object* v_00_u03b1_884_, lean_object* v_00_u03b2_885_, lean_object* v_00_u03c3_886_, lean_object* v_motive_887_, lean_object* v_t_888_, lean_object* v_h_889_, lean_object* v_return_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_DoResultPR_ctorElim___redArg(v_t_888_, v_return_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___impl___redArg(lean_object* v_x_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = lean_obj_tag_nat(v_x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___impl___redArg___boxed(lean_object* v_x_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_DoResultBC_ctorIdx___impl___redArg(v_x_894_);
lean_dec_ref(v_x_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___impl(lean_object* v_00_u03c3_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = lean_obj_tag_nat(v_x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorIdx___impl___boxed(lean_object* v_00_u03c3_899_, lean_object* v_x_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_DoResultBC_ctorIdx___impl(v_00_u03c3_899_, v_x_900_);
lean_dec_ref(v_x_900_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___redArg(lean_object* v_t_902_, lean_object* v_k_903_){
_start:
{
lean_object* v_a_904_; lean_object* v___x_905_; 
v_a_904_ = lean_ctor_get(v_t_902_, 0);
lean_inc(v_a_904_);
lean_dec_ref(v_t_902_);
v___x_905_ = lean_apply_1(v_k_903_, v_a_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim(lean_object* v_00_u03c3_906_, lean_object* v_motive_907_, lean_object* v_ctorIdx_908_, lean_object* v_t_909_, lean_object* v_h_910_, lean_object* v_k_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_DoResultBC_ctorElim___redArg(v_t_909_, v_k_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_ctorElim___boxed(lean_object* v_00_u03c3_913_, lean_object* v_motive_914_, lean_object* v_ctorIdx_915_, lean_object* v_t_916_, lean_object* v_h_917_, lean_object* v_k_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_DoResultBC_ctorElim(v_00_u03c3_913_, v_motive_914_, v_ctorIdx_915_, v_t_916_, v_h_917_, v_k_918_);
lean_dec(v_ctorIdx_915_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_break_elim___redArg(lean_object* v_t_920_, lean_object* v_break_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_DoResultBC_ctorElim___redArg(v_t_920_, v_break_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_break_elim(lean_object* v_00_u03c3_923_, lean_object* v_motive_924_, lean_object* v_t_925_, lean_object* v_h_926_, lean_object* v_break_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_DoResultBC_ctorElim___redArg(v_t_925_, v_break_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim___redArg(lean_object* v_t_929_, lean_object* v_continue_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_DoResultBC_ctorElim___redArg(v_t_929_, v_continue_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_DoResultBC_continue_elim(lean_object* v_00_u03c3_932_, lean_object* v_motive_933_, lean_object* v_t_934_, lean_object* v_h_935_, lean_object* v_continue_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_DoResultBC_ctorElim___redArg(v_t_934_, v_continue_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___impl___redArg(lean_object* v_x_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = lean_obj_tag_nat(v_x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___impl___redArg___boxed(lean_object* v_x_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_DoResultSBC_ctorIdx___impl___redArg(v_x_940_);
lean_dec_ref(v_x_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___impl(lean_object* v_00_u03b1_942_, lean_object* v_00_u03c3_943_, lean_object* v_x_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = lean_obj_tag_nat(v_x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorIdx___impl___boxed(lean_object* v_00_u03b1_946_, lean_object* v_00_u03c3_947_, lean_object* v_x_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_DoResultSBC_ctorIdx___impl(v_00_u03b1_946_, v_00_u03c3_947_, v_x_948_);
lean_dec_ref(v_x_948_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim___redArg(lean_object* v_t_950_, lean_object* v_k_951_){
_start:
{
if (lean_obj_tag(v_t_950_) == 0)
{
lean_object* v_a_952_; lean_object* v_a_953_; lean_object* v___x_954_; 
v_a_952_ = lean_ctor_get(v_t_950_, 0);
lean_inc(v_a_952_);
v_a_953_ = lean_ctor_get(v_t_950_, 1);
lean_inc(v_a_953_);
lean_dec_ref_known(v_t_950_, 2);
v___x_954_ = lean_apply_2(v_k_951_, v_a_952_, v_a_953_);
return v___x_954_;
}
else
{
lean_object* v_a_955_; lean_object* v___x_956_; 
v_a_955_ = lean_ctor_get(v_t_950_, 0);
lean_inc(v_a_955_);
lean_dec_ref(v_t_950_);
v___x_956_ = lean_apply_1(v_k_951_, v_a_955_);
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim(lean_object* v_00_u03b1_957_, lean_object* v_00_u03c3_958_, lean_object* v_motive_959_, lean_object* v_ctorIdx_960_, lean_object* v_t_961_, lean_object* v_h_962_, lean_object* v_k_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_DoResultSBC_ctorElim___redArg(v_t_961_, v_k_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_ctorElim___boxed(lean_object* v_00_u03b1_965_, lean_object* v_00_u03c3_966_, lean_object* v_motive_967_, lean_object* v_ctorIdx_968_, lean_object* v_t_969_, lean_object* v_h_970_, lean_object* v_k_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_DoResultSBC_ctorElim(v_00_u03b1_965_, v_00_u03c3_966_, v_motive_967_, v_ctorIdx_968_, v_t_969_, v_h_970_, v_k_971_);
lean_dec(v_ctorIdx_968_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_pureReturn_elim___redArg(lean_object* v_t_973_, lean_object* v_pureReturn_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_DoResultSBC_ctorElim___redArg(v_t_973_, v_pureReturn_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_pureReturn_elim(lean_object* v_00_u03b1_976_, lean_object* v_00_u03c3_977_, lean_object* v_motive_978_, lean_object* v_t_979_, lean_object* v_h_980_, lean_object* v_pureReturn_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_DoResultSBC_ctorElim___redArg(v_t_979_, v_pureReturn_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_break_elim___redArg(lean_object* v_t_983_, lean_object* v_break_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_DoResultSBC_ctorElim___redArg(v_t_983_, v_break_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_break_elim(lean_object* v_00_u03b1_986_, lean_object* v_00_u03c3_987_, lean_object* v_motive_988_, lean_object* v_t_989_, lean_object* v_h_990_, lean_object* v_break_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_DoResultSBC_ctorElim___redArg(v_t_989_, v_break_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_continue_elim___redArg(lean_object* v_t_993_, lean_object* v_continue_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_DoResultSBC_ctorElim___redArg(v_t_993_, v_continue_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_DoResultSBC_continue_elim(lean_object* v_00_u03b1_996_, lean_object* v_00_u03c3_997_, lean_object* v_motive_998_, lean_object* v_t_999_, lean_object* v_h_1000_, lean_object* v_continue_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_DoResultSBC_ctorElim___redArg(v_t_999_, v_continue_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2248____1___closed__1(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2248____1___closed__0));
v___x_1024_ = l_String_toRawSubstring_x27(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2248____1(lean_object* v_x_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = ((lean_object*)(l_term___u2248___00__closed__1));
lean_inc(v_x_1036_);
v___x_1040_ = l_Lean_Syntax_isOfKind(v_x_1036_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec(v_x_1036_);
v___x_1041_ = lean_box(1);
v___x_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v_a_1038_);
return v___x_1042_;
}
else
{
lean_object* v_quotContext_1043_; lean_object* v_currMacroScope_1044_; lean_object* v_ref_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_quotContext_1043_ = lean_ctor_get(v_a_1037_, 1);
v_currMacroScope_1044_ = lean_ctor_get(v_a_1037_, 2);
v_ref_1045_ = lean_ctor_get(v_a_1037_, 5);
v___x_1046_ = lean_unsigned_to_nat(0u);
v___x_1047_ = l_Lean_Syntax_getArg(v_x_1036_, v___x_1046_);
v___x_1048_ = lean_unsigned_to_nat(2u);
v___x_1049_ = l_Lean_Syntax_getArg(v_x_1036_, v___x_1048_);
lean_dec(v_x_1036_);
v___x_1050_ = 0;
v___x_1051_ = l_Lean_SourceInfo_fromRef(v_ref_1045_, v___x_1050_);
v___x_1052_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1053_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2248____1___closed__1, &l___aux__Init__Core______macroRules__term___u2248____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2248____1___closed__1);
v___x_1054_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2248____1___closed__4));
lean_inc(v_currMacroScope_1044_);
lean_inc(v_quotContext_1043_);
v___x_1055_ = l_Lean_addMacroScope(v_quotContext_1043_, v___x_1054_, v_currMacroScope_1044_);
v___x_1056_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2248____1___closed__6));
lean_inc_n(v___x_1051_, 2);
v___x_1057_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1051_);
lean_ctor_set(v___x_1057_, 1, v___x_1053_);
lean_ctor_set(v___x_1057_, 2, v___x_1055_);
lean_ctor_set(v___x_1057_, 3, v___x_1056_);
v___x_1058_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1059_ = l_Lean_Syntax_node2(v___x_1051_, v___x_1058_, v___x_1047_, v___x_1049_);
v___x_1060_ = l_Lean_Syntax_node2(v___x_1051_, v___x_1052_, v___x_1057_, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v_a_1038_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2248____1___boxed(lean_object* v_x_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___aux__Init__Core______macroRules__term___u2248____1(v_x_1062_, v_a_1063_, v_a_1064_);
lean_dec_ref(v_a_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasEquiv__Equiv__1(lean_object* v_x_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1066_);
v___x_1070_ = l_Lean_Syntax_isOfKind(v_x_1066_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec(v_x_1066_);
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v_a_1068_);
return v___x_1072_;
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = l_Lean_Syntax_getArg(v_x_1066_, v___x_1073_);
v___x_1075_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1074_);
v___x_1076_ = l_Lean_Syntax_isOfKind(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec(v___x_1074_);
lean_dec(v_x_1066_);
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v_a_1068_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = l_Lean_Syntax_getArg(v_x_1066_, v___x_1079_);
lean_dec(v_x_1066_);
v___x_1081_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1080_);
v___x_1082_ = l_Lean_Syntax_matchesNull(v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v___x_1080_);
lean_dec(v___x_1074_);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_1068_);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v_ref_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1085_ = l_Lean_Syntax_getArg(v___x_1080_, v___x_1073_);
v___x_1086_ = l_Lean_Syntax_getArg(v___x_1080_, v___x_1079_);
lean_dec(v___x_1080_);
v_ref_1087_ = l_Lean_replaceRef(v___x_1074_, v_a_1067_);
lean_dec(v___x_1074_);
v___x_1088_ = 0;
v___x_1089_ = l_Lean_SourceInfo_fromRef(v_ref_1087_, v___x_1088_);
lean_dec(v_ref_1087_);
v___x_1090_ = ((lean_object*)(l_term___u2248___00__closed__1));
v___x_1091_ = ((lean_object*)(l_term___u2248___00__closed__2));
lean_inc(v___x_1089_);
v___x_1092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1089_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l_Lean_Syntax_node3(v___x_1089_, v___x_1090_, v___x_1085_, v___x_1092_, v___x_1086_);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v_a_1068_);
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasEquiv__Equiv__1___boxed(lean_object* v_x_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___aux__Init__Core______unexpand__HasEquiv__Equiv__1(v_x_1095_, v_a_1096_, v_a_1097_);
lean_dec(v_a_1096_);
return v_res_1098_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2286____1___closed__1(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2286____1___closed__0));
v___x_1117_ = l_String_toRawSubstring_x27(v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2286____1(lean_object* v_x_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = ((lean_object*)(l_term___u2286___00__closed__1));
lean_inc(v_x_1130_);
v___x_1134_ = l_Lean_Syntax_isOfKind(v_x_1130_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v_x_1130_);
v___x_1135_ = lean_box(1);
v___x_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v_a_1132_);
return v___x_1136_;
}
else
{
lean_object* v_quotContext_1137_; lean_object* v_currMacroScope_1138_; lean_object* v_ref_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v_quotContext_1137_ = lean_ctor_get(v_a_1131_, 1);
v_currMacroScope_1138_ = lean_ctor_get(v_a_1131_, 2);
v_ref_1139_ = lean_ctor_get(v_a_1131_, 5);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = l_Lean_Syntax_getArg(v_x_1130_, v___x_1140_);
v___x_1142_ = lean_unsigned_to_nat(2u);
v___x_1143_ = l_Lean_Syntax_getArg(v_x_1130_, v___x_1142_);
lean_dec(v_x_1130_);
v___x_1144_ = 0;
v___x_1145_ = l_Lean_SourceInfo_fromRef(v_ref_1139_, v___x_1144_);
v___x_1146_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1147_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2286____1___closed__1, &l___aux__Init__Core______macroRules__term___u2286____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2286____1___closed__1);
v___x_1148_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2286____1___closed__2));
lean_inc(v_currMacroScope_1138_);
lean_inc(v_quotContext_1137_);
v___x_1149_ = l_Lean_addMacroScope(v_quotContext_1137_, v___x_1148_, v_currMacroScope_1138_);
v___x_1150_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2286____1___closed__6));
lean_inc_n(v___x_1145_, 2);
v___x_1151_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1145_);
lean_ctor_set(v___x_1151_, 1, v___x_1147_);
lean_ctor_set(v___x_1151_, 2, v___x_1149_);
lean_ctor_set(v___x_1151_, 3, v___x_1150_);
v___x_1152_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1153_ = l_Lean_Syntax_node2(v___x_1145_, v___x_1152_, v___x_1141_, v___x_1143_);
v___x_1154_ = l_Lean_Syntax_node2(v___x_1145_, v___x_1146_, v___x_1151_, v___x_1153_);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v_a_1132_);
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2286____1___boxed(lean_object* v_x_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___aux__Init__Core______macroRules__term___u2286____1(v_x_1156_, v_a_1157_, v_a_1158_);
lean_dec_ref(v_a_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSubset__Subset__1(lean_object* v_x_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1160_);
v___x_1164_ = l_Lean_Syntax_isOfKind(v_x_1160_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec(v_x_1160_);
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v_a_1162_);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = l_Lean_Syntax_getArg(v_x_1160_, v___x_1167_);
v___x_1169_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1168_);
v___x_1170_ = l_Lean_Syntax_isOfKind(v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec(v___x_1168_);
lean_dec(v_x_1160_);
v___x_1171_ = lean_box(0);
v___x_1172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v_a_1162_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1173_ = lean_unsigned_to_nat(1u);
v___x_1174_ = l_Lean_Syntax_getArg(v_x_1160_, v___x_1173_);
lean_dec(v_x_1160_);
v___x_1175_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1174_);
v___x_1176_ = l_Lean_Syntax_matchesNull(v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec(v___x_1174_);
lean_dec(v___x_1168_);
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v_a_1162_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v_ref_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1179_ = l_Lean_Syntax_getArg(v___x_1174_, v___x_1167_);
v___x_1180_ = l_Lean_Syntax_getArg(v___x_1174_, v___x_1173_);
lean_dec(v___x_1174_);
v_ref_1181_ = l_Lean_replaceRef(v___x_1168_, v_a_1161_);
lean_dec(v___x_1168_);
v___x_1182_ = 0;
v___x_1183_ = l_Lean_SourceInfo_fromRef(v_ref_1181_, v___x_1182_);
lean_dec(v_ref_1181_);
v___x_1184_ = ((lean_object*)(l_term___u2286___00__closed__1));
v___x_1185_ = ((lean_object*)(l_term___u2286___00__closed__2));
lean_inc(v___x_1183_);
v___x_1186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1183_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = l_Lean_Syntax_node3(v___x_1183_, v___x_1184_, v___x_1179_, v___x_1186_, v___x_1180_);
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v_a_1162_);
return v___x_1188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSubset__Subset__1___boxed(lean_object* v_x_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___aux__Init__Core______unexpand__HasSubset__Subset__1(v_x_1189_, v_a_1190_, v_a_1191_);
lean_dec(v_a_1190_);
return v_res_1192_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2282____1___closed__1(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2282____1___closed__0));
v___x_1211_ = l_String_toRawSubstring_x27(v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2282____1(lean_object* v_x_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = ((lean_object*)(l_term___u2282___00__closed__1));
lean_inc(v_x_1224_);
v___x_1228_ = l_Lean_Syntax_isOfKind(v_x_1224_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec(v_x_1224_);
v___x_1229_ = lean_box(1);
v___x_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v_a_1226_);
return v___x_1230_;
}
else
{
lean_object* v_quotContext_1231_; lean_object* v_currMacroScope_1232_; lean_object* v_ref_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_quotContext_1231_ = lean_ctor_get(v_a_1225_, 1);
v_currMacroScope_1232_ = lean_ctor_get(v_a_1225_, 2);
v_ref_1233_ = lean_ctor_get(v_a_1225_, 5);
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = l_Lean_Syntax_getArg(v_x_1224_, v___x_1234_);
v___x_1236_ = lean_unsigned_to_nat(2u);
v___x_1237_ = l_Lean_Syntax_getArg(v_x_1224_, v___x_1236_);
lean_dec(v_x_1224_);
v___x_1238_ = 0;
v___x_1239_ = l_Lean_SourceInfo_fromRef(v_ref_1233_, v___x_1238_);
v___x_1240_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1241_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2282____1___closed__1, &l___aux__Init__Core______macroRules__term___u2282____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2282____1___closed__1);
v___x_1242_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2282____1___closed__2));
lean_inc(v_currMacroScope_1232_);
lean_inc(v_quotContext_1231_);
v___x_1243_ = l_Lean_addMacroScope(v_quotContext_1231_, v___x_1242_, v_currMacroScope_1232_);
v___x_1244_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2282____1___closed__6));
lean_inc_n(v___x_1239_, 2);
v___x_1245_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1239_);
lean_ctor_set(v___x_1245_, 1, v___x_1241_);
lean_ctor_set(v___x_1245_, 2, v___x_1243_);
lean_ctor_set(v___x_1245_, 3, v___x_1244_);
v___x_1246_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1247_ = l_Lean_Syntax_node2(v___x_1239_, v___x_1246_, v___x_1235_, v___x_1237_);
v___x_1248_ = l_Lean_Syntax_node2(v___x_1239_, v___x_1240_, v___x_1245_, v___x_1247_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v_a_1226_);
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2282____1___boxed(lean_object* v_x_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l___aux__Init__Core______macroRules__term___u2282____1(v_x_1250_, v_a_1251_, v_a_1252_);
lean_dec_ref(v_a_1251_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSSubset__SSubset__1(lean_object* v_x_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1254_);
v___x_1258_ = l_Lean_Syntax_isOfKind(v_x_1254_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v_x_1254_);
v___x_1259_ = lean_box(0);
v___x_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v_a_1256_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = l_Lean_Syntax_getArg(v_x_1254_, v___x_1261_);
v___x_1263_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1262_);
v___x_1264_ = l_Lean_Syntax_isOfKind(v___x_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec(v___x_1262_);
lean_dec(v_x_1254_);
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v_a_1256_);
return v___x_1266_;
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = l_Lean_Syntax_getArg(v_x_1254_, v___x_1267_);
lean_dec(v_x_1254_);
v___x_1269_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1268_);
v___x_1270_ = l_Lean_Syntax_matchesNull(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec(v___x_1268_);
lean_dec(v___x_1262_);
v___x_1271_ = lean_box(0);
v___x_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v_a_1256_);
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v_ref_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1273_ = l_Lean_Syntax_getArg(v___x_1268_, v___x_1261_);
v___x_1274_ = l_Lean_Syntax_getArg(v___x_1268_, v___x_1267_);
lean_dec(v___x_1268_);
v_ref_1275_ = l_Lean_replaceRef(v___x_1262_, v_a_1255_);
lean_dec(v___x_1262_);
v___x_1276_ = 0;
v___x_1277_ = l_Lean_SourceInfo_fromRef(v_ref_1275_, v___x_1276_);
lean_dec(v_ref_1275_);
v___x_1278_ = ((lean_object*)(l_term___u2282___00__closed__1));
v___x_1279_ = ((lean_object*)(l_term___u2282___00__closed__2));
lean_inc(v___x_1277_);
v___x_1280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1277_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = l_Lean_Syntax_node3(v___x_1277_, v___x_1278_, v___x_1273_, v___x_1280_, v___x_1274_);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v_a_1256_);
return v___x_1282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__HasSSubset__SSubset__1___boxed(lean_object* v_x_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l___aux__Init__Core______unexpand__HasSSubset__SSubset__1(v_x_1283_, v_a_1284_, v_a_1285_);
lean_dec(v_a_1284_);
return v_res_1286_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2287____1___closed__1(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2287____1___closed__0));
v___x_1305_ = l_String_toRawSubstring_x27(v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2287____1(lean_object* v_x_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_term___u2287___00__closed__1));
lean_inc(v_x_1314_);
v___x_1318_ = l_Lean_Syntax_isOfKind(v_x_1314_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_dec(v_x_1314_);
v___x_1319_ = lean_box(1);
v___x_1320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v_a_1316_);
return v___x_1320_;
}
else
{
lean_object* v_quotContext_1321_; lean_object* v_currMacroScope_1322_; lean_object* v_ref_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_quotContext_1321_ = lean_ctor_get(v_a_1315_, 1);
v_currMacroScope_1322_ = lean_ctor_get(v_a_1315_, 2);
v_ref_1323_ = lean_ctor_get(v_a_1315_, 5);
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = l_Lean_Syntax_getArg(v_x_1314_, v___x_1324_);
v___x_1326_ = lean_unsigned_to_nat(2u);
v___x_1327_ = l_Lean_Syntax_getArg(v_x_1314_, v___x_1326_);
lean_dec(v_x_1314_);
v___x_1328_ = 0;
v___x_1329_ = l_Lean_SourceInfo_fromRef(v_ref_1323_, v___x_1328_);
v___x_1330_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1331_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2287____1___closed__1, &l___aux__Init__Core______macroRules__term___u2287____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2287____1___closed__1);
v___x_1332_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2287____1___closed__2));
lean_inc(v_currMacroScope_1322_);
lean_inc(v_quotContext_1321_);
v___x_1333_ = l_Lean_addMacroScope(v_quotContext_1321_, v___x_1332_, v_currMacroScope_1322_);
v___x_1334_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2287____1___closed__4));
lean_inc_n(v___x_1329_, 2);
v___x_1335_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1329_);
lean_ctor_set(v___x_1335_, 1, v___x_1331_);
lean_ctor_set(v___x_1335_, 2, v___x_1333_);
lean_ctor_set(v___x_1335_, 3, v___x_1334_);
v___x_1336_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1337_ = l_Lean_Syntax_node2(v___x_1329_, v___x_1336_, v___x_1325_, v___x_1327_);
v___x_1338_ = l_Lean_Syntax_node2(v___x_1329_, v___x_1330_, v___x_1335_, v___x_1337_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v_a_1316_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2287____1___boxed(lean_object* v_x_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___aux__Init__Core______macroRules__term___u2287____1(v_x_1340_, v_a_1341_, v_a_1342_);
lean_dec_ref(v_a_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Superset__1(lean_object* v_x_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1344_);
v___x_1348_ = l_Lean_Syntax_isOfKind(v_x_1344_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v_x_1344_);
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v_a_1346_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = l_Lean_Syntax_getArg(v_x_1344_, v___x_1351_);
v___x_1353_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1352_);
v___x_1354_ = l_Lean_Syntax_isOfKind(v___x_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v___x_1352_);
lean_dec(v_x_1344_);
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
lean_ctor_set(v___x_1356_, 1, v_a_1346_);
return v___x_1356_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = l_Lean_Syntax_getArg(v_x_1344_, v___x_1357_);
lean_dec(v_x_1344_);
v___x_1359_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1358_);
v___x_1360_ = l_Lean_Syntax_matchesNull(v___x_1358_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec(v___x_1358_);
lean_dec(v___x_1352_);
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v_a_1346_);
return v___x_1362_;
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_ref_1365_; uint8_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1363_ = l_Lean_Syntax_getArg(v___x_1358_, v___x_1351_);
v___x_1364_ = l_Lean_Syntax_getArg(v___x_1358_, v___x_1357_);
lean_dec(v___x_1358_);
v_ref_1365_ = l_Lean_replaceRef(v___x_1352_, v_a_1345_);
lean_dec(v___x_1352_);
v___x_1366_ = 0;
v___x_1367_ = l_Lean_SourceInfo_fromRef(v_ref_1365_, v___x_1366_);
lean_dec(v_ref_1365_);
v___x_1368_ = ((lean_object*)(l_term___u2287___00__closed__1));
v___x_1369_ = ((lean_object*)(l_term___u2287___00__closed__2));
lean_inc(v___x_1367_);
v___x_1370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1367_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = l_Lean_Syntax_node3(v___x_1367_, v___x_1368_, v___x_1363_, v___x_1370_, v___x_1364_);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v_a_1346_);
return v___x_1372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Superset__1___boxed(lean_object* v_x_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___aux__Init__Core______unexpand__Superset__1(v_x_1373_, v_a_1374_, v_a_1375_);
lean_dec(v_a_1374_);
return v_res_1376_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2283____1___closed__1(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2283____1___closed__0));
v___x_1395_ = l_String_toRawSubstring_x27(v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2283____1(lean_object* v_x_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1407_ = ((lean_object*)(l_term___u2283___00__closed__1));
lean_inc(v_x_1404_);
v___x_1408_ = l_Lean_Syntax_isOfKind(v_x_1404_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
lean_dec(v_x_1404_);
v___x_1409_ = lean_box(1);
v___x_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v_a_1406_);
return v___x_1410_;
}
else
{
lean_object* v_quotContext_1411_; lean_object* v_currMacroScope_1412_; lean_object* v_ref_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_quotContext_1411_ = lean_ctor_get(v_a_1405_, 1);
v_currMacroScope_1412_ = lean_ctor_get(v_a_1405_, 2);
v_ref_1413_ = lean_ctor_get(v_a_1405_, 5);
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1415_ = l_Lean_Syntax_getArg(v_x_1404_, v___x_1414_);
v___x_1416_ = lean_unsigned_to_nat(2u);
v___x_1417_ = l_Lean_Syntax_getArg(v_x_1404_, v___x_1416_);
lean_dec(v_x_1404_);
v___x_1418_ = 0;
v___x_1419_ = l_Lean_SourceInfo_fromRef(v_ref_1413_, v___x_1418_);
v___x_1420_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1421_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2283____1___closed__1, &l___aux__Init__Core______macroRules__term___u2283____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2283____1___closed__1);
v___x_1422_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2283____1___closed__2));
lean_inc(v_currMacroScope_1412_);
lean_inc(v_quotContext_1411_);
v___x_1423_ = l_Lean_addMacroScope(v_quotContext_1411_, v___x_1422_, v_currMacroScope_1412_);
v___x_1424_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2283____1___closed__4));
lean_inc_n(v___x_1419_, 2);
v___x_1425_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1419_);
lean_ctor_set(v___x_1425_, 1, v___x_1421_);
lean_ctor_set(v___x_1425_, 2, v___x_1423_);
lean_ctor_set(v___x_1425_, 3, v___x_1424_);
v___x_1426_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1427_ = l_Lean_Syntax_node2(v___x_1419_, v___x_1426_, v___x_1415_, v___x_1417_);
v___x_1428_ = l_Lean_Syntax_node2(v___x_1419_, v___x_1420_, v___x_1425_, v___x_1427_);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
lean_ctor_set(v___x_1429_, 1, v_a_1406_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2283____1___boxed(lean_object* v_x_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l___aux__Init__Core______macroRules__term___u2283____1(v_x_1430_, v_a_1431_, v_a_1432_);
lean_dec_ref(v_a_1431_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SSuperset__1(lean_object* v_x_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1434_);
v___x_1438_ = l_Lean_Syntax_isOfKind(v_x_1434_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec(v_x_1434_);
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v_a_1436_);
return v___x_1440_;
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = l_Lean_Syntax_getArg(v_x_1434_, v___x_1441_);
v___x_1443_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1442_);
v___x_1444_ = l_Lean_Syntax_isOfKind(v___x_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec(v___x_1442_);
lean_dec(v_x_1434_);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v_a_1436_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = l_Lean_Syntax_getArg(v_x_1434_, v___x_1447_);
lean_dec(v_x_1434_);
v___x_1449_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1448_);
v___x_1450_ = l_Lean_Syntax_matchesNull(v___x_1448_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec(v___x_1448_);
lean_dec(v___x_1442_);
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
lean_ctor_set(v___x_1452_, 1, v_a_1436_);
return v___x_1452_;
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_ref_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1453_ = l_Lean_Syntax_getArg(v___x_1448_, v___x_1441_);
v___x_1454_ = l_Lean_Syntax_getArg(v___x_1448_, v___x_1447_);
lean_dec(v___x_1448_);
v_ref_1455_ = l_Lean_replaceRef(v___x_1442_, v_a_1435_);
lean_dec(v___x_1442_);
v___x_1456_ = 0;
v___x_1457_ = l_Lean_SourceInfo_fromRef(v_ref_1455_, v___x_1456_);
lean_dec(v_ref_1455_);
v___x_1458_ = ((lean_object*)(l_term___u2283___00__closed__1));
v___x_1459_ = ((lean_object*)(l_term___u2283___00__closed__2));
lean_inc(v___x_1457_);
v___x_1460_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1457_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = l_Lean_Syntax_node3(v___x_1457_, v___x_1458_, v___x_1453_, v___x_1460_, v___x_1454_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v_a_1436_);
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SSuperset__1___boxed(lean_object* v_x_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l___aux__Init__Core______unexpand__SSuperset__1(v_x_1463_, v_a_1464_, v_a_1465_);
lean_dec(v_a_1464_);
return v_res_1466_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u222a____1___closed__1(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u222a____1___closed__0));
v___x_1487_ = l_String_toRawSubstring_x27(v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u222a____1(lean_object* v_x_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = ((lean_object*)(l_term___u222a___00__closed__1));
lean_inc(v_x_1499_);
v___x_1503_ = l_Lean_Syntax_isOfKind(v_x_1499_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec(v_x_1499_);
v___x_1504_ = lean_box(1);
v___x_1505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v_a_1501_);
return v___x_1505_;
}
else
{
lean_object* v_quotContext_1506_; lean_object* v_currMacroScope_1507_; lean_object* v_ref_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_quotContext_1506_ = lean_ctor_get(v_a_1500_, 1);
v_currMacroScope_1507_ = lean_ctor_get(v_a_1500_, 2);
v_ref_1508_ = lean_ctor_get(v_a_1500_, 5);
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = l_Lean_Syntax_getArg(v_x_1499_, v___x_1509_);
v___x_1511_ = lean_unsigned_to_nat(2u);
v___x_1512_ = l_Lean_Syntax_getArg(v_x_1499_, v___x_1511_);
lean_dec(v_x_1499_);
v___x_1513_ = 0;
v___x_1514_ = l_Lean_SourceInfo_fromRef(v_ref_1508_, v___x_1513_);
v___x_1515_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1516_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u222a____1___closed__1, &l___aux__Init__Core______macroRules__term___u222a____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u222a____1___closed__1);
v___x_1517_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u222a____1___closed__4));
lean_inc(v_currMacroScope_1507_);
lean_inc(v_quotContext_1506_);
v___x_1518_ = l_Lean_addMacroScope(v_quotContext_1506_, v___x_1517_, v_currMacroScope_1507_);
v___x_1519_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u222a____1___closed__6));
lean_inc_n(v___x_1514_, 2);
v___x_1520_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1514_);
lean_ctor_set(v___x_1520_, 1, v___x_1516_);
lean_ctor_set(v___x_1520_, 2, v___x_1518_);
lean_ctor_set(v___x_1520_, 3, v___x_1519_);
v___x_1521_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1522_ = l_Lean_Syntax_node2(v___x_1514_, v___x_1521_, v___x_1510_, v___x_1512_);
v___x_1523_ = l_Lean_Syntax_node2(v___x_1514_, v___x_1515_, v___x_1520_, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v_a_1501_);
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u222a____1___boxed(lean_object* v_x_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___aux__Init__Core______macroRules__term___u222a____1(v_x_1525_, v_a_1526_, v_a_1527_);
lean_dec_ref(v_a_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Union__union__1(lean_object* v_x_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1529_);
v___x_1533_ = l_Lean_Syntax_isOfKind(v_x_1529_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v_x_1529_);
v___x_1534_ = lean_box(0);
v___x_1535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v_a_1531_);
return v___x_1535_;
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = l_Lean_Syntax_getArg(v_x_1529_, v___x_1536_);
v___x_1538_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1537_);
v___x_1539_ = l_Lean_Syntax_isOfKind(v___x_1537_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec(v___x_1537_);
lean_dec(v_x_1529_);
v___x_1540_ = lean_box(0);
v___x_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v_a_1531_);
return v___x_1541_;
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = l_Lean_Syntax_getArg(v_x_1529_, v___x_1542_);
lean_dec(v_x_1529_);
v___x_1544_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1543_);
v___x_1545_ = l_Lean_Syntax_matchesNull(v___x_1543_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec(v___x_1543_);
lean_dec(v___x_1537_);
v___x_1546_ = lean_box(0);
v___x_1547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v_a_1531_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v_ref_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1548_ = l_Lean_Syntax_getArg(v___x_1543_, v___x_1536_);
v___x_1549_ = l_Lean_Syntax_getArg(v___x_1543_, v___x_1542_);
lean_dec(v___x_1543_);
v_ref_1550_ = l_Lean_replaceRef(v___x_1537_, v_a_1530_);
lean_dec(v___x_1537_);
v___x_1551_ = 0;
v___x_1552_ = l_Lean_SourceInfo_fromRef(v_ref_1550_, v___x_1551_);
lean_dec(v_ref_1550_);
v___x_1553_ = ((lean_object*)(l_term___u222a___00__closed__1));
v___x_1554_ = ((lean_object*)(l_term___u222a___00__closed__2));
lean_inc(v___x_1552_);
v___x_1555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1552_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = l_Lean_Syntax_node3(v___x_1552_, v___x_1553_, v___x_1548_, v___x_1555_, v___x_1549_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v_a_1531_);
return v___x_1557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Union__union__1___boxed(lean_object* v_x_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___aux__Init__Core______unexpand__Union__union__1(v_x_1558_, v_a_1559_, v_a_1560_);
lean_dec(v_a_1559_);
return v_res_1561_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2229____1___closed__1(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2229____1___closed__0));
v___x_1582_ = l_String_toRawSubstring_x27(v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2229____1(lean_object* v_x_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1597_ = ((lean_object*)(l_term___u2229___00__closed__1));
lean_inc(v_x_1594_);
v___x_1598_ = l_Lean_Syntax_isOfKind(v_x_1594_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec(v_x_1594_);
v___x_1599_ = lean_box(1);
v___x_1600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v_a_1596_);
return v___x_1600_;
}
else
{
lean_object* v_quotContext_1601_; lean_object* v_currMacroScope_1602_; lean_object* v_ref_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_quotContext_1601_ = lean_ctor_get(v_a_1595_, 1);
v_currMacroScope_1602_ = lean_ctor_get(v_a_1595_, 2);
v_ref_1603_ = lean_ctor_get(v_a_1595_, 5);
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1604_);
v___x_1606_ = lean_unsigned_to_nat(2u);
v___x_1607_ = l_Lean_Syntax_getArg(v_x_1594_, v___x_1606_);
lean_dec(v_x_1594_);
v___x_1608_ = 0;
v___x_1609_ = l_Lean_SourceInfo_fromRef(v_ref_1603_, v___x_1608_);
v___x_1610_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1611_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2229____1___closed__1, &l___aux__Init__Core______macroRules__term___u2229____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2229____1___closed__1);
v___x_1612_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2229____1___closed__4));
lean_inc(v_currMacroScope_1602_);
lean_inc(v_quotContext_1601_);
v___x_1613_ = l_Lean_addMacroScope(v_quotContext_1601_, v___x_1612_, v_currMacroScope_1602_);
v___x_1614_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2229____1___closed__6));
lean_inc_n(v___x_1609_, 2);
v___x_1615_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1609_);
lean_ctor_set(v___x_1615_, 1, v___x_1611_);
lean_ctor_set(v___x_1615_, 2, v___x_1613_);
lean_ctor_set(v___x_1615_, 3, v___x_1614_);
v___x_1616_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1617_ = l_Lean_Syntax_node2(v___x_1609_, v___x_1616_, v___x_1605_, v___x_1607_);
v___x_1618_ = l_Lean_Syntax_node2(v___x_1609_, v___x_1610_, v___x_1615_, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v_a_1596_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2229____1___boxed(lean_object* v_x_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___aux__Init__Core______macroRules__term___u2229____1(v_x_1620_, v_a_1621_, v_a_1622_);
lean_dec_ref(v_a_1621_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Inter__inter__1(lean_object* v_x_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1624_);
v___x_1628_ = l_Lean_Syntax_isOfKind(v_x_1624_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_dec(v_x_1624_);
v___x_1629_ = lean_box(0);
v___x_1630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v_a_1626_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = l_Lean_Syntax_getArg(v_x_1624_, v___x_1631_);
v___x_1633_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1632_);
v___x_1634_ = l_Lean_Syntax_isOfKind(v___x_1632_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec(v___x_1632_);
lean_dec(v_x_1624_);
v___x_1635_ = lean_box(0);
v___x_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v_a_1626_);
return v___x_1636_;
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1638_ = l_Lean_Syntax_getArg(v_x_1624_, v___x_1637_);
lean_dec(v_x_1624_);
v___x_1639_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1638_);
v___x_1640_ = l_Lean_Syntax_matchesNull(v___x_1638_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_dec(v___x_1638_);
lean_dec(v___x_1632_);
v___x_1641_ = lean_box(0);
v___x_1642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_a_1626_);
return v___x_1642_;
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v_ref_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1643_ = l_Lean_Syntax_getArg(v___x_1638_, v___x_1631_);
v___x_1644_ = l_Lean_Syntax_getArg(v___x_1638_, v___x_1637_);
lean_dec(v___x_1638_);
v_ref_1645_ = l_Lean_replaceRef(v___x_1632_, v_a_1625_);
lean_dec(v___x_1632_);
v___x_1646_ = 0;
v___x_1647_ = l_Lean_SourceInfo_fromRef(v_ref_1645_, v___x_1646_);
lean_dec(v_ref_1645_);
v___x_1648_ = ((lean_object*)(l_term___u2229___00__closed__1));
v___x_1649_ = ((lean_object*)(l_term___u2229___00__closed__2));
lean_inc(v___x_1647_);
v___x_1650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1647_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = l_Lean_Syntax_node3(v___x_1647_, v___x_1648_, v___x_1643_, v___x_1650_, v___x_1644_);
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v_a_1626_);
return v___x_1652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Inter__inter__1___boxed(lean_object* v_x_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l___aux__Init__Core______unexpand__Inter__inter__1(v_x_1653_, v_a_1654_, v_a_1655_);
lean_dec(v_a_1654_);
return v_res_1656_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x5c____1___closed__1(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x5c____1___closed__0));
v___x_1675_ = l_String_toRawSubstring_x27(v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x5c____1(lean_object* v_x_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = ((lean_object*)(l_term___x5c___00__closed__1));
lean_inc(v_x_1687_);
v___x_1691_ = l_Lean_Syntax_isOfKind(v_x_1687_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec(v_x_1687_);
v___x_1692_ = lean_box(1);
v___x_1693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v_a_1689_);
return v___x_1693_;
}
else
{
lean_object* v_quotContext_1694_; lean_object* v_currMacroScope_1695_; lean_object* v_ref_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_quotContext_1694_ = lean_ctor_get(v_a_1688_, 1);
v_currMacroScope_1695_ = lean_ctor_get(v_a_1688_, 2);
v_ref_1696_ = lean_ctor_get(v_a_1688_, 5);
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = l_Lean_Syntax_getArg(v_x_1687_, v___x_1697_);
v___x_1699_ = lean_unsigned_to_nat(2u);
v___x_1700_ = l_Lean_Syntax_getArg(v_x_1687_, v___x_1699_);
lean_dec(v_x_1687_);
v___x_1701_ = 0;
v___x_1702_ = l_Lean_SourceInfo_fromRef(v_ref_1696_, v___x_1701_);
v___x_1703_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_1704_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x5c____1___closed__1, &l___aux__Init__Core______macroRules__term___x5c____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x5c____1___closed__1);
v___x_1705_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x5c____1___closed__4));
lean_inc(v_currMacroScope_1695_);
lean_inc(v_quotContext_1694_);
v___x_1706_ = l_Lean_addMacroScope(v_quotContext_1694_, v___x_1705_, v_currMacroScope_1695_);
v___x_1707_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x5c____1___closed__6));
lean_inc_n(v___x_1702_, 2);
v___x_1708_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1702_);
lean_ctor_set(v___x_1708_, 1, v___x_1704_);
lean_ctor_set(v___x_1708_, 2, v___x_1706_);
lean_ctor_set(v___x_1708_, 3, v___x_1707_);
v___x_1709_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_1710_ = l_Lean_Syntax_node2(v___x_1702_, v___x_1709_, v___x_1698_, v___x_1700_);
v___x_1711_ = l_Lean_Syntax_node2(v___x_1702_, v___x_1703_, v___x_1708_, v___x_1710_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
lean_ctor_set(v___x_1712_, 1, v_a_1689_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x5c____1___boxed(lean_object* v_x_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___aux__Init__Core______macroRules__term___x5c____1(v_x_1713_, v_a_1714_, v_a_1715_);
lean_dec_ref(v_a_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SDiff__sdiff__1(lean_object* v_x_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1720_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_1717_);
v___x_1721_ = l_Lean_Syntax_isOfKind(v_x_1717_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec(v_x_1717_);
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v_a_1719_);
return v___x_1723_;
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1724_ = lean_unsigned_to_nat(0u);
v___x_1725_ = l_Lean_Syntax_getArg(v_x_1717_, v___x_1724_);
v___x_1726_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_1725_);
v___x_1727_ = l_Lean_Syntax_isOfKind(v___x_1725_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec(v___x_1725_);
lean_dec(v_x_1717_);
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v_a_1719_);
return v___x_1729_;
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1730_ = lean_unsigned_to_nat(1u);
v___x_1731_ = l_Lean_Syntax_getArg(v_x_1717_, v___x_1730_);
lean_dec(v_x_1717_);
v___x_1732_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1731_);
v___x_1733_ = l_Lean_Syntax_matchesNull(v___x_1731_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec(v___x_1731_);
lean_dec(v___x_1725_);
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
lean_ctor_set(v___x_1735_, 1, v_a_1719_);
return v___x_1735_;
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_ref_1738_; uint8_t v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1736_ = l_Lean_Syntax_getArg(v___x_1731_, v___x_1724_);
v___x_1737_ = l_Lean_Syntax_getArg(v___x_1731_, v___x_1730_);
lean_dec(v___x_1731_);
v_ref_1738_ = l_Lean_replaceRef(v___x_1725_, v_a_1718_);
lean_dec(v___x_1725_);
v___x_1739_ = 0;
v___x_1740_ = l_Lean_SourceInfo_fromRef(v_ref_1738_, v___x_1739_);
lean_dec(v_ref_1738_);
v___x_1741_ = ((lean_object*)(l_term___x5c___00__closed__1));
v___x_1742_ = ((lean_object*)(l_term___x5c___00__closed__2));
lean_inc(v___x_1740_);
v___x_1743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1740_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = l_Lean_Syntax_node3(v___x_1740_, v___x_1741_, v___x_1736_, v___x_1743_, v___x_1737_);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v_a_1719_);
return v___x_1745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__SDiff__sdiff__1___boxed(lean_object* v_x_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___aux__Init__Core______unexpand__SDiff__sdiff__1(v_x_1746_, v_a_1747_, v_a_1748_);
lean_dec(v_a_1747_);
return v_res_1749_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__0));
v___x_1770_ = l_String_toRawSubstring_x27(v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1(lean_object* v_x_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = ((lean_object*)(l_term_x7b_x7d___closed__1));
v___x_1786_ = l_Lean_Syntax_isOfKind(v_x_1782_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
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
v_currMacroScope_1790_ = lean_ctor_get(v_a_1783_, 2);
v_ref_1791_ = lean_ctor_get(v_a_1783_, 5);
v___x_1792_ = 0;
v___x_1793_ = l_Lean_SourceInfo_fromRef(v_ref_1791_, v___x_1792_);
v___x_1794_ = lean_obj_once(&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1, &l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1_once, _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1);
v___x_1795_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4));
lean_inc(v_currMacroScope_1790_);
lean_inc(v_quotContext_1789_);
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
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_x7b_x7d__1___boxed(lean_object* v_x_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___aux__Init__Core______macroRules__term_x7b_x7d__1(v_x_1800_, v_a_1801_, v_a_1802_);
lean_dec_ref(v_a_1801_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1(lean_object* v_x_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v_x_1804_);
v___x_1808_ = l_Lean_Syntax_isOfKind(v_x_1804_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v_x_1804_);
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v_a_1806_);
return v___x_1810_;
}
else
{
lean_object* v_ref_1811_; uint8_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v_ref_1811_ = l_Lean_replaceRef(v_x_1804_, v_a_1805_);
lean_dec(v_x_1804_);
v___x_1812_ = 0;
v___x_1813_ = l_Lean_SourceInfo_fromRef(v_ref_1811_, v___x_1812_);
lean_dec(v_ref_1811_);
v___x_1814_ = ((lean_object*)(l_term_x7b_x7d___closed__1));
v___x_1815_ = ((lean_object*)(l_term_x7b_x7d___closed__2));
lean_inc_n(v___x_1813_, 2);
v___x_1816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1813_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = ((lean_object*)(l_term_x7b_x7d___closed__4));
v___x_1818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1813_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = l_Lean_Syntax_node2(v___x_1813_, v___x_1814_, v___x_1816_, v___x_1818_);
v___x_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v_a_1806_);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1___boxed(lean_object* v_x_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__1(v_x_1821_, v_a_1822_, v_a_1823_);
lean_dec(v_a_1822_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_u2205__1(lean_object* v_x_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_term_u2205___closed__1));
v___x_1840_ = l_Lean_Syntax_isOfKind(v_x_1836_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_box(1);
v___x_1842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v_a_1838_);
return v___x_1842_;
}
else
{
lean_object* v_quotContext_1843_; lean_object* v_currMacroScope_1844_; lean_object* v_ref_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_quotContext_1843_ = lean_ctor_get(v_a_1837_, 1);
v_currMacroScope_1844_ = lean_ctor_get(v_a_1837_, 2);
v_ref_1845_ = lean_ctor_get(v_a_1837_, 5);
v___x_1846_ = 0;
v___x_1847_ = l_Lean_SourceInfo_fromRef(v_ref_1845_, v___x_1846_);
v___x_1848_ = lean_obj_once(&l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1, &l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1_once, _init_l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__1);
v___x_1849_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__4));
lean_inc(v_currMacroScope_1844_);
lean_inc(v_quotContext_1843_);
v___x_1850_ = l_Lean_addMacroScope(v_quotContext_1843_, v___x_1849_, v_currMacroScope_1844_);
v___x_1851_ = ((lean_object*)(l___aux__Init__Core______macroRules__term_x7b_x7d__1___closed__6));
v___x_1852_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1847_);
lean_ctor_set(v___x_1852_, 1, v___x_1848_);
lean_ctor_set(v___x_1852_, 2, v___x_1850_);
lean_ctor_set(v___x_1852_, 3, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v_a_1838_);
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term_u2205__1___boxed(lean_object* v_x_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l___aux__Init__Core______macroRules__term_u2205__1(v_x_1854_, v_a_1855_, v_a_1856_);
lean_dec_ref(v_a_1855_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2(lean_object* v_x_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v_x_1858_);
v___x_1862_ = l_Lean_Syntax_isOfKind(v_x_1858_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec(v_x_1858_);
v___x_1863_ = lean_box(0);
v___x_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v_a_1860_);
return v___x_1864_;
}
else
{
lean_object* v_ref_1865_; uint8_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_ref_1865_ = l_Lean_replaceRef(v_x_1858_, v_a_1859_);
lean_dec(v_x_1858_);
v___x_1866_ = 0;
v___x_1867_ = l_Lean_SourceInfo_fromRef(v_ref_1865_, v___x_1866_);
lean_dec(v_ref_1865_);
v___x_1868_ = ((lean_object*)(l_term_u2205___closed__1));
v___x_1869_ = ((lean_object*)(l_term_u2205___closed__2));
lean_inc(v___x_1867_);
v___x_1870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1867_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_Syntax_node1(v___x_1867_, v___x_1868_, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v_a_1860_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2___boxed(lean_object* v_x_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___aux__Init__Core______unexpand__EmptyCollection__emptyCollection__2(v_x_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask_default___redArg(lean_object* v_inst_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_inst_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask_default(lean_object* v_00_u03b1_1879_, lean_object* v_inst_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v_inst_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask___redArg(lean_object* v_inst_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v_inst_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedTask(lean_object* v_a_1884_, lean_object* v_inst_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v_inst_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Task_pure___boxed(lean_object* v_00_u03b1_1889_, lean_object* v_get_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = lean_task_pure(v_get_1890_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Task_get___boxed(lean_object* v_00_u03b1_1894_, lean_object* v_self_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = lean_task_get_own(v_self_1895_);
return v_res_1896_;
}
}
static lean_object* _init_l_Task_Priority_default(void){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = lean_unsigned_to_nat(0u);
return v___x_1897_;
}
}
static lean_object* _init_l_Task_Priority_max(void){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_unsigned_to_nat(8u);
return v___x_1898_;
}
}
static lean_object* _init_l_Task_Priority_dedicated(void){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_unsigned_to_nat(9u);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Task_spawn___boxed(lean_object* v_00_u03b1_1903_, lean_object* v_fn_1904_, lean_object* v_prio_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = lean_task_spawn(v_fn_1904_, v_prio_1905_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Task_map___boxed(lean_object* v_00_u03b1_1913_, lean_object* v_00_u03b2_1914_, lean_object* v_f_1915_, lean_object* v_x_1916_, lean_object* v_prio_1917_, lean_object* v_sync_1918_){
_start:
{
uint8_t v_sync_boxed_1919_; lean_object* v_res_1920_; 
v_sync_boxed_1919_ = lean_unbox(v_sync_1918_);
v_res_1920_ = lean_task_map(v_f_1915_, v_x_1916_, v_prio_1917_, v_sync_boxed_1919_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Task_bind___boxed(lean_object* v_00_u03b1_1927_, lean_object* v_00_u03b2_1928_, lean_object* v_x_1929_, lean_object* v_f_1930_, lean_object* v_prio_1931_, lean_object* v_sync_1932_){
_start:
{
uint8_t v_sync_boxed_1933_; lean_object* v_res_1934_; 
v_sync_boxed_1933_ = lean_unbox(v_sync_1932_);
v_res_1934_ = lean_task_bind(v_x_1929_, v_f_1930_, v_prio_1931_, v_sync_boxed_1933_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_strictOr___boxed(lean_object* v_b_u2081_1937_, lean_object* v_b_u2082_1938_){
_start:
{
uint8_t v_b_u2081_boxed_1939_; uint8_t v_b_u2082_boxed_1940_; uint8_t v_res_1941_; lean_object* v_r_1942_; 
v_b_u2081_boxed_1939_ = lean_unbox(v_b_u2081_1937_);
v_b_u2082_boxed_1940_ = lean_unbox(v_b_u2082_1938_);
v_res_1941_ = lean_strict_or(v_b_u2081_boxed_1939_, v_b_u2082_boxed_1940_);
v_r_1942_ = lean_box(v_res_1941_);
return v_r_1942_;
}
}
LEAN_EXPORT lean_object* l_strictAnd___boxed(lean_object* v_b_u2081_1945_, lean_object* v_b_u2082_1946_){
_start:
{
uint8_t v_b_u2081_boxed_1947_; uint8_t v_b_u2082_boxed_1948_; uint8_t v_res_1949_; lean_object* v_r_1950_; 
v_b_u2081_boxed_1947_ = lean_unbox(v_b_u2081_1945_);
v_b_u2082_boxed_1948_ = lean_unbox(v_b_u2082_1946_);
v_res_1949_ = lean_strict_and(v_b_u2081_boxed_1947_, v_b_u2082_boxed_1948_);
v_r_1950_ = lean_box(v_res_1949_);
return v_r_1950_;
}
}
LEAN_EXPORT uint8_t l_bne___redArg(lean_object* v_inst_1951_, lean_object* v_a_1952_, lean_object* v_b_1953_){
_start:
{
lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1954_ = lean_apply_2(v_inst_1951_, v_a_1952_, v_b_1953_);
v___x_1955_ = lean_unbox(v___x_1954_);
if (v___x_1955_ == 0)
{
uint8_t v___x_1956_; 
v___x_1956_ = 1;
return v___x_1956_;
}
else
{
uint8_t v___x_1957_; 
v___x_1957_ = 0;
return v___x_1957_;
}
}
}
LEAN_EXPORT lean_object* l_bne___redArg___boxed(lean_object* v_inst_1958_, lean_object* v_a_1959_, lean_object* v_b_1960_){
_start:
{
uint8_t v_res_1961_; lean_object* v_r_1962_; 
v_res_1961_ = l_bne___redArg(v_inst_1958_, v_a_1959_, v_b_1960_);
v_r_1962_ = lean_box(v_res_1961_);
return v_r_1962_;
}
}
LEAN_EXPORT uint8_t l_bne(lean_object* v_00_u03b1_1963_, lean_object* v_inst_1964_, lean_object* v_a_1965_, lean_object* v_b_1966_){
_start:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = lean_apply_2(v_inst_1964_, v_a_1965_, v_b_1966_);
v___x_1968_ = lean_unbox(v___x_1967_);
if (v___x_1968_ == 0)
{
uint8_t v___x_1969_; 
v___x_1969_ = 1;
return v___x_1969_;
}
else
{
uint8_t v___x_1970_; 
v___x_1970_ = 0;
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_bne___boxed(lean_object* v_00_u03b1_1971_, lean_object* v_inst_1972_, lean_object* v_a_1973_, lean_object* v_b_1974_){
_start:
{
uint8_t v_res_1975_; lean_object* v_r_1976_; 
v_res_1975_ = l_bne(v_00_u03b1_1971_, v_inst_1972_, v_a_1973_, v_b_1974_);
v_r_1976_ = lean_box(v_res_1975_);
return v_r_1976_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__0));
v___x_1995_ = l_String_toRawSubstring_x27(v___x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1(lean_object* v_x_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
lean_inc(v_x_2004_);
v___x_2008_ = l_Lean_Syntax_isOfKind(v_x_2004_, v___x_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec(v_x_2004_);
v___x_2009_ = lean_box(1);
v___x_2010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_ctor_set(v___x_2010_, 1, v_a_2006_);
return v___x_2010_;
}
else
{
lean_object* v_quotContext_2011_; lean_object* v_currMacroScope_2012_; lean_object* v_ref_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_quotContext_2011_ = lean_ctor_get(v_a_2005_, 1);
v_currMacroScope_2012_ = lean_ctor_get(v_a_2005_, 2);
v_ref_2013_ = lean_ctor_get(v_a_2005_, 5);
v___x_2014_ = lean_unsigned_to_nat(0u);
v___x_2015_ = l_Lean_Syntax_getArg(v_x_2004_, v___x_2014_);
v___x_2016_ = lean_unsigned_to_nat(2u);
v___x_2017_ = l_Lean_Syntax_getArg(v_x_2004_, v___x_2016_);
lean_dec(v_x_2004_);
v___x_2018_ = 0;
v___x_2019_ = l_Lean_SourceInfo_fromRef(v_ref_2013_, v___x_2018_);
v___x_2020_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_2021_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1, &l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1);
v___x_2022_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2));
lean_inc(v_currMacroScope_2012_);
lean_inc(v_quotContext_2011_);
v___x_2023_ = l_Lean_addMacroScope(v_quotContext_2011_, v___x_2022_, v_currMacroScope_2012_);
v___x_2024_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4));
lean_inc_n(v___x_2019_, 2);
v___x_2025_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2019_);
lean_ctor_set(v___x_2025_, 1, v___x_2021_);
lean_ctor_set(v___x_2025_, 2, v___x_2023_);
lean_ctor_set(v___x_2025_, 3, v___x_2024_);
v___x_2026_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_2027_ = l_Lean_Syntax_node2(v___x_2019_, v___x_2026_, v___x_2015_, v___x_2017_);
v___x_2028_ = l_Lean_Syntax_node2(v___x_2019_, v___x_2020_, v___x_2025_, v___x_2027_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
lean_ctor_set(v___x_2029_, 1, v_a_2006_);
return v___x_2029_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____1___boxed(lean_object* v_x_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l___aux__Init__Core______macroRules__term___x21_x3d____1(v_x_2030_, v_a_2031_, v_a_2032_);
lean_dec_ref(v_a_2031_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__bne__1(lean_object* v_x_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_2034_);
v___x_2038_ = l_Lean_Syntax_isOfKind(v_x_2034_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec(v_x_2034_);
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v_a_2036_);
return v___x_2040_;
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2041_ = lean_unsigned_to_nat(0u);
v___x_2042_ = l_Lean_Syntax_getArg(v_x_2034_, v___x_2041_);
v___x_2043_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_2042_);
v___x_2044_ = l_Lean_Syntax_isOfKind(v___x_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_dec(v___x_2042_);
lean_dec(v_x_2034_);
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
lean_ctor_set(v___x_2046_, 1, v_a_2036_);
return v___x_2046_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2047_ = lean_unsigned_to_nat(1u);
v___x_2048_ = l_Lean_Syntax_getArg(v_x_2034_, v___x_2047_);
lean_dec(v_x_2034_);
v___x_2049_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2048_);
v___x_2050_ = l_Lean_Syntax_matchesNull(v___x_2048_, v___x_2049_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_dec(v___x_2048_);
lean_dec(v___x_2042_);
v___x_2051_ = lean_box(0);
v___x_2052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v_a_2036_);
return v___x_2052_;
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v_ref_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2053_ = l_Lean_Syntax_getArg(v___x_2048_, v___x_2041_);
v___x_2054_ = l_Lean_Syntax_getArg(v___x_2048_, v___x_2047_);
lean_dec(v___x_2048_);
v_ref_2055_ = l_Lean_replaceRef(v___x_2042_, v_a_2035_);
lean_dec(v___x_2042_);
v___x_2056_ = 0;
v___x_2057_ = l_Lean_SourceInfo_fromRef(v_ref_2055_, v___x_2056_);
lean_dec(v_ref_2055_);
v___x_2058_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
v___x_2059_ = ((lean_object*)(l_term___x21_x3d___00__closed__2));
lean_inc(v___x_2057_);
v___x_2060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2057_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = l_Lean_Syntax_node3(v___x_2057_, v___x_2058_, v___x_2053_, v___x_2060_, v___x_2054_);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v_a_2036_);
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__bne__1___boxed(lean_object* v_x_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l___aux__Init__Core______unexpand__bne__1(v_x_2063_, v_a_2064_, v_a_2065_);
lean_dec(v_a_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2(lean_object* v_x_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = ((lean_object*)(l_term___x21_x3d___00__closed__1));
lean_inc(v_x_2074_);
v___x_2078_ = l_Lean_Syntax_isOfKind(v_x_2074_, v___x_2077_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_dec(v_x_2074_);
v___x_2079_ = lean_box(1);
v___x_2080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v_a_2076_);
return v___x_2080_;
}
else
{
lean_object* v_quotContext_2081_; lean_object* v_currMacroScope_2082_; lean_object* v_ref_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_quotContext_2081_ = lean_ctor_get(v_a_2075_, 1);
v_currMacroScope_2082_ = lean_ctor_get(v_a_2075_, 2);
v_ref_2083_ = lean_ctor_get(v_a_2075_, 5);
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = l_Lean_Syntax_getArg(v_x_2074_, v___x_2084_);
v___x_2086_ = lean_unsigned_to_nat(2u);
v___x_2087_ = l_Lean_Syntax_getArg(v_x_2074_, v___x_2086_);
lean_dec(v_x_2074_);
v___x_2088_ = 0;
v___x_2089_ = l_Lean_SourceInfo_fromRef(v_ref_2083_, v___x_2088_);
v___x_2090_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__1));
v___x_2091_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____2___closed__2));
lean_inc_n(v___x_2089_, 2);
v___x_2092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2089_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1, &l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__1);
v___x_2094_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__2));
lean_inc(v_currMacroScope_2082_);
lean_inc(v_quotContext_2081_);
v___x_2095_ = l_Lean_addMacroScope(v_quotContext_2081_, v___x_2094_, v_currMacroScope_2082_);
v___x_2096_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x21_x3d____1___closed__4));
v___x_2097_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2089_);
lean_ctor_set(v___x_2097_, 1, v___x_2093_);
lean_ctor_set(v___x_2097_, 2, v___x_2095_);
lean_ctor_set(v___x_2097_, 3, v___x_2096_);
v___x_2098_ = l_Lean_Syntax_node4(v___x_2089_, v___x_2090_, v___x_2092_, v___x_2097_, v___x_2085_, v___x_2087_);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v_a_2076_);
return v___x_2099_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___x21_x3d____2___boxed(lean_object* v_x_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l___aux__Init__Core______macroRules__term___x21_x3d____2(v_x_2100_, v_a_2101_, v_a_2102_);
lean_dec_ref(v_a_2101_);
return v_res_2103_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfLawfulBEq___redArg(lean_object* v_inst_2104_, lean_object* v_x_2105_, lean_object* v_y_2106_){
_start:
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = lean_apply_2(v_inst_2104_, v_x_2105_, v_y_2106_);
v___x_2108_ = lean_unbox(v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfLawfulBEq___redArg___boxed(lean_object* v_inst_2109_, lean_object* v_x_2110_, lean_object* v_y_2111_){
_start:
{
uint8_t v_res_2112_; lean_object* v_r_2113_; 
v_res_2112_ = l_instDecidableEqOfLawfulBEq___redArg(v_inst_2109_, v_x_2110_, v_y_2111_);
v_r_2113_ = lean_box(v_res_2112_);
return v_r_2113_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfLawfulBEq(lean_object* v_00_u03b1_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_x_2117_, lean_object* v_y_2118_){
_start:
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = lean_apply_2(v_inst_2115_, v_x_2117_, v_y_2118_);
v___x_2120_ = lean_unbox(v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfLawfulBEq___boxed(lean_object* v_00_u03b1_2121_, lean_object* v_inst_2122_, lean_object* v_inst_2123_, lean_object* v_x_2124_, lean_object* v_y_2125_){
_start:
{
uint8_t v_res_2126_; lean_object* v_r_2127_; 
v_res_2126_ = l_instDecidableEqOfLawfulBEq(v_00_u03b1_2121_, v_inst_2122_, v_inst_2123_, v_x_2124_, v_y_2125_);
v_r_2127_ = lean_box(v_res_2126_);
return v_r_2127_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__0));
v___x_2146_ = l_String_toRawSubstring_x27(v___x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____1(lean_object* v_x_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2158_ = ((lean_object*)(l_term___u2260___00__closed__1));
lean_inc(v_x_2155_);
v___x_2159_ = l_Lean_Syntax_isOfKind(v_x_2155_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
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
v_currMacroScope_2163_ = lean_ctor_get(v_a_2156_, 2);
v_ref_2164_ = lean_ctor_get(v_a_2156_, 5);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = l_Lean_Syntax_getArg(v_x_2155_, v___x_2165_);
v___x_2167_ = lean_unsigned_to_nat(2u);
v___x_2168_ = l_Lean_Syntax_getArg(v_x_2155_, v___x_2167_);
lean_dec(v_x_2155_);
v___x_2169_ = 0;
v___x_2170_ = l_Lean_SourceInfo_fromRef(v_ref_2164_, v___x_2169_);
v___x_2171_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
v___x_2172_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2260____1___closed__1, &l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1);
v___x_2173_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__2));
lean_inc(v_currMacroScope_2163_);
lean_inc(v_quotContext_2162_);
v___x_2174_ = l_Lean_addMacroScope(v_quotContext_2162_, v___x_2173_, v_currMacroScope_2163_);
v___x_2175_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__4));
lean_inc_n(v___x_2170_, 2);
v___x_2176_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2170_);
lean_ctor_set(v___x_2176_, 1, v___x_2172_);
lean_ctor_set(v___x_2176_, 2, v___x_2174_);
lean_ctor_set(v___x_2176_, 3, v___x_2175_);
v___x_2177_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__13));
v___x_2178_ = l_Lean_Syntax_node2(v___x_2170_, v___x_2177_, v___x_2166_, v___x_2168_);
v___x_2179_ = l_Lean_Syntax_node2(v___x_2170_, v___x_2171_, v___x_2176_, v___x_2178_);
v___x_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set(v___x_2180_, 1, v_a_2157_);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____1___boxed(lean_object* v_x_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l___aux__Init__Core______macroRules__term___u2260____1(v_x_2181_, v_a_2182_, v_a_2183_);
lean_dec_ref(v_a_2182_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Ne__1(lean_object* v_x_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v___x_2188_; uint8_t v___x_2189_; 
v___x_2188_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___x3c_x2d_x3e____1___closed__4));
lean_inc(v_x_2185_);
v___x_2189_ = l_Lean_Syntax_isOfKind(v_x_2185_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec(v_x_2185_);
v___x_2190_ = lean_box(0);
v___x_2191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v_a_2187_);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2192_ = lean_unsigned_to_nat(0u);
v___x_2193_ = l_Lean_Syntax_getArg(v_x_2185_, v___x_2192_);
v___x_2194_ = ((lean_object*)(l___aux__Init__Core______unexpand__Iff__1___closed__1));
lean_inc(v___x_2193_);
v___x_2195_ = l_Lean_Syntax_isOfKind(v___x_2193_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec(v___x_2193_);
lean_dec(v_x_2185_);
v___x_2196_ = lean_box(0);
v___x_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
lean_ctor_set(v___x_2197_, 1, v_a_2187_);
return v___x_2197_;
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = l_Lean_Syntax_getArg(v_x_2185_, v___x_2198_);
lean_dec(v_x_2185_);
v___x_2200_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2199_);
v___x_2201_ = l_Lean_Syntax_matchesNull(v___x_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec(v___x_2199_);
lean_dec(v___x_2193_);
v___x_2202_ = lean_box(0);
v___x_2203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
lean_ctor_set(v___x_2203_, 1, v_a_2187_);
return v___x_2203_;
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_ref_2206_; uint8_t v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2204_ = l_Lean_Syntax_getArg(v___x_2199_, v___x_2192_);
v___x_2205_ = l_Lean_Syntax_getArg(v___x_2199_, v___x_2198_);
lean_dec(v___x_2199_);
v_ref_2206_ = l_Lean_replaceRef(v___x_2193_, v_a_2186_);
lean_dec(v___x_2193_);
v___x_2207_ = 0;
v___x_2208_ = l_Lean_SourceInfo_fromRef(v_ref_2206_, v___x_2207_);
lean_dec(v_ref_2206_);
v___x_2209_ = ((lean_object*)(l_term___u2260___00__closed__1));
v___x_2210_ = ((lean_object*)(l_term___u2260___00__closed__2));
lean_inc(v___x_2208_);
v___x_2211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2208_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = l_Lean_Syntax_node3(v___x_2208_, v___x_2209_, v___x_2204_, v___x_2211_, v___x_2205_);
v___x_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v_a_2187_);
return v___x_2213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______unexpand__Ne__1___boxed(lean_object* v_x_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l___aux__Init__Core______unexpand__Ne__1(v_x_2214_, v_a_2215_, v_a_2216_);
lean_dec(v_a_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____2(lean_object* v_x_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = ((lean_object*)(l_term___u2260___00__closed__1));
lean_inc(v_x_2225_);
v___x_2229_ = l_Lean_Syntax_isOfKind(v_x_2225_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v_x_2225_);
v___x_2230_ = lean_box(1);
v___x_2231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
lean_ctor_set(v___x_2231_, 1, v_a_2227_);
return v___x_2231_;
}
else
{
lean_object* v_quotContext_2232_; lean_object* v_currMacroScope_2233_; lean_object* v_ref_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v_quotContext_2232_ = lean_ctor_get(v_a_2226_, 1);
v_currMacroScope_2233_ = lean_ctor_get(v_a_2226_, 2);
v_ref_2234_ = lean_ctor_get(v_a_2226_, 5);
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = l_Lean_Syntax_getArg(v_x_2225_, v___x_2235_);
v___x_2237_ = lean_unsigned_to_nat(2u);
v___x_2238_ = l_Lean_Syntax_getArg(v_x_2225_, v___x_2237_);
lean_dec(v_x_2225_);
v___x_2239_ = 0;
v___x_2240_ = l_Lean_SourceInfo_fromRef(v_ref_2234_, v___x_2239_);
v___x_2241_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____2___closed__1));
v___x_2242_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____2___closed__2));
lean_inc_n(v___x_2240_, 2);
v___x_2243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2240_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = lean_obj_once(&l___aux__Init__Core______macroRules__term___u2260____1___closed__1, &l___aux__Init__Core______macroRules__term___u2260____1___closed__1_once, _init_l___aux__Init__Core______macroRules__term___u2260____1___closed__1);
v___x_2245_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__2));
lean_inc(v_currMacroScope_2233_);
lean_inc(v_quotContext_2232_);
v___x_2246_ = l_Lean_addMacroScope(v_quotContext_2232_, v___x_2245_, v_currMacroScope_2233_);
v___x_2247_ = ((lean_object*)(l___aux__Init__Core______macroRules__term___u2260____1___closed__4));
v___x_2248_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2240_);
lean_ctor_set(v___x_2248_, 1, v___x_2244_);
lean_ctor_set(v___x_2248_, 2, v___x_2246_);
lean_ctor_set(v___x_2248_, 3, v___x_2247_);
v___x_2249_ = l_Lean_Syntax_node4(v___x_2240_, v___x_2241_, v___x_2243_, v___x_2248_, v___x_2236_, v___x_2238_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v_a_2227_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__term___u2260____2___boxed(lean_object* v_x_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l___aux__Init__Core______macroRules__term___u2260____2(v_x_2251_, v_a_2252_, v_a_2253_);
lean_dec_ref(v_a_2252_);
return v_res_2254_;
}
}
static lean_object* _init_l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__5));
v___x_2270_ = l_String_toRawSubstring_x27(v___x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1(lean_object* v_x_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__2));
v___x_2285_ = l_Lean_Syntax_isOfKind(v_x_2281_, v___x_2284_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_box(1);
v___x_2287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v_a_2283_);
return v___x_2287_;
}
else
{
lean_object* v_quotContext_2288_; lean_object* v_currMacroScope_2289_; lean_object* v_ref_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_quotContext_2288_ = lean_ctor_get(v_a_2282_, 1);
v_currMacroScope_2289_ = lean_ctor_get(v_a_2282_, 2);
v_ref_2290_ = lean_ctor_get(v_a_2282_, 5);
v___x_2291_ = 0;
v___x_2292_ = l_Lean_SourceInfo_fromRef(v_ref_2290_, v___x_2291_);
v___x_2293_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__3));
v___x_2294_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__4));
lean_inc_n(v___x_2292_, 2);
v___x_2295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2292_);
lean_ctor_set(v___x_2295_, 1, v___x_2293_);
v___x_2296_ = lean_obj_once(&l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6, &l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6_once, _init_l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__6);
v___x_2297_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__8));
lean_inc(v_currMacroScope_2289_);
lean_inc(v_quotContext_2288_);
v___x_2298_ = l_Lean_addMacroScope(v_quotContext_2288_, v___x_2297_, v_currMacroScope_2289_);
v___x_2299_ = ((lean_object*)(l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___closed__10));
v___x_2300_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2292_);
lean_ctor_set(v___x_2300_, 1, v___x_2296_);
lean_ctor_set(v___x_2300_, 2, v___x_2298_);
lean_ctor_set(v___x_2300_, 3, v___x_2299_);
v___x_2301_ = l_Lean_Syntax_node2(v___x_2292_, v___x_2294_, v___x_2295_, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
lean_ctor_set(v___x_2302_, 1, v_a_2283_);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1___boxed(lean_object* v_x_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l___aux__Init__Core______macroRules__Lean__Parser__Tactic__tacticRfl__1(v_x_2303_, v_a_2304_, v_a_2305_);
lean_dec_ref(v_a_2304_);
return v_res_2306_;
}
}
static lean_object* _init_l_instTransIff(void){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_box(0);
return v___x_2307_;
}
}
LEAN_EXPORT uint8_t l_toBoolUsing___redArg(uint8_t v_d_2308_){
_start:
{
return v_d_2308_;
}
}
LEAN_EXPORT lean_object* l_toBoolUsing___redArg___boxed(lean_object* v_d_2309_){
_start:
{
uint8_t v_d_boxed_2310_; uint8_t v_res_2311_; lean_object* v_r_2312_; 
v_d_boxed_2310_ = lean_unbox(v_d_2309_);
v_res_2311_ = l_toBoolUsing___redArg(v_d_boxed_2310_);
v_r_2312_ = lean_box(v_res_2311_);
return v_r_2312_;
}
}
LEAN_EXPORT uint8_t l_toBoolUsing(lean_object* v_p_2313_, uint8_t v_d_2314_){
_start:
{
return v_d_2314_;
}
}
LEAN_EXPORT lean_object* l_toBoolUsing___boxed(lean_object* v_p_2315_, lean_object* v_d_2316_){
_start:
{
uint8_t v_d_boxed_2317_; uint8_t v_res_2318_; lean_object* v_r_2319_; 
v_d_boxed_2317_ = lean_unbox(v_d_2316_);
v_res_2318_ = l_toBoolUsing(v_p_2315_, v_d_boxed_2317_);
v_r_2319_ = lean_box(v_res_2318_);
return v_r_2319_;
}
}
static uint8_t _init_l_instDecidableTrue(void){
_start:
{
uint8_t v___x_2320_; 
v___x_2320_ = 1;
return v___x_2320_;
}
}
static uint8_t _init_l_instDecidableFalse(void){
_start:
{
uint8_t v___x_2321_; 
v___x_2321_ = 0;
return v___x_2321_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__iff___redArg(uint8_t v_dp_2322_){
_start:
{
return v_dp_2322_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__iff___redArg___boxed(lean_object* v_dp_2323_){
_start:
{
uint8_t v_dp_boxed_2324_; uint8_t v_res_2325_; lean_object* v_r_2326_; 
v_dp_boxed_2324_ = lean_unbox(v_dp_2323_);
v_res_2325_ = l_decidable__of__decidable__of__iff___redArg(v_dp_boxed_2324_);
v_r_2326_ = lean_box(v_res_2325_);
return v_r_2326_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__iff(lean_object* v_p_2327_, lean_object* v_q_2328_, uint8_t v_dp_2329_, lean_object* v_h_2330_){
_start:
{
return v_dp_2329_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__iff___boxed(lean_object* v_p_2331_, lean_object* v_q_2332_, lean_object* v_dp_2333_, lean_object* v_h_2334_){
_start:
{
uint8_t v_dp_boxed_2335_; uint8_t v_res_2336_; lean_object* v_r_2337_; 
v_dp_boxed_2335_ = lean_unbox(v_dp_2333_);
v_res_2336_ = l_decidable__of__decidable__of__iff(v_p_2331_, v_q_2332_, v_dp_boxed_2335_, v_h_2334_);
v_r_2337_ = lean_box(v_res_2336_);
return v_r_2337_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__eq___redArg(uint8_t v_inst_2338_){
_start:
{
return v_inst_2338_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__eq___redArg___boxed(lean_object* v_inst_2339_){
_start:
{
uint8_t v_inst_8__boxed_2340_; uint8_t v_res_2341_; lean_object* v_r_2342_; 
v_inst_8__boxed_2340_ = lean_unbox(v_inst_2339_);
v_res_2341_ = l_decidable__of__decidable__of__eq___redArg(v_inst_8__boxed_2340_);
v_r_2342_ = lean_box(v_res_2341_);
return v_r_2342_;
}
}
LEAN_EXPORT uint8_t l_decidable__of__decidable__of__eq(lean_object* v_p_2343_, lean_object* v_q_2344_, uint8_t v_inst_2345_, lean_object* v_h_2346_){
_start:
{
return v_inst_2345_;
}
}
LEAN_EXPORT lean_object* l_decidable__of__decidable__of__eq___boxed(lean_object* v_p_2347_, lean_object* v_q_2348_, lean_object* v_inst_2349_, lean_object* v_h_2350_){
_start:
{
uint8_t v_inst_11__boxed_2351_; uint8_t v_res_2352_; lean_object* v_r_2353_; 
v_inst_11__boxed_2351_ = lean_unbox(v_inst_2349_);
v_res_2352_ = l_decidable__of__decidable__of__eq(v_p_2347_, v_q_2348_, v_inst_11__boxed_2351_, v_h_2350_);
v_r_2353_ = lean_box(v_res_2352_);
return v_r_2353_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIff___redArg(uint8_t v_dp_2354_, uint8_t v_dq_2355_){
_start:
{
if (v_dq_2355_ == 0)
{
if (v_dp_2354_ == 0)
{
uint8_t v___x_2356_; 
v___x_2356_ = 1;
return v___x_2356_;
}
else
{
return v_dq_2355_;
}
}
else
{
return v_dp_2354_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableIff___redArg___boxed(lean_object* v_dp_2357_, lean_object* v_dq_2358_){
_start:
{
uint8_t v_dp_boxed_2359_; uint8_t v_dq_boxed_2360_; uint8_t v_res_2361_; lean_object* v_r_2362_; 
v_dp_boxed_2359_ = lean_unbox(v_dp_2357_);
v_dq_boxed_2360_ = lean_unbox(v_dq_2358_);
v_res_2361_ = l_instDecidableIff___redArg(v_dp_boxed_2359_, v_dq_boxed_2360_);
v_r_2362_ = lean_box(v_res_2361_);
return v_r_2362_;
}
}
LEAN_EXPORT uint8_t l_instDecidableIff(lean_object* v_p_2363_, lean_object* v_q_2364_, uint8_t v_dp_2365_, uint8_t v_dq_2366_){
_start:
{
if (v_dq_2366_ == 0)
{
if (v_dp_2365_ == 0)
{
uint8_t v___x_2367_; 
v___x_2367_ = 1;
return v___x_2367_;
}
else
{
return v_dq_2366_;
}
}
else
{
return v_dp_2365_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableIff___boxed(lean_object* v_p_2368_, lean_object* v_q_2369_, lean_object* v_dp_2370_, lean_object* v_dq_2371_){
_start:
{
uint8_t v_dp_boxed_2372_; uint8_t v_dq_boxed_2373_; uint8_t v_res_2374_; lean_object* v_r_2375_; 
v_dp_boxed_2372_ = lean_unbox(v_dp_2370_);
v_dq_boxed_2373_ = lean_unbox(v_dq_2371_);
v_res_2374_ = l_instDecidableIff(v_p_2368_, v_q_2369_, v_dp_boxed_2372_, v_dq_boxed_2373_);
v_r_2375_ = lean_box(v_res_2374_);
return v_r_2375_;
}
}
LEAN_EXPORT lean_object* l_iteInduction___redArg(uint8_t v_inst_2376_, lean_object* v_hpos_2377_, lean_object* v_hneg_2378_){
_start:
{
if (v_inst_2376_ == 0)
{
lean_object* v___x_2379_; 
lean_dec(v_hpos_2377_);
v___x_2379_ = lean_apply_1(v_hneg_2378_, lean_box(0));
return v___x_2379_;
}
else
{
lean_object* v___x_2380_; 
lean_dec(v_hneg_2378_);
v___x_2380_ = lean_apply_1(v_hpos_2377_, lean_box(0));
return v___x_2380_;
}
}
}
LEAN_EXPORT lean_object* l_iteInduction___redArg___boxed(lean_object* v_inst_2381_, lean_object* v_hpos_2382_, lean_object* v_hneg_2383_){
_start:
{
uint8_t v_inst_boxed_2384_; lean_object* v_res_2385_; 
v_inst_boxed_2384_ = lean_unbox(v_inst_2381_);
v_res_2385_ = l_iteInduction___redArg(v_inst_boxed_2384_, v_hpos_2382_, v_hneg_2383_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_iteInduction(lean_object* v_00_u03b1_2386_, lean_object* v_c_2387_, uint8_t v_inst_2388_, lean_object* v_motive_2389_, lean_object* v_t_2390_, lean_object* v_e_2391_, lean_object* v_hpos_2392_, lean_object* v_hneg_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_iteInduction___redArg(v_inst_2388_, v_hpos_2392_, v_hneg_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_iteInduction___boxed(lean_object* v_00_u03b1_2395_, lean_object* v_c_2396_, lean_object* v_inst_2397_, lean_object* v_motive_2398_, lean_object* v_t_2399_, lean_object* v_e_2400_, lean_object* v_hpos_2401_, lean_object* v_hneg_2402_){
_start:
{
uint8_t v_inst_boxed_2403_; lean_object* v_res_2404_; 
v_inst_boxed_2403_ = lean_unbox(v_inst_2397_);
v_res_2404_ = l_iteInduction(v_00_u03b1_2395_, v_c_2396_, v_inst_boxed_2403_, v_motive_2398_, v_t_2399_, v_e_2400_, v_hpos_2401_, v_hneg_2402_);
lean_dec(v_e_2400_);
lean_dec(v_t_2399_);
return v_res_2404_;
}
}
LEAN_EXPORT uint8_t l_instDecidableDite___redArg(uint8_t v_dC_2405_, lean_object* v_dT_2406_, lean_object* v_dE_2407_){
_start:
{
if (v_dC_2405_ == 0)
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
lean_dec_ref(v_dT_2406_);
v___x_2408_ = lean_apply_1(v_dE_2407_, lean_box(0));
v___x_2409_ = lean_unbox(v___x_2408_);
return v___x_2409_;
}
else
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
lean_dec_ref(v_dE_2407_);
v___x_2410_ = lean_apply_1(v_dT_2406_, lean_box(0));
v___x_2411_ = lean_unbox(v___x_2410_);
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableDite___redArg___boxed(lean_object* v_dC_2412_, lean_object* v_dT_2413_, lean_object* v_dE_2414_){
_start:
{
uint8_t v_dC_boxed_2415_; uint8_t v_res_2416_; lean_object* v_r_2417_; 
v_dC_boxed_2415_ = lean_unbox(v_dC_2412_);
v_res_2416_ = l_instDecidableDite___redArg(v_dC_boxed_2415_, v_dT_2413_, v_dE_2414_);
v_r_2417_ = lean_box(v_res_2416_);
return v_r_2417_;
}
}
LEAN_EXPORT uint8_t l_instDecidableDite(lean_object* v_c_2418_, lean_object* v_t_2419_, lean_object* v_e_2420_, uint8_t v_dC_2421_, lean_object* v_dT_2422_, lean_object* v_dE_2423_){
_start:
{
if (v_dC_2421_ == 0)
{
lean_object* v___x_2424_; uint8_t v___x_2425_; 
lean_dec_ref(v_dT_2422_);
v___x_2424_ = lean_apply_1(v_dE_2423_, lean_box(0));
v___x_2425_ = lean_unbox(v___x_2424_);
return v___x_2425_;
}
else
{
lean_object* v___x_2426_; uint8_t v___x_2427_; 
lean_dec_ref(v_dE_2423_);
v___x_2426_ = lean_apply_1(v_dT_2422_, lean_box(0));
v___x_2427_ = lean_unbox(v___x_2426_);
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableDite___boxed(lean_object* v_c_2428_, lean_object* v_t_2429_, lean_object* v_e_2430_, lean_object* v_dC_2431_, lean_object* v_dT_2432_, lean_object* v_dE_2433_){
_start:
{
uint8_t v_dC_boxed_2434_; uint8_t v_res_2435_; lean_object* v_r_2436_; 
v_dC_boxed_2434_ = lean_unbox(v_dC_2431_);
v_res_2435_ = l_instDecidableDite(v_c_2428_, v_t_2429_, v_e_2430_, v_dC_boxed_2434_, v_dT_2432_, v_dE_2433_);
v_r_2436_ = lean_box(v_res_2435_);
return v_r_2436_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg___lam__0(lean_object* v_a_2437_){
_start:
{
lean_inc(v_a_2437_);
return v_a_2437_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg___lam__0___boxed(lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_noConfusionEnum___redArg___lam__0(v_a_2438_);
lean_dec(v_a_2438_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum___redArg(lean_object* v_f_2441_, lean_object* v_x_2442_, lean_object* v_y_2443_){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; lean_object* v___f_2447_; 
lean_inc_ref(v_f_2441_);
v___x_2444_ = lean_apply_1(v_f_2441_, v_x_2442_);
v___x_2445_ = lean_apply_1(v_f_2441_, v_y_2443_);
v___x_2446_ = lean_nat_dec_eq(v___x_2444_, v___x_2445_);
lean_dec(v___x_2445_);
lean_dec(v___x_2444_);
v___f_2447_ = ((lean_object*)(l_noConfusionEnum___redArg___closed__0));
return v___f_2447_;
}
}
LEAN_EXPORT lean_object* l_noConfusionEnum(lean_object* v_00_u03b1_2448_, lean_object* v_f_2449_, lean_object* v_P_2450_, lean_object* v_x_2451_, lean_object* v_y_2452_, lean_object* v_h_2453_){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; lean_object* v___f_2457_; 
lean_inc_ref(v_f_2449_);
v___x_2454_ = lean_apply_1(v_f_2449_, v_x_2451_);
v___x_2455_ = lean_apply_1(v_f_2449_, v_y_2452_);
v___x_2456_ = lean_nat_dec_eq(v___x_2454_, v___x_2455_);
lean_dec(v___x_2455_);
lean_dec(v___x_2454_);
v___f_2457_ = ((lean_object*)(l_noConfusionEnum___redArg___closed__0));
return v___f_2457_;
}
}
static lean_object* _init_l_instInhabitedProp(void){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_box(0);
return v___x_2458_;
}
}
static lean_object* _init_l_instInhabitedNonScalar_default(void){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_unsigned_to_nat(0u);
return v___x_2459_;
}
}
static lean_object* _init_l_instInhabitedNonScalar(void){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_unsigned_to_nat(0u);
return v___x_2460_;
}
}
static lean_object* _init_l_instInhabitedPNonScalar_default(void){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_unsigned_to_nat(0u);
return v___x_2461_;
}
}
static lean_object* _init_l_instInhabitedPNonScalar(void){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_unsigned_to_nat(0u);
return v___x_2462_;
}
}
static lean_object* _init_l_instInhabitedTrue(void){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_box(0);
return v___x_2463_;
}
}
LEAN_EXPORT uint8_t l_Subtype_instBEq___redArg___lam__0(lean_object* v_inst_2464_, lean_object* v_x_2465_, lean_object* v_y_2466_){
_start:
{
lean_object* v___x_2467_; uint8_t v___x_2468_; 
v___x_2467_ = lean_apply_2(v_inst_2464_, v_x_2465_, v_y_2466_);
v___x_2468_ = lean_unbox(v___x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq___redArg___lam__0___boxed(lean_object* v_inst_2469_, lean_object* v_x_2470_, lean_object* v_y_2471_){
_start:
{
uint8_t v_res_2472_; lean_object* v_r_2473_; 
v_res_2472_ = l_Subtype_instBEq___redArg___lam__0(v_inst_2469_, v_x_2470_, v_y_2471_);
v_r_2473_ = lean_box(v_res_2472_);
return v_r_2473_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq___redArg(lean_object* v_inst_2474_){
_start:
{
lean_object* v___f_2475_; 
v___f_2475_ = lean_alloc_closure((void*)(l_Subtype_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2475_, 0, v_inst_2474_);
return v___f_2475_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instBEq(lean_object* v_00_u03b1_2476_, lean_object* v_p_2477_, lean_object* v_inst_2478_){
_start:
{
lean_object* v___f_2479_; 
v___f_2479_ = lean_alloc_closure((void*)(l_Subtype_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2479_, 0, v_inst_2478_);
return v___f_2479_;
}
}
LEAN_EXPORT uint8_t l_Subtype_instDecidableEq___redArg(lean_object* v_inst_2480_, lean_object* v_x_2481_, lean_object* v_x_2482_){
_start:
{
lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2483_ = lean_apply_2(v_inst_2480_, v_x_2481_, v_x_2482_);
v___x_2484_ = lean_unbox(v___x_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instDecidableEq___redArg___boxed(lean_object* v_inst_2485_, lean_object* v_x_2486_, lean_object* v_x_2487_){
_start:
{
uint8_t v_res_2488_; lean_object* v_r_2489_; 
v_res_2488_ = l_Subtype_instDecidableEq___redArg(v_inst_2485_, v_x_2486_, v_x_2487_);
v_r_2489_ = lean_box(v_res_2488_);
return v_r_2489_;
}
}
LEAN_EXPORT uint8_t l_Subtype_instDecidableEq(lean_object* v_00_u03b1_2490_, lean_object* v_p_2491_, lean_object* v_inst_2492_, lean_object* v_x_2493_, lean_object* v_x_2494_){
_start:
{
lean_object* v___x_2495_; uint8_t v___x_2496_; 
v___x_2495_ = lean_apply_2(v_inst_2492_, v_x_2493_, v_x_2494_);
v___x_2496_ = lean_unbox(v___x_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instDecidableEq___boxed(lean_object* v_00_u03b1_2497_, lean_object* v_p_2498_, lean_object* v_inst_2499_, lean_object* v_x_2500_, lean_object* v_x_2501_){
_start:
{
uint8_t v_res_2502_; lean_object* v_r_2503_; 
v_res_2502_ = l_Subtype_instDecidableEq(v_00_u03b1_2497_, v_p_2498_, v_inst_2499_, v_x_2500_, v_x_2501_);
v_r_2503_ = lean_box(v_res_2502_);
return v_r_2503_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedLeft___redArg(lean_object* v_inst_2504_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v_inst_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedLeft(lean_object* v_00_u03b1_2506_, lean_object* v_00_u03b2_2507_, lean_object* v_inst_2508_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_inst_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedRight___redArg(lean_object* v_inst_2510_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2511_, 0, v_inst_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Sum_inhabitedRight(lean_object* v_00_u03b1_2512_, lean_object* v_00_u03b2_2513_, lean_object* v_inst_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2515_, 0, v_inst_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum_decEq___redArg(lean_object* v_inst_2516_, lean_object* v_inst_2517_, lean_object* v_x_2518_, lean_object* v_x_2519_){
_start:
{
if (lean_obj_tag(v_x_2518_) == 0)
{
lean_dec_ref(v_inst_2517_);
if (lean_obj_tag(v_x_2519_) == 0)
{
lean_object* v_val_2520_; lean_object* v_val_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v_val_2520_ = lean_ctor_get(v_x_2518_, 0);
lean_inc(v_val_2520_);
lean_dec_ref_known(v_x_2518_, 1);
v_val_2521_ = lean_ctor_get(v_x_2519_, 0);
lean_inc(v_val_2521_);
lean_dec_ref_known(v_x_2519_, 1);
v___x_2522_ = lean_apply_2(v_inst_2516_, v_val_2520_, v_val_2521_);
v___x_2523_ = lean_unbox(v___x_2522_);
return v___x_2523_;
}
else
{
uint8_t v___x_2524_; 
lean_dec_ref_known(v_x_2519_, 1);
lean_dec_ref_known(v_x_2518_, 1);
lean_dec_ref(v_inst_2516_);
v___x_2524_ = 0;
return v___x_2524_;
}
}
else
{
lean_dec_ref(v_inst_2516_);
if (lean_obj_tag(v_x_2519_) == 0)
{
uint8_t v___x_2525_; 
lean_dec_ref_known(v_x_2519_, 1);
lean_dec_ref_known(v_x_2518_, 1);
lean_dec_ref(v_inst_2517_);
v___x_2525_ = 0;
return v___x_2525_;
}
else
{
lean_object* v_val_2526_; lean_object* v_val_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v_val_2526_ = lean_ctor_get(v_x_2518_, 0);
lean_inc(v_val_2526_);
lean_dec_ref_known(v_x_2518_, 1);
v_val_2527_ = lean_ctor_get(v_x_2519_, 0);
lean_inc(v_val_2527_);
lean_dec_ref_known(v_x_2519_, 1);
v___x_2528_ = lean_apply_2(v_inst_2517_, v_val_2526_, v_val_2527_);
v___x_2529_ = lean_unbox(v___x_2528_);
return v___x_2529_;
}
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum_decEq___redArg___boxed(lean_object* v_inst_2530_, lean_object* v_inst_2531_, lean_object* v_x_2532_, lean_object* v_x_2533_){
_start:
{
uint8_t v_res_2534_; lean_object* v_r_2535_; 
v_res_2534_ = l_instDecidableEqSum_decEq___redArg(v_inst_2530_, v_inst_2531_, v_x_2532_, v_x_2533_);
v_r_2535_ = lean_box(v_res_2534_);
return v_r_2535_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum_decEq(lean_object* v_00_u03b1_2536_, lean_object* v_00_u03b2_2537_, lean_object* v_inst_2538_, lean_object* v_inst_2539_, lean_object* v_x_2540_, lean_object* v_x_2541_){
_start:
{
uint8_t v___x_2542_; 
v___x_2542_ = l_instDecidableEqSum_decEq___redArg(v_inst_2538_, v_inst_2539_, v_x_2540_, v_x_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum_decEq___boxed(lean_object* v_00_u03b1_2543_, lean_object* v_00_u03b2_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_x_2547_, lean_object* v_x_2548_){
_start:
{
uint8_t v_res_2549_; lean_object* v_r_2550_; 
v_res_2549_ = l_instDecidableEqSum_decEq(v_00_u03b1_2543_, v_00_u03b2_2544_, v_inst_2545_, v_inst_2546_, v_x_2547_, v_x_2548_);
v_r_2550_ = lean_box(v_res_2549_);
return v_r_2550_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum___redArg(lean_object* v_inst_2551_, lean_object* v_inst_2552_, lean_object* v_x_2553_, lean_object* v_x_2554_){
_start:
{
uint8_t v___x_2555_; 
v___x_2555_ = l_instDecidableEqSum_decEq___redArg(v_inst_2551_, v_inst_2552_, v_x_2553_, v_x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum___redArg___boxed(lean_object* v_inst_2556_, lean_object* v_inst_2557_, lean_object* v_x_2558_, lean_object* v_x_2559_){
_start:
{
uint8_t v_res_2560_; lean_object* v_r_2561_; 
v_res_2560_ = l_instDecidableEqSum___redArg(v_inst_2556_, v_inst_2557_, v_x_2558_, v_x_2559_);
v_r_2561_ = lean_box(v_res_2560_);
return v_r_2561_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSum(lean_object* v_00_u03b1_2562_, lean_object* v_00_u03b2_2563_, lean_object* v_inst_2564_, lean_object* v_inst_2565_, lean_object* v_x_2566_, lean_object* v_x_2567_){
_start:
{
uint8_t v___x_2568_; 
v___x_2568_ = l_instDecidableEqSum_decEq___redArg(v_inst_2564_, v_inst_2565_, v_x_2566_, v_x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSum___boxed(lean_object* v_00_u03b1_2569_, lean_object* v_00_u03b2_2570_, lean_object* v_inst_2571_, lean_object* v_inst_2572_, lean_object* v_x_2573_, lean_object* v_x_2574_){
_start:
{
uint8_t v_res_2575_; lean_object* v_r_2576_; 
v_res_2575_ = l_instDecidableEqSum(v_00_u03b1_2569_, v_00_u03b2_2570_, v_inst_2571_, v_inst_2572_, v_x_2573_, v_x_2574_);
v_r_2576_ = lean_box(v_res_2575_);
return v_r_2576_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedProd___redArg(lean_object* v_inst_2577_, lean_object* v_inst_2578_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v_inst_2577_);
lean_ctor_set(v___x_2579_, 1, v_inst_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedProd(lean_object* v_00_u03b1_2580_, lean_object* v_00_u03b2_2581_, lean_object* v_inst_2582_, lean_object* v_inst_2583_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v_inst_2582_);
lean_ctor_set(v___x_2584_, 1, v_inst_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedMProd___redArg(lean_object* v_inst_2585_, lean_object* v_inst_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v_inst_2585_);
lean_ctor_set(v___x_2587_, 1, v_inst_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedMProd(lean_object* v_00_u03b1_2588_, lean_object* v_00_u03b2_2589_, lean_object* v_inst_2590_, lean_object* v_inst_2591_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2592_, 0, v_inst_2590_);
lean_ctor_set(v___x_2592_, 1, v_inst_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedPProd___redArg(lean_object* v_inst_2593_, lean_object* v_inst_2594_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v_inst_2593_);
lean_ctor_set(v___x_2595_, 1, v_inst_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedPProd(lean_object* v_00_u03b1_2596_, lean_object* v_00_u03b2_2597_, lean_object* v_inst_2598_, lean_object* v_inst_2599_){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v_inst_2598_);
lean_ctor_set(v___x_2600_, 1, v_inst_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqProd___redArg(lean_object* v_h_2601_, lean_object* v_h_x27_2602_, lean_object* v_x_2603_, lean_object* v_x_2604_){
_start:
{
lean_object* v_fst_2605_; lean_object* v_snd_2606_; lean_object* v_fst_2607_; lean_object* v_snd_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v_fst_2605_ = lean_ctor_get(v_x_2603_, 0);
lean_inc(v_fst_2605_);
v_snd_2606_ = lean_ctor_get(v_x_2603_, 1);
lean_inc(v_snd_2606_);
lean_dec_ref(v_x_2603_);
v_fst_2607_ = lean_ctor_get(v_x_2604_, 0);
lean_inc(v_fst_2607_);
v_snd_2608_ = lean_ctor_get(v_x_2604_, 1);
lean_inc(v_snd_2608_);
lean_dec_ref(v_x_2604_);
v___x_2609_ = lean_apply_2(v_h_2601_, v_fst_2605_, v_fst_2607_);
v___x_2610_ = lean_unbox(v___x_2609_);
if (v___x_2610_ == 0)
{
uint8_t v___x_2611_; 
lean_dec(v_snd_2608_);
lean_dec(v_snd_2606_);
lean_dec_ref(v_h_x27_2602_);
v___x_2611_ = lean_unbox(v___x_2609_);
return v___x_2611_;
}
else
{
lean_object* v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = lean_apply_2(v_h_x27_2602_, v_snd_2606_, v_snd_2608_);
v___x_2613_ = lean_unbox(v___x_2612_);
return v___x_2613_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqProd___redArg___boxed(lean_object* v_h_2614_, lean_object* v_h_x27_2615_, lean_object* v_x_2616_, lean_object* v_x_2617_){
_start:
{
uint8_t v_res_2618_; lean_object* v_r_2619_; 
v_res_2618_ = l_instDecidableEqProd___redArg(v_h_2614_, v_h_x27_2615_, v_x_2616_, v_x_2617_);
v_r_2619_ = lean_box(v_res_2618_);
return v_r_2619_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqProd(lean_object* v_00_u03b1_2620_, lean_object* v_00_u03b2_2621_, lean_object* v_h_2622_, lean_object* v_h_x27_2623_, lean_object* v_x_2624_, lean_object* v_x_2625_){
_start:
{
uint8_t v___x_2626_; 
v___x_2626_ = l_instDecidableEqProd___redArg(v_h_2622_, v_h_x27_2623_, v_x_2624_, v_x_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqProd___boxed(lean_object* v_00_u03b1_2627_, lean_object* v_00_u03b2_2628_, lean_object* v_h_2629_, lean_object* v_h_x27_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_){
_start:
{
uint8_t v_res_2633_; lean_object* v_r_2634_; 
v_res_2633_ = l_instDecidableEqProd(v_00_u03b1_2627_, v_00_u03b2_2628_, v_h_2629_, v_h_x27_2630_, v_x_2631_, v_x_2632_);
v_r_2634_ = lean_box(v_res_2633_);
return v_r_2634_;
}
}
LEAN_EXPORT uint8_t l_instBEqProd___redArg___lam__0(lean_object* v_inst_2635_, lean_object* v_inst_2636_, lean_object* v_x_2637_, lean_object* v_x_2638_){
_start:
{
lean_object* v_fst_2639_; lean_object* v_snd_2640_; lean_object* v_fst_2641_; lean_object* v_snd_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; 
v_fst_2639_ = lean_ctor_get(v_x_2637_, 0);
lean_inc(v_fst_2639_);
v_snd_2640_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_snd_2640_);
lean_dec_ref(v_x_2637_);
v_fst_2641_ = lean_ctor_get(v_x_2638_, 0);
lean_inc(v_fst_2641_);
v_snd_2642_ = lean_ctor_get(v_x_2638_, 1);
lean_inc(v_snd_2642_);
lean_dec_ref(v_x_2638_);
v___x_2643_ = lean_apply_2(v_inst_2635_, v_fst_2639_, v_fst_2641_);
v___x_2644_ = lean_unbox(v___x_2643_);
if (v___x_2644_ == 0)
{
uint8_t v___x_2645_; 
lean_dec(v_snd_2642_);
lean_dec(v_snd_2640_);
lean_dec_ref(v_inst_2636_);
v___x_2645_ = lean_unbox(v___x_2643_);
return v___x_2645_;
}
else
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = lean_apply_2(v_inst_2636_, v_snd_2640_, v_snd_2642_);
v___x_2647_ = lean_unbox(v___x_2646_);
return v___x_2647_;
}
}
}
LEAN_EXPORT lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object* v_inst_2648_, lean_object* v_inst_2649_, lean_object* v_x_2650_, lean_object* v_x_2651_){
_start:
{
uint8_t v_res_2652_; lean_object* v_r_2653_; 
v_res_2652_ = l_instBEqProd___redArg___lam__0(v_inst_2648_, v_inst_2649_, v_x_2650_, v_x_2651_);
v_r_2653_ = lean_box(v_res_2652_);
return v_r_2653_;
}
}
LEAN_EXPORT lean_object* l_instBEqProd___redArg(lean_object* v_inst_2654_, lean_object* v_inst_2655_){
_start:
{
lean_object* v___f_2656_; 
v___f_2656_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2656_, 0, v_inst_2654_);
lean_closure_set(v___f_2656_, 1, v_inst_2655_);
return v___f_2656_;
}
}
LEAN_EXPORT lean_object* l_instBEqProd(lean_object* v_00_u03b1_2657_, lean_object* v_00_u03b2_2658_, lean_object* v_inst_2659_, lean_object* v_inst_2660_){
_start:
{
lean_object* v___f_2661_; 
v___f_2661_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2661_, 0, v_inst_2659_);
lean_closure_set(v___f_2661_, 1, v_inst_2660_);
return v___f_2661_;
}
}
LEAN_EXPORT uint8_t l_Prod_lexLtDec___redArg(lean_object* v_inst_2662_, lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_x_2665_, lean_object* v_x_2666_){
_start:
{
lean_object* v_fst_2667_; lean_object* v_snd_2668_; lean_object* v_fst_2669_; lean_object* v_snd_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; 
v_fst_2667_ = lean_ctor_get(v_x_2665_, 0);
lean_inc_n(v_fst_2667_, 2);
v_snd_2668_ = lean_ctor_get(v_x_2665_, 1);
lean_inc(v_snd_2668_);
lean_dec_ref(v_x_2665_);
v_fst_2669_ = lean_ctor_get(v_x_2666_, 0);
lean_inc_n(v_fst_2669_, 2);
v_snd_2670_ = lean_ctor_get(v_x_2666_, 1);
lean_inc(v_snd_2670_);
lean_dec_ref(v_x_2666_);
v___x_2671_ = lean_apply_2(v_inst_2663_, v_fst_2667_, v_fst_2669_);
v___x_2672_ = lean_unbox(v___x_2671_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2673_ = lean_apply_2(v_inst_2662_, v_fst_2667_, v_fst_2669_);
v___x_2674_ = lean_unbox(v___x_2673_);
if (v___x_2674_ == 0)
{
uint8_t v___x_2675_; 
lean_dec(v_snd_2670_);
lean_dec(v_snd_2668_);
lean_dec_ref(v_inst_2664_);
v___x_2675_ = lean_unbox(v___x_2673_);
return v___x_2675_;
}
else
{
lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = lean_apply_2(v_inst_2664_, v_snd_2668_, v_snd_2670_);
v___x_2677_ = lean_unbox(v___x_2676_);
return v___x_2677_;
}
}
else
{
uint8_t v___x_2678_; 
lean_dec(v_snd_2670_);
lean_dec(v_fst_2669_);
lean_dec(v_snd_2668_);
lean_dec(v_fst_2667_);
lean_dec_ref(v_inst_2664_);
lean_dec_ref(v_inst_2662_);
v___x_2678_ = lean_unbox(v___x_2671_);
return v___x_2678_;
}
}
}
LEAN_EXPORT lean_object* l_Prod_lexLtDec___redArg___boxed(lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_x_2682_, lean_object* v_x_2683_){
_start:
{
uint8_t v_res_2684_; lean_object* v_r_2685_; 
v_res_2684_ = l_Prod_lexLtDec___redArg(v_inst_2679_, v_inst_2680_, v_inst_2681_, v_x_2682_, v_x_2683_);
v_r_2685_ = lean_box(v_res_2684_);
return v_r_2685_;
}
}
LEAN_EXPORT uint8_t l_Prod_lexLtDec(lean_object* v_00_u03b1_2686_, lean_object* v_00_u03b2_2687_, lean_object* v_inst_2688_, lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_x_2693_, lean_object* v_x_2694_){
_start:
{
uint8_t v___x_2695_; 
v___x_2695_ = l_Prod_lexLtDec___redArg(v_inst_2690_, v_inst_2691_, v_inst_2692_, v_x_2693_, v_x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Prod_lexLtDec___boxed(lean_object* v_00_u03b1_2696_, lean_object* v_00_u03b2_2697_, lean_object* v_inst_2698_, lean_object* v_inst_2699_, lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_x_2703_, lean_object* v_x_2704_){
_start:
{
uint8_t v_res_2705_; lean_object* v_r_2706_; 
v_res_2705_ = l_Prod_lexLtDec(v_00_u03b1_2696_, v_00_u03b2_2697_, v_inst_2698_, v_inst_2699_, v_inst_2700_, v_inst_2701_, v_inst_2702_, v_x_2703_, v_x_2704_);
v_r_2706_ = lean_box(v_res_2705_);
return v_r_2706_;
}
}
LEAN_EXPORT lean_object* l_Prod_map___redArg(lean_object* v_f_2707_, lean_object* v_g_2708_, lean_object* v_x_2709_){
_start:
{
lean_object* v_fst_2710_; lean_object* v_snd_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2720_; 
v_fst_2710_ = lean_ctor_get(v_x_2709_, 0);
v_snd_2711_ = lean_ctor_get(v_x_2709_, 1);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_x_2709_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2713_ = v_x_2709_;
v_isShared_2714_ = v_isSharedCheck_2720_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_snd_2711_);
lean_inc(v_fst_2710_);
lean_dec(v_x_2709_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2720_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2715_ = lean_apply_1(v_f_2707_, v_fst_2710_);
v___x_2716_ = lean_apply_1(v_g_2708_, v_snd_2711_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 1, v___x_2716_);
lean_ctor_set(v___x_2713_, 0, v___x_2715_);
v___x_2718_ = v___x_2713_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_map(lean_object* v_00_u03b1_u2081_2721_, lean_object* v_00_u03b1_u2082_2722_, lean_object* v_00_u03b2_u2081_2723_, lean_object* v_00_u03b2_u2082_2724_, lean_object* v_f_2725_, lean_object* v_g_2726_, lean_object* v_x_2727_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Prod_map___redArg(v_f_2725_, v_g_2726_, v_x_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSigma___redArg(lean_object* v_h_u2081_2729_, lean_object* v_h_u2082_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_){
_start:
{
lean_object* v_fst_2733_; lean_object* v_snd_2734_; lean_object* v_fst_2735_; lean_object* v_snd_2736_; lean_object* v_decide_2737_; uint8_t v___x_2738_; 
v_fst_2733_ = lean_ctor_get(v_x_2731_, 0);
lean_inc_n(v_fst_2733_, 2);
v_snd_2734_ = lean_ctor_get(v_x_2731_, 1);
lean_inc(v_snd_2734_);
lean_dec_ref(v_x_2731_);
v_fst_2735_ = lean_ctor_get(v_x_2732_, 0);
lean_inc(v_fst_2735_);
v_snd_2736_ = lean_ctor_get(v_x_2732_, 1);
lean_inc(v_snd_2736_);
lean_dec_ref(v_x_2732_);
v_decide_2737_ = lean_apply_2(v_h_u2081_2729_, v_fst_2733_, v_fst_2735_);
v___x_2738_ = lean_unbox(v_decide_2737_);
if (v___x_2738_ == 0)
{
uint8_t v___x_2739_; 
lean_dec(v_snd_2736_);
lean_dec(v_snd_2734_);
lean_dec(v_fst_2733_);
lean_dec_ref(v_h_u2082_2730_);
v___x_2739_ = lean_unbox(v_decide_2737_);
return v___x_2739_;
}
else
{
lean_object* v_decide_2740_; uint8_t v___x_2741_; 
v_decide_2740_ = lean_apply_3(v_h_u2082_2730_, v_fst_2733_, v_snd_2734_, v_snd_2736_);
v___x_2741_ = lean_unbox(v_decide_2740_);
return v___x_2741_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSigma___redArg___boxed(lean_object* v_h_u2081_2742_, lean_object* v_h_u2082_2743_, lean_object* v_x_2744_, lean_object* v_x_2745_){
_start:
{
uint8_t v_res_2746_; lean_object* v_r_2747_; 
v_res_2746_ = l_instDecidableEqSigma___redArg(v_h_u2081_2742_, v_h_u2082_2743_, v_x_2744_, v_x_2745_);
v_r_2747_ = lean_box(v_res_2746_);
return v_r_2747_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqSigma(lean_object* v_00_u03b1_2748_, lean_object* v_00_u03b2_2749_, lean_object* v_h_u2081_2750_, lean_object* v_h_u2082_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_){
_start:
{
uint8_t v___x_2754_; 
v___x_2754_ = l_instDecidableEqSigma___redArg(v_h_u2081_2750_, v_h_u2082_2751_, v_x_2752_, v_x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqSigma___boxed(lean_object* v_00_u03b1_2755_, lean_object* v_00_u03b2_2756_, lean_object* v_h_u2081_2757_, lean_object* v_h_u2082_2758_, lean_object* v_x_2759_, lean_object* v_x_2760_){
_start:
{
uint8_t v_res_2761_; lean_object* v_r_2762_; 
v_res_2761_ = l_instDecidableEqSigma(v_00_u03b1_2755_, v_00_u03b2_2756_, v_h_u2081_2757_, v_h_u2082_2758_, v_x_2759_, v_x_2760_);
v_r_2762_ = lean_box(v_res_2761_);
return v_r_2762_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPSigma___redArg(lean_object* v_h_u2081_2763_, lean_object* v_h_u2082_2764_, lean_object* v_x_2765_, lean_object* v_x_2766_){
_start:
{
lean_object* v_fst_2767_; lean_object* v_snd_2768_; lean_object* v_fst_2769_; lean_object* v_snd_2770_; lean_object* v_decide_2771_; uint8_t v___x_2772_; 
v_fst_2767_ = lean_ctor_get(v_x_2765_, 0);
lean_inc_n(v_fst_2767_, 2);
v_snd_2768_ = lean_ctor_get(v_x_2765_, 1);
lean_inc(v_snd_2768_);
lean_dec_ref(v_x_2765_);
v_fst_2769_ = lean_ctor_get(v_x_2766_, 0);
lean_inc(v_fst_2769_);
v_snd_2770_ = lean_ctor_get(v_x_2766_, 1);
lean_inc(v_snd_2770_);
lean_dec_ref(v_x_2766_);
v_decide_2771_ = lean_apply_2(v_h_u2081_2763_, v_fst_2767_, v_fst_2769_);
v___x_2772_ = lean_unbox(v_decide_2771_);
if (v___x_2772_ == 0)
{
uint8_t v___x_2773_; 
lean_dec(v_snd_2770_);
lean_dec(v_snd_2768_);
lean_dec(v_fst_2767_);
lean_dec_ref(v_h_u2082_2764_);
v___x_2773_ = lean_unbox(v_decide_2771_);
return v___x_2773_;
}
else
{
lean_object* v_decide_2774_; uint8_t v___x_2775_; 
v_decide_2774_ = lean_apply_3(v_h_u2082_2764_, v_fst_2767_, v_snd_2768_, v_snd_2770_);
v___x_2775_ = lean_unbox(v_decide_2774_);
return v___x_2775_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPSigma___redArg___boxed(lean_object* v_h_u2081_2776_, lean_object* v_h_u2082_2777_, lean_object* v_x_2778_, lean_object* v_x_2779_){
_start:
{
uint8_t v_res_2780_; lean_object* v_r_2781_; 
v_res_2780_ = l_instDecidableEqPSigma___redArg(v_h_u2081_2776_, v_h_u2082_2777_, v_x_2778_, v_x_2779_);
v_r_2781_ = lean_box(v_res_2780_);
return v_r_2781_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPSigma(lean_object* v_00_u03b1_2782_, lean_object* v_00_u03b2_2783_, lean_object* v_h_u2081_2784_, lean_object* v_h_u2082_2785_, lean_object* v_x_2786_, lean_object* v_x_2787_){
_start:
{
uint8_t v___x_2788_; 
v___x_2788_ = l_instDecidableEqPSigma___redArg(v_h_u2081_2784_, v_h_u2082_2785_, v_x_2786_, v_x_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPSigma___boxed(lean_object* v_00_u03b1_2789_, lean_object* v_00_u03b2_2790_, lean_object* v_h_u2081_2791_, lean_object* v_h_u2082_2792_, lean_object* v_x_2793_, lean_object* v_x_2794_){
_start:
{
uint8_t v_res_2795_; lean_object* v_r_2796_; 
v_res_2795_ = l_instDecidableEqPSigma(v_00_u03b1_2789_, v_00_u03b2_2790_, v_h_u2081_2791_, v_h_u2082_2792_, v_x_2793_, v_x_2794_);
v_r_2796_ = lean_box(v_res_2795_);
return v_r_2796_;
}
}
static lean_object* _init_l_instInhabitedPUnit(void){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = lean_box(0);
return v___x_2797_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPUnit___redArg(){
_start:
{
uint8_t v___x_2799_; 
v___x_2799_ = 1;
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPUnit___redArg___boxed(lean_object* v___dummy_2800_){
_start:
{
uint8_t v_res_2801_; lean_object* v_r_2802_; 
v_res_2801_ = l_instDecidableEqPUnit___redArg();
v_r_2802_ = lean_box(v_res_2801_);
return v_r_2802_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqPUnit(lean_object* v_a_2803_, lean_object* v_b_2804_){
_start:
{
uint8_t v___x_2805_; 
v___x_2805_ = 1;
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqPUnit___boxed(lean_object* v_a_2806_, lean_object* v_b_2807_){
_start:
{
uint8_t v_res_2808_; lean_object* v_r_2809_; 
v_res_2808_ = l_instDecidableEqPUnit(v_a_2806_, v_b_2807_);
v_r_2809_ = lean_box(v_res_2808_);
return v_r_2809_;
}
}
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid___redArg(){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_box(0);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid___redArg___boxed(lean_object* v___dummy_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_instHasEquivOfSetoid___redArg();
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_instHasEquivOfSetoid(lean_object* v_00_u03b1_2814_, lean_object* v_inst_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = lean_box(0);
return v___x_2816_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfIff___redArg(uint8_t v_d_2817_){
_start:
{
return v_d_2817_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___redArg___boxed(lean_object* v_d_2818_){
_start:
{
uint8_t v_d_boxed_2819_; uint8_t v_res_2820_; lean_object* v_r_2821_; 
v_d_boxed_2819_ = lean_unbox(v_d_2818_);
v_res_2820_ = l_instDecidableEqOfIff___redArg(v_d_boxed_2819_);
v_r_2821_ = lean_box(v_res_2820_);
return v_r_2821_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqOfIff(lean_object* v_p_2822_, lean_object* v_q_2823_, uint8_t v_d_2824_){
_start:
{
return v_d_2824_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqOfIff___boxed(lean_object* v_p_2825_, lean_object* v_q_2826_, lean_object* v_d_2827_){
_start:
{
uint8_t v_d_boxed_2828_; uint8_t v_res_2829_; lean_object* v_r_2830_; 
v_d_boxed_2828_ = lean_unbox(v_d_2827_);
v_res_2829_ = l_instDecidableEqOfIff(v_p_2825_, v_q_2826_, v_d_boxed_2828_);
v_r_2830_ = lean_box(v_res_2829_);
return v_r_2830_;
}
}
LEAN_EXPORT lean_object* l_Not_elim___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Not_elim___redArg___boxed(lean_object* v___dummy_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Not_elim___redArg();
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Not_elim(lean_object* v_a_2834_, lean_object* v_00_u03b1_2835_, lean_object* v_H1_2836_, lean_object* v_H2_2837_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_And_elim___redArg(lean_object* v_f_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_apply_2(v_f_2838_, lean_box(0), lean_box(0));
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_And_elim(lean_object* v_a_2840_, lean_object* v_b_2841_, lean_object* v_00_u03b1_2842_, lean_object* v_f_2843_, lean_object* v_h_2844_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_apply_2(v_f_2843_, lean_box(0), lean_box(0));
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Iff_elim___redArg(lean_object* v_f_2846_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = lean_apply_2(v_f_2846_, lean_box(0), lean_box(0));
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Iff_elim(lean_object* v_a_2848_, lean_object* v_b_2849_, lean_object* v_00_u03b1_2850_, lean_object* v_f_2851_, lean_object* v_h_2852_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_apply_2(v_f_2851_, lean_box(0), lean_box(0));
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Quot_rec___redArg(lean_object* v_f_2854_, lean_object* v_q_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = lean_apply_1(v_f_2854_, v_q_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Quot_rec(lean_object* v_00_u03b1_2857_, lean_object* v_r_2858_, lean_object* v_motive_2859_, lean_object* v_f_2860_, lean_object* v_h_2861_, lean_object* v_q_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = lean_apply_1(v_f_2860_, v_q_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOn___redArg(lean_object* v_q_2864_, lean_object* v_f_2865_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = lean_apply_1(v_f_2865_, v_q_2864_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOn(lean_object* v_00_u03b1_2867_, lean_object* v_r_2868_, lean_object* v_motive_2869_, lean_object* v_q_2870_, lean_object* v_f_2871_, lean_object* v_h_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = lean_apply_1(v_f_2871_, v_q_2870_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOnSubsingleton___redArg(lean_object* v_q_2874_, lean_object* v_f_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = lean_apply_1(v_f_2875_, v_q_2874_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Quot_recOnSubsingleton(lean_object* v_00_u03b1_2877_, lean_object* v_r_2878_, lean_object* v_motive_2879_, lean_object* v_h_2880_, lean_object* v_q_2881_, lean_object* v_f_2882_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_apply_1(v_f_2882_, v_q_2881_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Quot_hrecOn___redArg(lean_object* v_q_2884_, lean_object* v_f_2885_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = lean_apply_1(v_f_2885_, v_q_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Quot_hrecOn(lean_object* v_00_u03b1_2887_, lean_object* v_r_2888_, lean_object* v_motive_2889_, lean_object* v_q_2890_, lean_object* v_f_2891_, lean_object* v_c_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = lean_apply_1(v_f_2891_, v_q_2890_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___redArg(lean_object* v_a_2894_){
_start:
{
lean_inc(v_a_2894_);
return v_a_2894_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___redArg___boxed(lean_object* v_a_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Quotient_mk___redArg(v_a_2895_);
lean_dec(v_a_2895_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk(lean_object* v_00_u03b1_2897_, lean_object* v_s_2898_, lean_object* v_a_2899_){
_start:
{
lean_inc(v_a_2899_);
return v_a_2899_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk___boxed(lean_object* v_00_u03b1_2900_, lean_object* v_s_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Quotient_mk(v_00_u03b1_2900_, v_s_2901_, v_a_2902_);
lean_dec(v_a_2902_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___redArg(lean_object* v_a_2904_){
_start:
{
lean_inc(v_a_2904_);
return v_a_2904_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___redArg___boxed(lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Quotient_mk_x27___redArg(v_a_2905_);
lean_dec(v_a_2905_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27(lean_object* v_00_u03b1_2907_, lean_object* v_s_2908_, lean_object* v_a_2909_){
_start:
{
lean_inc(v_a_2909_);
return v_a_2909_;
}
}
LEAN_EXPORT lean_object* l_Quotient_mk_x27___boxed(lean_object* v_00_u03b1_2910_, lean_object* v_s_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Quotient_mk_x27(v_00_u03b1_2910_, v_s_2911_, v_a_2912_);
lean_dec(v_a_2912_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift___redArg(lean_object* v_f_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_apply_1(v_f_2914_, v_a_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift(lean_object* v_00_u03b1_2917_, lean_object* v_00_u03b2_2918_, lean_object* v_s_2919_, lean_object* v_f_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_apply_1(v_f_2920_, v_a_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn___redArg(lean_object* v_q_2924_, lean_object* v_f_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_apply_1(v_f_2925_, v_q_2924_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn(lean_object* v_00_u03b1_2927_, lean_object* v_00_u03b2_2928_, lean_object* v_s_2929_, lean_object* v_q_2930_, lean_object* v_f_2931_, lean_object* v_c_2932_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_apply_1(v_f_2931_, v_q_2930_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Quotient_rec___redArg(lean_object* v_f_2934_, lean_object* v_q_2935_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = lean_apply_1(v_f_2934_, v_q_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Quotient_rec(lean_object* v_00_u03b1_2937_, lean_object* v_s_2938_, lean_object* v_motive_2939_, lean_object* v_f_2940_, lean_object* v_h_2941_, lean_object* v_q_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_apply_1(v_f_2940_, v_q_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOn___redArg(lean_object* v_q_2944_, lean_object* v_f_2945_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_apply_1(v_f_2945_, v_q_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOn(lean_object* v_00_u03b1_2947_, lean_object* v_s_2948_, lean_object* v_motive_2949_, lean_object* v_q_2950_, lean_object* v_f_2951_, lean_object* v_h_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = lean_apply_1(v_f_2951_, v_q_2950_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton___redArg(lean_object* v_q_2954_, lean_object* v_f_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = lean_apply_1(v_f_2955_, v_q_2954_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton(lean_object* v_00_u03b1_2957_, lean_object* v_s_2958_, lean_object* v_motive_2959_, lean_object* v_h_2960_, lean_object* v_q_2961_, lean_object* v_f_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_apply_1(v_f_2962_, v_q_2961_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Quotient_hrecOn___redArg(lean_object* v_q_2964_, lean_object* v_f_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_apply_1(v_f_2965_, v_q_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Quotient_hrecOn(lean_object* v_00_u03b1_2967_, lean_object* v_s_2968_, lean_object* v_motive_2969_, lean_object* v_q_2970_, lean_object* v_f_2971_, lean_object* v_c_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_apply_1(v_f_2971_, v_q_2970_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift_u2082___redArg(lean_object* v_f_2974_, lean_object* v_q_u2081_2975_, lean_object* v_q_u2082_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_apply_2(v_f_2974_, v_q_u2081_2975_, v_q_u2082_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Quotient_lift_u2082(lean_object* v_00_u03b1_2978_, lean_object* v_00_u03b2_2979_, lean_object* v_00_u03c6_2980_, lean_object* v_s_u2081_2981_, lean_object* v_s_u2082_2982_, lean_object* v_f_2983_, lean_object* v_c_2984_, lean_object* v_q_u2081_2985_, lean_object* v_q_u2082_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_apply_2(v_f_2983_, v_q_u2081_2985_, v_q_u2082_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn_u2082___redArg(lean_object* v_q_u2081_2988_, lean_object* v_q_u2082_2989_, lean_object* v_f_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_apply_2(v_f_2990_, v_q_u2081_2988_, v_q_u2082_2989_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Quotient_liftOn_u2082(lean_object* v_00_u03b1_2992_, lean_object* v_00_u03b2_2993_, lean_object* v_00_u03c6_2994_, lean_object* v_s_u2081_2995_, lean_object* v_s_u2082_2996_, lean_object* v_q_u2081_2997_, lean_object* v_q_u2082_2998_, lean_object* v_f_2999_, lean_object* v_c_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_apply_2(v_f_2999_, v_q_u2081_2997_, v_q_u2082_2998_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton_u2082___redArg(lean_object* v_q_u2081_3002_, lean_object* v_q_u2082_3003_, lean_object* v_g_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_apply_2(v_g_3004_, v_q_u2081_3002_, v_q_u2082_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Quotient_recOnSubsingleton_u2082(lean_object* v_00_u03b1_3006_, lean_object* v_00_u03b2_3007_, lean_object* v_s_u2081_3008_, lean_object* v_s_u2082_3009_, lean_object* v_motive_3010_, lean_object* v_s_3011_, lean_object* v_q_u2081_3012_, lean_object* v_q_u2082_3013_, lean_object* v_g_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_apply_2(v_g_3014_, v_q_u2081_3012_, v_q_u2082_3013_);
return v___x_3015_;
}
}
LEAN_EXPORT uint8_t l_Quotient_decidableEq___redArg(lean_object* v_d_3016_, lean_object* v_q_u2081_3017_, lean_object* v_q_u2082_3018_){
_start:
{
lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3019_ = lean_apply_2(v_d_3016_, v_q_u2081_3017_, v_q_u2082_3018_);
v___x_3020_ = lean_unbox(v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Quotient_decidableEq___redArg___boxed(lean_object* v_d_3021_, lean_object* v_q_u2081_3022_, lean_object* v_q_u2082_3023_){
_start:
{
uint8_t v_res_3024_; lean_object* v_r_3025_; 
v_res_3024_ = l_Quotient_decidableEq___redArg(v_d_3021_, v_q_u2081_3022_, v_q_u2082_3023_);
v_r_3025_ = lean_box(v_res_3024_);
return v_r_3025_;
}
}
LEAN_EXPORT uint8_t l_Quotient_decidableEq(lean_object* v_00_u03b1_3026_, lean_object* v_s_3027_, lean_object* v_d_3028_, lean_object* v_q_u2081_3029_, lean_object* v_q_u2082_3030_){
_start:
{
lean_object* v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = lean_apply_2(v_d_3028_, v_q_u2081_3029_, v_q_u2082_3030_);
v___x_3032_ = lean_unbox(v___x_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Quotient_decidableEq___boxed(lean_object* v_00_u03b1_3033_, lean_object* v_s_3034_, lean_object* v_d_3035_, lean_object* v_q_u2081_3036_, lean_object* v_q_u2082_3037_){
_start:
{
uint8_t v_res_3038_; lean_object* v_r_3039_; 
v_res_3038_ = l_Quotient_decidableEq(v_00_u03b1_3033_, v_s_3034_, v_d_3035_, v_q_u2081_3036_, v_q_u2082_3037_);
v_r_3039_ = lean_box(v_res_3038_);
return v_r_3039_;
}
}
LEAN_EXPORT lean_object* l_Quot_pliftOn___redArg(lean_object* v_q_3040_, lean_object* v_f_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_apply_2(v_f_3041_, v_q_3040_, lean_box(0));
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Quot_pliftOn(lean_object* v_00_u03b2_3043_, lean_object* v_00_u03b1_3044_, lean_object* v_r_3045_, lean_object* v_q_3046_, lean_object* v_f_3047_, lean_object* v_h_3048_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_apply_2(v_f_3047_, v_q_3046_, lean_box(0));
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Quotient_pliftOn___redArg(lean_object* v_q_3050_, lean_object* v_f_3051_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_apply_2(v_f_3051_, v_q_3050_, lean_box(0));
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Quotient_pliftOn(lean_object* v_00_u03b2_3053_, lean_object* v_00_u03b1_3054_, lean_object* v_s_3055_, lean_object* v_q_3056_, lean_object* v_f_3057_, lean_object* v_h_3058_){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_apply_2(v_f_3057_, v_q_3056_, lean_box(0));
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Setoid_trivial___redArg(){
_start:
{
lean_object* v___x_3061_; 
v___x_3061_ = lean_box(0);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Setoid_trivial___redArg___boxed(lean_object* v___dummy_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Setoid_trivial___redArg();
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Setoid_trivial(lean_object* v_00_u03b1_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_box(0);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___redArg(lean_object* v_x_3066_){
_start:
{
lean_inc(v_x_3066_);
return v_x_3066_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___redArg___boxed(lean_object* v_x_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Squash_mk___redArg(v_x_3067_);
lean_dec(v_x_3067_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk(lean_object* v_00_u03b1_3069_, lean_object* v_x_3070_){
_start:
{
lean_inc(v_x_3070_);
return v_x_3070_;
}
}
LEAN_EXPORT lean_object* l_Squash_mk___boxed(lean_object* v_00_u03b1_3071_, lean_object* v_x_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Squash_mk(v_00_u03b1_3071_, v_x_3072_);
lean_dec(v_x_3072_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Squash_lift___redArg(lean_object* v_s_3074_, lean_object* v_f_3075_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_apply_1(v_f_3075_, v_s_3074_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Squash_lift(lean_object* v_00_u03b1_3077_, lean_object* v_00_u03b2_3078_, lean_object* v_inst_3079_, lean_object* v_s_3080_, lean_object* v_f_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = lean_apply_1(v_f_3081_, v_s_3080_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___redArg(lean_object* v_x_3083_){
_start:
{
lean_inc(v_x_3083_);
return v_x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___redArg___boxed(lean_object* v_x_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_opaqueId___redArg(v_x_3084_);
lean_dec(v_x_3084_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId(lean_object* v_00_u03b1_3086_, lean_object* v_x_3087_){
_start:
{
lean_inc(v_x_3087_);
return v_x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_opaqueId___boxed(lean_object* v_00_u03b1_3088_, lean_object* v_x_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_opaqueId(v_00_u03b1_3088_, v_x_3089_);
lean_dec(v_x_3089_);
return v_res_3090_;
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
