// Lean compiler output
// Module: Lake.Config.Glob
// Imports: public import Lean.Util.Path import Init.Data.ToString.Name import Lean.Data.Name
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_forEachModuleInDir___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_singleton(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_one_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_one_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_submodules_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_submodules_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_andSubmodules_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_andSubmodules_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_instInhabitedGlob_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedGlob_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedGlob_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedGlob_default = (const lean_object*)&l_Lake_instInhabitedGlob_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedGlob = (const lean_object*)&l_Lake_instInhabitedGlob_default___closed__0_value;
static const lean_string_object l_Lake_instReprGlob_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lake.Glob.one"};
static const lean_object* l_Lake_instReprGlob_repr___closed__0 = (const lean_object*)&l_Lake_instReprGlob_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprGlob_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprGlob_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprGlob_repr___closed__1 = (const lean_object*)&l_Lake_instReprGlob_repr___closed__1_value;
static const lean_ctor_object l_Lake_instReprGlob_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprGlob_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprGlob_repr___closed__2 = (const lean_object*)&l_Lake_instReprGlob_repr___closed__2_value;
static lean_once_cell_t l_Lake_instReprGlob_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprGlob_repr___closed__3;
static lean_once_cell_t l_Lake_instReprGlob_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprGlob_repr___closed__4;
static const lean_string_object l_Lake_instReprGlob_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.Glob.submodules"};
static const lean_object* l_Lake_instReprGlob_repr___closed__5 = (const lean_object*)&l_Lake_instReprGlob_repr___closed__5_value;
static const lean_ctor_object l_Lake_instReprGlob_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprGlob_repr___closed__5_value)}};
static const lean_object* l_Lake_instReprGlob_repr___closed__6 = (const lean_object*)&l_Lake_instReprGlob_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprGlob_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprGlob_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprGlob_repr___closed__7 = (const lean_object*)&l_Lake_instReprGlob_repr___closed__7_value;
static const lean_string_object l_Lake_instReprGlob_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lake.Glob.andSubmodules"};
static const lean_object* l_Lake_instReprGlob_repr___closed__8 = (const lean_object*)&l_Lake_instReprGlob_repr___closed__8_value;
static const lean_ctor_object l_Lake_instReprGlob_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprGlob_repr___closed__8_value)}};
static const lean_object* l_Lake_instReprGlob_repr___closed__9 = (const lean_object*)&l_Lake_instReprGlob_repr___closed__9_value;
static const lean_ctor_object l_Lake_instReprGlob_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprGlob_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprGlob_repr___closed__10 = (const lean_object*)&l_Lake_instReprGlob_repr___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_instReprGlob_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprGlob_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprGlob___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprGlob_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprGlob___closed__0 = (const lean_object*)&l_Lake_instReprGlob___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprGlob = (const lean_object*)&l_Lake_instReprGlob___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqGlob_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqGlob_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqGlob(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqGlob___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeNameGlob___lam__0(lean_object*);
static const lean_closure_object l_Lake_instCoeNameGlob___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeNameGlob___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeNameGlob___closed__0 = (const lean_object*)&l_Lake_instCoeNameGlob___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeNameGlob = (const lean_object*)&l_Lake_instCoeNameGlob___closed__0_value;
static const lean_closure_object l_Lake_instCoeGlobArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_singleton, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_instCoeGlobArray___closed__0 = (const lean_object*)&l_Lake_instCoeGlobArray___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeGlobArray = (const lean_object*)&l_Lake_instCoeGlobArray___closed__0_value;
static const lean_string_object l_Lake_term_____x2e_x2a___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_term_____x2e_x2a___closed__0 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__0_value;
static const lean_string_object l_Lake_term_____x2e_x2a___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term__.*"};
static const lean_object* l_Lake_term_____x2e_x2a___closed__1 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__1_value;
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_term_____x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_term_____x2e_x2a___closed__2_value_aux_0),((lean_object*)&l_Lake_term_____x2e_x2a___closed__1_value),LEAN_SCALAR_PTR_LITERAL(61, 124, 105, 77, 27, 110, 223, 140)}};
static const lean_object* l_Lake_term_____x2e_x2a___closed__2 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__2_value;
static const lean_string_object l_Lake_term_____x2e_x2a___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lake_term_____x2e_x2a___closed__3 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__3_value;
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_term_____x2e_x2a___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lake_term_____x2e_x2a___closed__4 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__4_value;
static const lean_string_object l_Lake_term_____x2e_x2a___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lake_term_____x2e_x2a___closed__5 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__5_value;
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_term_____x2e_x2a___closed__5_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lake_term_____x2e_x2a___closed__6 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__6_value;
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_term_____x2e_x2a___closed__6_value)}};
static const lean_object* l_Lake_term_____x2e_x2a___closed__7 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__7_value;
static const lean_string_object l_Lake_term_____x2e_x2a___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lake_term_____x2e_x2a___closed__8 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__8_value;
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_term_____x2e_x2a___closed__8_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lake_term_____x2e_x2a___closed__9 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__9_value;
static const lean_string_object l_Lake_term_____x2e_x2a___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noWs"};
static const lean_object* l_Lake_term_____x2e_x2a___closed__10 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__10_value;
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_term_____x2e_x2a___closed__10_value),LEAN_SCALAR_PTR_LITERAL(92, 29, 204, 148, 167, 109, 242, 21)}};
static const lean_object* l_Lake_term_____x2e_x2a___closed__11 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__11_value;
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_term_____x2e_x2a___closed__11_value)}};
static const lean_object* l_Lake_term_____x2e_x2a___closed__12 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__12_value;
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_term_____x2e_x2a___closed__9_value),((lean_object*)&l_Lake_term_____x2e_x2a___closed__12_value)}};
static const lean_object* l_Lake_term_____x2e_x2a___closed__13 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__13_value;
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_term_____x2e_x2a___closed__4_value),((lean_object*)&l_Lake_term_____x2e_x2a___closed__7_value),((lean_object*)&l_Lake_term_____x2e_x2a___closed__13_value)}};
static const lean_object* l_Lake_term_____x2e_x2a___closed__14 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__14_value;
static const lean_string_object l_Lake_term_____x2e_x2a___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".*"};
static const lean_object* l_Lake_term_____x2e_x2a___closed__15 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__15_value;
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_term_____x2e_x2a___closed__15_value)}};
static const lean_object* l_Lake_term_____x2e_x2a___closed__16 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__16_value;
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_term_____x2e_x2a___closed__4_value),((lean_object*)&l_Lake_term_____x2e_x2a___closed__14_value),((lean_object*)&l_Lake_term_____x2e_x2a___closed__16_value)}};
static const lean_object* l_Lake_term_____x2e_x2a___closed__17 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__17_value;
static const lean_ctor_object l_Lake_term_____x2e_x2a___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_term_____x2e_x2a___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lake_term_____x2e_x2a___closed__17_value)}};
static const lean_object* l_Lake_term_____x2e_x2a___closed__18 = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__18_value;
LEAN_EXPORT const lean_object* l_Lake_term_____x2e_x2a = (const lean_object*)&l_Lake_term_____x2e_x2a___closed__18_value;
static const lean_string_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value;
static const lean_string_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value;
static const lean_string_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value;
static const lean_string_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4_value;
static const lean_string_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Glob.andSubmodules"};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5_value;
static lean_once_cell_t l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6;
static const lean_string_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Glob"};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value;
static const lean_string_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "andSubmodules"};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(26, 132, 67, 250, 48, 109, 63, 126)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(222, 145, 41, 104, 49, 15, 85, 40)}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_term_____x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(222, 149, 144, 131, 37, 196, 123, 168)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(202, 0, 72, 87, 26, 211, 128, 20)}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__10_value)}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__11_value),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__13_value)}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14_value;
static const lean_string_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16_value;
static const lean_string_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value_aux_2),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_term_____x2e_x2b___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term__.+"};
static const lean_object* l_Lake_term_____x2e_x2b___closed__0 = (const lean_object*)&l_Lake_term_____x2e_x2b___closed__0_value;
static const lean_ctor_object l_Lake_term_____x2e_x2b___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_term_____x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_term_____x2e_x2b___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_term_____x2e_x2b___closed__1_value_aux_0),((lean_object*)&l_Lake_term_____x2e_x2b___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 74, 46, 183, 128, 87, 172, 156)}};
static const lean_object* l_Lake_term_____x2e_x2b___closed__1 = (const lean_object*)&l_Lake_term_____x2e_x2b___closed__1_value;
static const lean_string_object l_Lake_term_____x2e_x2b___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".+"};
static const lean_object* l_Lake_term_____x2e_x2b___closed__2 = (const lean_object*)&l_Lake_term_____x2e_x2b___closed__2_value;
static const lean_ctor_object l_Lake_term_____x2e_x2b___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_term_____x2e_x2b___closed__2_value)}};
static const lean_object* l_Lake_term_____x2e_x2b___closed__3 = (const lean_object*)&l_Lake_term_____x2e_x2b___closed__3_value;
static const lean_ctor_object l_Lake_term_____x2e_x2b___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lake_term_____x2e_x2a___closed__4_value),((lean_object*)&l_Lake_term_____x2e_x2a___closed__14_value),((lean_object*)&l_Lake_term_____x2e_x2b___closed__3_value)}};
static const lean_object* l_Lake_term_____x2e_x2b___closed__4 = (const lean_object*)&l_Lake_term_____x2e_x2b___closed__4_value;
static const lean_ctor_object l_Lake_term_____x2e_x2b___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_term_____x2e_x2b___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lake_term_____x2e_x2b___closed__4_value)}};
static const lean_object* l_Lake_term_____x2e_x2b___closed__5 = (const lean_object*)&l_Lake_term_____x2e_x2b___closed__5_value;
LEAN_EXPORT const lean_object* l_Lake_term_____x2e_x2b = (const lean_object*)&l_Lake_term_____x2e_x2b___closed__5_value;
static const lean_string_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Glob.submodules"};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0_value;
static lean_once_cell_t l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1;
static const lean_string_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "submodules"};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(26, 132, 67, 250, 48, 109, 63, 126)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(30, 142, 32, 161, 255, 145, 57, 209)}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_term_____x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_0),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(222, 149, 144, 131, 37, 196, 123, 168)}};
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value_aux_1),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(138, 92, 73, 223, 11, 170, 61, 155)}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__4_value)}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7_value;
static const lean_ctor_object l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__5_value),((lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__7_value)}};
static const lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8 = (const lean_object*)&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8_value;
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_toString(lean_object*);
static const lean_closure_object l_Lake_Glob_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Glob_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Glob_instToString___closed__0 = (const lean_object*)&l_Lake_Glob_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Glob_instToString = (const lean_object*)&l_Lake_Glob_instToString___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_Glob_matches(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_matches___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0 = (const lean_object*)&l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lake_Glob_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
lean_object* v_a_7_; lean_object* v___x_8_; 
v_a_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_7_);
lean_dec_ref(v_t_5_);
v___x_8_ = lean_apply_1(v_k_6_, v_a_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lake_Glob_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lake_Glob_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_one_elim___redArg(lean_object* v_t_21_, lean_object* v_one_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lake_Glob_ctorElim___redArg(v_t_21_, v_one_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_one_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_one_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lake_Glob_ctorElim___redArg(v_t_25_, v_one_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_submodules_elim___redArg(lean_object* v_t_29_, lean_object* v_submodules_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lake_Glob_ctorElim___redArg(v_t_29_, v_submodules_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_submodules_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_submodules_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lake_Glob_ctorElim___redArg(v_t_33_, v_submodules_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_andSubmodules_elim___redArg(lean_object* v_t_37_, lean_object* v_andSubmodules_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lake_Glob_ctorElim___redArg(v_t_37_, v_andSubmodules_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_andSubmodules_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_andSubmodules_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lake_Glob_ctorElim___redArg(v_t_41_, v_andSubmodules_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Lake_instReprGlob_repr___closed__3(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(2u);
v___x_56_ = lean_nat_to_int(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lake_instReprGlob_repr___closed__4(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(1u);
v___x_58_ = lean_nat_to_int(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprGlob_repr(lean_object* v_x_71_, lean_object* v_prec_72_){
_start:
{
switch(lean_obj_tag(v_x_71_))
{
case 0:
{
lean_object* v_a_73_; lean_object* v___y_75_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_a_73_ = lean_ctor_get(v_x_71_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v_x_71_, 1);
v___x_84_ = lean_unsigned_to_nat(1024u);
v___x_85_ = lean_nat_dec_le(v___x_84_, v_prec_72_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; 
v___x_86_ = lean_obj_once(&l_Lake_instReprGlob_repr___closed__3, &l_Lake_instReprGlob_repr___closed__3_once, _init_l_Lake_instReprGlob_repr___closed__3);
v___y_75_ = v___x_86_;
goto v___jp_74_;
}
else
{
lean_object* v___x_87_; 
v___x_87_ = lean_obj_once(&l_Lake_instReprGlob_repr___closed__4, &l_Lake_instReprGlob_repr___closed__4_once, _init_l_Lake_instReprGlob_repr___closed__4);
v___y_75_ = v___x_87_;
goto v___jp_74_;
}
v___jp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_76_ = ((lean_object*)(l_Lake_instReprGlob_repr___closed__2));
v___x_77_ = lean_unsigned_to_nat(1024u);
v___x_78_ = l_Lean_Name_reprPrec(v_a_73_, v___x_77_);
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_76_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
lean_inc(v___y_75_);
v___x_80_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_80_, 0, v___y_75_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = 0;
v___x_82_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v___x_81_);
v___x_83_ = l_Repr_addAppParen(v___x_82_, v_prec_72_);
return v___x_83_;
}
}
case 1:
{
lean_object* v_a_88_; lean_object* v___y_90_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_a_88_ = lean_ctor_get(v_x_71_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v_x_71_, 1);
v___x_99_ = lean_unsigned_to_nat(1024u);
v___x_100_ = lean_nat_dec_le(v___x_99_, v_prec_72_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Lake_instReprGlob_repr___closed__3, &l_Lake_instReprGlob_repr___closed__3_once, _init_l_Lake_instReprGlob_repr___closed__3);
v___y_90_ = v___x_101_;
goto v___jp_89_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lake_instReprGlob_repr___closed__4, &l_Lake_instReprGlob_repr___closed__4_once, _init_l_Lake_instReprGlob_repr___closed__4);
v___y_90_ = v___x_102_;
goto v___jp_89_;
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_91_ = ((lean_object*)(l_Lake_instReprGlob_repr___closed__7));
v___x_92_ = lean_unsigned_to_nat(1024u);
v___x_93_ = l_Lean_Name_reprPrec(v_a_88_, v___x_92_);
v___x_94_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_91_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
lean_inc(v___y_90_);
v___x_95_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_95_, 0, v___y_90_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = 0;
v___x_97_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1, v___x_96_);
v___x_98_ = l_Repr_addAppParen(v___x_97_, v_prec_72_);
return v___x_98_;
}
}
default: 
{
lean_object* v_a_103_; lean_object* v___y_105_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_a_103_ = lean_ctor_get(v_x_71_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v_x_71_, 1);
v___x_114_ = lean_unsigned_to_nat(1024u);
v___x_115_ = lean_nat_dec_le(v___x_114_, v_prec_72_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Lake_instReprGlob_repr___closed__3, &l_Lake_instReprGlob_repr___closed__3_once, _init_l_Lake_instReprGlob_repr___closed__3);
v___y_105_ = v___x_116_;
goto v___jp_104_;
}
else
{
lean_object* v___x_117_; 
v___x_117_ = lean_obj_once(&l_Lake_instReprGlob_repr___closed__4, &l_Lake_instReprGlob_repr___closed__4_once, _init_l_Lake_instReprGlob_repr___closed__4);
v___y_105_ = v___x_117_;
goto v___jp_104_;
}
v___jp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_106_ = ((lean_object*)(l_Lake_instReprGlob_repr___closed__10));
v___x_107_ = lean_unsigned_to_nat(1024u);
v___x_108_ = l_Lean_Name_reprPrec(v_a_103_, v___x_107_);
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_106_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
lean_inc(v___y_105_);
v___x_110_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_110_, 0, v___y_105_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = 0;
v___x_112_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*1, v___x_111_);
v___x_113_ = l_Repr_addAppParen(v___x_112_, v_prec_72_);
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprGlob_repr___boxed(lean_object* v_x_118_, lean_object* v_prec_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lake_instReprGlob_repr(v_x_118_, v_prec_119_);
lean_dec(v_prec_119_);
return v_res_120_;
}
}
uint8_t l_Lake_instDecidableEqGlob_decEq(lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
switch(lean_obj_tag(v_x_123_))
{
case 0:
{
if (lean_obj_tag(v_x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v_a_126_; uint8_t v___x_127_; 
v_a_125_ = lean_ctor_get(v_x_123_, 0);
v_a_126_ = lean_ctor_get(v_x_124_, 0);
v___x_127_ = lean_name_eq(v_a_125_, v_a_126_);
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
}
case 1:
{
if (lean_obj_tag(v_x_124_) == 1)
{
lean_object* v_a_129_; lean_object* v_a_130_; uint8_t v___x_131_; 
v_a_129_ = lean_ctor_get(v_x_123_, 0);
v_a_130_ = lean_ctor_get(v_x_124_, 0);
v___x_131_ = lean_name_eq(v_a_129_, v_a_130_);
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
}
default: 
{
if (lean_obj_tag(v_x_124_) == 2)
{
lean_object* v_a_133_; lean_object* v_a_134_; uint8_t v___x_135_; 
v_a_133_ = lean_ctor_get(v_x_123_, 0);
v_a_134_ = lean_ctor_get(v_x_124_, 0);
v___x_135_ = lean_name_eq(v_a_133_, v_a_134_);
return v___x_135_;
}
else
{
uint8_t v___x_136_; 
v___x_136_ = 0;
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instDecidableEqGlob_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_123_ = stack[0].m_obj;
lean_object* v_x_124_ = stack[1].m_obj;
uint8_t v_res_137_;
v_res_137_ = l_Lake_instDecidableEqGlob_decEq(v_x_123_, v_x_124_);
stack->m_num = v_res_137_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqGlob_decEq___boxed(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Lake_instDecidableEqGlob_decEq(v_x_138_, v_x_139_);
lean_dec_ref(v_x_139_);
lean_dec_ref(v_x_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
uint8_t l_Lake_instDecidableEqGlob(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = l_Lake_instDecidableEqGlob_decEq(v_x_142_, v_x_143_);
return v___x_144_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqGlob_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_142_ = stack[0].m_obj;
lean_object* v_x_143_ = stack[1].m_obj;
uint8_t v_res_145_;
v_res_145_ = l_Lake_instDecidableEqGlob(v_x_142_, v_x_143_);
stack->m_num = v_res_145_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqGlob___boxed(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Lake_instDecidableEqGlob(v_x_146_, v_x_147_);
lean_dec_ref(v_x_147_);
lean_dec_ref(v_x_146_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeNameGlob___lam__0(lean_object* v_a_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v_a_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__5));
v___x_207_ = l_String_toRawSubstring_x27(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1(lean_object* v_x_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lake_term_____x2e_x2a___closed__2));
lean_inc(v_x_237_);
v___x_241_ = l_Lean_Syntax_isOfKind(v_x_237_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_x_237_);
v___x_242_ = lean_box(1);
v___x_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v_a_239_);
return v___x_243_;
}
else
{
lean_object* v_quotContext_244_; lean_object* v_currMacroScope_245_; lean_object* v_ref_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_quotContext_244_ = lean_ctor_get(v_a_238_, 1);
v_currMacroScope_245_ = lean_ctor_get(v_a_238_, 2);
v_ref_246_ = lean_ctor_get(v_a_238_, 5);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = l_Lean_Syntax_getArg(v_x_237_, v___x_247_);
lean_dec(v_x_237_);
v___x_249_ = 0;
v___x_250_ = l_Lean_SourceInfo_fromRef(v_ref_246_, v___x_249_);
v___x_251_ = ((lean_object*)(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4));
v___x_252_ = lean_obj_once(&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6, &l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6_once, _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__6);
v___x_253_ = ((lean_object*)(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__9));
lean_inc(v_currMacroScope_245_);
lean_inc(v_quotContext_244_);
v___x_254_ = l_Lean_addMacroScope(v_quotContext_244_, v___x_253_, v_currMacroScope_245_);
v___x_255_ = ((lean_object*)(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__14));
lean_inc_n(v___x_250_, 2);
v___x_256_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_256_, 0, v___x_250_);
lean_ctor_set(v___x_256_, 1, v___x_252_);
lean_ctor_set(v___x_256_, 2, v___x_254_);
lean_ctor_set(v___x_256_, 3, v___x_255_);
v___x_257_ = ((lean_object*)(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16));
v___x_258_ = ((lean_object*)(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18));
v___x_259_ = lean_unsigned_to_nat(1u);
v___x_260_ = lean_mk_empty_array_with_capacity(v___x_259_);
v___x_261_ = lean_array_push(v___x_260_, v___x_248_);
v___x_262_ = lean_box(2);
v___x_263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_258_);
lean_ctor_set(v___x_263_, 2, v___x_261_);
v___x_264_ = l_Lean_Syntax_node1(v___x_250_, v___x_257_, v___x_263_);
v___x_265_ = l_Lean_Syntax_node2(v___x_250_, v___x_251_, v___x_256_, v___x_264_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_a_239_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___boxed(lean_object* v_x_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1(v_x_267_, v_a_268_, v_a_269_);
lean_dec_ref(v_a_268_);
return v_res_270_;
}
}
static lean_object* _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__0));
v___x_289_ = l_String_toRawSubstring_x27(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1(lean_object* v_x_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = ((lean_object*)(l_Lake_term_____x2e_x2b___closed__1));
lean_inc(v_x_309_);
v___x_313_ = l_Lean_Syntax_isOfKind(v_x_309_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_x_309_);
v___x_314_ = lean_box(1);
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_a_311_);
return v___x_315_;
}
else
{
lean_object* v_quotContext_316_; lean_object* v_currMacroScope_317_; lean_object* v_ref_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_quotContext_316_ = lean_ctor_get(v_a_310_, 1);
v_currMacroScope_317_ = lean_ctor_get(v_a_310_, 2);
v_ref_318_ = lean_ctor_get(v_a_310_, 5);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = l_Lean_Syntax_getArg(v_x_309_, v___x_319_);
lean_dec(v_x_309_);
v___x_321_ = 0;
v___x_322_ = l_Lean_SourceInfo_fromRef(v_ref_318_, v___x_321_);
v___x_323_ = ((lean_object*)(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__4));
v___x_324_ = lean_obj_once(&l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1, &l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1_once, _init_l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__1);
v___x_325_ = ((lean_object*)(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__3));
lean_inc(v_currMacroScope_317_);
lean_inc(v_quotContext_316_);
v___x_326_ = l_Lean_addMacroScope(v_quotContext_316_, v___x_325_, v_currMacroScope_317_);
v___x_327_ = ((lean_object*)(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___closed__8));
lean_inc_n(v___x_322_, 2);
v___x_328_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_328_, 0, v___x_322_);
lean_ctor_set(v___x_328_, 1, v___x_324_);
lean_ctor_set(v___x_328_, 2, v___x_326_);
lean_ctor_set(v___x_328_, 3, v___x_327_);
v___x_329_ = ((lean_object*)(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__16));
v___x_330_ = ((lean_object*)(l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2a__1___closed__18));
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = lean_mk_empty_array_with_capacity(v___x_331_);
v___x_333_ = lean_array_push(v___x_332_, v___x_320_);
v___x_334_ = lean_box(2);
v___x_335_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_330_);
lean_ctor_set(v___x_335_, 2, v___x_333_);
v___x_336_ = l_Lean_Syntax_node1(v___x_322_, v___x_329_, v___x_335_);
v___x_337_ = l_Lean_Syntax_node2(v___x_322_, v___x_323_, v___x_328_, v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v_a_311_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1___boxed(lean_object* v_x_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lake___aux__Lake__Config__Glob______macroRules__Lake__term_____x2e_x2b__1(v_x_339_, v_a_340_, v_a_341_);
lean_dec_ref(v_a_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_toString(lean_object* v_x_343_){
_start:
{
switch(lean_obj_tag(v_x_343_))
{
case 0:
{
lean_object* v_a_344_; uint8_t v___x_345_; lean_object* v___x_346_; 
v_a_344_ = lean_ctor_get(v_x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v_x_343_, 1);
v___x_345_ = 1;
v___x_346_ = l_Lean_Name_toString(v_a_344_, v___x_345_);
return v___x_346_;
}
case 1:
{
lean_object* v_a_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_a_347_ = lean_ctor_get(v_x_343_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v_x_343_, 1);
v___x_348_ = 1;
v___x_349_ = l_Lean_Name_toString(v_a_347_, v___x_348_);
v___x_350_ = ((lean_object*)(l_Lake_term_____x2e_x2b___closed__2));
v___x_351_ = lean_string_append(v___x_349_, v___x_350_);
return v___x_351_;
}
default: 
{
lean_object* v_a_352_; uint8_t v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_a_352_ = lean_ctor_get(v_x_343_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v_x_343_, 1);
v___x_353_ = 1;
v___x_354_ = l_Lean_Name_toString(v_a_352_, v___x_353_);
v___x_355_ = ((lean_object*)(l_Lake_term_____x2e_x2a___closed__15));
v___x_356_ = lean_string_append(v___x_354_, v___x_355_);
return v___x_356_;
}
}
}
}
uint8_t l_Lake_Glob_matches(lean_object* v_m_359_, lean_object* v_x_360_){
_start:
{
switch(lean_obj_tag(v_x_360_))
{
case 0:
{
lean_object* v_a_361_; uint8_t v___x_362_; 
v_a_361_ = lean_ctor_get(v_x_360_, 0);
v___x_362_ = lean_name_eq(v_a_361_, v_m_359_);
return v___x_362_;
}
case 1:
{
lean_object* v_a_363_; uint8_t v___x_364_; 
v_a_363_ = lean_ctor_get(v_x_360_, 0);
v___x_364_ = l_Lean_Name_isPrefixOf(v_a_363_, v_m_359_);
if (v___x_364_ == 0)
{
return v___x_364_;
}
else
{
uint8_t v___x_365_; 
v___x_365_ = lean_name_eq(v_a_363_, v_m_359_);
if (v___x_365_ == 0)
{
return v___x_364_;
}
else
{
uint8_t v___x_366_; 
v___x_366_ = 0;
return v___x_366_;
}
}
}
default: 
{
lean_object* v_a_367_; uint8_t v___x_368_; 
v_a_367_ = lean_ctor_get(v_x_360_, 0);
v___x_368_ = l_Lean_Name_isPrefixOf(v_a_367_, v_m_359_);
return v___x_368_;
}
}
}
}
LEAN_EXPORT void l_Lake_Glob_matches_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_359_ = stack[0].m_obj;
lean_object* v_x_360_ = stack[1].m_obj;
uint8_t v_res_369_;
v_res_369_ = l_Lake_Glob_matches(v_m_359_, v_x_360_);
stack->m_num = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lake_Glob_matches___boxed(lean_object* v_m_370_, lean_object* v_x_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Lake_Glob_matches(v_m_370_, v_x_371_);
lean_dec_ref(v_x_371_);
lean_dec(v_m_370_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__0(lean_object* v_a_374_, lean_object* v_f_375_, lean_object* v_x_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = l_Lean_Name_append(v_a_374_, v_x_376_);
v___x_378_ = lean_apply_1(v_f_375_, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__2(lean_object* v_dir_380_, lean_object* v_a_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v___f_384_, lean_object* v_x_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = ((lean_object*)(l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0));
v___x_387_ = l_Lean_modToFilePath(v_dir_380_, v_a_381_, v___x_386_);
v___x_388_ = l_Lean_forEachModuleInDir___redArg(v_inst_382_, v_inst_383_, v___x_387_, v___f_384_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed(lean_object* v_dir_389_, lean_object* v_a_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v___f_393_, lean_object* v_x_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lake_Glob_forEachModuleIn___redArg___lam__2(v_dir_389_, v_a_390_, v_inst_391_, v_inst_392_, v___f_393_, v_x_394_);
lean_dec_ref(v_dir_389_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn___redArg(lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_dir_398_, lean_object* v_f_399_, lean_object* v_x_400_){
_start:
{
switch(lean_obj_tag(v_x_400_))
{
case 0:
{
lean_object* v_a_401_; lean_object* v___x_402_; 
lean_dec_ref(v_dir_398_);
lean_dec(v_inst_397_);
lean_dec_ref(v_inst_396_);
v_a_401_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v_x_400_, 1);
v___x_402_ = lean_apply_1(v_f_399_, v_a_401_);
return v___x_402_;
}
case 1:
{
lean_object* v_a_403_; lean_object* v___f_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_a_403_ = lean_ctor_get(v_x_400_, 0);
lean_inc_n(v_a_403_, 2);
lean_dec_ref_known(v_x_400_, 1);
v___f_404_ = lean_alloc_closure((void*)(l_Lake_Glob_forEachModuleIn___redArg___lam__0), 3, 2);
lean_closure_set(v___f_404_, 0, v_a_403_);
lean_closure_set(v___f_404_, 1, v_f_399_);
v___x_405_ = ((lean_object*)(l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0));
v___x_406_ = l_Lean_modToFilePath(v_dir_398_, v_a_403_, v___x_405_);
lean_dec_ref(v_dir_398_);
v___x_407_ = l_Lean_forEachModuleInDir___redArg(v_inst_396_, v_inst_397_, v___x_406_, v___f_404_);
return v___x_407_;
}
default: 
{
lean_object* v_toApplicative_408_; lean_object* v_toSeqRight_409_; lean_object* v_a_410_; lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_toApplicative_408_ = lean_ctor_get(v_inst_396_, 0);
v_toSeqRight_409_ = lean_ctor_get(v_toApplicative_408_, 4);
lean_inc(v_toSeqRight_409_);
v_a_410_ = lean_ctor_get(v_x_400_, 0);
lean_inc_n(v_a_410_, 3);
lean_dec_ref_known(v_x_400_, 1);
lean_inc(v_f_399_);
v___f_411_ = lean_alloc_closure((void*)(l_Lake_Glob_forEachModuleIn___redArg___lam__0), 3, 2);
lean_closure_set(v___f_411_, 0, v_a_410_);
lean_closure_set(v___f_411_, 1, v_f_399_);
v___f_412_ = lean_alloc_closure((void*)(l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_412_, 0, v_dir_398_);
lean_closure_set(v___f_412_, 1, v_a_410_);
lean_closure_set(v___f_412_, 2, v_inst_396_);
lean_closure_set(v___f_412_, 3, v_inst_397_);
lean_closure_set(v___f_412_, 4, v___f_411_);
v___x_413_ = lean_apply_1(v_f_399_, v_a_410_);
v___x_414_ = lean_apply_4(v_toSeqRight_409_, lean_box(0), lean_box(0), v___x_413_, v___f_412_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_forEachModuleIn(lean_object* v_m_415_, lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_dir_418_, lean_object* v_f_419_, lean_object* v_x_420_){
_start:
{
switch(lean_obj_tag(v_x_420_))
{
case 0:
{
lean_object* v_a_421_; lean_object* v___x_422_; 
lean_dec_ref(v_dir_418_);
lean_dec(v_inst_417_);
lean_dec_ref(v_inst_416_);
v_a_421_ = lean_ctor_get(v_x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v_x_420_, 1);
v___x_422_ = lean_apply_1(v_f_419_, v_a_421_);
return v___x_422_;
}
case 1:
{
lean_object* v_a_423_; lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_a_423_ = lean_ctor_get(v_x_420_, 0);
lean_inc_n(v_a_423_, 2);
lean_dec_ref_known(v_x_420_, 1);
v___f_424_ = lean_alloc_closure((void*)(l_Lake_Glob_forEachModuleIn___redArg___lam__0), 3, 2);
lean_closure_set(v___f_424_, 0, v_a_423_);
lean_closure_set(v___f_424_, 1, v_f_419_);
v___x_425_ = ((lean_object*)(l_Lake_Glob_forEachModuleIn___redArg___lam__2___closed__0));
v___x_426_ = l_Lean_modToFilePath(v_dir_418_, v_a_423_, v___x_425_);
lean_dec_ref(v_dir_418_);
v___x_427_ = l_Lean_forEachModuleInDir___redArg(v_inst_416_, v_inst_417_, v___x_426_, v___f_424_);
return v___x_427_;
}
default: 
{
lean_object* v_toApplicative_428_; lean_object* v_toSeqRight_429_; lean_object* v_a_430_; lean_object* v___f_431_; lean_object* v___f_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_toApplicative_428_ = lean_ctor_get(v_inst_416_, 0);
v_toSeqRight_429_ = lean_ctor_get(v_toApplicative_428_, 4);
lean_inc(v_toSeqRight_429_);
v_a_430_ = lean_ctor_get(v_x_420_, 0);
lean_inc_n(v_a_430_, 3);
lean_dec_ref_known(v_x_420_, 1);
lean_inc(v_f_419_);
v___f_431_ = lean_alloc_closure((void*)(l_Lake_Glob_forEachModuleIn___redArg___lam__0), 3, 2);
lean_closure_set(v___f_431_, 0, v_a_430_);
lean_closure_set(v___f_431_, 1, v_f_419_);
v___f_432_ = lean_alloc_closure((void*)(l_Lake_Glob_forEachModuleIn___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_432_, 0, v_dir_418_);
lean_closure_set(v___f_432_, 1, v_a_430_);
lean_closure_set(v___f_432_, 2, v_inst_416_);
lean_closure_set(v___f_432_, 3, v_inst_417_);
lean_closure_set(v___f_432_, 4, v___f_431_);
v___x_433_ = lean_apply_1(v_f_419_, v_a_430_);
v___x_434_ = lean_apply_4(v_toSeqRight_429_, lean_box(0), lean_box(0), v___x_433_, v___f_432_);
return v___x_434_;
}
}
}
}
lean_object* runtime_initialize_Lean_Util_Path(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Name(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Glob(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Glob(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_Path(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Lean_Data_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Glob(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Glob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Glob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Glob(builtin);
}
#ifdef __cplusplus
}
#endif
