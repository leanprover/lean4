// Lean compiler output
// Module: Lean.Compiler.ModPkgExt
// Imports: public import Lean.Environment import Lean.Compiler.NameMangling
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPackageSymbolPrefix(lean_object*);
lean_object* l_Lean_Name_mangle(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__0 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__1 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__1_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__2 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__2_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__3 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__4 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__4_value;
static const lean_array_object l_Lean_registerModuleEnvExtension___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__5 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__5_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__6 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__7 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__7_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__8 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__9 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__9_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__10 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__11 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__11_value;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__12;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__13;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__14 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__14_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__15 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__15_value;
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__16_value_aux_0),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__16_value_aux_1),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__16_value_aux_2),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__16 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__16_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__17 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__17_value;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__18;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__19;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__20;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__21;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__22;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__23;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__24;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__25;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__26;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__27;
static lean_once_cell_t l_Lean_registerModuleEnvExtension___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___auto__1;
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__4(lean_object*);
static const lean_closure_object l_Lean_registerModuleEnvExtension___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerModuleEnvExtension___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerModuleEnvExtension___redArg___closed__0 = (const lean_object*)&l_Lean_registerModuleEnvExtension___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerModuleEnvExtension___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerModuleEnvExtension___redArg___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerModuleEnvExtension___redArg___closed__1 = (const lean_object*)&l_Lean_registerModuleEnvExtension___redArg___closed__1_value;
static const lean_closure_object l_Lean_registerModuleEnvExtension___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerModuleEnvExtension___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerModuleEnvExtension___redArg___closed__2 = (const lean_object*)&l_Lean_registerModuleEnvExtension___redArg___closed__2_value;
static const lean_closure_object l_Lean_registerModuleEnvExtension___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerModuleEnvExtension___redArg___lam__4, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerModuleEnvExtension___redArg___closed__3 = (const lean_object*)&l_Lean_registerModuleEnvExtension___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__0 = (const lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__0_value)}};
static const lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__1 = (const lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__0 = (const lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__0 = (const lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__0_value;
static const lean_closure_object l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__1 = (const lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__1_value;
static lean_once_cell_t l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__2;
static lean_once_cell_t l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ModPkgExt"};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 204, 27, 30, 229, 171, 155, 230)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(54, 24, 93, 111, 84, 76, 103, 70)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 103, 117, 183, 112, 214, 20, 110)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "modPkgExt"};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(179, 135, 14, 167, 209, 11, 249, 83)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackageByIdx_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackageByIdx_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackage_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_setModulePackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_symbol_stem(lean_object*, lean_object*);
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__12, &l_Lean_registerModuleEnvExtension___auto__1___closed__12_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__18(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__17));
v___x_41_ = l_Lean_mkAtom(v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__19(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__18, &l_Lean_registerModuleEnvExtension___auto__1___closed__18_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__18);
v___x_43_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__5));
v___x_44_ = lean_array_push(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__20(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_45_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__19, &l_Lean_registerModuleEnvExtension___auto__1___closed__19_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__19);
v___x_46_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__16));
v___x_47_ = lean_box(2);
v___x_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_45_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__21(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__20, &l_Lean_registerModuleEnvExtension___auto__1___closed__20_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__20);
v___x_50_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__13, &l_Lean_registerModuleEnvExtension___auto__1___closed__13_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__13);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__22(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__21, &l_Lean_registerModuleEnvExtension___auto__1___closed__21_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__21);
v___x_53_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__11));
v___x_54_ = lean_box(2);
v___x_55_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_52_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__23(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__22, &l_Lean_registerModuleEnvExtension___auto__1___closed__22_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__22);
v___x_57_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__5));
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__24(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__23, &l_Lean_registerModuleEnvExtension___auto__1___closed__23_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__23);
v___x_60_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__9));
v___x_61_ = lean_box(2);
v___x_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_59_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__25(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__24, &l_Lean_registerModuleEnvExtension___auto__1___closed__24_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__24);
v___x_64_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__5));
v___x_65_ = lean_array_push(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__26(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__25, &l_Lean_registerModuleEnvExtension___auto__1___closed__25_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__25);
v___x_67_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__7));
v___x_68_ = lean_box(2);
v___x_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__27(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__26, &l_Lean_registerModuleEnvExtension___auto__1___closed__26_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__26);
v___x_71_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__5));
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__28(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__27, &l_Lean_registerModuleEnvExtension___auto__1___closed__27_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__27);
v___x_74_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__4));
v___x_75_ = lean_box(2);
v___x_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_registerModuleEnvExtension___auto__1___closed__28, &l_Lean_registerModuleEnvExtension___auto__1___closed__28_once, _init_l_Lean_registerModuleEnvExtension___auto__1___closed__28);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__0(lean_object* v_mkInitial_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_apply_1(v_mkInitial_78_, lean_box(0));
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__0___boxed(lean_object* v_mkInitial_83_, lean_object* v_x_84_, lean_object* v_x_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_registerModuleEnvExtension___redArg___lam__0(v_mkInitial_83_, v_x_84_, v_x_85_);
lean_dec_ref(v_x_85_);
lean_dec_ref(v_x_84_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__1(lean_object* v_s_88_, lean_object* v_x_89_){
_start:
{
lean_inc(v_s_88_);
return v_s_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__1___boxed(lean_object* v_s_90_, lean_object* v_x_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_registerModuleEnvExtension___redArg___lam__1(v_s_90_, v_x_91_);
lean_dec(v_x_91_);
lean_dec(v_s_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2(lean_object* v_x_93_, lean_object* v_s_94_, uint8_t v_x_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = lean_mk_empty_array_with_capacity(v___x_96_);
v___x_98_ = lean_array_push(v___x_97_, v_s_94_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2___boxed(lean_object* v_x_99_, lean_object* v_s_100_, lean_object* v_x_101_){
_start:
{
uint8_t v_x_73__boxed_102_; lean_object* v_res_103_; 
v_x_73__boxed_102_ = lean_unbox(v_x_101_);
v_res_103_ = l_Lean_registerModuleEnvExtension___redArg___lam__2(v_x_99_, v_s_100_, v_x_73__boxed_102_);
lean_dec_ref(v_x_99_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__3(lean_object* v_x_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_box(0);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__3___boxed(lean_object* v_x_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_registerModuleEnvExtension___redArg___lam__3(v_x_106_);
lean_dec(v_x_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__4(lean_object* v_s_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_mk_empty_array_with_capacity(v___x_109_);
v___x_111_ = lean_array_push(v___x_110_, v_s_108_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg(lean_object* v_mkInitial_116_, lean_object* v_name_117_){
_start:
{
lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___f_122_; lean_object* v___f_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_inc_ref(v_mkInitial_116_);
v___f_119_ = lean_alloc_closure((void*)(l_Lean_registerModuleEnvExtension___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_119_, 0, v_mkInitial_116_);
v___f_120_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__0));
v___f_121_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__1));
v___f_122_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__2));
v___f_123_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__3));
v___x_124_ = lean_box(2);
v___x_125_ = lean_box(0);
v___x_126_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_126_, 0, v_name_117_);
lean_ctor_set(v___x_126_, 1, v_mkInitial_116_);
lean_ctor_set(v___x_126_, 2, v___f_119_);
lean_ctor_set(v___x_126_, 3, v___f_120_);
lean_ctor_set(v___x_126_, 4, v___f_121_);
lean_ctor_set(v___x_126_, 5, v___f_122_);
lean_ctor_set(v___x_126_, 6, v___x_124_);
lean_ctor_set(v___x_126_, 7, v___x_125_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___f_123_);
v___x_128_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___boxed(lean_object* v_mkInitial_129_, lean_object* v_name_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_registerModuleEnvExtension___redArg(v_mkInitial_129_, v_name_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension(lean_object* v_00_u03c3_133_, lean_object* v_inst_134_, lean_object* v_mkInitial_135_, lean_object* v_name_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_registerModuleEnvExtension___redArg(v_mkInitial_135_, v_name_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___boxed(lean_object* v_00_u03c3_139_, lean_object* v_inst_140_, lean_object* v_mkInitial_141_, lean_object* v_name_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_registerModuleEnvExtension(v_00_u03c3_139_, v_inst_140_, v_mkInitial_141_, v_name_142_);
lean_dec(v_inst_140_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0(lean_object* v_x_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__1));
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___boxed(lean_object* v_x_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0(v_x_153_, v___y_154_);
lean_dec_ref(v___y_154_);
lean_dec_ref(v_x_153_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2(lean_object* v_x_159_, lean_object* v_x_160_, uint8_t v_x_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__0));
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___boxed(lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
uint8_t v_x_89__boxed_166_; lean_object* v_res_167_; 
v_x_89__boxed_166_ = lean_unbox(v_x_165_);
v_res_167_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2(v_x_163_, v_x_164_, v_x_89__boxed_166_);
lean_dec(v_x_164_);
lean_dec_ref(v_x_163_);
return v_res_167_;
}
}
static lean_object* _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__2(void){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_170_;
}
}
static lean_object* _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3(void){
_start:
{
lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___f_171_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__2));
v___f_172_ = ((lean_object*)(l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__1));
v___f_173_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__0));
v___f_174_ = ((lean_object*)(l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__0));
v___x_175_ = lean_box(0);
v___x_176_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__2, &l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__2_once, _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__2);
v___x_177_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___f_174_);
lean_ctor_set(v___x_177_, 3, v___f_173_);
lean_ctor_set(v___x_177_, 4, v___f_172_);
lean_ctor_set(v___x_177_, 5, v___f_171_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1(lean_object* v_00_u03c3_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3, &l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3_once, _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited(lean_object* v_00_u03c3_180_, lean_object* v_inst_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3, &l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3_once, _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___boxed(lean_object* v_00_u03c3_183_, lean_object* v_inst_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_ModuleEnvExtension_instInhabited(v_00_u03c3_183_, v_inst_184_);
lean_dec(v_inst_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(lean_object* v_inst_186_, lean_object* v_ext_187_, lean_object* v_env_188_, lean_object* v_idx_189_){
_start:
{
uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_190_ = 0;
v___x_191_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v_inst_186_, v_ext_187_, v_env_188_, v_idx_189_, v___x_190_);
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_array_get_size(v___x_191_);
v___x_194_ = lean_nat_dec_lt(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_dec_ref(v___x_191_);
v___x_195_ = lean_box(0);
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_array_fget(v___x_191_, v___x_192_);
lean_dec_ref(v___x_191_);
v___x_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg___boxed(lean_object* v_inst_198_, lean_object* v_ext_199_, lean_object* v_env_200_, lean_object* v_idx_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(v_inst_198_, v_ext_199_, v_env_200_, v_idx_201_);
lean_dec(v_idx_201_);
lean_dec_ref(v_env_200_);
lean_dec_ref(v_ext_199_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f(lean_object* v_00_u03c3_203_, lean_object* v_inst_204_, lean_object* v_ext_205_, lean_object* v_env_206_, lean_object* v_idx_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(v_inst_204_, v_ext_205_, v_env_206_, v_idx_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___boxed(lean_object* v_00_u03c3_209_, lean_object* v_inst_210_, lean_object* v_ext_211_, lean_object* v_env_212_, lean_object* v_idx_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f(v_00_u03c3_209_, v_inst_210_, v_ext_211_, v_env_212_, v_idx_213_);
lean_dec(v_idx_213_);
lean_dec_ref(v_env_212_);
lean_dec_ref(v_ext_211_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_(lean_object* v___x_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2____boxed(lean_object* v___x_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_(v___x_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___f_249_ = ((lean_object*)(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_));
v___x_250_ = ((lean_object*)(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_));
v___x_251_ = l_Lean_registerModuleEnvExtension___redArg(v___f_249_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2____boxed(lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_();
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackageByIdx_x3f(lean_object* v_env_254_, lean_object* v_idx_255_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_box(0);
v___x_257_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v___x_258_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(v___x_256_, v___x_257_, v_env_254_, v_idx_255_);
if (lean_obj_tag(v___x_258_) == 0)
{
return v___x_256_;
}
else
{
lean_object* v_val_259_; 
v_val_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_val_259_);
lean_dec_ref(v___x_258_);
return v_val_259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackageByIdx_x3f___boxed(lean_object* v_env_260_, lean_object* v_idx_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Environment_getModulePackageByIdx_x3f(v_env_260_, v_idx_261_);
lean_dec(v_idx_261_);
lean_dec_ref(v_env_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackage_x3f(lean_object* v_env_263_){
_start:
{
lean_object* v___x_264_; lean_object* v_toEnvExtension_265_; lean_object* v_asyncMode_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_264_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc_ref(v_toEnvExtension_265_);
v_asyncMode_266_ = lean_ctor_get(v_toEnvExtension_265_, 2);
lean_inc(v_asyncMode_266_);
lean_dec_ref(v_toEnvExtension_265_);
v___x_267_ = lean_box(0);
v___x_268_ = lean_box(0);
v___x_269_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_267_, v___x_264_, v_env_263_, v_asyncMode_266_, v___x_268_);
lean_dec(v_asyncMode_266_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setModulePackage(lean_object* v_pkg_x3f_270_, lean_object* v_env_271_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v___x_273_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_272_, v_env_271_, v_pkg_x3f_270_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* lean_get_symbol_stem(lean_object* v_env_274_, lean_object* v_declName_275_){
_start:
{
lean_object* v___y_277_; lean_object* v___x_280_; 
v___x_280_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_274_, v_declName_275_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; lean_object* v_toEnvExtension_282_; lean_object* v_asyncMode_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_281_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc_ref(v_toEnvExtension_282_);
v_asyncMode_283_ = lean_ctor_get(v_toEnvExtension_282_, 2);
lean_inc(v_asyncMode_283_);
lean_dec_ref(v_toEnvExtension_282_);
v___x_284_ = lean_box(0);
v___x_285_ = lean_box(0);
v___x_286_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_284_, v___x_281_, v_env_274_, v_asyncMode_283_, v___x_285_);
lean_dec(v_asyncMode_283_);
v___y_277_ = v___x_286_;
goto v___jp_276_;
}
else
{
lean_object* v_val_287_; lean_object* v___x_288_; 
v_val_287_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_287_);
lean_dec_ref(v___x_280_);
v___x_288_ = l_Lean_Environment_getModulePackageByIdx_x3f(v_env_274_, v_val_287_);
lean_dec(v_val_287_);
lean_dec_ref(v_env_274_);
v___y_277_ = v___x_288_;
goto v___jp_276_;
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = l_Lean_mkPackageSymbolPrefix(v___y_277_);
lean_dec(v___y_277_);
v___x_279_ = l_Lean_Name_mangle(v_declName_275_, v___x_278_);
return v___x_279_;
}
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NameMangling(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NameMangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_registerModuleEnvExtension___auto__1 = _init_l_Lean_registerModuleEnvExtension___auto__1();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ModPkgExt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NameMangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_ModPkgExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_ModPkgExt(builtin);
}
#ifdef __cplusplus
}
#endif
