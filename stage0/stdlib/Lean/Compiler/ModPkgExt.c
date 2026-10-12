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
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__4(lean_object*);
static const lean_closure_object l_Lean_registerModuleEnvExtension___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerModuleEnvExtension___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerModuleEnvExtension___redArg___closed__0 = (const lean_object*)&l_Lean_registerModuleEnvExtension___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerModuleEnvExtension___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerModuleEnvExtension___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerModuleEnvExtension___redArg___closed__1 = (const lean_object*)&l_Lean_registerModuleEnvExtension___redArg___closed__1_value;
static const lean_closure_object l_Lean_registerModuleEnvExtension___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerModuleEnvExtension___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerModuleEnvExtension___redArg___closed__2 = (const lean_object*)&l_Lean_registerModuleEnvExtension___redArg___closed__2_value;
static const lean_closure_object l_Lean_registerModuleEnvExtension___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerModuleEnvExtension___redArg___lam__4, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerModuleEnvExtension___redArg___closed__3 = (const lean_object*)&l_Lean_registerModuleEnvExtension___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__0 = (const lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__0_value;
static const lean_closure_object l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__1 = (const lean_object*)&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__2;
static lean_once_cell_t l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg();
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ModuleEnvExtension_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ModuleEnvExtension_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ModPkgExt"};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 204, 27, 30, 229, 171, 155, 230)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(54, 24, 93, 111, 84, 76, 103, 70)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 103, 117, 183, 112, 214, 20, 110)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "modPkgExt"};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(179, 135, 14, 167, 209, 11, 249, 83)}};
static const lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackageByIdx_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackageByIdx_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackage_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_setModulePackage___lam__0(lean_object*, lean_object*);
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
lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__0(lean_object* v_mkInitial_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_apply_1(v_mkInitial_78_, lean_box(0));
return v___x_82_;
}
}
LEAN_EXPORT void l_Lean_registerModuleEnvExtension___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mkInitial_78_ = stack[0].m_obj;
lean_object* v_x_79_ = stack[1].m_obj;
lean_object* v_x_80_ = stack[2].m_obj;
lean_object* v_res_83_;
v_res_83_ = l_Lean_registerModuleEnvExtension___redArg___lam__0(v_mkInitial_78_, v_x_79_, v_x_80_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__0___boxed(lean_object* v_mkInitial_84_, lean_object* v_x_85_, lean_object* v_x_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_registerModuleEnvExtension___redArg___lam__0(v_mkInitial_84_, v_x_85_, v_x_86_);
lean_dec_ref(v_x_86_);
lean_dec_ref(v_x_85_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__1(lean_object* v_s_89_, lean_object* v_x_90_){
_start:
{
lean_inc(v_s_89_);
return v_s_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__1___boxed(lean_object* v_s_91_, lean_object* v_x_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_registerModuleEnvExtension___redArg___lam__1(v_s_91_, v_x_92_);
lean_dec(v_x_92_);
lean_dec(v_s_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2(lean_object* v_x_94_, lean_object* v_s_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = lean_mk_empty_array_with_capacity(v___x_96_);
v___x_98_ = lean_array_push(v___x_97_, v_s_95_);
lean_inc_ref_n(v___x_98_, 2);
v___x_99_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
lean_ctor_set(v___x_99_, 2, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2___boxed(lean_object* v_x_100_, lean_object* v_s_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_registerModuleEnvExtension___redArg___lam__2(v_x_100_, v_s_101_);
lean_dec_ref(v_x_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__3(lean_object* v_x_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(0);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__3___boxed(lean_object* v_x_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_registerModuleEnvExtension___redArg___lam__3(v_x_105_);
lean_dec(v_x_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__4(lean_object* v_s_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_mk_empty_array_with_capacity(v___x_108_);
v___x_110_ = lean_array_push(v___x_109_, v_s_107_);
return v___x_110_;
}
}
lean_object* l_Lean_registerModuleEnvExtension___redArg(lean_object* v_mkInitial_115_, lean_object* v_name_116_){
_start:
{
lean_object* v___f_118_; lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___f_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_inc_ref(v_mkInitial_115_);
v___f_118_ = lean_alloc_closure((void*)(l_Lean_registerModuleEnvExtension___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_118_, 0, v_mkInitial_115_);
v___f_119_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__0));
v___f_120_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__1));
v___f_121_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__2));
v___f_122_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__3));
v___x_123_ = lean_box(2);
v___x_124_ = lean_box(0);
v___x_125_ = 0;
v___x_126_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_126_, 0, v_name_116_);
lean_ctor_set(v___x_126_, 1, v_mkInitial_115_);
lean_ctor_set(v___x_126_, 2, v___f_118_);
lean_ctor_set(v___x_126_, 3, v___f_119_);
lean_ctor_set(v___x_126_, 4, v___f_120_);
lean_ctor_set(v___x_126_, 5, v___f_121_);
lean_ctor_set(v___x_126_, 6, v___x_123_);
lean_ctor_set(v___x_126_, 7, v___x_124_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*8, v___x_125_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*8 + 1, v___x_125_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___f_122_);
v___x_128_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT void l_Lean_registerModuleEnvExtension___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mkInitial_115_ = stack[0].m_obj;
lean_object* v_name_116_ = stack[1].m_obj;
lean_object* v_res_129_;
v_res_129_ = l_Lean_registerModuleEnvExtension___redArg(v_mkInitial_115_, v_name_116_);
stack->m_obj
 = v_res_129_;
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___boxed(lean_object* v_mkInitial_130_, lean_object* v_name_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_registerModuleEnvExtension___redArg(v_mkInitial_130_, v_name_131_);
return v_res_133_;
}
}
lean_object* l_Lean_registerModuleEnvExtension(lean_object* v_00_u03c3_134_, lean_object* v_inst_135_, lean_object* v_mkInitial_136_, lean_object* v_name_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_registerModuleEnvExtension___redArg(v_mkInitial_136_, v_name_137_);
return v___x_139_;
}
}
LEAN_EXPORT void l_Lean_registerModuleEnvExtension_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_135_ = stack[1].m_obj;
lean_object* v_mkInitial_136_ = stack[2].m_obj;
lean_object* v_name_137_ = stack[3].m_obj;
lean_object* v_res_140_;
v_res_140_ = l_Lean_registerModuleEnvExtension(lean_box(0), v_inst_135_, v_mkInitial_136_, v_name_137_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___boxed(lean_object* v_00_u03c3_141_, lean_object* v_inst_142_, lean_object* v_mkInitial_143_, lean_object* v_name_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_registerModuleEnvExtension(v_00_u03c3_141_, v_inst_142_, v_mkInitial_143_, v_name_144_);
lean_dec(v_inst_142_);
return v_res_146_;
}
}
lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0(lean_object* v_x_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT void l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_150_ = stack[0].m_obj;
lean_object* v___y_151_ = stack[1].m_obj;
lean_object* v_res_155_;
v_res_155_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0(v_x_150_, v___y_151_);
stack->m_obj
 = v_res_155_;
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___boxed(lean_object* v_x_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0(v_x_156_, v___y_157_);
lean_dec_ref(v___y_157_);
lean_dec_ref(v_x_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2(lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = ((lean_object*)(l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__1));
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___boxed(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2(v_x_167_, v_x_168_);
lean_dec(v_x_168_);
lean_dec_ref(v_x_167_);
return v_res_169_;
}
}
static lean_object* _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_172_;
}
}
static lean_object* _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3(void){
_start:
{
lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___f_173_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__2));
v___f_174_ = ((lean_object*)(l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__1));
v___f_175_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__0));
v___f_176_ = ((lean_object*)(l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__0));
v___x_177_ = lean_box(0);
v___x_178_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__2, &l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__2_once, _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__2);
v___x_179_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_177_);
lean_ctor_set(v___x_179_, 2, v___f_176_);
lean_ctor_set(v___x_179_, 3, v___f_175_);
lean_ctor_set(v___x_179_, 4, v___f_174_);
lean_ctor_set(v___x_179_, 5, v___f_173_);
return v___x_179_;
}
}
lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg(){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3, &l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3_once, _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3);
return v___x_181_;
}
}
LEAN_EXPORT void l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_182_;
v_res_182_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg();
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___boxed(lean_object* v___dummy_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg();
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1(lean_object* v_00_u03c3_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3, &l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3_once, _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3);
return v___x_186_;
}
}
lean_object* l_Lean_ModuleEnvExtension_instInhabited___redArg(){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3, &l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3_once, _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3);
return v___x_188_;
}
}
LEAN_EXPORT void l_Lean_ModuleEnvExtension_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_189_;
v_res_189_ = l_Lean_ModuleEnvExtension_instInhabited___redArg();
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___redArg___boxed(lean_object* v___dummy_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_ModuleEnvExtension_instInhabited___redArg();
return v_res_191_;
}
}
static lean_object* _init_l_Lean_ModuleEnvExtension_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_ModuleEnvExtension_instInhabited___redArg();
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited(lean_object* v_00_u03c3_193_, lean_object* v_inst_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___closed__0, &l_Lean_ModuleEnvExtension_instInhabited___closed__0_once, _init_l_Lean_ModuleEnvExtension_instInhabited___closed__0);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___boxed(lean_object* v_00_u03c3_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_ModuleEnvExtension_instInhabited(v_00_u03c3_196_, v_inst_197_);
lean_dec(v_inst_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(lean_object* v_inst_199_, lean_object* v_ext_200_, lean_object* v_env_201_, lean_object* v_idx_202_){
_start:
{
uint8_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_203_ = 0;
v___x_204_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v_inst_199_, v_ext_200_, v_env_201_, v_idx_202_, v___x_203_);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_array_get_size(v___x_204_);
v___x_207_ = lean_nat_dec_lt(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
lean_dec_ref(v___x_204_);
v___x_208_ = lean_box(0);
return v___x_208_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_array_fget(v___x_204_, v___x_205_);
lean_dec_ref(v___x_204_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg___boxed(lean_object* v_inst_211_, lean_object* v_ext_212_, lean_object* v_env_213_, lean_object* v_idx_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(v_inst_211_, v_ext_212_, v_env_213_, v_idx_214_);
lean_dec(v_idx_214_);
lean_dec_ref(v_env_213_);
lean_dec_ref(v_ext_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f(lean_object* v_00_u03c3_216_, lean_object* v_inst_217_, lean_object* v_ext_218_, lean_object* v_env_219_, lean_object* v_idx_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(v_inst_217_, v_ext_218_, v_env_219_, v_idx_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___boxed(lean_object* v_00_u03c3_222_, lean_object* v_inst_223_, lean_object* v_ext_224_, lean_object* v_env_225_, lean_object* v_idx_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f(v_00_u03c3_222_, v_inst_223_, v_ext_224_, v_env_225_, v_idx_226_);
lean_dec(v_idx_226_);
lean_dec_ref(v_env_225_);
lean_dec_ref(v_ext_224_);
return v_res_227_;
}
}
lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_(lean_object* v___x_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
return v___x_230_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_228_ = stack[0].m_obj;
lean_object* v_res_231_;
v_res_231_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_(v___x_228_);
stack->m_obj
 = v_res_231_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2____boxed(lean_object* v___x_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_(v___x_232_);
return v_res_234_;
}
}
lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___f_263_ = ((lean_object*)(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_));
v___x_264_ = ((lean_object*)(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_));
v___x_265_ = l_Lean_registerModuleEnvExtension___redArg(v___f_263_, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_266_;
v_res_266_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_();
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2____boxed(lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_();
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackageByIdx_x3f(lean_object* v_env_269_, lean_object* v_idx_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_box(0);
v___x_272_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v___x_273_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(v___x_271_, v___x_272_, v_env_269_, v_idx_270_);
if (lean_obj_tag(v___x_273_) == 0)
{
return v___x_271_;
}
else
{
lean_object* v_val_274_; 
v_val_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_val_274_);
lean_dec_ref_known(v___x_273_, 1);
return v_val_274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackageByIdx_x3f___boxed(lean_object* v_env_275_, lean_object* v_idx_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Environment_getModulePackageByIdx_x3f(v_env_275_, v_idx_276_);
lean_dec(v_idx_276_);
lean_dec_ref(v_env_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackage_x3f(lean_object* v_env_278_){
_start:
{
lean_object* v___x_279_; lean_object* v_toEnvExtension_280_; lean_object* v_asyncMode_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; 
v___x_279_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_280_ = lean_ctor_get(v___x_279_, 0);
v_asyncMode_281_ = lean_ctor_get(v_toEnvExtension_280_, 2);
v___x_282_ = lean_box(0);
v___x_283_ = lean_box(0);
v___x_284_ = 0;
v___x_285_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_282_, v___x_279_, v_env_278_, v_asyncMode_281_, v___x_283_, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setModulePackage___lam__0(lean_object* v_pkg_x3f_286_, lean_object* v_ps_287_){
_start:
{
lean_object* v_importedEntries_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
v_importedEntries_288_ = lean_ctor_get(v_ps_287_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_ps_287_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_ps_287_, 1);
lean_dec(v_unused_296_);
v___x_290_ = v_ps_287_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_importedEntries_288_);
lean_dec(v_ps_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 1, v_pkg_x3f_286_);
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_importedEntries_288_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_pkg_x3f_286_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setModulePackage(lean_object* v_pkg_x3f_297_, lean_object* v_env_298_){
_start:
{
lean_object* v___x_299_; lean_object* v_toEnvExtension_300_; lean_object* v_asyncMode_301_; uint8_t v_logWrites_302_; lean_object* v___f_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_299_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_300_ = lean_ctor_get(v___x_299_, 0);
v_asyncMode_301_ = lean_ctor_get(v_toEnvExtension_300_, 2);
v_logWrites_302_ = lean_ctor_get_uint8(v_toEnvExtension_300_, sizeof(void*)*6);
v___f_303_ = lean_alloc_closure((void*)(l_Lean_Environment_setModulePackage___lam__0), 2, 1);
lean_closure_set(v___f_303_, 0, v_pkg_x3f_297_);
v___x_304_ = lean_box(0);
v___x_305_ = 1;
if (v_logWrites_302_ == 0)
{
lean_object* v___x_306_; 
lean_inc_ref(v_toEnvExtension_300_);
v___x_306_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_300_, v_env_298_, v___f_303_, v_asyncMode_301_, v___x_304_, v___x_305_);
return v___x_306_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_inc_ref_n(v_toEnvExtension_300_, 2);
v___x_307_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_300_, v_env_298_);
lean_dec_ref(v_env_298_);
v___x_308_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_300_, v___x_307_, v___f_303_, v_asyncMode_301_, v___x_304_, v___x_305_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* lean_get_symbol_stem(lean_object* v_env_309_, lean_object* v_declName_310_){
_start:
{
lean_object* v___y_312_; lean_object* v___x_315_; 
v___x_315_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_309_, v_declName_310_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v___x_316_; lean_object* v_toEnvExtension_317_; lean_object* v_asyncMode_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; 
v___x_316_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_317_ = lean_ctor_get(v___x_316_, 0);
v_asyncMode_318_ = lean_ctor_get(v_toEnvExtension_317_, 2);
v___x_319_ = lean_box(0);
v___x_320_ = lean_box(0);
v___x_321_ = 0;
v___x_322_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_319_, v___x_316_, v_env_309_, v_asyncMode_318_, v___x_320_, v___x_321_);
v___y_312_ = v___x_322_;
goto v___jp_311_;
}
else
{
lean_object* v_val_323_; lean_object* v___x_324_; 
v_val_323_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_val_323_);
lean_dec_ref_known(v___x_315_, 1);
v___x_324_ = l_Lean_Environment_getModulePackageByIdx_x3f(v_env_309_, v_val_323_);
lean_dec(v_val_323_);
lean_dec_ref(v_env_309_);
v___y_312_ = v___x_324_;
goto v___jp_311_;
}
v___jp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = l_Lean_mkPackageSymbolPrefix(v___y_312_);
lean_dec(v___y_312_);
v___x_314_ = l_Lean_Name_mangle(v_declName_310_, v___x_313_);
return v___x_314_;
}
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NameMangling(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NameMangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_();
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
