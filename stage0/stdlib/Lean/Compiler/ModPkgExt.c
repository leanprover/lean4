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
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2(lean_object* v_x_93_, lean_object* v_s_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = lean_mk_empty_array_with_capacity(v___x_95_);
v___x_97_ = lean_array_push(v___x_96_, v_s_94_);
lean_inc_ref_n(v___x_97_, 2);
v___x_98_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
lean_ctor_set(v___x_98_, 2, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2___boxed(lean_object* v_x_99_, lean_object* v_s_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_registerModuleEnvExtension___redArg___lam__2(v_x_99_, v_s_100_);
lean_dec_ref(v_x_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__3(lean_object* v_x_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_box(0);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__3___boxed(lean_object* v_x_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_registerModuleEnvExtension___redArg___lam__3(v_x_104_);
lean_dec(v_x_104_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__4(lean_object* v_s_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_unsigned_to_nat(1u);
v___x_108_ = lean_mk_empty_array_with_capacity(v___x_107_);
v___x_109_ = lean_array_push(v___x_108_, v_s_106_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg(lean_object* v_mkInitial_114_, lean_object* v_name_115_){
_start:
{
lean_object* v___f_117_; lean_object* v___f_118_; lean_object* v___f_119_; lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
lean_inc_ref(v_mkInitial_114_);
v___f_117_ = lean_alloc_closure((void*)(l_Lean_registerModuleEnvExtension___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_117_, 0, v_mkInitial_114_);
v___f_118_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__0));
v___f_119_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__1));
v___f_120_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__2));
v___f_121_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__3));
v___x_122_ = lean_box(2);
v___x_123_ = lean_box(0);
v___x_124_ = 0;
v___x_125_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_125_, 0, v_name_115_);
lean_ctor_set(v___x_125_, 1, v_mkInitial_114_);
lean_ctor_set(v___x_125_, 2, v___f_117_);
lean_ctor_set(v___x_125_, 3, v___f_118_);
lean_ctor_set(v___x_125_, 4, v___f_119_);
lean_ctor_set(v___x_125_, 5, v___f_120_);
lean_ctor_set(v___x_125_, 6, v___x_122_);
lean_ctor_set(v___x_125_, 7, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*8, v___x_124_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*8 + 1, v___x_124_);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___f_121_);
v___x_127_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___boxed(lean_object* v_mkInitial_128_, lean_object* v_name_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_registerModuleEnvExtension___redArg(v_mkInitial_128_, v_name_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension(lean_object* v_00_u03c3_132_, lean_object* v_inst_133_, lean_object* v_mkInitial_134_, lean_object* v_name_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_registerModuleEnvExtension___redArg(v_mkInitial_134_, v_name_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___boxed(lean_object* v_00_u03c3_138_, lean_object* v_inst_139_, lean_object* v_mkInitial_140_, lean_object* v_name_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_registerModuleEnvExtension(v_00_u03c3_138_, v_inst_139_, v_mkInitial_140_, v_name_141_);
lean_dec(v_inst_139_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0(lean_object* v_x_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___closed__1));
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0___boxed(lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__0(v_x_152_, v___y_153_);
lean_dec_ref(v___y_153_);
lean_dec_ref(v_x_152_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2(lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___closed__1));
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2___boxed(lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___lam__2(v_x_163_, v_x_164_);
lean_dec(v_x_164_);
lean_dec_ref(v_x_163_);
return v_res_165_;
}
}
static lean_object* _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_168_;
}
}
static lean_object* _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3(void){
_start:
{
lean_object* v___f_169_; lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___f_169_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__2));
v___f_170_ = ((lean_object*)(l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__1));
v___f_171_ = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__0));
v___f_172_ = ((lean_object*)(l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__0));
v___x_173_ = lean_box(0);
v___x_174_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__2, &l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__2_once, _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__2);
v___x_175_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
lean_ctor_set(v___x_175_, 2, v___f_172_);
lean_ctor_set(v___x_175_, 3, v___f_171_);
lean_ctor_set(v___x_175_, 4, v___f_170_);
lean_ctor_set(v___x_175_, 5, v___f_169_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg(){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3, &l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3_once, _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___boxed(lean_object* v___dummy_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg();
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___aux__1(lean_object* v_00_u03c3_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3, &l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3_once, _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___redArg(){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3, &l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3_once, _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___redArg___closed__3);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___redArg___boxed(lean_object* v___dummy_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_ModuleEnvExtension_instInhabited___redArg();
return v_res_185_;
}
}
static lean_object* _init_l_Lean_ModuleEnvExtension_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_ModuleEnvExtension_instInhabited___redArg();
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited(lean_object* v_00_u03c3_187_, lean_object* v_inst_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_Lean_ModuleEnvExtension_instInhabited___closed__0, &l_Lean_ModuleEnvExtension_instInhabited___closed__0_once, _init_l_Lean_ModuleEnvExtension_instInhabited___closed__0);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___boxed(lean_object* v_00_u03c3_190_, lean_object* v_inst_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_ModuleEnvExtension_instInhabited(v_00_u03c3_190_, v_inst_191_);
lean_dec(v_inst_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(lean_object* v_inst_193_, lean_object* v_ext_194_, lean_object* v_env_195_, lean_object* v_idx_196_){
_start:
{
uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_197_ = 0;
v___x_198_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v_inst_193_, v_ext_194_, v_env_195_, v_idx_196_, v___x_197_);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_array_get_size(v___x_198_);
v___x_201_ = lean_nat_dec_lt(v___x_199_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
lean_dec_ref(v___x_198_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_array_fget(v___x_198_, v___x_199_);
lean_dec_ref(v___x_198_);
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg___boxed(lean_object* v_inst_205_, lean_object* v_ext_206_, lean_object* v_env_207_, lean_object* v_idx_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(v_inst_205_, v_ext_206_, v_env_207_, v_idx_208_);
lean_dec(v_idx_208_);
lean_dec_ref(v_env_207_);
lean_dec_ref(v_ext_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f(lean_object* v_00_u03c3_210_, lean_object* v_inst_211_, lean_object* v_ext_212_, lean_object* v_env_213_, lean_object* v_idx_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(v_inst_211_, v_ext_212_, v_env_213_, v_idx_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___boxed(lean_object* v_00_u03c3_216_, lean_object* v_inst_217_, lean_object* v_ext_218_, lean_object* v_env_219_, lean_object* v_idx_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f(v_00_u03c3_216_, v_inst_217_, v_ext_218_, v_env_219_, v_idx_220_);
lean_dec(v_idx_220_);
lean_dec_ref(v_env_219_);
lean_dec_ref(v_ext_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_(lean_object* v___x_222_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2____boxed(lean_object* v___x_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_(v___x_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___f_256_ = ((lean_object*)(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_));
v___x_257_ = ((lean_object*)(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_));
v___x_258_ = l_Lean_registerModuleEnvExtension___redArg(v___f_256_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2____boxed(lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_();
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackageByIdx_x3f(lean_object* v_env_261_, lean_object* v_idx_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_box(0);
v___x_264_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v___x_265_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(v___x_263_, v___x_264_, v_env_261_, v_idx_262_);
if (lean_obj_tag(v___x_265_) == 0)
{
return v___x_263_;
}
else
{
lean_object* v_val_266_; 
v_val_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_val_266_);
lean_dec_ref_known(v___x_265_, 1);
return v_val_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackageByIdx_x3f___boxed(lean_object* v_env_267_, lean_object* v_idx_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Environment_getModulePackageByIdx_x3f(v_env_267_, v_idx_268_);
lean_dec(v_idx_268_);
lean_dec_ref(v_env_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackage_x3f(lean_object* v_env_270_){
_start:
{
lean_object* v___x_271_; lean_object* v_toEnvExtension_272_; lean_object* v_asyncMode_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; 
v___x_271_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_272_ = lean_ctor_get(v___x_271_, 0);
v_asyncMode_273_ = lean_ctor_get(v_toEnvExtension_272_, 2);
v___x_274_ = lean_box(0);
v___x_275_ = lean_box(0);
v___x_276_ = 0;
v___x_277_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_274_, v___x_271_, v_env_270_, v_asyncMode_273_, v___x_275_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setModulePackage___lam__0(lean_object* v_pkg_x3f_278_, lean_object* v_ps_279_){
_start:
{
lean_object* v_importedEntries_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
v_importedEntries_280_ = lean_ctor_get(v_ps_279_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v_ps_279_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v_ps_279_, 1);
lean_dec(v_unused_288_);
v___x_282_ = v_ps_279_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_importedEntries_280_);
lean_dec(v_ps_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v_pkg_x3f_278_);
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_importedEntries_280_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_pkg_x3f_278_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setModulePackage(lean_object* v_pkg_x3f_289_, lean_object* v_env_290_){
_start:
{
lean_object* v___x_291_; lean_object* v_toEnvExtension_292_; lean_object* v_asyncMode_293_; uint8_t v_logWrites_294_; lean_object* v___f_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_291_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_292_ = lean_ctor_get(v___x_291_, 0);
v_asyncMode_293_ = lean_ctor_get(v_toEnvExtension_292_, 2);
v_logWrites_294_ = lean_ctor_get_uint8(v_toEnvExtension_292_, sizeof(void*)*6);
v___f_295_ = lean_alloc_closure((void*)(l_Lean_Environment_setModulePackage___lam__0), 2, 1);
lean_closure_set(v___f_295_, 0, v_pkg_x3f_289_);
v___x_296_ = lean_box(0);
v___x_297_ = 1;
if (v_logWrites_294_ == 0)
{
lean_object* v___x_298_; 
lean_inc_ref(v_toEnvExtension_292_);
v___x_298_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_292_, v_env_290_, v___f_295_, v_asyncMode_293_, v___x_296_, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_inc_ref_n(v_toEnvExtension_292_, 2);
v___x_299_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_292_, v_env_290_);
lean_dec_ref(v_env_290_);
v___x_300_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_292_, v___x_299_, v___f_295_, v_asyncMode_293_, v___x_296_, v___x_297_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* lean_get_symbol_stem(lean_object* v_env_301_, lean_object* v_declName_302_){
_start:
{
lean_object* v___y_304_; lean_object* v___x_307_; 
v___x_307_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_301_, v_declName_302_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; lean_object* v_toEnvExtension_309_; lean_object* v_asyncMode_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; 
v___x_308_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_309_ = lean_ctor_get(v___x_308_, 0);
v_asyncMode_310_ = lean_ctor_get(v_toEnvExtension_309_, 2);
v___x_311_ = lean_box(0);
v___x_312_ = lean_box(0);
v___x_313_ = 0;
v___x_314_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_311_, v___x_308_, v_env_301_, v_asyncMode_310_, v___x_312_, v___x_313_);
v___y_304_ = v___x_314_;
goto v___jp_303_;
}
else
{
lean_object* v_val_315_; lean_object* v___x_316_; 
v_val_315_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_val_315_);
lean_dec_ref_known(v___x_307_, 1);
v___x_316_ = l_Lean_Environment_getModulePackageByIdx_x3f(v_env_301_, v_val_315_);
lean_dec(v_val_315_);
lean_dec_ref(v_env_301_);
v___y_304_ = v___x_316_;
goto v___jp_303_;
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = l_Lean_mkPackageSymbolPrefix(v___y_304_);
lean_dec(v___y_304_);
v___x_306_ = l_Lean_Name_mangle(v_declName_302_, v___x_305_);
return v___x_306_;
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
