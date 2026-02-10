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
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__0 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__1 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__1_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__2 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__2_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__3 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__4 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__5;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__6 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__7 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__7_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__8 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__9 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__9_value;
static const lean_string_object l_Lean_registerModuleEnvExtension___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__10 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_registerModuleEnvExtension___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__11 = (const lean_object*)&l_Lean_registerModuleEnvExtension___auto__1___closed__11_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__12;
lean_object* lean_array_push(lean_object*, lean_object*);
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
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__18;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__19;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__20;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__21;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__22;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__23;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__24;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__25;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__26;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__27;
static lean_object* l_Lean_registerModuleEnvExtension___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___auto__1;
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__1___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2___closed__0;
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
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackage_x3f(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_setModulePackage(lean_object*, lean_object*);
lean_object* l_Lean_mkPackageSymbolPrefix(lean_object*);
lean_object* l_Lean_Name_mangle(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_symbol_stem(lean_object*, lean_object*);
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__10));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_registerModuleEnvExtension___auto__1___closed__12;
x_2 = l_Lean_registerModuleEnvExtension___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__17));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_registerModuleEnvExtension___auto__1___closed__18;
x_2 = l_Lean_registerModuleEnvExtension___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_registerModuleEnvExtension___auto__1___closed__19;
x_2 = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__16));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_registerModuleEnvExtension___auto__1___closed__20;
x_2 = l_Lean_registerModuleEnvExtension___auto__1___closed__13;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_registerModuleEnvExtension___auto__1___closed__21;
x_2 = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_registerModuleEnvExtension___auto__1___closed__22;
x_2 = l_Lean_registerModuleEnvExtension___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_registerModuleEnvExtension___auto__1___closed__23;
x_2 = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_registerModuleEnvExtension___auto__1___closed__24;
x_2 = l_Lean_registerModuleEnvExtension___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_registerModuleEnvExtension___auto__1___closed__25;
x_2 = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_registerModuleEnvExtension___auto__1___closed__26;
x_2 = l_Lean_registerModuleEnvExtension___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_registerModuleEnvExtension___auto__1___closed__27;
x_2 = ((lean_object*)(l_Lean_registerModuleEnvExtension___auto__1___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_registerModuleEnvExtension___auto__1___closed__28;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_registerModuleEnvExtension___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_registerModuleEnvExtension___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_registerModuleEnvExtension___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_registerModuleEnvExtension___redArg___lam__2___closed__0;
x_5 = lean_array_push(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_registerModuleEnvExtension___redArg___lam__2(x_1, x_2, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_registerModuleEnvExtension___redArg___lam__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___lam__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_registerModuleEnvExtension___redArg___lam__2___closed__0;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_registerModuleEnvExtension___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__0));
x_6 = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__1));
x_7 = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__2));
x_8 = ((lean_object*)(l_Lean_registerModuleEnvExtension___redArg___closed__3));
x_9 = lean_box(2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_5);
lean_ctor_set(x_11, 4, x_6);
lean_ctor_set(x_11, 5, x_7);
lean_ctor_set(x_11, 6, x_9);
lean_ctor_set(x_11, 7, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_registerModuleEnvExtension___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_registerModuleEnvExtension___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_registerModuleEnvExtension___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_registerModuleEnvExtension(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ModuleEnvExtension_instInhabited___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_instInhabited___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ModuleEnvExtension_instInhabited(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = 0;
x_6 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_6);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget(x_6, x_7);
lean_dec_ref(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ModuleEnvExtension_getStateByIdx_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_));
x_4 = l_Lean_registerModuleEnvExtension___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackageByIdx_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
x_5 = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(x_3, x_4, x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
return x_3;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackageByIdx_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_getModulePackageByIdx_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModulePackage_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = l_Lean_PersistentEnvExtension_getState___redArg(x_5, x_2, x_1, x_4, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setModulePackage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
x_4 = l_Lean_PersistentEnvExtension_setState___redArg(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_get_symbol_stem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; 
x_7 = l_Lean_Environment_getModuleIdxFor_x3f(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = l_Lean_PersistentEnvExtension_getState___redArg(x_11, x_8, x_1, x_10, x_12);
lean_dec(x_10);
x_3 = x_13;
goto block_6;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec_ref(x_7);
x_15 = l_Lean_Environment_getModulePackageByIdx_x3f(x_1, x_14);
lean_dec(x_14);
lean_dec_ref(x_1);
x_3 = x_15;
goto block_6;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_mkPackageSymbolPrefix(x_3);
lean_dec(x_3);
x_5 = l_Lean_Name_mangle(x_2, x_4);
return x_5;
}
}
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
l_Lean_registerModuleEnvExtension___auto__1___closed__5 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__5();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__5);
l_Lean_registerModuleEnvExtension___auto__1___closed__12 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__12();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__12);
l_Lean_registerModuleEnvExtension___auto__1___closed__13 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__13();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__13);
l_Lean_registerModuleEnvExtension___auto__1___closed__18 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__18();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__18);
l_Lean_registerModuleEnvExtension___auto__1___closed__19 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__19();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__19);
l_Lean_registerModuleEnvExtension___auto__1___closed__20 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__20();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__20);
l_Lean_registerModuleEnvExtension___auto__1___closed__21 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__21();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__21);
l_Lean_registerModuleEnvExtension___auto__1___closed__22 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__22();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__22);
l_Lean_registerModuleEnvExtension___auto__1___closed__23 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__23();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__23);
l_Lean_registerModuleEnvExtension___auto__1___closed__24 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__24();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__24);
l_Lean_registerModuleEnvExtension___auto__1___closed__25 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__25();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__25);
l_Lean_registerModuleEnvExtension___auto__1___closed__26 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__26();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__26);
l_Lean_registerModuleEnvExtension___auto__1___closed__27 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__27();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__27);
l_Lean_registerModuleEnvExtension___auto__1___closed__28 = _init_l_Lean_registerModuleEnvExtension___auto__1___closed__28();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1___closed__28);
l_Lean_registerModuleEnvExtension___auto__1 = _init_l_Lean_registerModuleEnvExtension___auto__1();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1);
l_Lean_registerModuleEnvExtension___redArg___lam__2___closed__0 = _init_l_Lean_registerModuleEnvExtension___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lean_registerModuleEnvExtension___redArg___lam__2___closed__0);
res = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_1097734621____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
