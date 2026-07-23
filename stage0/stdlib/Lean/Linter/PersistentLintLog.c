// Lean compiler output
// Module: Lean.Linter.PersistentLintLog
// Imports: public import Lean.Environment public import Lean.Message public import Lean.Linter.Init public import Lean.Elab.DeclarationRange
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_MessageData_isLinterMessage(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lintLogExt"};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(242, 67, 33, 35, 106, 101, 161, 119)}};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_push___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_lintLogExt;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getAllLints(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getAllLints___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO___closed__0;
LEAN_EXPORT lean_object* l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO;
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Linter_recordLints_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Linter_recordLints_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_recordLints_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_recordLints_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_recordLints(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_recordLints___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(lean_object* v___x_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed(lean_object* v___x_8_, lean_object* v___y_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(v___x_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(lean_object* v___x_11_, lean_object* v_x_12_, lean_object* v___y_13_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_11_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed(lean_object* v___x_16_, lean_object* v_x_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(v___x_16_, v_x_17_, v___y_18_);
lean_dec_ref(v___y_18_);
lean_dec_ref(v_x_17_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(lean_object* v___x_21_, lean_object* v_x_22_, lean_object* v_entries_23_){
_start:
{
lean_object* v___x_24_; 
lean_inc_ref(v_entries_23_);
v___x_24_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_24_, 0, v___x_21_);
lean_ctor_set(v___x_24_, 1, v_entries_23_);
lean_ctor_set(v___x_24_, 2, v_entries_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed(lean_object* v___x_25_, lean_object* v_x_26_, lean_object* v_entries_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(v___x_25_, v_x_26_, v_entries_27_);
lean_dec_ref(v_x_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(lean_object* v___x_29_, lean_object* v_x_30_){
_start:
{
lean_inc_ref(v___x_29_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed(lean_object* v___x_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(v___x_31_, v_x_32_);
lean_dec_ref(v_x_32_);
lean_dec_ref(v___x_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_));
v___x_67_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2____boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_();
return v_res_69_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Array_instInhabited(lean_box(0));
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg(lean_object* v_env_71_, size_t v_sz_72_, size_t v_i_73_, lean_object* v_bs_74_){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = lean_usize_dec_lt(v_i_73_, v_sz_72_);
if (v___x_75_ == 0)
{
return v_bs_74_;
}
else
{
lean_object* v___x_76_; lean_object* v_v_77_; lean_object* v___x_78_; lean_object* v_bs_x27_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; size_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; 
v___x_76_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0);
v_v_77_ = lean_array_uget(v_bs_74_, v_i_73_);
v___x_78_ = lean_unsigned_to_nat(0u);
v_bs_x27_79_ = lean_array_uset(v_bs_74_, v_i_73_, v___x_78_);
v___x_80_ = lean_usize_to_nat(v_i_73_);
v___x_81_ = l_Lean_Linter_lintLogExt;
v___x_82_ = 1;
v___x_83_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_76_, v___x_81_, v_env_71_, v___x_80_, v___x_82_);
lean_dec(v___x_80_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v_v_77_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = ((size_t)1ULL);
v___x_86_ = lean_usize_add(v_i_73_, v___x_85_);
v___x_87_ = lean_array_uset(v_bs_x27_79_, v_i_73_, v___x_84_);
v_i_73_ = v___x_86_;
v_bs_74_ = v___x_87_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg___boxed(lean_object* v_env_89_, lean_object* v_sz_90_, lean_object* v_i_91_, lean_object* v_bs_92_){
_start:
{
size_t v_sz_boxed_93_; size_t v_i_boxed_94_; lean_object* v_res_95_; 
v_sz_boxed_93_ = lean_unbox_usize(v_sz_90_);
lean_dec(v_sz_90_);
v_i_boxed_94_ = lean_unbox_usize(v_i_91_);
lean_dec(v_i_91_);
v_res_95_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg(v_env_89_, v_sz_boxed_93_, v_i_boxed_94_, v_bs_92_);
lean_dec_ref(v_env_89_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getAllLints(lean_object* v_env_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; size_t v_sz_99_; size_t v___x_100_; lean_object* v___x_101_; 
v___x_97_ = l_Lean_Environment_header(v_env_96_);
v___x_98_ = l_Lean_EnvironmentHeader_moduleNames(v___x_97_);
v_sz_99_ = lean_array_size(v___x_98_);
v___x_100_ = ((size_t)0ULL);
v___x_101_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg(v_env_96_, v_sz_99_, v___x_100_, v___x_98_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getAllLints___boxed(lean_object* v_env_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Linter_getAllLints(v_env_102_);
lean_dec_ref(v_env_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0(lean_object* v_env_104_, lean_object* v_as_105_, size_t v_sz_106_, size_t v_i_107_, lean_object* v_bs_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___redArg(v_env_104_, v_sz_106_, v_i_107_, v_bs_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0___boxed(lean_object* v_env_110_, lean_object* v_as_111_, lean_object* v_sz_112_, lean_object* v_i_113_, lean_object* v_bs_114_){
_start:
{
size_t v_sz_boxed_115_; size_t v_i_boxed_116_; lean_object* v_res_117_; 
v_sz_boxed_115_ = lean_unbox_usize(v_sz_112_);
lean_dec(v_sz_112_);
v_i_boxed_116_ = lean_unbox_usize(v_i_113_);
lean_dec(v_i_113_);
v_res_117_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Linter_getAllLints_spec__0(v_env_110_, v_as_111_, v_sz_boxed_115_, v_i_boxed_116_, v_bs_114_);
lean_dec_ref(v_as_111_);
lean_dec_ref(v_env_110_);
return v_res_117_;
}
}
static lean_object* _init_l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO___closed__0(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = l_instMonadBaseIO;
v___x_119_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_119_, 0, lean_box(0));
lean_closure_set(v___x_119_, 1, lean_box(0));
lean_closure_set(v___x_119_, 2, v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_obj_once(&l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO___closed__0, &l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO___closed__0_once, _init_l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO___closed__0);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Linter_recordLints_spec__1(lean_object* v_stx_121_, lean_object* v___y_122_){
_start:
{
uint8_t v___x_124_; lean_object* v___x_125_; 
v___x_124_ = 0;
v___x_125_ = l_Lean_Syntax_getRange_x3f(v_stx_121_, v___x_124_);
if (lean_obj_tag(v___x_125_) == 1)
{
lean_object* v_val_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_136_; 
v_val_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_136_ == 0)
{
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_val_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v_start_130_; lean_object* v_stop_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v_start_130_ = lean_ctor_get(v_val_126_, 0);
lean_inc(v_start_130_);
v_stop_131_ = lean_ctor_get(v_val_126_, 1);
lean_inc(v_stop_131_);
lean_dec(v_val_126_);
lean_inc_ref(v___y_122_);
v___x_132_ = l_Lean_DeclarationRange_ofStringPositions(v___y_122_, v_start_130_, v_stop_131_);
lean_dec(v_stop_131_);
lean_dec(v_start_130_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_132_);
v___x_134_ = v___x_128_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
else
{
lean_object* v___x_137_; 
lean_dec(v___x_125_);
v___x_137_ = lean_box(0);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Linter_recordLints_spec__1___boxed(lean_object* v_stx_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Linter_recordLints_spec__1(v_stx_138_, v___y_139_);
lean_dec_ref(v___y_139_);
lean_dec(v_stx_138_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(lean_object* v___y_142_, lean_object* v_as_143_, size_t v_i_144_, size_t v_stop_145_, lean_object* v_b_146_){
_start:
{
lean_object* v_val_149_; uint8_t v___x_153_; 
v___x_153_ = lean_usize_dec_eq(v_i_144_, v_stop_145_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v_fileName_155_; lean_object* v_pos_156_; lean_object* v_endPos_157_; uint8_t v_keepFullRange_158_; uint8_t v_severity_159_; uint8_t v_isSilent_160_; lean_object* v_caption_161_; lean_object* v_data_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_180_; 
v___x_154_ = lean_array_uget(v_as_143_, v_i_144_);
v_fileName_155_ = lean_ctor_get(v___x_154_, 0);
v_pos_156_ = lean_ctor_get(v___x_154_, 1);
v_endPos_157_ = lean_ctor_get(v___x_154_, 2);
v_keepFullRange_158_ = lean_ctor_get_uint8(v___x_154_, sizeof(void*)*5);
v_severity_159_ = lean_ctor_get_uint8(v___x_154_, sizeof(void*)*5 + 1);
v_isSilent_160_ = lean_ctor_get_uint8(v___x_154_, sizeof(void*)*5 + 2);
v_caption_161_ = lean_ctor_get(v___x_154_, 3);
v_data_162_ = lean_ctor_get(v___x_154_, 4);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_180_ == 0)
{
v___x_164_ = v___x_154_;
v_isShared_165_ = v_isSharedCheck_180_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_data_162_);
lean_inc(v_caption_161_);
lean_inc(v_endPos_157_);
lean_inc(v_pos_156_);
lean_inc(v_fileName_155_);
lean_dec(v___x_154_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_180_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
uint8_t v___x_166_; 
lean_inc(v_data_162_);
v___x_166_ = l_Lean_MessageData_isLinterMessage(v_data_162_);
if (v___x_166_ == 0)
{
lean_del_object(v___x_164_);
lean_dec(v_data_162_);
lean_dec_ref(v_caption_161_);
lean_dec(v_endPos_157_);
lean_dec_ref(v_pos_156_);
lean_dec_ref(v_fileName_155_);
v_val_149_ = v_b_146_;
goto v___jp_148_;
}
else
{
lean_object* v_kind_167_; uint8_t v___x_168_; 
v_kind_167_ = l_Lean_MessageData_kind(v_data_162_);
v___x_168_ = l_Lean_Name_isAnonymous(v_kind_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_toEnvExtension_171_; lean_object* v_asyncMode_172_; lean_object* v___x_174_; 
v___x_169_ = l_Lean_MessageData_toString(v_data_162_);
v___x_170_ = l_Lean_Linter_lintLogExt;
v_toEnvExtension_171_ = lean_ctor_get(v___x_170_, 0);
v_asyncMode_172_ = lean_ctor_get(v_toEnvExtension_171_, 2);
lean_inc_ref(v_fileName_155_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 4, v___x_169_);
v___x_174_ = v___x_164_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_fileName_155_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_pos_156_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_endPos_157_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_caption_161_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v___x_169_);
lean_ctor_set_uint8(v_reuseFailAlloc_179_, sizeof(void*)*5, v_keepFullRange_158_);
lean_ctor_set_uint8(v_reuseFailAlloc_179_, sizeof(void*)*5 + 1, v_severity_159_);
lean_ctor_set_uint8(v_reuseFailAlloc_179_, sizeof(void*)*5 + 2, v_isSilent_160_);
v___x_174_ = v_reuseFailAlloc_179_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
lean_inc(v_kind_167_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v_kind_167_);
lean_inc(v___y_142_);
v___x_176_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_176_, 0, v_kind_167_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
lean_ctor_set(v___x_176_, 2, v___y_142_);
lean_ctor_set(v___x_176_, 3, v_fileName_155_);
v___x_177_ = lean_box(0);
v___x_178_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_170_, v_b_146_, v___x_176_, v_asyncMode_172_, v___x_177_);
v_val_149_ = v___x_178_;
goto v___jp_148_;
}
}
else
{
lean_dec(v_kind_167_);
lean_del_object(v___x_164_);
lean_dec(v_data_162_);
lean_dec_ref(v_caption_161_);
lean_dec(v_endPos_157_);
lean_dec_ref(v_pos_156_);
lean_dec_ref(v_fileName_155_);
v_val_149_ = v_b_146_;
goto v___jp_148_;
}
}
}
}
else
{
lean_dec(v___y_142_);
return v_b_146_;
}
v___jp_148_:
{
size_t v___x_150_; size_t v___x_151_; 
v___x_150_ = ((size_t)1ULL);
v___x_151_ = lean_usize_add(v_i_144_, v___x_150_);
v_i_144_ = v___x_151_;
v_b_146_ = v_val_149_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1___boxed(lean_object* v___y_181_, lean_object* v_as_182_, lean_object* v_i_183_, lean_object* v_stop_184_, lean_object* v_b_185_, lean_object* v___y_186_){
_start:
{
size_t v_i_boxed_187_; size_t v_stop_boxed_188_; lean_object* v_res_189_; 
v_i_boxed_187_ = lean_unbox_usize(v_i_183_);
lean_dec(v_i_183_);
v_stop_boxed_188_ = lean_unbox_usize(v_stop_184_);
lean_dec(v_stop_184_);
v_res_189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_181_, v_as_182_, v_i_boxed_187_, v_stop_boxed_188_, v_b_185_);
lean_dec_ref(v_as_182_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(lean_object* v___y_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
lean_object* v_cs_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_cs_194_ = lean_ctor_get(v_x_191_, 0);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_array_get_size(v_cs_194_);
v___x_197_ = lean_nat_dec_lt(v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_dec(v___y_190_);
return v_x_192_;
}
else
{
uint8_t v___x_198_; 
v___x_198_ = lean_nat_dec_le(v___x_196_, v___x_196_);
if (v___x_198_ == 0)
{
if (v___x_197_ == 0)
{
lean_dec(v___y_190_);
return v_x_192_;
}
else
{
size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; 
v___x_199_ = ((size_t)0ULL);
v___x_200_ = lean_usize_of_nat(v___x_196_);
v___x_201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(v___y_190_, v_cs_194_, v___x_199_, v___x_200_, v_x_192_);
return v___x_201_;
}
}
else
{
size_t v___x_202_; size_t v___x_203_; lean_object* v___x_204_; 
v___x_202_ = ((size_t)0ULL);
v___x_203_ = lean_usize_of_nat(v___x_196_);
v___x_204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(v___y_190_, v_cs_194_, v___x_202_, v___x_203_, v_x_192_);
return v___x_204_;
}
}
}
else
{
lean_object* v_vs_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_vs_205_ = lean_ctor_get(v_x_191_, 0);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_array_get_size(v_vs_205_);
v___x_208_ = lean_nat_dec_lt(v___x_206_, v___x_207_);
if (v___x_208_ == 0)
{
lean_dec(v___y_190_);
return v_x_192_;
}
else
{
uint8_t v___x_209_; 
v___x_209_ = lean_nat_dec_le(v___x_207_, v___x_207_);
if (v___x_209_ == 0)
{
if (v___x_208_ == 0)
{
lean_dec(v___y_190_);
return v_x_192_;
}
else
{
size_t v___x_210_; size_t v___x_211_; lean_object* v___x_212_; 
v___x_210_ = ((size_t)0ULL);
v___x_211_ = lean_usize_of_nat(v___x_207_);
v___x_212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_190_, v_vs_205_, v___x_210_, v___x_211_, v_x_192_);
return v___x_212_;
}
}
else
{
size_t v___x_213_; size_t v___x_214_; lean_object* v___x_215_; 
v___x_213_ = ((size_t)0ULL);
v___x_214_ = lean_usize_of_nat(v___x_207_);
v___x_215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_190_, v_vs_205_, v___x_213_, v___x_214_, v_x_192_);
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(lean_object* v___y_216_, lean_object* v_as_217_, size_t v_i_218_, size_t v_stop_219_, lean_object* v_b_220_){
_start:
{
uint8_t v___x_222_; 
v___x_222_ = lean_usize_dec_eq(v_i_218_, v_stop_219_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; size_t v___x_225_; size_t v___x_226_; 
v___x_223_ = lean_array_uget_borrowed(v_as_217_, v_i_218_);
lean_inc(v___y_216_);
v___x_224_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(v___y_216_, v___x_223_, v_b_220_);
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_add(v_i_218_, v___x_225_);
v_i_218_ = v___x_226_;
v_b_220_ = v___x_224_;
goto _start;
}
else
{
lean_dec(v___y_216_);
return v_b_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2___boxed(lean_object* v___y_228_, lean_object* v_as_229_, lean_object* v_i_230_, lean_object* v_stop_231_, lean_object* v_b_232_, lean_object* v___y_233_){
_start:
{
size_t v_i_boxed_234_; size_t v_stop_boxed_235_; lean_object* v_res_236_; 
v_i_boxed_234_ = lean_unbox_usize(v_i_230_);
lean_dec(v_i_230_);
v_stop_boxed_235_ = lean_unbox_usize(v_stop_231_);
lean_dec(v_stop_231_);
v_res_236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(v___y_228_, v_as_229_, v_i_boxed_234_, v_stop_boxed_235_, v_b_232_);
lean_dec_ref(v_as_229_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2___boxed(lean_object* v___y_237_, lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(v___y_237_, v_x_238_, v_x_239_);
lean_dec_ref(v_x_238_);
return v_res_241_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(lean_object* v___y_243_, lean_object* v_x_244_, size_t v_x_245_, size_t v_x_246_, lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
lean_object* v_cs_249_; lean_object* v___x_250_; size_t v___x_251_; lean_object* v_j_252_; lean_object* v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_cs_249_ = lean_ctor_get(v_x_244_, 0);
v___x_250_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0);
v___x_251_ = lean_usize_shift_right(v_x_245_, v_x_246_);
v_j_252_ = lean_usize_to_nat(v___x_251_);
v___x_253_ = lean_array_get_borrowed(v___x_250_, v_cs_249_, v_j_252_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_shift_left(v___x_254_, v_x_246_);
v___x_256_ = lean_usize_sub(v___x_255_, v___x_254_);
v___x_257_ = lean_usize_land(v_x_245_, v___x_256_);
v___x_258_ = ((size_t)5ULL);
v___x_259_ = lean_usize_sub(v_x_246_, v___x_258_);
lean_inc(v___y_243_);
v___x_260_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(v___y_243_, v___x_253_, v___x_257_, v___x_259_, v_x_247_);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_add(v_j_252_, v___x_261_);
lean_dec(v_j_252_);
v___x_263_ = lean_array_get_size(v_cs_249_);
v___x_264_ = lean_nat_dec_lt(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_dec(v___x_262_);
lean_dec(v___y_243_);
return v___x_260_;
}
else
{
uint8_t v___x_265_; 
v___x_265_ = lean_nat_dec_le(v___x_263_, v___x_263_);
if (v___x_265_ == 0)
{
if (v___x_264_ == 0)
{
lean_dec(v___x_262_);
lean_dec(v___y_243_);
return v___x_260_;
}
else
{
size_t v___x_266_; size_t v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_usize_of_nat(v___x_262_);
lean_dec(v___x_262_);
v___x_267_ = lean_usize_of_nat(v___x_263_);
v___x_268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(v___y_243_, v_cs_249_, v___x_266_, v___x_267_, v___x_260_);
return v___x_268_;
}
}
else
{
size_t v___x_269_; size_t v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_usize_of_nat(v___x_262_);
lean_dec(v___x_262_);
v___x_270_ = lean_usize_of_nat(v___x_263_);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(v___y_243_, v_cs_249_, v___x_269_, v___x_270_, v___x_260_);
return v___x_271_;
}
}
}
else
{
lean_object* v_vs_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_vs_272_ = lean_ctor_get(v_x_244_, 0);
v___x_273_ = lean_usize_to_nat(v_x_245_);
v___x_274_ = lean_array_get_size(v_vs_272_);
v___x_275_ = lean_nat_dec_lt(v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
lean_dec(v___x_273_);
lean_dec(v___y_243_);
return v_x_247_;
}
else
{
uint8_t v___x_276_; 
v___x_276_ = lean_nat_dec_le(v___x_274_, v___x_274_);
if (v___x_276_ == 0)
{
if (v___x_275_ == 0)
{
lean_dec(v___x_273_);
lean_dec(v___y_243_);
return v_x_247_;
}
else
{
size_t v___x_277_; size_t v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_usize_of_nat(v___x_273_);
lean_dec(v___x_273_);
v___x_278_ = lean_usize_of_nat(v___x_274_);
v___x_279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_243_, v_vs_272_, v___x_277_, v___x_278_, v_x_247_);
return v___x_279_;
}
}
else
{
size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_usize_of_nat(v___x_273_);
lean_dec(v___x_273_);
v___x_281_ = lean_usize_of_nat(v___x_274_);
v___x_282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_243_, v_vs_272_, v___x_280_, v___x_281_, v_x_247_);
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___boxed(lean_object* v___y_283_, lean_object* v_x_284_, lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v___y_288_){
_start:
{
size_t v_x_2303__boxed_289_; size_t v_x_2304__boxed_290_; lean_object* v_res_291_; 
v_x_2303__boxed_289_ = lean_unbox_usize(v_x_285_);
lean_dec(v_x_285_);
v_x_2304__boxed_290_ = lean_unbox_usize(v_x_286_);
lean_dec(v_x_286_);
v_res_291_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(v___y_283_, v_x_284_, v_x_2303__boxed_289_, v_x_2304__boxed_290_, v_x_287_);
lean_dec_ref(v_x_284_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(lean_object* v___y_292_, lean_object* v_t_293_, lean_object* v_init_294_, lean_object* v_start_295_){
_start:
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_nat_dec_eq(v_start_295_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v_root_299_; lean_object* v_tail_300_; size_t v_shift_301_; lean_object* v_tailOff_302_; uint8_t v___x_303_; 
v_root_299_ = lean_ctor_get(v_t_293_, 0);
v_tail_300_ = lean_ctor_get(v_t_293_, 1);
v_shift_301_ = lean_ctor_get_usize(v_t_293_, 4);
v_tailOff_302_ = lean_ctor_get(v_t_293_, 3);
v___x_303_ = lean_nat_dec_le(v_tailOff_302_, v_start_295_);
if (v___x_303_ == 0)
{
size_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_304_ = lean_usize_of_nat(v_start_295_);
lean_inc(v___y_292_);
v___x_305_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(v___y_292_, v_root_299_, v___x_304_, v_shift_301_, v_init_294_);
v___x_306_ = lean_array_get_size(v_tail_300_);
v___x_307_ = lean_nat_dec_lt(v___x_297_, v___x_306_);
if (v___x_307_ == 0)
{
lean_dec(v___y_292_);
return v___x_305_;
}
else
{
uint8_t v___x_308_; 
v___x_308_ = lean_nat_dec_le(v___x_306_, v___x_306_);
if (v___x_308_ == 0)
{
if (v___x_307_ == 0)
{
lean_dec(v___y_292_);
return v___x_305_;
}
else
{
size_t v___x_309_; size_t v___x_310_; lean_object* v___x_311_; 
v___x_309_ = ((size_t)0ULL);
v___x_310_ = lean_usize_of_nat(v___x_306_);
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_292_, v_tail_300_, v___x_309_, v___x_310_, v___x_305_);
return v___x_311_;
}
}
else
{
size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; 
v___x_312_ = ((size_t)0ULL);
v___x_313_ = lean_usize_of_nat(v___x_306_);
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_292_, v_tail_300_, v___x_312_, v___x_313_, v___x_305_);
return v___x_314_;
}
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_315_ = lean_nat_sub(v_start_295_, v_tailOff_302_);
v___x_316_ = lean_array_get_size(v_tail_300_);
v___x_317_ = lean_nat_dec_lt(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
lean_dec(v___x_315_);
lean_dec(v___y_292_);
return v_init_294_;
}
else
{
uint8_t v___x_318_; 
v___x_318_ = lean_nat_dec_le(v___x_316_, v___x_316_);
if (v___x_318_ == 0)
{
if (v___x_317_ == 0)
{
lean_dec(v___x_315_);
lean_dec(v___y_292_);
return v_init_294_;
}
else
{
size_t v___x_319_; size_t v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_usize_of_nat(v___x_315_);
lean_dec(v___x_315_);
v___x_320_ = lean_usize_of_nat(v___x_316_);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_292_, v_tail_300_, v___x_319_, v___x_320_, v_init_294_);
return v___x_321_;
}
}
else
{
size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_usize_of_nat(v___x_315_);
lean_dec(v___x_315_);
v___x_323_ = lean_usize_of_nat(v___x_316_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_292_, v_tail_300_, v___x_322_, v___x_323_, v_init_294_);
return v___x_324_;
}
}
}
}
else
{
lean_object* v_root_325_; lean_object* v_tail_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_root_325_ = lean_ctor_get(v_t_293_, 0);
v_tail_326_ = lean_ctor_get(v_t_293_, 1);
lean_inc(v___y_292_);
v___x_327_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(v___y_292_, v_root_325_, v_init_294_);
v___x_328_ = lean_array_get_size(v_tail_326_);
v___x_329_ = lean_nat_dec_lt(v___x_297_, v___x_328_);
if (v___x_329_ == 0)
{
lean_dec(v___y_292_);
return v___x_327_;
}
else
{
uint8_t v___x_330_; 
v___x_330_ = lean_nat_dec_le(v___x_328_, v___x_328_);
if (v___x_330_ == 0)
{
if (v___x_329_ == 0)
{
lean_dec(v___y_292_);
return v___x_327_;
}
else
{
size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; 
v___x_331_ = ((size_t)0ULL);
v___x_332_ = lean_usize_of_nat(v___x_328_);
v___x_333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_292_, v_tail_326_, v___x_331_, v___x_332_, v___x_327_);
return v___x_333_;
}
}
else
{
size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; 
v___x_334_ = ((size_t)0ULL);
v___x_335_ = lean_usize_of_nat(v___x_328_);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_292_, v_tail_326_, v___x_334_, v___x_335_, v___x_327_);
return v___x_336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0___boxed(lean_object* v___y_337_, lean_object* v_t_338_, lean_object* v_init_339_, lean_object* v_start_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(v___y_337_, v_t_338_, v_init_339_, v_start_340_);
lean_dec(v_start_340_);
lean_dec_ref(v_t_338_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_recordLints_spec__2(lean_object* v_fileMap_343_, lean_object* v_as_344_, size_t v_i_345_, size_t v_stop_346_, lean_object* v_b_347_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = lean_usize_dec_eq(v_i_345_, v_stop_346_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v_fst_351_; lean_object* v_snd_352_; lean_object* v___y_354_; 
v___x_350_ = lean_array_uget_borrowed(v_as_344_, v_i_345_);
v_fst_351_ = lean_ctor_get(v___x_350_, 0);
v_snd_352_ = lean_ctor_get(v___x_350_, 1);
if (lean_obj_tag(v_fst_351_) == 0)
{
goto v___jp_361_;
}
else
{
lean_object* v_val_363_; lean_object* v___x_364_; 
v_val_363_ = lean_ctor_get(v_fst_351_, 0);
v___x_364_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Linter_recordLints_spec__1(v_val_363_, v_fileMap_343_);
if (lean_obj_tag(v___x_364_) == 0)
{
goto v___jp_361_;
}
else
{
lean_object* v_val_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
v_val_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_373_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_val_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_pos_369_; lean_object* v___x_371_; 
v_pos_369_ = lean_ctor_get(v_val_365_, 0);
lean_inc_ref(v_pos_369_);
lean_dec(v_val_365_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v_pos_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_pos_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
v___y_354_ = v___x_371_;
goto v___jp_353_;
}
}
}
}
v___jp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; size_t v___x_358_; size_t v___x_359_; 
lean_inc(v_snd_352_);
v___x_355_ = l_Lean_MessageLog_reportedPlusUnreported(v_snd_352_);
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(v___y_354_, v___x_355_, v_b_347_, v___x_356_);
lean_dec_ref(v___x_355_);
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_add(v_i_345_, v___x_358_);
v_i_345_ = v___x_359_;
v_b_347_ = v___x_357_;
goto _start;
}
v___jp_361_:
{
lean_object* v___x_362_; 
v___x_362_ = lean_box(0);
v___y_354_ = v___x_362_;
goto v___jp_353_;
}
}
else
{
return v_b_347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_recordLints_spec__2___boxed(lean_object* v_fileMap_374_, lean_object* v_as_375_, lean_object* v_i_376_, lean_object* v_stop_377_, lean_object* v_b_378_, lean_object* v___y_379_){
_start:
{
size_t v_i_boxed_380_; size_t v_stop_boxed_381_; lean_object* v_res_382_; 
v_i_boxed_380_ = lean_unbox_usize(v_i_376_);
lean_dec(v_i_376_);
v_stop_boxed_381_ = lean_unbox_usize(v_stop_377_);
lean_dec(v_stop_377_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_recordLints_spec__2(v_fileMap_374_, v_as_375_, v_i_boxed_380_, v_stop_boxed_381_, v_b_378_);
lean_dec_ref(v_as_375_);
lean_dec_ref(v_fileMap_374_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_recordLints(lean_object* v_fileMap_383_, lean_object* v_env_384_, lean_object* v_commandLints_385_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_array_get_size(v_commandLints_385_);
v___x_389_ = lean_nat_dec_lt(v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
return v_env_384_;
}
else
{
uint8_t v___x_390_; 
v___x_390_ = lean_nat_dec_le(v___x_388_, v___x_388_);
if (v___x_390_ == 0)
{
if (v___x_389_ == 0)
{
return v_env_384_;
}
else
{
size_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; 
v___x_391_ = ((size_t)0ULL);
v___x_392_ = lean_usize_of_nat(v___x_388_);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_recordLints_spec__2(v_fileMap_383_, v_commandLints_385_, v___x_391_, v___x_392_, v_env_384_);
return v___x_393_;
}
}
else
{
size_t v___x_394_; size_t v___x_395_; lean_object* v___x_396_; 
v___x_394_ = ((size_t)0ULL);
v___x_395_ = lean_usize_of_nat(v___x_388_);
v___x_396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_recordLints_spec__2(v_fileMap_383_, v_commandLints_385_, v___x_394_, v___x_395_, v_env_384_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_recordLints___boxed(lean_object* v_fileMap_397_, lean_object* v_env_398_, lean_object* v_commandLints_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Linter_recordLints(v_fileMap_397_, v_env_398_, v_commandLints_399_);
lean_dec_ref(v_commandLints_399_);
lean_dec_ref(v_fileMap_397_);
return v_res_401_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Message(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DeclarationRange(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_PersistentLintLog(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_3011828955____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_lintLogExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_lintLogExt);
lean_dec_ref(res);
l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO = _init_l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO();
lean_mark_persistent(l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_PersistentLintLog(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_Message(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_PersistentLintLog(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_PersistentLintLog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_PersistentLintLog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_PersistentLintLog(builtin);
}
#ifdef __cplusplus
}
#endif
