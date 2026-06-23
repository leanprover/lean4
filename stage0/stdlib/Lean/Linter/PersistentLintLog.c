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
lean_object* l_Array_instInhabited(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_MessageData_isLinterMessage(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lintLogExt"};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(242, 67, 33, 35, 106, 101, 161, 119)}};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_push___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_lintLogExt;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getAllLints(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getAllLints___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(lean_object* v___y_1_){
_start:
{
lean_inc_ref(v___y_1_);
return v___y_1_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(lean_object* v___y_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(v___y_2_);
lean_dec_ref(v___y_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(lean_object* v_x_4_, lean_object* v_s_5_){
_start:
{
lean_object* v___x_6_; 
lean_inc_ref_n(v_s_5_, 2);
v___x_6_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6_, 0, v_s_5_);
lean_ctor_set(v___x_6_, 1, v_s_5_);
lean_ctor_set(v___x_6_, 2, v_s_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(lean_object* v_x_7_, lean_object* v_s_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(v_x_7_, v_s_8_);
lean_dec_ref(v_x_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(lean_object* v_x_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(v_x_12_);
lean_dec_ref(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(lean_object* v___x_14_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(lean_object* v___x_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(v___x_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(lean_object* v___x_20_, lean_object* v_x_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_24_, 0, v___x_20_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(lean_object* v___x_25_, lean_object* v_x_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(v___x_25_, v_x_26_, v___y_27_);
lean_dec_ref(v___y_27_);
lean_dec_ref(v_x_26_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = ((lean_object*)(l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_));
v___x_61_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_();
return v_res_63_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Array_instInhabited(lean_box(0));
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg(lean_object* v_env_65_, lean_object* v_as_66_, lean_object* v_i_67_, lean_object* v_j_68_, lean_object* v_bs_69_){
_start:
{
lean_object* v_zero_70_; uint8_t v_isZero_71_; 
v_zero_70_ = lean_unsigned_to_nat(0u);
v_isZero_71_ = lean_nat_dec_eq(v_i_67_, v_zero_70_);
if (v_isZero_71_ == 1)
{
lean_dec(v_j_68_);
lean_dec(v_i_67_);
return v_bs_69_;
}
else
{
lean_object* v___x_72_; lean_object* v_one_73_; lean_object* v_n_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_72_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___closed__0);
v_one_73_ = lean_unsigned_to_nat(1u);
v_n_74_ = lean_nat_sub(v_i_67_, v_one_73_);
lean_dec(v_i_67_);
v___x_75_ = lean_array_fget_borrowed(v_as_66_, v_j_68_);
v___x_76_ = l_Lean_Linter_lintLogExt;
v___x_77_ = 0;
v___x_78_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_72_, v___x_76_, v_env_65_, v_j_68_, v___x_77_);
lean_inc(v___x_75_);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_75_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_nat_add(v_j_68_, v_one_73_);
lean_dec(v_j_68_);
v___x_81_ = lean_array_push(v_bs_69_, v___x_79_);
v_i_67_ = v_n_74_;
v_j_68_ = v___x_80_;
v_bs_69_ = v___x_81_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg___boxed(lean_object* v_env_83_, lean_object* v_as_84_, lean_object* v_i_85_, lean_object* v_j_86_, lean_object* v_bs_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg(v_env_83_, v_as_84_, v_i_85_, v_j_86_, v_bs_87_);
lean_dec_ref(v_as_84_);
lean_dec_ref(v_env_83_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getAllLints(lean_object* v_env_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_90_ = l_Lean_Environment_header(v_env_89_);
v___x_91_ = l_Lean_EnvironmentHeader_moduleNames(v___x_90_);
v___x_92_ = lean_array_get_size(v___x_91_);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_mk_empty_array_with_capacity(v___x_92_);
v___x_95_ = l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg(v_env_89_, v___x_91_, v___x_92_, v___x_93_, v___x_94_);
lean_dec_ref(v___x_91_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getAllLints___boxed(lean_object* v_env_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Linter_getAllLints(v_env_96_);
lean_dec_ref(v_env_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0(lean_object* v_env_98_, lean_object* v_as_99_, lean_object* v_i_100_, lean_object* v_j_101_, lean_object* v_inv_102_, lean_object* v_bs_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___redArg(v_env_98_, v_as_99_, v_i_100_, v_j_101_, v_bs_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0___boxed(lean_object* v_env_105_, lean_object* v_as_106_, lean_object* v_i_107_, lean_object* v_j_108_, lean_object* v_inv_109_, lean_object* v_bs_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Array_mapFinIdxM_map___at___00Lean_Linter_getAllLints_spec__0(v_env_105_, v_as_106_, v_i_107_, v_j_108_, v_inv_109_, v_bs_110_);
lean_dec_ref(v_as_106_);
lean_dec_ref(v_env_105_);
return v_res_111_;
}
}
static lean_object* _init_l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO___closed__0(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = l_instMonadBaseIO;
v___x_113_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_113_, 0, lean_box(0));
lean_closure_set(v___x_113_, 1, lean_box(0));
lean_closure_set(v___x_113_, 2, v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO___closed__0, &l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO___closed__0_once, _init_l_Lean_Linter_instMonadFileMapReaderTFileMapBaseIO___closed__0);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Linter_recordLints_spec__1(lean_object* v_stx_115_, lean_object* v___y_116_){
_start:
{
uint8_t v___x_118_; lean_object* v___x_119_; 
v___x_118_ = 0;
v___x_119_ = l_Lean_Syntax_getRange_x3f(v_stx_115_, v___x_118_);
if (lean_obj_tag(v___x_119_) == 1)
{
lean_object* v_val_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_130_; 
v_val_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_130_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_val_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v_start_124_; lean_object* v_stop_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
v_start_124_ = lean_ctor_get(v_val_120_, 0);
lean_inc(v_start_124_);
v_stop_125_ = lean_ctor_get(v_val_120_, 1);
lean_inc(v_stop_125_);
lean_dec(v_val_120_);
lean_inc_ref(v___y_116_);
v___x_126_ = l_Lean_DeclarationRange_ofStringPositions(v___y_116_, v_start_124_, v_stop_125_);
lean_dec(v_stop_125_);
lean_dec(v_start_124_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_126_);
v___x_128_ = v___x_122_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v___x_131_; 
lean_dec(v___x_119_);
v___x_131_ = lean_box(0);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Linter_recordLints_spec__1___boxed(lean_object* v_stx_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Linter_recordLints_spec__1(v_stx_132_, v___y_133_);
lean_dec_ref(v___y_133_);
lean_dec(v_stx_132_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(lean_object* v___y_136_, lean_object* v_as_137_, size_t v_i_138_, size_t v_stop_139_, lean_object* v_b_140_){
_start:
{
lean_object* v_val_143_; uint8_t v___x_147_; 
v___x_147_ = lean_usize_dec_eq(v_i_138_, v_stop_139_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v_fileName_149_; lean_object* v_pos_150_; lean_object* v_endPos_151_; uint8_t v_keepFullRange_152_; uint8_t v_severity_153_; uint8_t v_isSilent_154_; lean_object* v_caption_155_; lean_object* v_data_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_174_; 
v___x_148_ = lean_array_uget(v_as_137_, v_i_138_);
v_fileName_149_ = lean_ctor_get(v___x_148_, 0);
v_pos_150_ = lean_ctor_get(v___x_148_, 1);
v_endPos_151_ = lean_ctor_get(v___x_148_, 2);
v_keepFullRange_152_ = lean_ctor_get_uint8(v___x_148_, sizeof(void*)*5);
v_severity_153_ = lean_ctor_get_uint8(v___x_148_, sizeof(void*)*5 + 1);
v_isSilent_154_ = lean_ctor_get_uint8(v___x_148_, sizeof(void*)*5 + 2);
v_caption_155_ = lean_ctor_get(v___x_148_, 3);
v_data_156_ = lean_ctor_get(v___x_148_, 4);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_174_ == 0)
{
v___x_158_ = v___x_148_;
v_isShared_159_ = v_isSharedCheck_174_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_data_156_);
lean_inc(v_caption_155_);
lean_inc(v_endPos_151_);
lean_inc(v_pos_150_);
lean_inc(v_fileName_149_);
lean_dec(v___x_148_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_174_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
uint8_t v___x_160_; 
lean_inc(v_data_156_);
v___x_160_ = l_Lean_MessageData_isLinterMessage(v_data_156_);
if (v___x_160_ == 0)
{
lean_del_object(v___x_158_);
lean_dec(v_data_156_);
lean_dec_ref(v_caption_155_);
lean_dec(v_endPos_151_);
lean_dec_ref(v_pos_150_);
lean_dec_ref(v_fileName_149_);
v_val_143_ = v_b_140_;
goto v___jp_142_;
}
else
{
lean_object* v_kind_161_; uint8_t v___x_162_; 
v_kind_161_ = l_Lean_MessageData_kind(v_data_156_);
v___x_162_ = l_Lean_Name_isAnonymous(v_kind_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_toEnvExtension_165_; lean_object* v_asyncMode_166_; lean_object* v___x_168_; 
v___x_163_ = l_Lean_MessageData_toString(v_data_156_);
v___x_164_ = l_Lean_Linter_lintLogExt;
v_toEnvExtension_165_ = lean_ctor_get(v___x_164_, 0);
v_asyncMode_166_ = lean_ctor_get(v_toEnvExtension_165_, 2);
lean_inc_ref(v_fileName_149_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 4, v___x_163_);
v___x_168_ = v___x_158_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_fileName_149_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_pos_150_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_endPos_151_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v_caption_155_);
lean_ctor_set(v_reuseFailAlloc_173_, 4, v___x_163_);
lean_ctor_set_uint8(v_reuseFailAlloc_173_, sizeof(void*)*5, v_keepFullRange_152_);
lean_ctor_set_uint8(v_reuseFailAlloc_173_, sizeof(void*)*5 + 1, v_severity_153_);
lean_ctor_set_uint8(v_reuseFailAlloc_173_, sizeof(void*)*5 + 2, v_isSilent_154_);
v___x_168_ = v_reuseFailAlloc_173_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_inc(v_kind_161_);
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_kind_161_);
lean_inc(v___y_136_);
v___x_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_170_, 0, v_kind_161_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
lean_ctor_set(v___x_170_, 2, v___y_136_);
lean_ctor_set(v___x_170_, 3, v_fileName_149_);
v___x_171_ = lean_box(0);
v___x_172_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_164_, v_b_140_, v___x_170_, v_asyncMode_166_, v___x_171_);
v_val_143_ = v___x_172_;
goto v___jp_142_;
}
}
else
{
lean_dec(v_kind_161_);
lean_del_object(v___x_158_);
lean_dec(v_data_156_);
lean_dec_ref(v_caption_155_);
lean_dec(v_endPos_151_);
lean_dec_ref(v_pos_150_);
lean_dec_ref(v_fileName_149_);
v_val_143_ = v_b_140_;
goto v___jp_142_;
}
}
}
}
else
{
lean_dec(v___y_136_);
return v_b_140_;
}
v___jp_142_:
{
size_t v___x_144_; size_t v___x_145_; 
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_add(v_i_138_, v___x_144_);
v_i_138_ = v___x_145_;
v_b_140_ = v_val_143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1___boxed(lean_object* v___y_175_, lean_object* v_as_176_, lean_object* v_i_177_, lean_object* v_stop_178_, lean_object* v_b_179_, lean_object* v___y_180_){
_start:
{
size_t v_i_boxed_181_; size_t v_stop_boxed_182_; lean_object* v_res_183_; 
v_i_boxed_181_ = lean_unbox_usize(v_i_177_);
lean_dec(v_i_177_);
v_stop_boxed_182_ = lean_unbox_usize(v_stop_178_);
lean_dec(v_stop_178_);
v_res_183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_175_, v_as_176_, v_i_boxed_181_, v_stop_boxed_182_, v_b_179_);
lean_dec_ref(v_as_176_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(lean_object* v___y_184_, lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
if (lean_obj_tag(v_x_185_) == 0)
{
lean_object* v_cs_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_cs_188_ = lean_ctor_get(v_x_185_, 0);
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_array_get_size(v_cs_188_);
v___x_191_ = lean_nat_dec_lt(v___x_189_, v___x_190_);
if (v___x_191_ == 0)
{
lean_dec(v___y_184_);
return v_x_186_;
}
else
{
uint8_t v___x_192_; 
v___x_192_ = lean_nat_dec_le(v___x_190_, v___x_190_);
if (v___x_192_ == 0)
{
if (v___x_191_ == 0)
{
lean_dec(v___y_184_);
return v_x_186_;
}
else
{
size_t v___x_193_; size_t v___x_194_; lean_object* v___x_195_; 
v___x_193_ = ((size_t)0ULL);
v___x_194_ = lean_usize_of_nat(v___x_190_);
v___x_195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(v___y_184_, v_cs_188_, v___x_193_, v___x_194_, v_x_186_);
return v___x_195_;
}
}
else
{
size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; 
v___x_196_ = ((size_t)0ULL);
v___x_197_ = lean_usize_of_nat(v___x_190_);
v___x_198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(v___y_184_, v_cs_188_, v___x_196_, v___x_197_, v_x_186_);
return v___x_198_;
}
}
}
else
{
lean_object* v_vs_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_vs_199_ = lean_ctor_get(v_x_185_, 0);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_array_get_size(v_vs_199_);
v___x_202_ = lean_nat_dec_lt(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_dec(v___y_184_);
return v_x_186_;
}
else
{
uint8_t v___x_203_; 
v___x_203_ = lean_nat_dec_le(v___x_201_, v___x_201_);
if (v___x_203_ == 0)
{
if (v___x_202_ == 0)
{
lean_dec(v___y_184_);
return v_x_186_;
}
else
{
size_t v___x_204_; size_t v___x_205_; lean_object* v___x_206_; 
v___x_204_ = ((size_t)0ULL);
v___x_205_ = lean_usize_of_nat(v___x_201_);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_184_, v_vs_199_, v___x_204_, v___x_205_, v_x_186_);
return v___x_206_;
}
}
else
{
size_t v___x_207_; size_t v___x_208_; lean_object* v___x_209_; 
v___x_207_ = ((size_t)0ULL);
v___x_208_ = lean_usize_of_nat(v___x_201_);
v___x_209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_184_, v_vs_199_, v___x_207_, v___x_208_, v_x_186_);
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(lean_object* v___y_210_, lean_object* v_as_211_, size_t v_i_212_, size_t v_stop_213_, lean_object* v_b_214_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = lean_usize_dec_eq(v_i_212_, v_stop_213_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; size_t v___x_219_; size_t v___x_220_; 
v___x_217_ = lean_array_uget_borrowed(v_as_211_, v_i_212_);
lean_inc(v___y_210_);
v___x_218_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(v___y_210_, v___x_217_, v_b_214_);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_add(v_i_212_, v___x_219_);
v_i_212_ = v___x_220_;
v_b_214_ = v___x_218_;
goto _start;
}
else
{
lean_dec(v___y_210_);
return v_b_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2___boxed(lean_object* v___y_222_, lean_object* v_as_223_, lean_object* v_i_224_, lean_object* v_stop_225_, lean_object* v_b_226_, lean_object* v___y_227_){
_start:
{
size_t v_i_boxed_228_; size_t v_stop_boxed_229_; lean_object* v_res_230_; 
v_i_boxed_228_ = lean_unbox_usize(v_i_224_);
lean_dec(v_i_224_);
v_stop_boxed_229_ = lean_unbox_usize(v_stop_225_);
lean_dec(v_stop_225_);
v_res_230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(v___y_222_, v_as_223_, v_i_boxed_228_, v_stop_boxed_229_, v_b_226_);
lean_dec_ref(v_as_223_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2___boxed(lean_object* v___y_231_, lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(v___y_231_, v_x_232_, v_x_233_);
lean_dec_ref(v_x_232_);
return v_res_235_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(lean_object* v___y_237_, lean_object* v_x_238_, size_t v_x_239_, size_t v_x_240_, lean_object* v_x_241_){
_start:
{
if (lean_obj_tag(v_x_238_) == 0)
{
lean_object* v_cs_243_; lean_object* v___x_244_; size_t v___x_245_; lean_object* v_j_246_; lean_object* v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_cs_243_ = lean_ctor_get(v_x_238_, 0);
v___x_244_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0);
v___x_245_ = lean_usize_shift_right(v_x_239_, v_x_240_);
v_j_246_ = lean_usize_to_nat(v___x_245_);
v___x_247_ = lean_array_get_borrowed(v___x_244_, v_cs_243_, v_j_246_);
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_shift_left(v___x_248_, v_x_240_);
v___x_250_ = lean_usize_sub(v___x_249_, v___x_248_);
v___x_251_ = lean_usize_land(v_x_239_, v___x_250_);
v___x_252_ = ((size_t)5ULL);
v___x_253_ = lean_usize_sub(v_x_240_, v___x_252_);
lean_inc(v___y_237_);
v___x_254_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(v___y_237_, v___x_247_, v___x_251_, v___x_253_, v_x_241_);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v_j_246_, v___x_255_);
lean_dec(v_j_246_);
v___x_257_ = lean_array_get_size(v_cs_243_);
v___x_258_ = lean_nat_dec_lt(v___x_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_dec(v___x_256_);
lean_dec(v___y_237_);
return v___x_254_;
}
else
{
uint8_t v___x_259_; 
v___x_259_ = lean_nat_dec_le(v___x_257_, v___x_257_);
if (v___x_259_ == 0)
{
if (v___x_258_ == 0)
{
lean_dec(v___x_256_);
lean_dec(v___y_237_);
return v___x_254_;
}
else
{
size_t v___x_260_; size_t v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_usize_of_nat(v___x_256_);
lean_dec(v___x_256_);
v___x_261_ = lean_usize_of_nat(v___x_257_);
v___x_262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(v___y_237_, v_cs_243_, v___x_260_, v___x_261_, v___x_254_);
return v___x_262_;
}
}
else
{
size_t v___x_263_; size_t v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_usize_of_nat(v___x_256_);
lean_dec(v___x_256_);
v___x_264_ = lean_usize_of_nat(v___x_257_);
v___x_265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__2(v___y_237_, v_cs_243_, v___x_263_, v___x_264_, v___x_254_);
return v___x_265_;
}
}
}
else
{
lean_object* v_vs_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_vs_266_ = lean_ctor_get(v_x_238_, 0);
v___x_267_ = lean_usize_to_nat(v_x_239_);
v___x_268_ = lean_array_get_size(v_vs_266_);
v___x_269_ = lean_nat_dec_lt(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_dec(v___x_267_);
lean_dec(v___y_237_);
return v_x_241_;
}
else
{
uint8_t v___x_270_; 
v___x_270_ = lean_nat_dec_le(v___x_268_, v___x_268_);
if (v___x_270_ == 0)
{
if (v___x_269_ == 0)
{
lean_dec(v___x_267_);
lean_dec(v___y_237_);
return v_x_241_;
}
else
{
size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_usize_of_nat(v___x_267_);
lean_dec(v___x_267_);
v___x_272_ = lean_usize_of_nat(v___x_268_);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_237_, v_vs_266_, v___x_271_, v___x_272_, v_x_241_);
return v___x_273_;
}
}
else
{
size_t v___x_274_; size_t v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_usize_of_nat(v___x_267_);
lean_dec(v___x_267_);
v___x_275_ = lean_usize_of_nat(v___x_268_);
v___x_276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_237_, v_vs_266_, v___x_274_, v___x_275_, v_x_241_);
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___boxed(lean_object* v___y_277_, lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v___y_282_){
_start:
{
size_t v_x_2303__boxed_283_; size_t v_x_2304__boxed_284_; lean_object* v_res_285_; 
v_x_2303__boxed_283_ = lean_unbox_usize(v_x_279_);
lean_dec(v_x_279_);
v_x_2304__boxed_284_ = lean_unbox_usize(v_x_280_);
lean_dec(v_x_280_);
v_res_285_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(v___y_277_, v_x_278_, v_x_2303__boxed_283_, v_x_2304__boxed_284_, v_x_281_);
lean_dec_ref(v_x_278_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(lean_object* v___y_286_, lean_object* v_t_287_, lean_object* v_init_288_, lean_object* v_start_289_){
_start:
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_nat_dec_eq(v_start_289_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v_root_293_; lean_object* v_tail_294_; size_t v_shift_295_; lean_object* v_tailOff_296_; uint8_t v___x_297_; 
v_root_293_ = lean_ctor_get(v_t_287_, 0);
v_tail_294_ = lean_ctor_get(v_t_287_, 1);
v_shift_295_ = lean_ctor_get_usize(v_t_287_, 4);
v_tailOff_296_ = lean_ctor_get(v_t_287_, 3);
v___x_297_ = lean_nat_dec_le(v_tailOff_296_, v_start_289_);
if (v___x_297_ == 0)
{
size_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_298_ = lean_usize_of_nat(v_start_289_);
lean_inc(v___y_286_);
v___x_299_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(v___y_286_, v_root_293_, v___x_298_, v_shift_295_, v_init_288_);
v___x_300_ = lean_array_get_size(v_tail_294_);
v___x_301_ = lean_nat_dec_lt(v___x_291_, v___x_300_);
if (v___x_301_ == 0)
{
lean_dec(v___y_286_);
return v___x_299_;
}
else
{
uint8_t v___x_302_; 
v___x_302_ = lean_nat_dec_le(v___x_300_, v___x_300_);
if (v___x_302_ == 0)
{
if (v___x_301_ == 0)
{
lean_dec(v___y_286_);
return v___x_299_;
}
else
{
size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; 
v___x_303_ = ((size_t)0ULL);
v___x_304_ = lean_usize_of_nat(v___x_300_);
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_286_, v_tail_294_, v___x_303_, v___x_304_, v___x_299_);
return v___x_305_;
}
}
else
{
size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; 
v___x_306_ = ((size_t)0ULL);
v___x_307_ = lean_usize_of_nat(v___x_300_);
v___x_308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_286_, v_tail_294_, v___x_306_, v___x_307_, v___x_299_);
return v___x_308_;
}
}
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_309_ = lean_nat_sub(v_start_289_, v_tailOff_296_);
v___x_310_ = lean_array_get_size(v_tail_294_);
v___x_311_ = lean_nat_dec_lt(v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
lean_dec(v___x_309_);
lean_dec(v___y_286_);
return v_init_288_;
}
else
{
uint8_t v___x_312_; 
v___x_312_ = lean_nat_dec_le(v___x_310_, v___x_310_);
if (v___x_312_ == 0)
{
if (v___x_311_ == 0)
{
lean_dec(v___x_309_);
lean_dec(v___y_286_);
return v_init_288_;
}
else
{
size_t v___x_313_; size_t v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_usize_of_nat(v___x_309_);
lean_dec(v___x_309_);
v___x_314_ = lean_usize_of_nat(v___x_310_);
v___x_315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_286_, v_tail_294_, v___x_313_, v___x_314_, v_init_288_);
return v___x_315_;
}
}
else
{
size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_usize_of_nat(v___x_309_);
lean_dec(v___x_309_);
v___x_317_ = lean_usize_of_nat(v___x_310_);
v___x_318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_286_, v_tail_294_, v___x_316_, v___x_317_, v_init_288_);
return v___x_318_;
}
}
}
}
else
{
lean_object* v_root_319_; lean_object* v_tail_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v_root_319_ = lean_ctor_get(v_t_287_, 0);
v_tail_320_ = lean_ctor_get(v_t_287_, 1);
lean_inc(v___y_286_);
v___x_321_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(v___y_286_, v_root_319_, v_init_288_);
v___x_322_ = lean_array_get_size(v_tail_320_);
v___x_323_ = lean_nat_dec_lt(v___x_291_, v___x_322_);
if (v___x_323_ == 0)
{
lean_dec(v___y_286_);
return v___x_321_;
}
else
{
uint8_t v___x_324_; 
v___x_324_ = lean_nat_dec_le(v___x_322_, v___x_322_);
if (v___x_324_ == 0)
{
if (v___x_323_ == 0)
{
lean_dec(v___y_286_);
return v___x_321_;
}
else
{
size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; 
v___x_325_ = ((size_t)0ULL);
v___x_326_ = lean_usize_of_nat(v___x_322_);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_286_, v_tail_320_, v___x_325_, v___x_326_, v___x_321_);
return v___x_327_;
}
}
else
{
size_t v___x_328_; size_t v___x_329_; lean_object* v___x_330_; 
v___x_328_ = ((size_t)0ULL);
v___x_329_ = lean_usize_of_nat(v___x_322_);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v___y_286_, v_tail_320_, v___x_328_, v___x_329_, v___x_321_);
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0___boxed(lean_object* v___y_331_, lean_object* v_t_332_, lean_object* v_init_333_, lean_object* v_start_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(v___y_331_, v_t_332_, v_init_333_, v_start_334_);
lean_dec(v_start_334_);
lean_dec_ref(v_t_332_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_recordLints_spec__2(lean_object* v_fileMap_337_, lean_object* v_as_338_, size_t v_i_339_, size_t v_stop_340_, lean_object* v_b_341_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = lean_usize_dec_eq(v_i_339_, v_stop_340_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v_fst_345_; lean_object* v_snd_346_; lean_object* v___y_348_; 
v___x_344_ = lean_array_uget_borrowed(v_as_338_, v_i_339_);
v_fst_345_ = lean_ctor_get(v___x_344_, 0);
v_snd_346_ = lean_ctor_get(v___x_344_, 1);
if (lean_obj_tag(v_fst_345_) == 0)
{
goto v___jp_355_;
}
else
{
lean_object* v_val_357_; lean_object* v___x_358_; 
v_val_357_ = lean_ctor_get(v_fst_345_, 0);
v___x_358_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Linter_recordLints_spec__1(v_val_357_, v_fileMap_337_);
if (lean_obj_tag(v___x_358_) == 0)
{
goto v___jp_355_;
}
else
{
lean_object* v_val_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_367_; 
v_val_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_367_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_val_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v_pos_363_; lean_object* v___x_365_; 
v_pos_363_ = lean_ctor_get(v_val_359_, 0);
lean_inc_ref(v_pos_363_);
lean_dec(v_val_359_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v_pos_363_);
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_pos_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
v___y_348_ = v___x_365_;
goto v___jp_347_;
}
}
}
}
v___jp_347_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; size_t v___x_352_; size_t v___x_353_; 
lean_inc(v_snd_346_);
v___x_349_ = l_Lean_MessageLog_reportedPlusUnreported(v_snd_346_);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(v___y_348_, v___x_349_, v_b_341_, v___x_350_);
lean_dec_ref(v___x_349_);
v___x_352_ = ((size_t)1ULL);
v___x_353_ = lean_usize_add(v_i_339_, v___x_352_);
v_i_339_ = v___x_353_;
v_b_341_ = v___x_351_;
goto _start;
}
v___jp_355_:
{
lean_object* v___x_356_; 
v___x_356_ = lean_box(0);
v___y_348_ = v___x_356_;
goto v___jp_347_;
}
}
else
{
return v_b_341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_recordLints_spec__2___boxed(lean_object* v_fileMap_368_, lean_object* v_as_369_, lean_object* v_i_370_, lean_object* v_stop_371_, lean_object* v_b_372_, lean_object* v___y_373_){
_start:
{
size_t v_i_boxed_374_; size_t v_stop_boxed_375_; lean_object* v_res_376_; 
v_i_boxed_374_ = lean_unbox_usize(v_i_370_);
lean_dec(v_i_370_);
v_stop_boxed_375_ = lean_unbox_usize(v_stop_371_);
lean_dec(v_stop_371_);
v_res_376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_recordLints_spec__2(v_fileMap_368_, v_as_369_, v_i_boxed_374_, v_stop_boxed_375_, v_b_372_);
lean_dec_ref(v_as_369_);
lean_dec_ref(v_fileMap_368_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_recordLints(lean_object* v_fileMap_377_, lean_object* v_env_378_, lean_object* v_commandLints_379_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = lean_array_get_size(v_commandLints_379_);
v___x_383_ = lean_nat_dec_lt(v___x_381_, v___x_382_);
if (v___x_383_ == 0)
{
return v_env_378_;
}
else
{
uint8_t v___x_384_; 
v___x_384_ = lean_nat_dec_le(v___x_382_, v___x_382_);
if (v___x_384_ == 0)
{
if (v___x_383_ == 0)
{
return v_env_378_;
}
else
{
size_t v___x_385_; size_t v___x_386_; lean_object* v___x_387_; 
v___x_385_ = ((size_t)0ULL);
v___x_386_ = lean_usize_of_nat(v___x_382_);
v___x_387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_recordLints_spec__2(v_fileMap_377_, v_commandLints_379_, v___x_385_, v___x_386_, v_env_378_);
return v___x_387_;
}
}
else
{
size_t v___x_388_; size_t v___x_389_; lean_object* v___x_390_; 
v___x_388_ = ((size_t)0ULL);
v___x_389_ = lean_usize_of_nat(v___x_382_);
v___x_390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_recordLints_spec__2(v_fileMap_377_, v_commandLints_379_, v___x_388_, v___x_389_, v_env_378_);
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_recordLints___boxed(lean_object* v_fileMap_391_, lean_object* v_env_392_, lean_object* v_commandLints_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Linter_recordLints(v_fileMap_391_, v_env_392_, v_commandLints_393_);
lean_dec_ref(v_commandLints_393_);
lean_dec_ref(v_fileMap_391_);
return v_res_395_;
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
res = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_();
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
