// Lean compiler output
// Module: Lean.Linter.PersistentLintLog
// Imports: public import Lean.Environment public import Lean.Message public import Lean.Linter.Init
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_recordLints(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_recordLints___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(lean_object* v_as_112_, size_t v_i_113_, size_t v_stop_114_, lean_object* v_b_115_){
_start:
{
lean_object* v_val_118_; uint8_t v___x_122_; 
v___x_122_ = lean_usize_dec_eq(v_i_113_, v_stop_114_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v_fileName_124_; lean_object* v_pos_125_; lean_object* v_endPos_126_; uint8_t v_keepFullRange_127_; uint8_t v_severity_128_; uint8_t v_isSilent_129_; lean_object* v_caption_130_; lean_object* v_data_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_149_; 
v___x_123_ = lean_array_uget(v_as_112_, v_i_113_);
v_fileName_124_ = lean_ctor_get(v___x_123_, 0);
v_pos_125_ = lean_ctor_get(v___x_123_, 1);
v_endPos_126_ = lean_ctor_get(v___x_123_, 2);
v_keepFullRange_127_ = lean_ctor_get_uint8(v___x_123_, sizeof(void*)*5);
v_severity_128_ = lean_ctor_get_uint8(v___x_123_, sizeof(void*)*5 + 1);
v_isSilent_129_ = lean_ctor_get_uint8(v___x_123_, sizeof(void*)*5 + 2);
v_caption_130_ = lean_ctor_get(v___x_123_, 3);
v_data_131_ = lean_ctor_get(v___x_123_, 4);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_149_ == 0)
{
v___x_133_ = v___x_123_;
v_isShared_134_ = v_isSharedCheck_149_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_data_131_);
lean_inc(v_caption_130_);
lean_inc(v_endPos_126_);
lean_inc(v_pos_125_);
lean_inc(v_fileName_124_);
lean_dec(v___x_123_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_149_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
uint8_t v___x_135_; 
lean_inc(v_data_131_);
v___x_135_ = l_Lean_MessageData_isLinterMessage(v_data_131_);
if (v___x_135_ == 0)
{
lean_del_object(v___x_133_);
lean_dec(v_data_131_);
lean_dec_ref(v_caption_130_);
lean_dec(v_endPos_126_);
lean_dec_ref(v_pos_125_);
lean_dec_ref(v_fileName_124_);
v_val_118_ = v_b_115_;
goto v___jp_117_;
}
else
{
lean_object* v_kind_136_; uint8_t v___x_137_; 
v_kind_136_ = l_Lean_MessageData_kind(v_data_131_);
v___x_137_ = l_Lean_Name_isAnonymous(v_kind_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v_toEnvExtension_140_; lean_object* v_asyncMode_141_; lean_object* v___x_143_; 
v___x_138_ = l_Lean_MessageData_toString(v_data_131_);
v___x_139_ = l_Lean_Linter_lintLogExt;
v_toEnvExtension_140_ = lean_ctor_get(v___x_139_, 0);
v_asyncMode_141_ = lean_ctor_get(v_toEnvExtension_140_, 2);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 4, v___x_138_);
v___x_143_ = v___x_133_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_fileName_124_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_pos_125_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_endPos_126_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v_caption_130_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v___x_138_);
lean_ctor_set_uint8(v_reuseFailAlloc_148_, sizeof(void*)*5, v_keepFullRange_127_);
lean_ctor_set_uint8(v_reuseFailAlloc_148_, sizeof(void*)*5 + 1, v_severity_128_);
lean_ctor_set_uint8(v_reuseFailAlloc_148_, sizeof(void*)*5 + 2, v_isSilent_129_);
v___x_143_ = v_reuseFailAlloc_148_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
lean_inc(v_kind_136_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_kind_136_);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v_kind_136_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = lean_box(0);
v___x_147_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_139_, v_b_115_, v___x_145_, v_asyncMode_141_, v___x_146_);
v_val_118_ = v___x_147_;
goto v___jp_117_;
}
}
else
{
lean_dec(v_kind_136_);
lean_del_object(v___x_133_);
lean_dec(v_data_131_);
lean_dec_ref(v_caption_130_);
lean_dec(v_endPos_126_);
lean_dec_ref(v_pos_125_);
lean_dec_ref(v_fileName_124_);
v_val_118_ = v_b_115_;
goto v___jp_117_;
}
}
}
}
else
{
return v_b_115_;
}
v___jp_117_:
{
size_t v___x_119_; size_t v___x_120_; 
v___x_119_ = ((size_t)1ULL);
v___x_120_ = lean_usize_add(v_i_113_, v___x_119_);
v_i_113_ = v___x_120_;
v_b_115_ = v_val_118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1___boxed(lean_object* v_as_150_, lean_object* v_i_151_, lean_object* v_stop_152_, lean_object* v_b_153_, lean_object* v___y_154_){
_start:
{
size_t v_i_boxed_155_; size_t v_stop_boxed_156_; lean_object* v_res_157_; 
v_i_boxed_155_ = lean_unbox_usize(v_i_151_);
lean_dec(v_i_151_);
v_stop_boxed_156_ = lean_unbox_usize(v_stop_152_);
lean_dec(v_stop_152_);
v_res_157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_as_150_, v_i_boxed_155_, v_stop_boxed_156_, v_b_153_);
lean_dec_ref(v_as_150_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v_cs_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_cs_161_ = lean_ctor_get(v_x_158_, 0);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_array_get_size(v_cs_161_);
v___x_164_ = lean_nat_dec_lt(v___x_162_, v___x_163_);
if (v___x_164_ == 0)
{
return v_x_159_;
}
else
{
uint8_t v___x_165_; 
v___x_165_ = lean_nat_dec_le(v___x_163_, v___x_163_);
if (v___x_165_ == 0)
{
if (v___x_164_ == 0)
{
return v_x_159_;
}
else
{
size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; 
v___x_166_ = ((size_t)0ULL);
v___x_167_ = lean_usize_of_nat(v___x_163_);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(v_cs_161_, v___x_166_, v___x_167_, v_x_159_);
return v___x_168_;
}
}
else
{
size_t v___x_169_; size_t v___x_170_; lean_object* v___x_171_; 
v___x_169_ = ((size_t)0ULL);
v___x_170_ = lean_usize_of_nat(v___x_163_);
v___x_171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(v_cs_161_, v___x_169_, v___x_170_, v_x_159_);
return v___x_171_;
}
}
}
else
{
lean_object* v_vs_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_vs_172_ = lean_ctor_get(v_x_158_, 0);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_array_get_size(v_vs_172_);
v___x_175_ = lean_nat_dec_lt(v___x_173_, v___x_174_);
if (v___x_175_ == 0)
{
return v_x_159_;
}
else
{
uint8_t v___x_176_; 
v___x_176_ = lean_nat_dec_le(v___x_174_, v___x_174_);
if (v___x_176_ == 0)
{
if (v___x_175_ == 0)
{
return v_x_159_;
}
else
{
size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((size_t)0ULL);
v___x_178_ = lean_usize_of_nat(v___x_174_);
v___x_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_vs_172_, v___x_177_, v___x_178_, v_x_159_);
return v___x_179_;
}
}
else
{
size_t v___x_180_; size_t v___x_181_; lean_object* v___x_182_; 
v___x_180_ = ((size_t)0ULL);
v___x_181_ = lean_usize_of_nat(v___x_174_);
v___x_182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_vs_172_, v___x_180_, v___x_181_, v_x_159_);
return v___x_182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(lean_object* v_as_183_, size_t v_i_184_, size_t v_stop_185_, lean_object* v_b_186_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = lean_usize_dec_eq(v_i_184_, v_stop_185_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; size_t v___x_191_; size_t v___x_192_; 
v___x_189_ = lean_array_uget_borrowed(v_as_183_, v_i_184_);
v___x_190_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(v___x_189_, v_b_186_);
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_add(v_i_184_, v___x_191_);
v_i_184_ = v___x_192_;
v_b_186_ = v___x_190_;
goto _start;
}
else
{
return v_b_186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1___boxed(lean_object* v_as_194_, lean_object* v_i_195_, lean_object* v_stop_196_, lean_object* v_b_197_, lean_object* v___y_198_){
_start:
{
size_t v_i_boxed_199_; size_t v_stop_boxed_200_; lean_object* v_res_201_; 
v_i_boxed_199_ = lean_unbox_usize(v_i_195_);
lean_dec(v_i_195_);
v_stop_boxed_200_ = lean_unbox_usize(v_stop_196_);
lean_dec(v_stop_196_);
v_res_201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(v_as_194_, v_i_boxed_199_, v_stop_boxed_200_, v_b_197_);
lean_dec_ref(v_as_194_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2___boxed(lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(v_x_202_, v_x_203_);
lean_dec_ref(v_x_202_);
return v_res_205_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(lean_object* v_x_207_, size_t v_x_208_, size_t v_x_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v_cs_212_; lean_object* v___x_213_; size_t v___x_214_; lean_object* v_j_215_; lean_object* v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_cs_212_ = lean_ctor_get(v_x_207_, 0);
v___x_213_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___closed__0);
v___x_214_ = lean_usize_shift_right(v_x_208_, v_x_209_);
v_j_215_ = lean_usize_to_nat(v___x_214_);
v___x_216_ = lean_array_get_borrowed(v___x_213_, v_cs_212_, v_j_215_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_shift_left(v___x_217_, v_x_209_);
v___x_219_ = lean_usize_sub(v___x_218_, v___x_217_);
v___x_220_ = lean_usize_land(v_x_208_, v___x_219_);
v___x_221_ = ((size_t)5ULL);
v___x_222_ = lean_usize_sub(v_x_209_, v___x_221_);
v___x_223_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(v___x_216_, v___x_220_, v___x_222_, v_x_210_);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_add(v_j_215_, v___x_224_);
lean_dec(v_j_215_);
v___x_226_ = lean_array_get_size(v_cs_212_);
v___x_227_ = lean_nat_dec_lt(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_dec(v___x_225_);
return v___x_223_;
}
else
{
uint8_t v___x_228_; 
v___x_228_ = lean_nat_dec_le(v___x_226_, v___x_226_);
if (v___x_228_ == 0)
{
if (v___x_227_ == 0)
{
lean_dec(v___x_225_);
return v___x_223_;
}
else
{
size_t v___x_229_; size_t v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_usize_of_nat(v___x_225_);
lean_dec(v___x_225_);
v___x_230_ = lean_usize_of_nat(v___x_226_);
v___x_231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(v_cs_212_, v___x_229_, v___x_230_, v___x_223_);
return v___x_231_;
}
}
else
{
size_t v___x_232_; size_t v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_usize_of_nat(v___x_225_);
lean_dec(v___x_225_);
v___x_233_ = lean_usize_of_nat(v___x_226_);
v___x_234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0_spec__1(v_cs_212_, v___x_232_, v___x_233_, v___x_223_);
return v___x_234_;
}
}
}
else
{
lean_object* v_vs_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_vs_235_ = lean_ctor_get(v_x_207_, 0);
v___x_236_ = lean_usize_to_nat(v_x_208_);
v___x_237_ = lean_array_get_size(v_vs_235_);
v___x_238_ = lean_nat_dec_lt(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec(v___x_236_);
return v_x_210_;
}
else
{
uint8_t v___x_239_; 
v___x_239_ = lean_nat_dec_le(v___x_237_, v___x_237_);
if (v___x_239_ == 0)
{
if (v___x_238_ == 0)
{
lean_dec(v___x_236_);
return v_x_210_;
}
else
{
size_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_usize_of_nat(v___x_236_);
lean_dec(v___x_236_);
v___x_241_ = lean_usize_of_nat(v___x_237_);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_vs_235_, v___x_240_, v___x_241_, v_x_210_);
return v___x_242_;
}
}
else
{
size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_usize_of_nat(v___x_236_);
lean_dec(v___x_236_);
v___x_244_ = lean_usize_of_nat(v___x_237_);
v___x_245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_vs_235_, v___x_243_, v___x_244_, v_x_210_);
return v___x_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0___boxed(lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v___y_250_){
_start:
{
size_t v_x_1520__boxed_251_; size_t v_x_1521__boxed_252_; lean_object* v_res_253_; 
v_x_1520__boxed_251_ = lean_unbox_usize(v_x_247_);
lean_dec(v_x_247_);
v_x_1521__boxed_252_ = lean_unbox_usize(v_x_248_);
lean_dec(v_x_248_);
v_res_253_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(v_x_246_, v_x_1520__boxed_251_, v_x_1521__boxed_252_, v_x_249_);
lean_dec_ref(v_x_246_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(lean_object* v_t_254_, lean_object* v_init_255_, lean_object* v_start_256_){
_start:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = lean_nat_dec_eq(v_start_256_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v_root_260_; lean_object* v_tail_261_; size_t v_shift_262_; lean_object* v_tailOff_263_; uint8_t v___x_264_; 
v_root_260_ = lean_ctor_get(v_t_254_, 0);
v_tail_261_ = lean_ctor_get(v_t_254_, 1);
v_shift_262_ = lean_ctor_get_usize(v_t_254_, 4);
v_tailOff_263_ = lean_ctor_get(v_t_254_, 3);
v___x_264_ = lean_nat_dec_le(v_tailOff_263_, v_start_256_);
if (v___x_264_ == 0)
{
size_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_265_ = lean_usize_of_nat(v_start_256_);
v___x_266_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__0(v_root_260_, v___x_265_, v_shift_262_, v_init_255_);
v___x_267_ = lean_array_get_size(v_tail_261_);
v___x_268_ = lean_nat_dec_lt(v___x_258_, v___x_267_);
if (v___x_268_ == 0)
{
return v___x_266_;
}
else
{
uint8_t v___x_269_; 
v___x_269_ = lean_nat_dec_le(v___x_267_, v___x_267_);
if (v___x_269_ == 0)
{
if (v___x_268_ == 0)
{
return v___x_266_;
}
else
{
size_t v___x_270_; size_t v___x_271_; lean_object* v___x_272_; 
v___x_270_ = ((size_t)0ULL);
v___x_271_ = lean_usize_of_nat(v___x_267_);
v___x_272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_tail_261_, v___x_270_, v___x_271_, v___x_266_);
return v___x_272_;
}
}
else
{
size_t v___x_273_; size_t v___x_274_; lean_object* v___x_275_; 
v___x_273_ = ((size_t)0ULL);
v___x_274_ = lean_usize_of_nat(v___x_267_);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_tail_261_, v___x_273_, v___x_274_, v___x_266_);
return v___x_275_;
}
}
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_276_ = lean_nat_sub(v_start_256_, v_tailOff_263_);
v___x_277_ = lean_array_get_size(v_tail_261_);
v___x_278_ = lean_nat_dec_lt(v___x_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_dec(v___x_276_);
return v_init_255_;
}
else
{
uint8_t v___x_279_; 
v___x_279_ = lean_nat_dec_le(v___x_277_, v___x_277_);
if (v___x_279_ == 0)
{
if (v___x_278_ == 0)
{
lean_dec(v___x_276_);
return v_init_255_;
}
else
{
size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_usize_of_nat(v___x_276_);
lean_dec(v___x_276_);
v___x_281_ = lean_usize_of_nat(v___x_277_);
v___x_282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_tail_261_, v___x_280_, v___x_281_, v_init_255_);
return v___x_282_;
}
}
else
{
size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_usize_of_nat(v___x_276_);
lean_dec(v___x_276_);
v___x_284_ = lean_usize_of_nat(v___x_277_);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_tail_261_, v___x_283_, v___x_284_, v_init_255_);
return v___x_285_;
}
}
}
}
else
{
lean_object* v_root_286_; lean_object* v_tail_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_root_286_ = lean_ctor_get(v_t_254_, 0);
v_tail_287_ = lean_ctor_get(v_t_254_, 1);
v___x_288_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__2(v_root_286_, v_init_255_);
v___x_289_ = lean_array_get_size(v_tail_287_);
v___x_290_ = lean_nat_dec_lt(v___x_258_, v___x_289_);
if (v___x_290_ == 0)
{
return v___x_288_;
}
else
{
uint8_t v___x_291_; 
v___x_291_ = lean_nat_dec_le(v___x_289_, v___x_289_);
if (v___x_291_ == 0)
{
if (v___x_290_ == 0)
{
return v___x_288_;
}
else
{
size_t v___x_292_; size_t v___x_293_; lean_object* v___x_294_; 
v___x_292_ = ((size_t)0ULL);
v___x_293_ = lean_usize_of_nat(v___x_289_);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_tail_287_, v___x_292_, v___x_293_, v___x_288_);
return v___x_294_;
}
}
else
{
size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; 
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_289_);
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0_spec__1(v_tail_287_, v___x_295_, v___x_296_, v___x_288_);
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0___boxed(lean_object* v_t_298_, lean_object* v_init_299_, lean_object* v_start_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(v_t_298_, v_init_299_, v_start_300_);
lean_dec(v_start_300_);
lean_dec_ref(v_t_298_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_recordLints(lean_object* v_env_303_, lean_object* v_messages_304_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_304_);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_recordLints_spec__0(v___x_306_, v_env_303_, v___x_307_);
lean_dec_ref(v___x_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_recordLints___boxed(lean_object* v_env_309_, lean_object* v_messages_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Linter_recordLints(v_env_309_, v_messages_310_);
return v_res_312_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Message(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
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
res = l___private_Lean_Linter_PersistentLintLog_0__Lean_Linter_initFn_00___x40_Lean_Linter_PersistentLintLog_291324710____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_lintLogExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_lintLogExt);
lean_dec_ref(res);
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
