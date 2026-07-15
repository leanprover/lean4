// Lean compiler output
// Module: Lean.DocString.DeferredCheck
// Imports: public import Init.Dynamic public import Lean.Environment public import Lean.Data.OpenDecl public import Lean.Data.Options
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
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_decl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_decl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_moduleDoc_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_moduleDoc_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Doc_instInhabitedDeferredCheckSite_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instInhabitedDeferredCheckSite_default___closed__0 = (const lean_object*)&l_Lean_Doc_instInhabitedDeferredCheckSite_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedDeferredCheckSite_default = (const lean_object*)&l_Lean_Doc_instInhabitedDeferredCheckSite_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instInhabitedDeferredCheckSite = (const lean_object*)&l_Lean_Doc_instInhabitedDeferredCheckSite_default___closed__0_value;
static const lean_string_object l_Lean_Doc_instReprDeferredCheckSite_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Doc.DeferredCheckSite.decl"};
static const lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr___closed__0 = (const lean_object*)&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprDeferredCheckSite_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr___closed__1 = (const lean_object*)&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprDeferredCheckSite_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr___closed__2 = (const lean_object*)&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__2_value;
static lean_once_cell_t l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3;
static lean_once_cell_t l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4;
static const lean_string_object l_Lean_Doc_instReprDeferredCheckSite_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Doc.DeferredCheckSite.moduleDoc"};
static const lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr___closed__5 = (const lean_object*)&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__5_value;
static const lean_ctor_object l_Lean_Doc_instReprDeferredCheckSite_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr___closed__6 = (const lean_object*)&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__6_value;
static const lean_ctor_object l_Lean_Doc_instReprDeferredCheckSite_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr___closed__7 = (const lean_object*)&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instReprDeferredCheckSite___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instReprDeferredCheckSite_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instReprDeferredCheckSite___closed__0 = (const lean_object*)&l_Lean_Doc_instReprDeferredCheckSite___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instReprDeferredCheckSite = (const lean_object*)&l_Lean_Doc_instReprDeferredCheckSite___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDeferredCheckSite_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDeferredCheckSite_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instBEqDeferredCheckSite___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instBEqDeferredCheckSite_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instBEqDeferredCheckSite___closed__0 = (const lean_object*)&l_Lean_Doc_instBEqDeferredCheckSite___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instBEqDeferredCheckSite = (const lean_object*)&l_Lean_Doc_instBEqDeferredCheckSite___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__5_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "deferredCheckExt"};
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__5_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__5_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__5_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 235, 188, 137, 78, 141, 125, 233)}};
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__8_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__8_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__8_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__9_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__7_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__9_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__9_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__10_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_push___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__10_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__10_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__8_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__9_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__10_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__12_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__12_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__12_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_deferredCheckExt;
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Doc_DeferredCheckSite_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
lean_object* v_name_8_; lean_object* v___x_9_; 
v_name_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_name_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_name_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Doc_DeferredCheckSite_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_decl_elim___redArg(lean_object* v_t_22_, lean_object* v_decl_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(v_t_22_, v_decl_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_decl_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_decl_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(v_t_26_, v_decl_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_moduleDoc_elim___redArg(lean_object* v_t_30_, lean_object* v_moduleDoc_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(v_t_30_, v_moduleDoc_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_moduleDoc_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_moduleDoc_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(v_t_34_, v_moduleDoc_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_unsigned_to_nat(2u);
v___x_49_ = lean_nat_to_int(v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(1u);
v___x_51_ = lean_nat_to_int(v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr(lean_object* v_x_58_, lean_object* v_prec_59_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v_name_60_; lean_object* v___y_62_; lean_object* v___x_71_; uint8_t v___x_72_; 
v_name_60_ = lean_ctor_get(v_x_58_, 0);
lean_inc(v_name_60_);
lean_dec_ref_known(v_x_58_, 1);
v___x_71_ = lean_unsigned_to_nat(1024u);
v___x_72_ = lean_nat_dec_le(v___x_71_, v_prec_59_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3, &l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3_once, _init_l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3);
v___y_62_ = v___x_73_;
goto v___jp_61_;
}
else
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4, &l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4_once, _init_l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4);
v___y_62_ = v___x_74_;
goto v___jp_61_;
}
v___jp_61_:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_63_ = ((lean_object*)(l_Lean_Doc_instReprDeferredCheckSite_repr___closed__2));
v___x_64_ = lean_unsigned_to_nat(1024u);
v___x_65_ = l_Lean_Name_reprPrec(v_name_60_, v___x_64_);
v___x_66_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_63_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
lean_inc(v___y_62_);
v___x_67_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_67_, 0, v___y_62_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = 0;
v___x_69_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set_uint8(v___x_69_, sizeof(void*)*1, v___x_68_);
v___x_70_ = l_Repr_addAppParen(v___x_69_, v_prec_59_);
return v___x_70_;
}
}
else
{
lean_object* v_n_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_95_; 
v_n_75_ = lean_ctor_get(v_x_58_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v_x_58_);
if (v_isSharedCheck_95_ == 0)
{
v___x_77_ = v_x_58_;
v_isShared_78_ = v_isSharedCheck_95_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_n_75_);
lean_dec(v_x_58_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_95_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___y_80_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(1024u);
v___x_92_ = lean_nat_dec_le(v___x_91_, v_prec_59_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
v___x_93_ = lean_obj_once(&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3, &l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3_once, _init_l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3);
v___y_80_ = v___x_93_;
goto v___jp_79_;
}
else
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_once(&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4, &l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4_once, _init_l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4);
v___y_80_ = v___x_94_;
goto v___jp_79_;
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_81_ = ((lean_object*)(l_Lean_Doc_instReprDeferredCheckSite_repr___closed__7));
v___x_82_ = l_Nat_reprFast(v_n_75_);
if (v_isShared_78_ == 0)
{
lean_ctor_set_tag(v___x_77_, 3);
lean_ctor_set(v___x_77_, 0, v___x_82_);
v___x_84_ = v___x_77_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_82_);
v___x_84_ = v_reuseFailAlloc_90_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_85_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_81_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
lean_inc(v___y_80_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___y_80_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = 0;
v___x_88_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1, v___x_87_);
v___x_89_ = l_Repr_addAppParen(v___x_88_, v_prec_59_);
return v___x_89_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr___boxed(lean_object* v_x_96_, lean_object* v_prec_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Doc_instReprDeferredCheckSite_repr(v_x_96_, v_prec_97_);
lean_dec(v_prec_97_);
return v_res_98_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDeferredCheckSite_beq(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
if (lean_obj_tag(v_x_102_) == 0)
{
lean_object* v_name_103_; lean_object* v_name_104_; uint8_t v___x_105_; 
v_name_103_ = lean_ctor_get(v_x_101_, 0);
v_name_104_ = lean_ctor_get(v_x_102_, 0);
v___x_105_ = lean_name_eq(v_name_103_, v_name_104_);
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = 0;
return v___x_106_;
}
}
else
{
if (lean_obj_tag(v_x_102_) == 1)
{
lean_object* v_n_107_; lean_object* v_n_108_; uint8_t v___x_109_; 
v_n_107_ = lean_ctor_get(v_x_101_, 0);
v_n_108_ = lean_ctor_get(v_x_102_, 0);
v___x_109_ = lean_nat_dec_eq(v_n_107_, v_n_108_);
return v___x_109_;
}
else
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDeferredCheckSite_beq___boxed(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_Lean_Doc_instBEqDeferredCheckSite_beq(v_x_111_, v_x_112_);
lean_dec_ref(v_x_112_);
lean_dec_ref(v_x_111_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object* v___y_117_){
_start:
{
lean_inc_ref(v___y_117_);
return v___y_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(v___y_118_);
lean_dec_ref(v___y_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object* v_x_120_, lean_object* v_s_121_){
_start:
{
lean_object* v___x_122_; 
lean_inc_ref_n(v_s_121_, 2);
v___x_122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_122_, 0, v_s_121_);
lean_ctor_set(v___x_122_, 1, v_s_121_);
lean_ctor_set(v___x_122_, 2, v_s_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object* v_x_123_, lean_object* v_s_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(v_x_123_, v_s_124_);
lean_dec_ref(v_x_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object* v_x_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_box(0);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object* v_x_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(v_x_128_);
lean_dec_ref(v_x_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object* v___x_130_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object* v___x_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(v___x_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object* v___x_136_, lean_object* v_x_137_, lean_object* v___y_138_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_136_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object* v___x_141_, lean_object* v_x_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(v___x_141_, v_x_142_, v___y_143_);
lean_dec_ref(v___y_143_);
lean_dec_ref(v_x_142_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = ((lean_object*)(l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__12_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_));
v___x_177_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_();
return v_res_179_;
}
}
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_OpenDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_DeferredCheck(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_OpenDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Doc_deferredCheckExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Doc_deferredCheckExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_DeferredCheck(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Dynamic(uint8_t builtin);
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_Data_OpenDecl(uint8_t builtin);
lean_object* initialize_Lean_Data_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_DeferredCheck(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_OpenDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_DeferredCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_DeferredCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_DeferredCheck(builtin);
}
#ifdef __cplusplus
}
#endif
