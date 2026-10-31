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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorIdx___impl___boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__6_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__8_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__9_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__10_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__12_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__11_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__12_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___closed__12_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_deferredCheckExt;
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Doc_DeferredCheckSite_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
lean_object* v_name_7_; lean_object* v___x_8_; 
v_name_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_name_7_);
lean_dec_ref(v_t_5_);
v___x_8_ = lean_apply_1(v_k_6_, v_name_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Doc_DeferredCheckSite_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_decl_elim___redArg(lean_object* v_t_21_, lean_object* v_decl_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(v_t_21_, v_decl_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_decl_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_decl_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(v_t_25_, v_decl_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_moduleDoc_elim___redArg(lean_object* v_t_29_, lean_object* v_moduleDoc_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(v_t_29_, v_moduleDoc_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DeferredCheckSite_moduleDoc_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_moduleDoc_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Doc_DeferredCheckSite_ctorElim___redArg(v_t_33_, v_moduleDoc_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(2u);
v___x_48_ = lean_nat_to_int(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_nat_to_int(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr(lean_object* v_x_57_, lean_object* v_prec_58_){
_start:
{
if (lean_obj_tag(v_x_57_) == 0)
{
lean_object* v_name_59_; lean_object* v___y_61_; lean_object* v___x_70_; uint8_t v___x_71_; 
v_name_59_ = lean_ctor_get(v_x_57_, 0);
lean_inc(v_name_59_);
lean_dec_ref_known(v_x_57_, 1);
v___x_70_ = lean_unsigned_to_nat(1024u);
v___x_71_ = lean_nat_dec_le(v___x_70_, v_prec_58_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
v___x_72_ = lean_obj_once(&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3, &l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3_once, _init_l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3);
v___y_61_ = v___x_72_;
goto v___jp_60_;
}
else
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4, &l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4_once, _init_l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4);
v___y_61_ = v___x_73_;
goto v___jp_60_;
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_62_ = ((lean_object*)(l_Lean_Doc_instReprDeferredCheckSite_repr___closed__2));
v___x_63_ = lean_unsigned_to_nat(1024u);
v___x_64_ = l_Lean_Name_reprPrec(v_name_59_, v___x_63_);
v___x_65_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_62_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
lean_inc(v___y_61_);
v___x_66_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_66_, 0, v___y_61_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = 0;
v___x_68_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set_uint8(v___x_68_, sizeof(void*)*1, v___x_67_);
v___x_69_ = l_Repr_addAppParen(v___x_68_, v_prec_58_);
return v___x_69_;
}
}
else
{
lean_object* v_n_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_94_; 
v_n_74_ = lean_ctor_get(v_x_57_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_94_ == 0)
{
v___x_76_ = v_x_57_;
v_isShared_77_ = v_isSharedCheck_94_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_n_74_);
lean_dec(v_x_57_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_94_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___y_79_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(1024u);
v___x_91_ = lean_nat_dec_le(v___x_90_, v_prec_58_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
v___x_92_ = lean_obj_once(&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3, &l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3_once, _init_l_Lean_Doc_instReprDeferredCheckSite_repr___closed__3);
v___y_79_ = v___x_92_;
goto v___jp_78_;
}
else
{
lean_object* v___x_93_; 
v___x_93_ = lean_obj_once(&l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4, &l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4_once, _init_l_Lean_Doc_instReprDeferredCheckSite_repr___closed__4);
v___y_79_ = v___x_93_;
goto v___jp_78_;
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_80_ = ((lean_object*)(l_Lean_Doc_instReprDeferredCheckSite_repr___closed__7));
v___x_81_ = l_Nat_reprFast(v_n_74_);
if (v_isShared_77_ == 0)
{
lean_ctor_set_tag(v___x_76_, 3);
lean_ctor_set(v___x_76_, 0, v___x_81_);
v___x_83_ = v___x_76_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_89_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_84_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_80_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
lean_inc(v___y_79_);
v___x_85_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_85_, 0, v___y_79_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = 0;
v___x_87_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*1, v___x_86_);
v___x_88_ = l_Repr_addAppParen(v___x_87_, v_prec_58_);
return v___x_88_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDeferredCheckSite_repr___boxed(lean_object* v_x_95_, lean_object* v_prec_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Doc_instReprDeferredCheckSite_repr(v_x_95_, v_prec_96_);
lean_dec(v_prec_96_);
return v_res_97_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqDeferredCheckSite_beq(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
if (lean_obj_tag(v_x_101_) == 0)
{
lean_object* v_name_102_; lean_object* v_name_103_; uint8_t v___x_104_; 
v_name_102_ = lean_ctor_get(v_x_100_, 0);
v_name_103_ = lean_ctor_get(v_x_101_, 0);
v___x_104_ = lean_name_eq(v_name_102_, v_name_103_);
return v___x_104_;
}
else
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
else
{
if (lean_obj_tag(v_x_101_) == 1)
{
lean_object* v_n_106_; lean_object* v_n_107_; uint8_t v___x_108_; 
v_n_106_ = lean_ctor_get(v_x_100_, 0);
v_n_107_ = lean_ctor_get(v_x_101_, 0);
v___x_108_ = lean_nat_dec_eq(v_n_106_, v_n_107_);
return v___x_108_;
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqDeferredCheckSite_beq___boxed(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Lean_Doc_instBEqDeferredCheckSite_beq(v_x_110_, v_x_111_);
lean_dec_ref(v_x_111_);
lean_dec_ref(v_x_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object* v___y_116_){
_start:
{
lean_inc_ref(v___y_116_);
return v___y_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__0_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(v___y_117_);
lean_dec_ref(v___y_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object* v_x_119_, lean_object* v_s_120_){
_start:
{
lean_object* v___x_121_; 
lean_inc_ref_n(v_s_120_, 2);
v___x_121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_121_, 0, v_s_120_);
lean_ctor_set(v___x_121_, 1, v_s_120_);
lean_ctor_set(v___x_121_, 2, v_s_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object* v_x_122_, lean_object* v_s_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__1_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(v_x_122_, v_s_123_);
lean_dec_ref(v_x_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object* v_x_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(0);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object* v_x_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__2_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(v_x_127_);
lean_dec_ref(v_x_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object* v___x_129_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object* v___x_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__3_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(v___x_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(lean_object* v___x_135_, lean_object* v_x_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_135_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2____boxed(lean_object* v___x_140_, lean_object* v_x_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_DocString_DeferredCheck_0__Lean_Doc_initFn___lam__4_00___x40_Lean_DocString_DeferredCheck_4160150515____hygCtx___hyg_2_(v___x_140_, v_x_141_, v___y_142_);
lean_dec_ref(v___y_142_);
lean_dec_ref(v_x_141_);
return v_res_144_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_DeferredCheck(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
