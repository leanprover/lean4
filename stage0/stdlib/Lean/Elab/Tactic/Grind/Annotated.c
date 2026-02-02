// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Annotated
// Imports: public import Lean.Elab.Command import Init.Grind.Annotated import Std.Time.Format
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2____boxed(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_initFn___lam__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Grind_initFn___lam__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grindAnnotatedExt"};
static const lean_object* l_Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 99, 164, 119, 227, 118, 220, 78)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(238, 38, 146, 109, 179, 185, 88, 172)}};
static const lean_object* l_Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value;
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_grindAnnotatedExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Grind_isGrindAnnotatedModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_isGrindAnnotatedModule___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__2_value;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__1_value;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__0;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__4;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__5;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grindAnnotated"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__2_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 145, 42, 29, 223, 69, 23, 152)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Invalid date format: "};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__4_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "\nExpected format: YYYY-MM-DD (e.g., \"2025-01-15\")"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__6_value;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__7;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Std_Time_PlainDate_parse(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__0_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__1_value),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Annotated"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(247, 131, 192, 73, 124, 172, 140, 233)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__7_value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(10, 29, 248, 13, 230, 126, 243, 77)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 170, 198, 228, 40, 117, 79, 31)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__9_value),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(221, 62, 119, 18, 251, 240, 119, 45)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__10_value),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 182, 89, 221, 110, 75, 160, 162)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__11_value),((lean_object*)&l_Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(158, 168, 97, 213, 219, 133, 223, 8)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabGrindAnnotated"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(228, 254, 54, 69, 77, 25, 58, 113)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__14_value;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_NameSet_insert(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__0(x_11, x_16, x_17, x_4);
lean_dec(x_11);
x_5 = x_18;
goto block_9;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__0(x_11, x_19, x_20, x_4);
lean_dec(x_11);
x_5 = x_21;
goto block_9;
}
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_NameSet_empty;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__1(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2__spec__1(x_1, x_10, x_11, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_initFn___lam__1_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_));
x_3 = l_Lean_registerSimplePersistentEnvExtension___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Grind_isGrindAnnotatedModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_grindAnnotatedExt;
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
lean_inc_ref(x_1);
x_8 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_6, x_3, x_1, x_5, x_7);
lean_dec(x_5);
x_9 = l_Lean_Environment_header(x_1);
lean_dec_ref(x_1);
x_10 = l_Lean_EnvironmentHeader_moduleNames(x_9);
x_11 = lean_array_get(x_7, x_10, x_2);
lean_dec_ref(x_10);
x_12 = l_Lean_NameSet_contains(x_8, x_11);
lean_dec(x_11);
lean_dec(x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_isGrindAnnotatedModule___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Tactic_Grind_isGrindAnnotatedModule(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg();
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Lean_Environment_header(x_4);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
x_9 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0;
lean_ctor_set_tag(x_4, 7);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_1);
x_10 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_10);
x_11 = l_Lean_MessageData_ofSyntax(x_7);
x_12 = l_Lean_indentD(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_1 = x_13;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_18);
x_20 = l_Lean_MessageData_ofSyntax(x_16);
x_21 = l_Lean_indentD(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0;
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(7, 2, 0);
} else {
 x_29 = x_27;
 lean_ctor_set_tag(x_29, 7);
}
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MessageData_ofSyntax(x_26);
x_33 = l_Lean_indentD(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_1 = x_34;
x_2 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__4(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Command_instInhabitedScope_default;
x_8 = l_List_head_x21___redArg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_pp_macroStack;
x_11 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__4(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0;
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_18);
lean_ctor_set(x_14, 0, x_1);
x_19 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_MessageData_ofSyntax(x_16);
x_22 = l_Lean_indentD(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5(x_23, x_2);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_MessageData_ofSyntax(x_26);
x_32 = l_Lean_indentD(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5(x_33, x_2);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3;
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__2;
x_12 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__6;
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_7);
x_10 = l_Lean_Elab_getBetterRef(x_6, x_7);
lean_dec(x_6);
x_11 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg(x_9, x_7, x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg();
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_TSyntax_getString(x_9);
lean_dec(x_9);
x_11 = l_Std_Time_PlainDate_parse(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__5;
x_14 = l_Lean_stringToMessageData(x_12);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__7;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___redArg(x_17, x_2, x_3);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_19 = l_Lean_getMainModule___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__2___redArg(x_3);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_st_ref_take(x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_grindAnnotatedExt;
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_box(0);
x_29 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_25, x_24, x_21, x_27, x_28);
lean_dec(x_27);
lean_ctor_set(x_22, 0, x_29);
x_30 = lean_st_ref_set(x_3, x_22);
x_31 = lean_box(0);
lean_ctor_set(x_19, 0, x_31);
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
x_34 = lean_ctor_get(x_22, 2);
x_35 = lean_ctor_get(x_22, 3);
x_36 = lean_ctor_get(x_22, 4);
x_37 = lean_ctor_get(x_22, 5);
x_38 = lean_ctor_get(x_22, 6);
x_39 = lean_ctor_get(x_22, 7);
x_40 = lean_ctor_get(x_22, 8);
x_41 = lean_ctor_get(x_22, 9);
x_42 = lean_ctor_get(x_22, 10);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_43 = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_grindAnnotatedExt;
x_44 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_44, 2);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_box(0);
x_47 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_43, x_32, x_21, x_45, x_46);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_33);
lean_ctor_set(x_48, 2, x_34);
lean_ctor_set(x_48, 3, x_35);
lean_ctor_set(x_48, 4, x_36);
lean_ctor_set(x_48, 5, x_37);
lean_ctor_set(x_48, 6, x_38);
lean_ctor_set(x_48, 7, x_39);
lean_ctor_set(x_48, 8, x_40);
lean_ctor_set(x_48, 9, x_41);
lean_ctor_set(x_48, 10, x_42);
x_49 = lean_st_ref_set(x_3, x_48);
x_50 = lean_box(0);
lean_ctor_set(x_19, 0, x_50);
return x_19;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_51 = lean_ctor_get(x_19, 0);
lean_inc(x_51);
lean_dec(x_19);
x_52 = lean_st_ref_take(x_3);
x_53 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 5);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 6);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_52, 7);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_52, 8);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_52, 9);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_52, 10);
lean_inc_ref(x_63);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 lean_ctor_release(x_52, 6);
 lean_ctor_release(x_52, 7);
 lean_ctor_release(x_52, 8);
 lean_ctor_release(x_52, 9);
 lean_ctor_release(x_52, 10);
 x_64 = x_52;
} else {
 lean_dec_ref(x_52);
 x_64 = lean_box(0);
}
x_65 = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_grindAnnotatedExt;
x_66 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_66, 2);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_box(0);
x_69 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_65, x_53, x_51, x_67, x_68);
lean_dec(x_67);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 11, 0);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_54);
lean_ctor_set(x_70, 2, x_55);
lean_ctor_set(x_70, 3, x_56);
lean_ctor_set(x_70, 4, x_57);
lean_ctor_set(x_70, 5, x_58);
lean_ctor_set(x_70, 6, x_59);
lean_ctor_set(x_70, 7, x_60);
lean_ctor_set(x_70, 8, x_61);
lean_ctor_set(x_70, 9, x_62);
lean_ctor_set(x_70, 10, x_63);
x_71 = lean_st_ref_set(x_3, x_70);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__3));
x_4 = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___closed__14));
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1();
return x_2;
}
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Init_Grind_Annotated(uint8_t builtin);
lean_object* initialize_Std_Time_Format(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_Annotated(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Annotated_476932661____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_grindAnnotatedExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_grindAnnotatedExt);
lean_dec_ref(res);
}l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__0___redArg___closed__0);
l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0 = _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0();
lean_mark_persistent(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__0);
l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3 = _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3();
lean_mark_persistent(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2_spec__5___closed__3);
l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2 = _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__2___redArg___closed__2);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__0 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__0);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__1);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__2 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__2);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__3);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__4 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__4);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__5 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__5);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__6 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated_spec__1_spec__1___redArg___closed__6);
l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__5 = _init_l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__5);
l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__7 = _init_l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___closed__7);
if (builtin) {res = l___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated___regBuiltin___private_Lean_Elab_Tactic_Grind_Annotated_0__Lean_Elab_Tactic_Grind_elabGrindAnnotated__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
