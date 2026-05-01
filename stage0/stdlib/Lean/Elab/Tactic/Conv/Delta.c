// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Delta
// Imports: public import Lean.Elab.Tactic.Delta public import Lean.Elab.Tactic.Conv.Basic
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
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_evalDelta___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "delta"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 217, 17, 26, 4, 182, 95, 121)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalDelta"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(249, 242, 203, 140, 225, 25, 96, 185)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(16) << 1) | 1)),((lean_object*)(((size_t)(18) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__0_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__1_value),((lean_object*)(((size_t)(18) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__3_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__4_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg(v_e_30_, v___y_36_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___boxed(lean_object* v_e_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1(v_e_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_51_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2(lean_object* v_a_52_, lean_object* v_as_53_, size_t v_i_54_, size_t v_stop_55_){
_start:
{
uint8_t v___x_56_; 
v___x_56_ = lean_usize_dec_eq(v_i_54_, v_stop_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_array_uget_borrowed(v_as_53_, v_i_54_);
v___x_58_ = lean_name_eq(v_a_52_, v___x_57_);
if (v___x_58_ == 0)
{
size_t v___x_59_; size_t v___x_60_; 
v___x_59_ = ((size_t)1ULL);
v___x_60_ = lean_usize_add(v_i_54_, v___x_59_);
v_i_54_ = v___x_60_;
goto _start;
}
else
{
return v___x_58_;
}
}
else
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2___boxed(lean_object* v_a_63_, lean_object* v_as_64_, lean_object* v_i_65_, lean_object* v_stop_66_){
_start:
{
size_t v_i_boxed_67_; size_t v_stop_boxed_68_; uint8_t v_res_69_; lean_object* v_r_70_; 
v_i_boxed_67_ = lean_unbox_usize(v_i_65_);
lean_dec(v_i_65_);
v_stop_boxed_68_ = lean_unbox_usize(v_stop_66_);
lean_dec(v_stop_66_);
v_res_69_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2(v_a_63_, v_as_64_, v_i_boxed_67_, v_stop_boxed_68_);
lean_dec_ref(v_as_64_);
lean_dec(v_a_63_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2(lean_object* v_as_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_array_get_size(v_as_71_);
v___x_75_ = lean_nat_dec_lt(v___x_73_, v___x_74_);
if (v___x_75_ == 0)
{
return v___x_75_;
}
else
{
if (v___x_75_ == 0)
{
return v___x_75_;
}
else
{
size_t v___x_76_; size_t v___x_77_; uint8_t v___x_78_; 
v___x_76_ = ((size_t)0ULL);
v___x_77_ = lean_usize_of_nat(v___x_74_);
v___x_78_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2(v_a_72_, v_as_71_, v___x_76_, v___x_77_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2___boxed(lean_object* v_as_79_, lean_object* v_a_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2(v_as_79_, v_a_80_);
lean_dec(v_a_80_);
lean_dec_ref(v_as_79_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_evalDelta___lam__0(lean_object* v_a_83_, lean_object* v___y_84_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2(v_a_83_, v___y_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta___lam__0___boxed(lean_object* v_a_86_, lean_object* v___y_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Lean_Elab_Tactic_Conv_evalDelta___lam__0(v_a_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v_a_86_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(size_t v_sz_90_, size_t v_i_91_, lean_object* v_bs_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = lean_usize_dec_lt(v_i_91_, v_sz_90_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v_bs_92_);
return v___x_97_;
}
else
{
lean_object* v_v_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_v_98_ = lean_array_uget_borrowed(v_bs_92_, v_i_91_);
v___x_99_ = lean_box(0);
lean_inc(v_v_98_);
v___x_100_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_v_98_, v___x_99_, v___y_93_, v___y_94_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_102_; lean_object* v_bs_x27_103_; size_t v___x_104_; size_t v___x_105_; lean_object* v___x_106_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
lean_dec_ref(v___x_100_);
v___x_102_ = lean_unsigned_to_nat(0u);
v_bs_x27_103_ = lean_array_uset(v_bs_92_, v_i_91_, v___x_102_);
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_add(v_i_91_, v___x_104_);
v___x_106_ = lean_array_uset(v_bs_x27_103_, v_i_91_, v_a_101_);
v_i_91_ = v___x_105_;
v_bs_92_ = v___x_106_;
goto _start;
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
lean_dec_ref(v_bs_92_);
v_a_108_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_100_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_100_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg___boxed(lean_object* v_sz_116_, lean_object* v_i_117_, lean_object* v_bs_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
size_t v_sz_boxed_122_; size_t v_i_boxed_123_; lean_object* v_res_124_; 
v_sz_boxed_122_ = lean_unbox_usize(v_sz_116_);
lean_dec(v_sz_116_);
v_i_boxed_123_ = lean_unbox_usize(v_i_117_);
lean_dec(v_i_117_);
v_res_124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(v_sz_boxed_122_, v_i_boxed_123_, v_bs_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta___lam__1(lean_object* v___x_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
size_t v_sz_135_; size_t v___x_136_; lean_object* v___x_137_; 
v_sz_135_ = lean_array_size(v___x_125_);
v___x_136_ = ((size_t)0ULL);
v___x_137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(v_sz_135_, v___x_136_, v___x_125_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_139_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref(v___x_137_);
v___x_139_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_127_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_141_; lean_object* v_a_142_; lean_object* v___f_143_; uint8_t v___x_144_; lean_object* v___x_145_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_140_);
lean_dec_ref(v___x_139_);
v___x_141_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg(v_a_140_, v___y_131_);
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_a_142_);
lean_dec_ref(v___x_141_);
v___f_143_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDelta___lam__0___boxed), 2, 1);
lean_closure_set(v___f_143_, 0, v_a_138_);
v___x_144_ = 0;
v___x_145_ = l_Lean_Meta_deltaExpand(v_a_142_, v___f_143_, v___x_144_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_147_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_a_146_);
lean_dec_ref(v___x_145_);
v___x_147_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_146_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
return v___x_147_;
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_a_148_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_145_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_145_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec(v_a_138_);
v_a_156_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_139_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_139_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
v_a_164_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_137_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_137_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta___lam__1___boxed(lean_object* v___x_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Elab_Tactic_Conv_evalDelta___lam__1(v___x_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta(lean_object* v_stx_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___f_196_; lean_object* v___x_197_; 
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = l_Lean_Syntax_getArg(v_stx_183_, v___x_193_);
v___x_195_ = l_Lean_Syntax_getArgs(v___x_194_);
lean_dec(v___x_194_);
v___f_196_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDelta___lam__1___boxed), 10, 1);
lean_closure_set(v___f_196_, 0, v___x_195_);
v___x_197_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_196_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta___boxed(lean_object* v_stx_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Elab_Tactic_Conv_evalDelta(v_stx_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_stx_198_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0(size_t v_sz_209_, size_t v_i_210_, lean_object* v_bs_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(v_sz_209_, v_i_210_, v_bs_211_, v___y_218_, v___y_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___boxed(lean_object* v_sz_222_, lean_object* v_i_223_, lean_object* v_bs_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
size_t v_sz_boxed_234_; size_t v_i_boxed_235_; lean_object* v_res_236_; 
v_sz_boxed_234_ = lean_unbox_usize(v_sz_222_);
lean_dec(v_sz_222_);
v_i_boxed_235_ = lean_unbox_usize(v_i_223_);
lean_dec(v_i_223_);
v_res_236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0(v_sz_boxed_234_, v_i_boxed_235_, v_bs_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1(){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_257_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_258_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5));
v___x_259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8));
v___x_260_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDelta___boxed), 10, 0);
v___x_261_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_257_, v___x_258_, v___x_259_, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___boxed(lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1();
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3(){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8));
v___x_291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__6));
v___x_292_ = l_Lean_addBuiltinDeclarationRanges(v___x_290_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___boxed(lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3();
return v_res_294_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Delta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Delta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Delta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Delta(builtin);
}
#ifdef __cplusplus
}
#endif
