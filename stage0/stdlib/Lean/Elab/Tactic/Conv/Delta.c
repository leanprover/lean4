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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
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
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg(v_e_31_, v___y_37_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___boxed(lean_object* v_e_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1(v_e_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
return v_res_52_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2(lean_object* v_a_53_, lean_object* v_as_54_, size_t v_i_55_, size_t v_stop_56_){
_start:
{
uint8_t v___x_57_; 
v___x_57_ = lean_usize_dec_eq(v_i_55_, v_stop_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = lean_array_uget_borrowed(v_as_54_, v_i_55_);
v___x_59_ = lean_name_eq(v_a_53_, v___x_58_);
if (v___x_59_ == 0)
{
size_t v___x_60_; size_t v___x_61_; 
v___x_60_ = ((size_t)1ULL);
v___x_61_ = lean_usize_add(v_i_55_, v___x_60_);
v_i_55_ = v___x_61_;
goto _start;
}
else
{
return v___x_59_;
}
}
else
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2___boxed(lean_object* v_a_64_, lean_object* v_as_65_, lean_object* v_i_66_, lean_object* v_stop_67_){
_start:
{
size_t v_i_boxed_68_; size_t v_stop_boxed_69_; uint8_t v_res_70_; lean_object* v_r_71_; 
v_i_boxed_68_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_stop_boxed_69_ = lean_unbox_usize(v_stop_67_);
lean_dec(v_stop_67_);
v_res_70_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2(v_a_64_, v_as_65_, v_i_boxed_68_, v_stop_boxed_69_);
lean_dec_ref(v_as_65_);
lean_dec(v_a_64_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2(lean_object* v_as_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = lean_array_get_size(v_as_72_);
v___x_76_ = lean_nat_dec_lt(v___x_74_, v___x_75_);
if (v___x_76_ == 0)
{
return v___x_76_;
}
else
{
if (v___x_76_ == 0)
{
return v___x_76_;
}
else
{
size_t v___x_77_; size_t v___x_78_; uint8_t v___x_79_; 
v___x_77_ = ((size_t)0ULL);
v___x_78_ = lean_usize_of_nat(v___x_75_);
v___x_79_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2(v_a_73_, v_as_72_, v___x_77_, v___x_78_);
return v___x_79_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2___boxed(lean_object* v_as_80_, lean_object* v_a_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2(v_as_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_as_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Conv_evalDelta___lam__0(lean_object* v_a_84_, lean_object* v___y_85_){
_start:
{
uint8_t v___x_86_; 
v___x_86_ = l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2(v_a_84_, v___y_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta___lam__0___boxed(lean_object* v_a_87_, lean_object* v___y_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Lean_Elab_Tactic_Conv_evalDelta___lam__0(v_a_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec_ref(v_a_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(size_t v_sz_91_, size_t v_i_92_, lean_object* v_bs_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = lean_usize_dec_lt(v_i_92_, v_sz_91_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v_bs_93_);
return v___x_98_;
}
else
{
lean_object* v_v_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_v_99_ = lean_array_uget_borrowed(v_bs_93_, v_i_92_);
v___x_100_ = lean_box(0);
lean_inc(v_v_99_);
v___x_101_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_v_99_, v___x_100_, v___y_94_, v___y_95_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_103_; lean_object* v_bs_x27_104_; size_t v___x_105_; size_t v___x_106_; lean_object* v___x_107_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_101_, 1);
v___x_103_ = lean_unsigned_to_nat(0u);
v_bs_x27_104_ = lean_array_uset(v_bs_93_, v_i_92_, v___x_103_);
v___x_105_ = ((size_t)1ULL);
v___x_106_ = lean_usize_add(v_i_92_, v___x_105_);
v___x_107_ = lean_array_uset(v_bs_x27_104_, v_i_92_, v_a_102_);
v_i_92_ = v___x_106_;
v_bs_93_ = v___x_107_;
goto _start;
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
lean_dec_ref(v_bs_93_);
v_a_109_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_101_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_101_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg___boxed(lean_object* v_sz_117_, lean_object* v_i_118_, lean_object* v_bs_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
size_t v_sz_boxed_123_; size_t v_i_boxed_124_; lean_object* v_res_125_; 
v_sz_boxed_123_ = lean_unbox_usize(v_sz_117_);
lean_dec(v_sz_117_);
v_i_boxed_124_ = lean_unbox_usize(v_i_118_);
lean_dec(v_i_118_);
v_res_125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(v_sz_boxed_123_, v_i_boxed_124_, v_bs_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta___lam__1(lean_object* v___x_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
size_t v_sz_136_; size_t v___x_137_; lean_object* v___x_138_; 
v_sz_136_ = lean_array_size(v___x_126_);
v___x_137_ = ((size_t)0ULL);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(v_sz_136_, v___x_137_, v___x_126_, v___y_133_, v___y_134_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref_known(v___x_138_, 1);
v___x_140_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_128_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; lean_object* v_a_143_; lean_object* v___f_144_; uint8_t v___x_145_; lean_object* v___x_146_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_140_, 1);
v___x_142_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg(v_a_141_, v___y_132_);
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
lean_dec_ref(v___x_142_);
v___f_144_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDelta___lam__0___boxed), 2, 1);
lean_closure_set(v___f_144_, 0, v_a_139_);
v___x_145_ = 0;
v___x_146_ = l_Lean_Meta_deltaExpand(v_a_143_, v___f_144_, v___x_145_, v___y_133_, v___y_134_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_148_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_a_147_);
lean_dec_ref_known(v___x_146_, 1);
v___x_148_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_147_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
return v___x_148_;
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_a_149_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_146_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_146_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_dec(v_a_139_);
v_a_157_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_140_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_140_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v_a_165_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_138_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_138_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta___lam__1___boxed(lean_object* v___x_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Elab_Tactic_Conv_evalDelta___lam__1(v___x_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta(lean_object* v_stx_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = l_Lean_Syntax_getArg(v_stx_184_, v___x_194_);
v___x_196_ = l_Lean_Syntax_getArgs(v___x_195_);
lean_dec(v___x_195_);
v___f_197_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDelta___lam__1___boxed), 10, 1);
lean_closure_set(v___f_197_, 0, v___x_196_);
v___x_198_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_197_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalDelta___boxed(lean_object* v_stx_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Elab_Tactic_Conv_evalDelta(v_stx_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_stx_199_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0(size_t v_sz_210_, size_t v_i_211_, lean_object* v_bs_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(v_sz_210_, v_i_211_, v_bs_212_, v___y_219_, v___y_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___boxed(lean_object* v_sz_223_, lean_object* v_i_224_, lean_object* v_bs_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
size_t v_sz_boxed_235_; size_t v_i_boxed_236_; lean_object* v_res_237_; 
v_sz_boxed_235_ = lean_unbox_usize(v_sz_223_);
lean_dec(v_sz_223_);
v_i_boxed_236_ = lean_unbox_usize(v_i_224_);
lean_dec(v_i_224_);
v_res_237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0(v_sz_boxed_235_, v_i_boxed_236_, v_bs_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1(){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_258_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5));
v___x_260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8));
v___x_261_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalDelta___boxed), 10, 0);
v___x_262_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_258_, v___x_259_, v___x_260_, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___boxed(lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1();
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3(){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8));
v___x_292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__6));
v___x_293_ = l_Lean_addBuiltinDeclarationRanges(v___x_291_, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___boxed(lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3();
return v_res_295_;
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
