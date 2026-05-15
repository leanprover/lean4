// Lean compiler output
// Module: Lean.Elab.Tactic.Delta
// Imports: public import Lean.Meta.Tactic.Delta public import Lean.Elab.Tactic.Location
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
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "delta"};
static const lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 170, 171, 73, 211, 254, 35, 39)}};
static const lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "did not delta reduce "};
static const lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " at "};
static const lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 112, 73, 39, 125, 88, 225, 159)}};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalDelta"};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(228, 185, 81, 104, 43, 63, 49, 240)}};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "\"delta \" ident+ (location)\? "};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__1_value),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__4_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0(lean_object* v_a_1_, lean_object* v_as_2_, size_t v_i_3_, size_t v_stop_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_eq(v_i_3_, v_stop_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_array_uget_borrowed(v_as_2_, v_i_3_);
v___x_7_ = lean_name_eq(v_a_1_, v___x_6_);
if (v___x_7_ == 0)
{
size_t v___x_8_; size_t v___x_9_; 
v___x_8_ = ((size_t)1ULL);
v___x_9_ = lean_usize_add(v_i_3_, v___x_8_);
v_i_3_ = v___x_9_;
goto _start;
}
else
{
return v___x_7_;
}
}
else
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0___boxed(lean_object* v_a_12_, lean_object* v_as_13_, lean_object* v_i_14_, lean_object* v_stop_15_){
_start:
{
size_t v_i_boxed_16_; size_t v_stop_boxed_17_; uint8_t v_res_18_; lean_object* v_r_19_; 
v_i_boxed_16_ = lean_unbox_usize(v_i_14_);
lean_dec(v_i_14_);
v_stop_boxed_17_ = lean_unbox_usize(v_stop_15_);
lean_dec(v_stop_15_);
v_res_18_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0(v_a_12_, v_as_13_, v_i_boxed_16_, v_stop_boxed_17_);
lean_dec_ref(v_as_13_);
lean_dec(v_a_12_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0(lean_object* v_as_20_, lean_object* v_a_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_array_get_size(v_as_20_);
v___x_24_ = lean_nat_dec_lt(v___x_22_, v___x_23_);
if (v___x_24_ == 0)
{
return v___x_24_;
}
else
{
if (v___x_24_ == 0)
{
return v___x_24_;
}
else
{
size_t v___x_25_; size_t v___x_26_; uint8_t v___x_27_; 
v___x_25_ = ((size_t)0ULL);
v___x_26_ = lean_usize_of_nat(v___x_23_);
v___x_27_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0(v_a_21_, v_as_20_, v___x_25_, v___x_26_);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0___boxed(lean_object* v_as_28_, lean_object* v_a_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0(v_as_28_, v_a_29_);
lean_dec(v_a_29_);
lean_dec_ref(v_as_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0(lean_object* v_declNames_32_, lean_object* v___y_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0(v_declNames_32_, v___y_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0___boxed(lean_object* v_declNames_35_, lean_object* v___y_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0(v_declNames_35_, v___y_36_);
lean_dec(v___y_36_);
lean_dec_ref(v_declNames_35_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
if (lean_obj_tag(v_a_39_) == 0)
{
lean_object* v___x_41_; 
v___x_41_ = l_List_reverse___redArg(v_a_40_);
return v___x_41_;
}
else
{
lean_object* v_head_42_; lean_object* v_tail_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_52_; 
v_head_42_ = lean_ctor_get(v_a_39_, 0);
v_tail_43_ = lean_ctor_get(v_a_39_, 1);
v_isSharedCheck_52_ = !lean_is_exclusive(v_a_39_);
if (v_isSharedCheck_52_ == 0)
{
v___x_45_ = v_a_39_;
v_isShared_46_ = v_isSharedCheck_52_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_tail_43_);
lean_inc(v_head_42_);
lean_dec(v_a_39_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_52_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_47_ = l_Lean_MessageData_ofName(v_head_42_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v_a_40_);
lean_ctor_set(v___x_45_, 0, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_a_40_);
v___x_49_ = v_reuseFailAlloc_51_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
v_a_39_ = v_tail_43_;
v_a_40_ = v___x_49_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__2));
v___x_58_ = l_Lean_stringToMessageData(v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__4));
v___x_61_ = l_Lean_stringToMessageData(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg(lean_object* v_declNames_62_, lean_object* v_fvarId_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_72_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_71_);
lean_dec_ref(v___x_70_);
lean_inc(v_fvarId_63_);
v___x_72_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_63_, v_a_65_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___f_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref(v___x_72_);
lean_inc_ref(v_declNames_62_);
v___f_74_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_74_, 0, v_declNames_62_);
v___x_75_ = l_Lean_LocalDecl_type(v_a_73_);
v___x_76_ = 0;
lean_inc_ref(v___x_75_);
v___x_77_ = l_Lean_Meta_deltaExpand(v___x_75_, v___f_74_, v___x_76_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___y_83_; lean_object* v___y_84_; uint8_t v___x_98_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_a_78_);
lean_dec_ref(v___x_77_);
v___x_98_ = lean_expr_eqv(v_a_78_, v___x_75_);
lean_dec_ref(v___x_75_);
if (v___x_98_ == 0)
{
lean_dec(v_a_73_);
lean_dec_ref(v_declNames_62_);
v___y_80_ = v_a_64_;
v___y_81_ = v_a_65_;
v___y_82_ = v_a_66_;
v___y_83_ = v_a_67_;
v___y_84_ = v_a_68_;
goto v___jp_79_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_99_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1));
v___x_100_ = lean_obj_once(&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3, &l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3);
v___x_101_ = lean_array_to_list(v_declNames_62_);
v___x_102_ = lean_box(0);
v___x_103_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(v___x_101_, v___x_102_);
v___x_104_ = l_Lean_MessageData_ofList(v___x_103_);
v___x_105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_100_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = lean_obj_once(&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5, &l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5);
v___x_107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_105_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = l_Lean_LocalDecl_userName(v_a_73_);
lean_dec(v_a_73_);
v___x_109_ = l_Lean_MessageData_ofName(v___x_108_);
v___x_110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_107_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_inc(v_a_71_);
v___x_112_ = l_Lean_Meta_throwTacticEx___redArg(v___x_99_, v_a_71_, v___x_111_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_dec_ref(v___x_112_);
v___y_80_ = v_a_64_;
v___y_81_ = v_a_65_;
v___y_82_ = v_a_66_;
v___y_83_ = v_a_67_;
v___y_84_ = v_a_68_;
goto v___jp_79_;
}
else
{
lean_dec(v_a_78_);
lean_dec(v_a_71_);
lean_dec(v_fvarId_63_);
return v___x_112_;
}
}
v___jp_79_:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_a_71_, v_fvarId_63_, v_a_78_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_a_86_);
lean_dec_ref(v___x_85_);
v___x_87_ = lean_box(0);
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v_a_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_88_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
return v___x_89_;
}
else
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v_a_90_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v___x_85_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_85_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
lean_dec_ref(v___x_75_);
lean_dec(v_a_73_);
lean_dec(v_a_71_);
lean_dec(v_fvarId_63_);
lean_dec_ref(v_declNames_62_);
v_a_113_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_77_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_77_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec(v_a_71_);
lean_dec(v_fvarId_63_);
lean_dec_ref(v_declNames_62_);
v_a_121_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_72_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_72_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
else
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
lean_dec(v_fvarId_63_);
lean_dec_ref(v_declNames_62_);
v_a_129_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v___x_70_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_70_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___boxed(lean_object* v_declNames_137_, lean_object* v_fvarId_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg(v_declNames_137_, v_fvarId_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl(lean_object* v_declNames_146_, lean_object* v_fvarId_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg(v_declNames_146_, v_fvarId_147_, v_a_149_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___boxed(lean_object* v_declNames_158_, lean_object* v_fvarId_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Elab_Tactic_deltaLocalDecl(v_declNames_158_, v_fvarId_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaTarget(lean_object* v_declNames_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_172_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_182_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref(v___x_180_);
v___x_182_ = l_Lean_Elab_Tactic_getMainTarget(v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___f_184_; uint8_t v___x_185_; lean_object* v___x_186_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc_n(v_a_183_, 2);
lean_dec_ref(v___x_182_);
lean_inc_ref(v_declNames_170_);
v___f_184_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_184_, 0, v_declNames_170_);
v___x_185_ = 0;
v___x_186_ = l_Lean_Meta_deltaExpand(v_a_183_, v___f_184_, v___x_185_, v_a_177_, v_a_178_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; uint8_t v___x_207_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
lean_dec_ref(v___x_186_);
v___x_207_ = lean_expr_eqv(v_a_187_, v_a_183_);
lean_dec(v_a_183_);
if (v___x_207_ == 0)
{
lean_dec_ref(v_declNames_170_);
v___y_189_ = v_a_172_;
v___y_190_ = v_a_175_;
v___y_191_ = v_a_176_;
v___y_192_ = v_a_177_;
v___y_193_ = v_a_178_;
goto v___jp_188_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_208_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1));
v___x_209_ = lean_obj_once(&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3, &l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3);
v___x_210_ = lean_array_to_list(v_declNames_170_);
v___x_211_ = lean_box(0);
v___x_212_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(v___x_210_, v___x_211_);
v___x_213_ = l_Lean_MessageData_ofList(v___x_212_);
v___x_214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_209_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_inc(v_a_181_);
v___x_216_ = l_Lean_Meta_throwTacticEx___redArg(v___x_208_, v_a_181_, v___x_215_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_dec_ref(v___x_216_);
v___y_189_ = v_a_172_;
v___y_190_ = v_a_175_;
v___y_191_ = v_a_176_;
v___y_192_ = v_a_177_;
v___y_193_ = v_a_178_;
goto v___jp_188_;
}
else
{
lean_dec(v_a_187_);
lean_dec(v_a_181_);
return v___x_216_;
}
}
v___jp_188_:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_MVarId_replaceTargetDefEq(v_a_181_, v_a_187_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref(v___x_194_);
v___x_196_ = lean_box(0);
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v_a_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_197_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
return v___x_198_;
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_a_199_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_194_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_194_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec(v_a_183_);
lean_dec(v_a_181_);
lean_dec_ref(v_declNames_170_);
v_a_217_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_186_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_186_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec(v_a_181_);
lean_dec_ref(v_declNames_170_);
v_a_225_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_182_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_182_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec_ref(v_declNames_170_);
v_a_233_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_180_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_180_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaTarget___boxed(lean_object* v_declNames_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Elab_Tactic_deltaTarget(v_declNames_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___lam__0(lean_object* v_a_252_, lean_object* v_x_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_263_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1));
v___x_264_ = lean_obj_once(&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3, &l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3);
v___x_265_ = lean_array_to_list(v_a_252_);
v___x_266_ = lean_box(0);
v___x_267_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(v___x_265_, v___x_266_);
v___x_268_ = l_Lean_MessageData_ofList(v___x_267_);
v___x_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_264_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
v___x_271_ = l_Lean_Meta_throwTacticEx___redArg(v___x_263_, v_x_253_, v___x_270_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___lam__0___boxed(lean_object* v_a_272_, lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Elab_Tactic_evalDelta___lam__0(v_a_272_, v_x_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(size_t v_sz_284_, size_t v_i_285_, lean_object* v_bs_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = lean_usize_dec_lt(v_i_285_, v_sz_284_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v_bs_286_);
return v___x_291_;
}
else
{
lean_object* v_v_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_v_292_ = lean_array_uget_borrowed(v_bs_286_, v_i_285_);
v___x_293_ = lean_box(0);
lean_inc(v_v_292_);
v___x_294_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_v_292_, v___x_293_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_296_; lean_object* v_bs_x27_297_; size_t v___x_298_; size_t v___x_299_; lean_object* v___x_300_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref(v___x_294_);
v___x_296_ = lean_unsigned_to_nat(0u);
v_bs_x27_297_ = lean_array_uset(v_bs_286_, v_i_285_, v___x_296_);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_add(v_i_285_, v___x_298_);
v___x_300_ = lean_array_uset(v_bs_x27_297_, v_i_285_, v_a_295_);
v_i_285_ = v___x_299_;
v_bs_286_ = v___x_300_;
goto _start;
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec_ref(v_bs_286_);
v_a_302_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_294_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_294_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg___boxed(lean_object* v_sz_310_, lean_object* v_i_311_, lean_object* v_bs_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
size_t v_sz_boxed_316_; size_t v_i_boxed_317_; lean_object* v_res_318_; 
v_sz_boxed_316_ = lean_unbox_usize(v_sz_310_);
lean_dec(v_sz_310_);
v_i_boxed_317_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_res_318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_boxed_316_, v_i_boxed_317_, v_bs_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta(lean_object* v_stx_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; size_t v_sz_332_; size_t v___x_333_; lean_object* v___x_334_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = l_Lean_Syntax_getArg(v_stx_319_, v___x_329_);
v___x_331_ = l_Lean_Syntax_getArgs(v___x_330_);
lean_dec(v___x_330_);
v_sz_332_ = lean_array_size(v___x_331_);
v___x_333_ = ((size_t)0ULL);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_332_, v___x_333_, v___x_331_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc_n(v_a_335_, 3);
lean_dec_ref(v___x_334_);
v___f_336_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDelta___lam__0___boxed), 11, 1);
lean_closure_set(v___f_336_, 0, v_a_335_);
v___x_337_ = lean_unsigned_to_nat(2u);
v___x_338_ = l_Lean_Syntax_getArg(v_stx_319_, v___x_337_);
v___x_339_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_338_);
lean_dec(v___x_338_);
v___x_340_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_deltaLocalDecl___boxed), 11, 1);
lean_closure_set(v___x_340_, 0, v_a_335_);
v___x_341_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_deltaTarget___boxed), 10, 1);
lean_closure_set(v___x_341_, 0, v_a_335_);
v___x_342_ = l_Lean_Elab_Tactic_withLocation(v___x_339_, v___x_340_, v___x_341_, v___f_336_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
lean_dec(v___x_339_);
return v___x_342_;
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
v_a_343_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_334_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_334_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___boxed(lean_object* v_stx_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Elab_Tactic_evalDelta(v_stx_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_stx_351_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0(size_t v_sz_362_, size_t v_i_363_, lean_object* v_bs_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_362_, v_i_363_, v_bs_364_, v___y_371_, v___y_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___boxed(lean_object* v_sz_375_, lean_object* v_i_376_, lean_object* v_bs_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
size_t v_sz_boxed_387_; size_t v_i_boxed_388_; lean_object* v_res_389_; 
v_sz_boxed_387_ = lean_unbox_usize(v_sz_375_);
lean_dec(v_sz_375_);
v_i_boxed_388_ = lean_unbox_usize(v_i_376_);
lean_dec(v_i_376_);
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0(v_sz_boxed_387_, v_i_boxed_388_, v_bs_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1(){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_406_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3));
v___x_408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6));
v___x_409_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDelta___boxed), 10, 0);
v___x_410_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_406_, v___x_407_, v___x_408_, v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___boxed(lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1();
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3(){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6));
v___x_416_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0));
v___x_417_ = l_Lean_addBuiltinDocString(v___x_415_, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___boxed(lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3();
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5(){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6));
v___x_447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6));
v___x_448_ = l_Lean_addBuiltinDeclarationRanges(v___x_446_, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___boxed(lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5();
return v_res_450_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Delta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Delta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Delta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Delta(builtin);
}
#ifdef __cplusplus
}
#endif
