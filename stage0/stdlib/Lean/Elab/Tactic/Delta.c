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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "\"delta \" ident+ (location)\?"};
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
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0(lean_object* v_a_1_, lean_object* v_as_2_, size_t v_i_3_, size_t v_stop_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_as_2_ = stack[1].m_obj;
size_t v_i_3_ = stack[2].m_num;
size_t v_stop_4_ = stack[3].m_num;
uint8_t v_res_12_;
v_res_12_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0(v_a_1_, v_as_2_, v_i_3_, v_stop_4_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0___boxed(lean_object* v_a_13_, lean_object* v_as_14_, lean_object* v_i_15_, lean_object* v_stop_16_){
_start:
{
size_t v_i_boxed_17_; size_t v_stop_boxed_18_; uint8_t v_res_19_; lean_object* v_r_20_; 
v_i_boxed_17_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_stop_boxed_18_ = lean_unbox_usize(v_stop_16_);
lean_dec(v_stop_16_);
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0(v_a_13_, v_as_14_, v_i_boxed_17_, v_stop_boxed_18_);
lean_dec_ref(v_as_14_);
lean_dec(v_a_13_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
uint8_t l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0(lean_object* v_as_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_array_get_size(v_as_21_);
v___x_25_ = lean_nat_dec_lt(v___x_23_, v___x_24_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
size_t v___x_26_; size_t v___x_27_; uint8_t v___x_28_; 
v___x_26_ = ((size_t)0ULL);
v___x_27_ = lean_usize_of_nat(v___x_24_);
v___x_28_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0(v_a_22_, v_as_21_, v___x_26_, v___x_27_);
return v___x_28_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_21_ = stack[0].m_obj;
lean_object* v_a_22_ = stack[1].m_obj;
uint8_t v_res_29_;
v_res_29_ = l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0(v_as_21_, v_a_22_);
stack->m_num = v_res_29_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0___boxed(lean_object* v_as_30_, lean_object* v_a_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0(v_as_30_, v_a_31_);
lean_dec(v_a_31_);
lean_dec_ref(v_as_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
uint8_t l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0(lean_object* v_declNames_34_, lean_object* v___y_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0(v_declNames_34_, v___y_35_);
return v___x_36_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_34_ = stack[0].m_obj;
lean_object* v___y_35_ = stack[1].m_obj;
uint8_t v_res_37_;
v_res_37_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0(v_declNames_34_, v___y_35_);
stack->m_num = v_res_37_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0___boxed(lean_object* v_declNames_38_, lean_object* v___y_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0(v_declNames_38_, v___y_39_);
lean_dec(v___y_39_);
lean_dec_ref(v_declNames_38_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
if (lean_obj_tag(v_a_42_) == 0)
{
lean_object* v___x_44_; 
v___x_44_ = l_List_reverse___redArg(v_a_43_);
return v___x_44_;
}
else
{
lean_object* v_head_45_; lean_object* v_tail_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_55_; 
v_head_45_ = lean_ctor_get(v_a_42_, 0);
v_tail_46_ = lean_ctor_get(v_a_42_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v_a_42_);
if (v_isSharedCheck_55_ == 0)
{
v___x_48_ = v_a_42_;
v_isShared_49_ = v_isSharedCheck_55_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_tail_46_);
lean_inc(v_head_45_);
lean_dec(v_a_42_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_55_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_50_ = l_Lean_MessageData_ofName(v_head_45_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 1, v_a_43_);
lean_ctor_set(v___x_48_, 0, v___x_50_);
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_a_43_);
v___x_52_ = v_reuseFailAlloc_54_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
v_a_42_ = v_tail_46_;
v_a_43_ = v___x_52_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__2));
v___x_61_ = l_Lean_stringToMessageData(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__4));
v___x_64_ = l_Lean_stringToMessageData(v___x_63_);
return v___x_64_;
}
}
lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg(lean_object* v_declNames_65_, lean_object* v_fvarId_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___f_73_; lean_object* v___x_74_; 
lean_inc_ref(v_declNames_65_);
v___f_73_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_73_, 0, v_declNames_65_);
v___x_74_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_76_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v___x_74_, 1);
lean_inc(v_fvarId_66_);
v___x_76_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_66_, v_a_68_, v_a_70_, v_a_71_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_78_; uint8_t v___x_79_; lean_object* v___x_80_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_77_);
lean_dec_ref_known(v___x_76_, 1);
v___x_78_ = l_Lean_LocalDecl_type(v_a_77_);
v___x_79_ = 0;
lean_inc_ref(v___x_78_);
v___x_80_ = l_Lean_Meta_deltaExpand(v___x_78_, v___f_73_, v___x_79_, v_a_70_, v_a_71_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v___y_83_; lean_object* v___y_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; uint8_t v___x_101_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_a_81_);
lean_dec_ref_known(v___x_80_, 1);
v___x_101_ = lean_expr_eqv(v_a_81_, v___x_78_);
lean_dec_ref(v___x_78_);
if (v___x_101_ == 0)
{
lean_dec(v_a_77_);
lean_dec_ref(v_declNames_65_);
v___y_83_ = v_a_67_;
v___y_84_ = v_a_68_;
v___y_85_ = v_a_69_;
v___y_86_ = v_a_70_;
v___y_87_ = v_a_71_;
goto v___jp_82_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_102_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1));
v___x_103_ = lean_obj_once(&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3, &l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3);
v___x_104_ = lean_array_to_list(v_declNames_65_);
v___x_105_ = lean_box(0);
v___x_106_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(v___x_104_, v___x_105_);
v___x_107_ = l_Lean_MessageData_ofList(v___x_106_);
v___x_108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_103_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_obj_once(&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5, &l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5);
v___x_110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = l_Lean_LocalDecl_userName(v_a_77_);
lean_dec(v_a_77_);
v___x_112_ = l_Lean_MessageData_ofName(v___x_111_);
v___x_113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_110_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_inc(v_a_75_);
v___x_115_ = l_Lean_Meta_throwTacticEx___redArg(v___x_102_, v_a_75_, v___x_114_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_dec_ref_known(v___x_115_, 1);
v___y_83_ = v_a_67_;
v___y_84_ = v_a_68_;
v___y_85_ = v_a_69_;
v___y_86_ = v_a_70_;
v___y_87_ = v_a_71_;
goto v___jp_82_;
}
else
{
lean_dec(v_a_81_);
lean_dec(v_a_75_);
lean_dec(v_fvarId_66_);
return v___x_115_;
}
}
v___jp_82_:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_a_75_, v_fvarId_66_, v_a_81_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_a_89_);
lean_dec_ref_known(v___x_88_, 1);
v___x_90_ = lean_box(0);
v___x_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_91_, 0, v_a_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_91_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
return v___x_92_;
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
v_a_93_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_88_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_88_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec_ref(v___x_78_);
lean_dec(v_a_77_);
lean_dec(v_a_75_);
lean_dec(v_fvarId_66_);
lean_dec_ref(v_declNames_65_);
v_a_116_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_80_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_80_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec(v_a_75_);
lean_dec_ref(v___f_73_);
lean_dec(v_fvarId_66_);
lean_dec_ref(v_declNames_65_);
v_a_124_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_76_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_76_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
lean_dec_ref(v___f_73_);
lean_dec(v_fvarId_66_);
lean_dec_ref(v_declNames_65_);
v_a_132_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_74_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_74_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_deltaLocalDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_65_ = stack[0].m_obj;
lean_object* v_fvarId_66_ = stack[1].m_obj;
lean_object* v_a_67_ = stack[2].m_obj;
lean_object* v_a_68_ = stack[3].m_obj;
lean_object* v_a_69_ = stack[4].m_obj;
lean_object* v_a_70_ = stack[5].m_obj;
lean_object* v_a_71_ = stack[6].m_obj;
lean_object* v_res_140_;
v_res_140_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg(v_declNames_65_, v_fvarId_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___boxed(lean_object* v_declNames_141_, lean_object* v_fvarId_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg(v_declNames_141_, v_fvarId_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
return v_res_149_;
}
}
lean_object* l_Lean_Elab_Tactic_deltaLocalDecl(lean_object* v_declNames_150_, lean_object* v_fvarId_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg(v_declNames_150_, v_fvarId_151_, v_a_153_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
return v___x_161_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_deltaLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_150_ = stack[0].m_obj;
lean_object* v_fvarId_151_ = stack[1].m_obj;
lean_object* v_a_152_ = stack[2].m_obj;
lean_object* v_a_153_ = stack[3].m_obj;
lean_object* v_a_154_ = stack[4].m_obj;
lean_object* v_a_155_ = stack[5].m_obj;
lean_object* v_a_156_ = stack[6].m_obj;
lean_object* v_a_157_ = stack[7].m_obj;
lean_object* v_a_158_ = stack[8].m_obj;
lean_object* v_a_159_ = stack[9].m_obj;
lean_object* v_res_162_;
v_res_162_ = l_Lean_Elab_Tactic_deltaLocalDecl(v_declNames_150_, v_fvarId_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___boxed(lean_object* v_declNames_163_, lean_object* v_fvarId_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Elab_Tactic_deltaLocalDecl(v_declNames_163_, v_fvarId_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
return v_res_174_;
}
}
lean_object* l_Lean_Elab_Tactic_deltaTarget(lean_object* v_declNames_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___f_185_; lean_object* v___x_186_; 
lean_inc_ref(v_declNames_175_);
v___f_185_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_185_, 0, v_declNames_175_);
v___x_186_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_177_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_188_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
lean_dec_ref_known(v___x_186_, 1);
v___x_188_ = l_Lean_Elab_Tactic_getMainTarget(v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; uint8_t v___x_190_; lean_object* v___x_191_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc_n(v_a_189_, 2);
lean_dec_ref_known(v___x_188_, 1);
v___x_190_ = 0;
v___x_191_ = l_Lean_Meta_deltaExpand(v_a_189_, v___f_185_, v___x_190_, v_a_182_, v_a_183_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_198_; uint8_t v___x_212_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
lean_dec_ref_known(v___x_191_, 1);
v___x_212_ = lean_expr_eqv(v_a_192_, v_a_189_);
lean_dec(v_a_189_);
if (v___x_212_ == 0)
{
lean_dec_ref(v_declNames_175_);
v___y_194_ = v_a_177_;
v___y_195_ = v_a_180_;
v___y_196_ = v_a_181_;
v___y_197_ = v_a_182_;
v___y_198_ = v_a_183_;
goto v___jp_193_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_213_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1));
v___x_214_ = lean_obj_once(&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3, &l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3);
v___x_215_ = lean_array_to_list(v_declNames_175_);
v___x_216_ = lean_box(0);
v___x_217_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(v___x_215_, v___x_216_);
v___x_218_ = l_Lean_MessageData_ofList(v___x_217_);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_214_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_inc(v_a_187_);
v___x_221_ = l_Lean_Meta_throwTacticEx___redArg(v___x_213_, v_a_187_, v___x_220_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_dec_ref_known(v___x_221_, 1);
v___y_194_ = v_a_177_;
v___y_195_ = v_a_180_;
v___y_196_ = v_a_181_;
v___y_197_ = v_a_182_;
v___y_198_ = v_a_183_;
goto v___jp_193_;
}
else
{
lean_dec(v_a_192_);
lean_dec(v_a_187_);
return v___x_221_;
}
}
v___jp_193_:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_MVarId_replaceTargetDefEq(v_a_187_, v_a_192_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_200_);
lean_dec_ref_known(v___x_199_, 1);
v___x_201_ = lean_box(0);
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v_a_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_202_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
return v___x_203_;
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
v_a_204_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_199_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_199_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec(v_a_189_);
lean_dec(v_a_187_);
lean_dec_ref(v_declNames_175_);
v_a_222_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_191_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_191_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec(v_a_187_);
lean_dec_ref(v___f_185_);
lean_dec_ref(v_declNames_175_);
v_a_230_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_188_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_188_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec_ref(v___f_185_);
lean_dec_ref(v_declNames_175_);
v_a_238_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_186_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_186_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_deltaTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_175_ = stack[0].m_obj;
lean_object* v_a_176_ = stack[1].m_obj;
lean_object* v_a_177_ = stack[2].m_obj;
lean_object* v_a_178_ = stack[3].m_obj;
lean_object* v_a_179_ = stack[4].m_obj;
lean_object* v_a_180_ = stack[5].m_obj;
lean_object* v_a_181_ = stack[6].m_obj;
lean_object* v_a_182_ = stack[7].m_obj;
lean_object* v_a_183_ = stack[8].m_obj;
lean_object* v_res_246_;
v_res_246_ = l_Lean_Elab_Tactic_deltaTarget(v_declNames_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaTarget___boxed(lean_object* v_declNames_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Elab_Tactic_deltaTarget(v_declNames_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
return v_res_257_;
}
}
lean_object* l_Lean_Elab_Tactic_evalDelta___lam__0(lean_object* v_a_258_, lean_object* v_x_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_269_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1));
v___x_270_ = lean_obj_once(&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3, &l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3);
v___x_271_ = lean_array_to_list(v_a_258_);
v___x_272_ = lean_box(0);
v___x_273_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(v___x_271_, v___x_272_);
v___x_274_ = l_Lean_MessageData_ofList(v___x_273_);
v___x_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_270_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
v___x_277_ = l_Lean_Meta_throwTacticEx___redArg(v___x_269_, v_x_259_, v___x_276_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
return v___x_277_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalDelta___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_258_ = stack[0].m_obj;
lean_object* v_x_259_ = stack[1].m_obj;
lean_object* v___y_260_ = stack[2].m_obj;
lean_object* v___y_261_ = stack[3].m_obj;
lean_object* v___y_262_ = stack[4].m_obj;
lean_object* v___y_263_ = stack[5].m_obj;
lean_object* v___y_264_ = stack[6].m_obj;
lean_object* v___y_265_ = stack[7].m_obj;
lean_object* v___y_266_ = stack[8].m_obj;
lean_object* v___y_267_ = stack[9].m_obj;
lean_object* v_res_278_;
v_res_278_ = l_Lean_Elab_Tactic_evalDelta___lam__0(v_a_258_, v_x_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___lam__0___boxed(lean_object* v_a_279_, lean_object* v_x_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Elab_Tactic_evalDelta___lam__0(v_a_279_, v_x_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_290_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(size_t v_sz_291_, size_t v_i_292_, lean_object* v_bs_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = lean_usize_dec_lt(v_i_292_, v_sz_291_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v_bs_293_);
return v___x_298_;
}
else
{
lean_object* v_v_299_; lean_object* v___x_300_; lean_object* v_bs_x27_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_v_299_ = lean_array_uget(v_bs_293_, v_i_292_);
v___x_300_ = lean_unsigned_to_nat(0u);
v_bs_x27_301_ = lean_array_uset(v_bs_293_, v_i_292_, v___x_300_);
v___x_302_ = lean_box(0);
v___x_303_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_v_299_, v___x_302_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; size_t v___x_305_; size_t v___x_306_; lean_object* v___x_307_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_303_, 1);
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_add(v_i_292_, v___x_305_);
v___x_307_ = lean_array_uset(v_bs_x27_301_, v_i_292_, v_a_304_);
v_i_292_ = v___x_306_;
v_bs_293_ = v___x_307_;
goto _start;
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref(v_bs_x27_301_);
v_a_309_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_303_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_303_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_291_ = stack[0].m_num;
size_t v_i_292_ = stack[1].m_num;
lean_object* v_bs_293_ = stack[2].m_obj;
lean_object* v___y_294_ = stack[3].m_obj;
lean_object* v___y_295_ = stack[4].m_obj;
lean_object* v_res_317_;
v_res_317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_291_, v_i_292_, v_bs_293_, v___y_294_, v___y_295_);
stack->m_obj
 = v_res_317_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg___boxed(lean_object* v_sz_318_, lean_object* v_i_319_, lean_object* v_bs_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
size_t v_sz_boxed_324_; size_t v_i_boxed_325_; lean_object* v_res_326_; 
v_sz_boxed_324_ = lean_unbox_usize(v_sz_318_);
lean_dec(v_sz_318_);
v_i_boxed_325_ = lean_unbox_usize(v_i_319_);
lean_dec(v_i_319_);
v_res_326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_boxed_324_, v_i_boxed_325_, v_bs_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_326_;
}
}
lean_object* l_Lean_Elab_Tactic_evalDelta(lean_object* v_stx_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; size_t v_sz_340_; size_t v___x_341_; lean_object* v___x_342_; 
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = l_Lean_Syntax_getArg(v_stx_327_, v___x_337_);
v___x_339_ = l_Lean_Syntax_getArgs(v___x_338_);
lean_dec(v___x_338_);
v_sz_340_ = lean_array_size(v___x_339_);
v___x_341_ = ((size_t)0ULL);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_340_, v___x_341_, v___x_339_, v_a_334_, v_a_335_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___f_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc_n(v_a_343_, 3);
lean_dec_ref_known(v___x_342_, 1);
v___f_344_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDelta___lam__0___boxed), 11, 1);
lean_closure_set(v___f_344_, 0, v_a_343_);
v___x_345_ = lean_unsigned_to_nat(2u);
v___x_346_ = l_Lean_Syntax_getArg(v_stx_327_, v___x_345_);
v___x_347_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_346_);
lean_dec(v___x_346_);
v___x_348_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_deltaLocalDecl___boxed), 11, 1);
lean_closure_set(v___x_348_, 0, v_a_343_);
v___x_349_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_deltaTarget___boxed), 10, 1);
lean_closure_set(v___x_349_, 0, v_a_343_);
v___x_350_ = l_Lean_Elab_Tactic_withLocation(v___x_347_, v___x_348_, v___x_349_, v___f_344_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v___x_347_);
return v___x_350_;
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_342_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_342_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalDelta_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_327_ = stack[0].m_obj;
lean_object* v_a_328_ = stack[1].m_obj;
lean_object* v_a_329_ = stack[2].m_obj;
lean_object* v_a_330_ = stack[3].m_obj;
lean_object* v_a_331_ = stack[4].m_obj;
lean_object* v_a_332_ = stack[5].m_obj;
lean_object* v_a_333_ = stack[6].m_obj;
lean_object* v_a_334_ = stack[7].m_obj;
lean_object* v_a_335_ = stack[8].m_obj;
lean_object* v_res_359_;
v_res_359_ = l_Lean_Elab_Tactic_evalDelta(v_stx_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
stack->m_obj
 = v_res_359_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___boxed(lean_object* v_stx_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Elab_Tactic_evalDelta(v_stx_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_stx_360_);
return v_res_370_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0(size_t v_sz_371_, size_t v_i_372_, lean_object* v_bs_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_371_, v_i_372_, v_bs_373_, v___y_380_, v___y_381_);
return v___x_383_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_371_ = stack[0].m_num;
size_t v_i_372_ = stack[1].m_num;
lean_object* v_bs_373_ = stack[2].m_obj;
lean_object* v___y_374_ = stack[3].m_obj;
lean_object* v___y_375_ = stack[4].m_obj;
lean_object* v___y_376_ = stack[5].m_obj;
lean_object* v___y_377_ = stack[6].m_obj;
lean_object* v___y_378_ = stack[7].m_obj;
lean_object* v___y_379_ = stack[8].m_obj;
lean_object* v___y_380_ = stack[9].m_obj;
lean_object* v___y_381_ = stack[10].m_obj;
lean_object* v_res_384_;
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0(v_sz_371_, v_i_372_, v_bs_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
stack->m_obj
 = v_res_384_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___boxed(lean_object* v_sz_385_, lean_object* v_i_386_, lean_object* v_bs_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
size_t v_sz_boxed_397_; size_t v_i_boxed_398_; lean_object* v_res_399_; 
v_sz_boxed_397_ = lean_unbox_usize(v_sz_385_);
lean_dec(v_sz_385_);
v_i_boxed_398_ = lean_unbox_usize(v_i_386_);
lean_dec(v_i_386_);
v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0(v_sz_boxed_397_, v_i_boxed_398_, v_bs_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
return v_res_399_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1(){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_416_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3));
v___x_418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6));
v___x_419_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDelta___boxed), 10, 0);
v___x_420_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_416_, v___x_417_, v___x_418_, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_421_;
v_res_421_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1();
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___boxed(lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1();
return v_res_423_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3(){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6));
v___x_427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0));
v___x_428_ = l_Lean_addBuiltinDocString(v___x_426_, v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_429_;
v_res_429_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3();
stack->m_obj
 = v_res_429_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___boxed(lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3();
return v_res_431_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5(){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6));
v___x_459_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6));
v___x_460_ = l_Lean_addBuiltinDeclarationRanges(v___x_458_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_461_;
v_res_461_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5();
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___boxed(lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5();
return v_res_463_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Delta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
