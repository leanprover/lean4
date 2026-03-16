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
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 112, 73, 39, 125, 88, 225, 159)}};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalDelta"};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(228, 185, 81, 104, 43, 63, 49, 240)}};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "\"delta \" ident+ (location)\? "};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__1_value),((lean_object*)(((size_t)(65) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__4_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___boxed(lean_object*);
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
lean_inc_ref(v_a_65_);
lean_inc(v_fvarId_63_);
v___x_72_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_63_, v_a_65_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref(v___x_72_);
lean_inc_ref(v_declNames_62_);
v___f_74_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_74_, 0, v_declNames_62_);
v___x_75_ = l_Lean_LocalDecl_type(v_a_73_);
lean_inc(v_a_68_);
lean_inc_ref(v_a_67_);
lean_inc_ref(v___x_75_);
v___x_76_ = l_Lean_Meta_deltaExpand(v___x_75_, v___f_74_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___y_79_; lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___y_83_; uint8_t v___x_97_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_77_);
lean_dec_ref(v___x_76_);
v___x_97_ = lean_expr_eqv(v_a_77_, v___x_75_);
lean_dec_ref(v___x_75_);
if (v___x_97_ == 0)
{
lean_dec(v_a_73_);
lean_dec_ref(v_declNames_62_);
v___y_79_ = v_a_64_;
v___y_80_ = v_a_65_;
v___y_81_ = v_a_66_;
v___y_82_ = v_a_67_;
v___y_83_ = v_a_68_;
goto v___jp_78_;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_98_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1));
v___x_99_ = lean_obj_once(&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3, &l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3);
v___x_100_ = lean_array_to_list(v_declNames_62_);
v___x_101_ = lean_box(0);
v___x_102_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(v___x_100_, v___x_101_);
v___x_103_ = l_Lean_MessageData_ofList(v___x_102_);
v___x_104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_99_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_obj_once(&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5, &l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5);
v___x_106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = l_Lean_LocalDecl_userName(v_a_73_);
lean_dec(v_a_73_);
v___x_108_ = l_Lean_MessageData_ofName(v___x_107_);
v___x_109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_106_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_inc(v_a_71_);
v___x_111_ = l_Lean_Meta_throwTacticEx___redArg(v___x_98_, v_a_71_, v___x_110_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_dec_ref(v___x_111_);
v___y_79_ = v_a_64_;
v___y_80_ = v_a_65_;
v___y_81_ = v_a_66_;
v___y_82_ = v_a_67_;
v___y_83_ = v_a_68_;
goto v___jp_78_;
}
else
{
lean_dec(v_a_77_);
lean_dec(v_a_71_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_fvarId_63_);
return v___x_111_;
}
}
v___jp_78_:
{
lean_object* v___x_84_; 
lean_inc(v___y_83_);
lean_inc_ref(v___y_82_);
lean_inc(v___y_81_);
lean_inc_ref(v___y_80_);
v___x_84_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_a_71_, v_fvarId_63_, v_a_77_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_a_85_);
lean_dec_ref(v___x_84_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_87_, 0, v_a_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_87_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v___x_88_;
}
else
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
v_a_89_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_84_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_84_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
lean_dec_ref(v___x_75_);
lean_dec(v_a_73_);
lean_dec(v_a_71_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_fvarId_63_);
lean_dec_ref(v_declNames_62_);
v_a_112_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_76_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_76_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec(v_a_71_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_fvarId_63_);
lean_dec_ref(v_declNames_62_);
v_a_120_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_72_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_72_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
else
{
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_fvarId_63_);
lean_dec_ref(v_declNames_62_);
v_a_128_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_135_ == 0)
{
v___x_130_ = v___x_70_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_70_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___redArg___boxed(lean_object* v_declNames_136_, lean_object* v_fvarId_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg(v_declNames_136_, v_fvarId_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
lean_dec(v_a_138_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl(lean_object* v_declNames_145_, lean_object* v_fvarId_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg(v_declNames_145_, v_fvarId_146_, v_a_148_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaLocalDecl___boxed(lean_object* v_declNames_157_, lean_object* v_fvarId_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Elab_Tactic_deltaLocalDecl(v_declNames_157_, v_fvarId_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaTarget(lean_object* v_declNames_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_171_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref(v___x_179_);
v___x_181_ = l_Lean_Elab_Tactic_getMainTarget(v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___f_183_; lean_object* v___x_184_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref(v___x_181_);
lean_inc_ref(v_declNames_169_);
v___f_183_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_183_, 0, v_declNames_169_);
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
lean_inc(v_a_182_);
v___x_184_ = l_Lean_Meta_deltaExpand(v_a_182_, v___f_183_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; uint8_t v___x_205_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref(v___x_184_);
v___x_205_ = lean_expr_eqv(v_a_185_, v_a_182_);
lean_dec(v_a_182_);
if (v___x_205_ == 0)
{
lean_dec_ref(v_declNames_169_);
v___y_187_ = v_a_171_;
v___y_188_ = v_a_174_;
v___y_189_ = v_a_175_;
v___y_190_ = v_a_176_;
v___y_191_ = v_a_177_;
goto v___jp_186_;
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_206_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1));
v___x_207_ = lean_obj_once(&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3, &l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3);
v___x_208_ = lean_array_to_list(v_declNames_169_);
v___x_209_ = lean_box(0);
v___x_210_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(v___x_208_, v___x_209_);
v___x_211_ = l_Lean_MessageData_ofList(v___x_210_);
v___x_212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_207_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_inc(v_a_180_);
v___x_214_ = l_Lean_Meta_throwTacticEx___redArg(v___x_206_, v_a_180_, v___x_213_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_dec_ref(v___x_214_);
v___y_187_ = v_a_171_;
v___y_188_ = v_a_174_;
v___y_189_ = v_a_175_;
v___y_190_ = v_a_176_;
v___y_191_ = v_a_177_;
goto v___jp_186_;
}
else
{
lean_dec(v_a_185_);
lean_dec(v_a_180_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
return v___x_214_;
}
}
v___jp_186_:
{
lean_object* v___x_192_; 
lean_inc(v___y_191_);
lean_inc_ref(v___y_190_);
lean_inc(v___y_189_);
lean_inc_ref(v___y_188_);
v___x_192_ = l_Lean_MVarId_replaceTargetDefEq(v_a_180_, v_a_185_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
lean_dec_ref(v___x_192_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_195_, 0, v_a_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_195_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v___x_196_;
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
v_a_197_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_192_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_192_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec(v_a_182_);
lean_dec(v_a_180_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec_ref(v_declNames_169_);
v_a_215_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_184_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_184_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec(v_a_180_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec_ref(v_declNames_169_);
v_a_223_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_181_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_181_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec_ref(v_declNames_169_);
v_a_231_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_179_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_179_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_deltaTarget___boxed(lean_object* v_declNames_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Elab_Tactic_deltaTarget(v_declNames_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___lam__0(lean_object* v_a_250_, lean_object* v_x_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_261_ = ((lean_object*)(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1));
v___x_262_ = lean_obj_once(&l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3, &l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3);
v___x_263_ = lean_array_to_list(v_a_250_);
v___x_264_ = lean_box(0);
v___x_265_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(v___x_263_, v___x_264_);
v___x_266_ = l_Lean_MessageData_ofList(v___x_265_);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_262_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
v___x_269_ = l_Lean_Meta_throwTacticEx___redArg(v___x_261_, v_x_251_, v___x_268_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___lam__0___boxed(lean_object* v_a_270_, lean_object* v_x_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Elab_Tactic_evalDelta___lam__0(v_a_270_, v_x_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(size_t v_sz_282_, size_t v_i_283_, lean_object* v_bs_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
uint8_t v___x_288_; 
v___x_288_ = lean_usize_dec_lt(v_i_283_, v_sz_282_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; 
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v_bs_284_);
return v___x_289_;
}
else
{
lean_object* v_v_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_v_290_ = lean_array_uget_borrowed(v_bs_284_, v_i_283_);
v___x_291_ = lean_box(0);
lean_inc(v___y_286_);
lean_inc_ref(v___y_285_);
lean_inc(v_v_290_);
v___x_292_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_v_290_, v___x_291_, v___y_285_, v___y_286_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; lean_object* v_bs_x27_295_; size_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref(v___x_292_);
v___x_294_ = lean_unsigned_to_nat(0u);
v_bs_x27_295_ = lean_array_uset(v_bs_284_, v_i_283_, v___x_294_);
v___x_296_ = ((size_t)1ULL);
v___x_297_ = lean_usize_add(v_i_283_, v___x_296_);
v___x_298_ = lean_array_uset(v_bs_x27_295_, v_i_283_, v_a_293_);
v_i_283_ = v___x_297_;
v_bs_284_ = v___x_298_;
goto _start;
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec_ref(v_bs_284_);
v_a_300_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_292_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_292_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg___boxed(lean_object* v_sz_308_, lean_object* v_i_309_, lean_object* v_bs_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
size_t v_sz_boxed_314_; size_t v_i_boxed_315_; lean_object* v_res_316_; 
v_sz_boxed_314_ = lean_unbox_usize(v_sz_308_);
lean_dec(v_sz_308_);
v_i_boxed_315_ = lean_unbox_usize(v_i_309_);
lean_dec(v_i_309_);
v_res_316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_boxed_314_, v_i_boxed_315_, v_bs_310_, v___y_311_, v___y_312_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta(lean_object* v_stx_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; size_t v_sz_330_; size_t v___x_331_; lean_object* v___x_332_; 
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = l_Lean_Syntax_getArg(v_stx_317_, v___x_327_);
v___x_329_ = l_Lean_Syntax_getArgs(v___x_328_);
lean_dec(v___x_328_);
v_sz_330_ = lean_array_size(v___x_329_);
v___x_331_ = ((size_t)0ULL);
lean_inc(v_a_325_);
lean_inc_ref(v_a_324_);
v___x_332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_330_, v___x_331_, v___x_329_, v_a_324_, v_a_325_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___f_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref(v___x_332_);
lean_inc(v_a_333_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDelta___lam__0___boxed), 11, 1);
lean_closure_set(v___f_334_, 0, v_a_333_);
v___x_335_ = lean_unsigned_to_nat(2u);
v___x_336_ = l_Lean_Syntax_getArg(v_stx_317_, v___x_335_);
v___x_337_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_336_);
lean_dec(v___x_336_);
lean_inc(v_a_333_);
v___x_338_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_deltaLocalDecl___boxed), 11, 1);
lean_closure_set(v___x_338_, 0, v_a_333_);
v___x_339_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_deltaTarget___boxed), 10, 1);
lean_closure_set(v___x_339_, 0, v_a_333_);
v___x_340_ = l_Lean_Elab_Tactic_withLocation(v___x_337_, v___x_338_, v___x_339_, v___f_334_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
lean_dec(v___x_337_);
return v___x_340_;
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
v_a_341_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_332_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_332_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___boxed(lean_object* v_stx_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Elab_Tactic_evalDelta(v_stx_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
lean_dec(v_stx_349_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0(size_t v_sz_360_, size_t v_i_361_, lean_object* v_bs_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_360_, v_i_361_, v_bs_362_, v___y_369_, v___y_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___boxed(lean_object* v_sz_373_, lean_object* v_i_374_, lean_object* v_bs_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
size_t v_sz_boxed_385_; size_t v_i_boxed_386_; lean_object* v_res_387_; 
v_sz_boxed_385_ = lean_unbox_usize(v_sz_373_);
lean_dec(v_sz_373_);
v_i_boxed_386_ = lean_unbox_usize(v_i_374_);
lean_dec(v_i_374_);
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0(v_sz_boxed_385_, v_i_boxed_386_, v_bs_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1(){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_404_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_405_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3));
v___x_406_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6));
v___x_407_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDelta___boxed), 10, 0);
v___x_408_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_404_, v___x_405_, v___x_406_, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___boxed(lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1();
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3(){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6));
v___x_414_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0));
v___x_415_ = l_Lean_addBuiltinDocString(v___x_413_, v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___boxed(lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3();
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5(){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6));
v___x_445_ = ((lean_object*)(l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6));
v___x_446_ = l_Lean_addBuiltinDeclarationRanges(v___x_444_, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___boxed(lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5();
return v_res_448_;
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
res = l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5();
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
