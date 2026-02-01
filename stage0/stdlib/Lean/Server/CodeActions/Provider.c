// Lean compiler output
// Module: Lean.Server.CodeActions.Provider
// Imports: public import Std.Data.Iterators.Producers.Range public import Std.Data.Iterators.Combinators.StepSize public import Lean.Elab.BuiltinTerm public import Lean.Elab.BuiltinNotation public import Lean.Server.CodeActions.Attr
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
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value;
static const lean_string_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value;
static const lean_string_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value;
static const lean_string_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabHole"};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(6, 231, 135, 173, 201, 53, 99, 157)}};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value;
static const lean_string_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "elabSyntheticHole"};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_1),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_2),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(54, 70, 171, 41, 20, 127, 159, 116)}};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value;
static const lean_string_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabSorry"};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_0),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_2),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(188, 135, 76, 60, 43, 16, 249, 86)}};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9_value)}};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10_value)}};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11_value;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_CodeAction_holeCodeActionProvider___closed__0;
lean_object* l_Array_instInhabited(lean_object*);
static lean_object* l_Lean_CodeAction_holeCodeActionProvider___closed__1;
static lean_object* l_Lean_CodeAction_holeCodeActionProvider___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_CodeAction_holeCodeActionProvider___closed__3;
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_CodeAction_holeCodeActionExt;
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "CodeAction"};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value;
static const lean_string_object l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "holeCodeActionProvider"};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_0),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 156, 186, 144, 130, 73, 162, 22)}};
static const lean_ctor_object l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_1),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(136, 16, 220, 55, 95, 189, 101, 35)}};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value;
lean_object* l_Lean_Server_addBuiltinCodeActionProvider(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2_value;
static const lean_string_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value;
static const lean_string_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeqBracketed"};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(142, 80, 121, 250, 245, 54, 71, 145)}};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_findTactic_x3f(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1_value;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_instInhabitedRequestError_default;
lean_object* l_instInhabitedEST___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0;
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Server.CodeActions.Provider"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.CodeAction.cmdCodeActionProvider"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_CodeAction_cmdCodeActionProvider___closed__0;
extern lean_object* l_Lean_CodeAction_instInhabitedCommandCodeActions_default;
static lean_object* l_Lean_CodeAction_cmdCodeActionProvider___closed__1;
static lean_object* l_Lean_CodeAction_cmdCodeActionProvider___closed__2;
extern lean_object* l_Lean_CodeAction_cmdCodeActionExt;
lean_object* l_Lean_Elab_InfoTree_foldInfoTree___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cmdCodeActionProvider"};
static const lean_object* l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0 = (const lean_object*)&l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value;
static const lean_ctor_object l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_0),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 156, 186, 144, 130, 73, 162, 22)}};
static const lean_ctor_object l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_1),((lean_object*)&l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 13, 245, 170, 192, 34, 91, 12)}};
static const lean_object* l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1 = (const lean_object*)&l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_name_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_6; uint8_t x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_14 = ((lean_object*)(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11));
x_15 = l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(x_12, x_14);
if (x_15 == 0)
{
lean_dec_ref(x_3);
return x_5;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Syntax_getPos_x3f(x_13, x_15);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Syntax_getTailPos_x3f(x_13, x_15);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_nat_dec_le(x_17, x_1);
lean_dec(x_17);
if (x_20 == 0)
{
lean_dec(x_19);
x_7 = x_20;
goto block_10;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_2, x_19);
lean_dec(x_19);
x_7 = x_21;
goto block_10;
}
}
else
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_3);
return x_5;
}
}
else
{
lean_dec(x_16);
lean_dec_ref(x_3);
return x_5;
}
}
block_10:
{
if (x_7 == 0)
{
lean_dec_ref(x_3);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_array_push(x_5, x_8);
return x_9;
}
}
}
else
{
lean_dec_ref(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_CodeAction_holeCodeActionProvider___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_6, x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_uget(x_5, x_6);
lean_inc_ref(x_9);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_19 = lean_apply_6(x_18, x_1, x_2, x_3, x_4, x_9, lean_box(0));
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Array_append___redArg(x_8, x_20);
lean_dec(x_20);
x_11 = x_21;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_dec_ref(x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
x_11 = x_22;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_19;
}
}
}
else
{
lean_object* x_23; 
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_8);
return x_23;
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
x_6 = x_14;
x_8 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(x_1, x_2, x_3, x_4, x_5, x_11, x_12, x_8, x_9);
lean_dec_ref(x_5);
return x_13;
}
}
static lean_object* _init_l_Lean_CodeAction_holeCodeActionProvider___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_CodeAction_holeCodeActionProvider___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_CodeAction_holeCodeActionProvider___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_CodeAction_holeCodeActionProvider___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_9, 3);
lean_inc_ref(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_12);
x_14 = l_Lean_FileMap_lspPosToUtf8Pos(x_11, x_12);
lean_inc_ref(x_13);
x_15 = l_Lean_FileMap_lspPosToUtf8Pos(x_11, x_13);
lean_dec_ref(x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed), 5, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_CodeAction_holeCodeActionProvider___closed__0;
lean_inc_ref(x_2);
x_19 = l_Lean_Server_Snapshots_Snapshot_infoTree(x_2);
x_20 = l_Lean_Elab_InfoTree_foldInfo___redArg(x_16, x_18, x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_20);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_24 = lean_array_fget(x_20, x_17);
lean_dec(x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_CodeAction_holeCodeActionExt;
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_CodeAction_holeCodeActionProvider___closed__2;
x_31 = l_Lean_Server_Snapshots_Snapshot_env(x_2);
x_32 = lean_box(0);
x_33 = l_Lean_PersistentEnvExtension_getState___redArg(x_30, x_27, x_31, x_29, x_32);
lean_dec(x_29);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_CodeAction_holeCodeActionProvider___closed__3;
x_36 = lean_array_get_size(x_34);
x_37 = lean_nat_dec_lt(x_17, x_36);
if (x_37 == 0)
{
lean_dec(x_34);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_ctor_set(x_5, 0, x_35);
return x_5;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_36, x_36);
if (x_38 == 0)
{
if (x_37 == 0)
{
lean_dec(x_34);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_ctor_set(x_5, 0, x_35);
return x_5;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
lean_free_object(x_5);
x_39 = 0;
x_40 = lean_usize_of_nat(x_36);
x_41 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(x_1, x_2, x_25, x_26, x_34, x_39, x_40, x_35, x_3);
lean_dec(x_34);
return x_41;
}
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; 
lean_free_object(x_5);
x_42 = 0;
x_43 = lean_usize_of_nat(x_36);
x_44 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(x_1, x_2, x_25, x_26, x_34, x_42, x_43, x_35, x_3);
lean_dec(x_34);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_45 = lean_ctor_get(x_5, 0);
lean_inc(x_45);
lean_dec(x_5);
x_46 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_47);
lean_dec_ref(x_46);
x_48 = lean_ctor_get(x_1, 3);
x_49 = lean_ctor_get(x_47, 3);
lean_inc_ref(x_49);
lean_dec_ref(x_47);
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_50);
x_52 = l_Lean_FileMap_lspPosToUtf8Pos(x_49, x_50);
lean_inc_ref(x_51);
x_53 = l_Lean_FileMap_lspPosToUtf8Pos(x_49, x_51);
lean_dec_ref(x_49);
x_54 = lean_alloc_closure((void*)(l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed), 5, 2);
lean_closure_set(x_54, 0, x_53);
lean_closure_set(x_54, 1, x_52);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_CodeAction_holeCodeActionProvider___closed__0;
lean_inc_ref(x_2);
x_57 = l_Lean_Server_Snapshots_Snapshot_infoTree(x_2);
x_58 = l_Lean_Elab_InfoTree_foldInfo___redArg(x_54, x_56, x_57);
x_59 = lean_array_get_size(x_58);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_dec_eq(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_58);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_56);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_63 = lean_array_fget(x_58, x_55);
lean_dec(x_58);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_CodeAction_holeCodeActionExt;
x_67 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_67, 2);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l_Lean_CodeAction_holeCodeActionProvider___closed__2;
x_70 = l_Lean_Server_Snapshots_Snapshot_env(x_2);
x_71 = lean_box(0);
x_72 = l_Lean_PersistentEnvExtension_getState___redArg(x_69, x_66, x_70, x_68, x_71);
lean_dec(x_68);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_CodeAction_holeCodeActionProvider___closed__3;
x_75 = lean_array_get_size(x_73);
x_76 = lean_nat_dec_lt(x_55, x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_73);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_74);
return x_77;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_75, x_75);
if (x_78 == 0)
{
if (x_76 == 0)
{
lean_object* x_79; 
lean_dec(x_73);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_74);
return x_79;
}
else
{
size_t x_80; size_t x_81; lean_object* x_82; 
x_80 = 0;
x_81 = lean_usize_of_nat(x_75);
x_82 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(x_1, x_2, x_64, x_65, x_73, x_80, x_81, x_74, x_3);
lean_dec(x_73);
return x_82;
}
}
else
{
size_t x_83; size_t x_84; lean_object* x_85; 
x_83 = 0;
x_84 = lean_usize_of_nat(x_75);
x_85 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(x_1, x_2, x_64, x_65, x_73, x_83, x_84, x_74, x_3);
lean_dec(x_73);
return x_85;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_CodeAction_holeCodeActionProvider(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2));
x_3 = lean_alloc_closure((void*)(l_Lean_CodeAction_holeCodeActionProvider___boxed), 4, 0);
x_4 = l_Lean_Server_addBuiltinCodeActionProvider(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_CodeAction_FindTacticResult_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_box(x_5);
x_9 = lean_apply_3(x_2, x_8, x_6, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_CodeAction_FindTacticResult_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = l_Lean_Syntax_getPos_x3f(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
if (lean_obj_tag(x_3) == 0)
{
lean_inc(x_7);
x_9 = x_7;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
lean_dec_ref(x_3);
x_9 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_nat_dec_le(x_9, x_10);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Syntax_getTailInfo(x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = lean_nat_sub(x_18, x_17);
lean_dec(x_17);
lean_dec(x_18);
x_20 = lean_nat_add(x_16, x_19);
lean_dec(x_19);
x_21 = lean_nat_dec_le(x_11, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
x_22 = lean_box(0);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_7, x_10);
lean_dec(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = lean_box(x_23);
if (lean_is_scalar(x_8)) {
 x_25 = lean_alloc_ctor(1, 1, 0);
} else {
 x_25 = x_8;
}
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_nat_dec_le(x_11, x_16);
lean_dec(x_16);
x_27 = lean_box(x_26);
if (lean_is_scalar(x_8)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_8;
}
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
x_29 = lean_box(0);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_4 == 1)
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_5 == 0)
{
lean_inc_ref(x_3);
return x_3;
}
else
{
lean_inc_ref(x_2);
return x_2;
}
}
else
{
lean_inc_ref(x_2);
return x_2;
}
}
else
{
lean_inc_ref(x_2);
return x_2;
}
}
else
{
lean_inc_ref(x_2);
return x_2;
}
}
else
{
lean_inc_ref(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_4, x_1);
if (x_11 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_dec_ref(x_5);
x_12 = lean_box(0);
x_13 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0));
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_mul(x_14, x_4);
x_16 = l_Lean_Syntax_getArg(x_2, x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = l_Lean_Syntax_getPos_x3f(x_16, x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 1)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_nat_dec_lt(x_21, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
lean_free_object(x_18);
x_6 = x_13;
goto block_10;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_3, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_3, 0);
lean_dec(x_25);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_3, 1, x_12);
lean_ctor_set(x_3, 0, x_18);
return x_3;
}
else
{
lean_object* x_26; 
lean_dec(x_3);
lean_ctor_set(x_18, 0, x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_3, 1);
x_29 = lean_nat_dec_lt(x_28, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
x_6 = x_13;
goto block_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_30 = x_3;
} else {
 lean_dec_ref(x_3);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_4);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_12);
return x_32;
}
}
}
else
{
lean_dec(x_18);
x_6 = x_13;
goto block_10;
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
x_4 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Syntax_getArg(x_1, x_2);
x_13 = l_Lean_Syntax_getTailPos_x3f(x_12, x_3);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
x_7 = x_5;
goto block_11;
}
else
{
lean_dec(x_5);
x_7 = x_13;
goto block_11;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_7, 2);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_nat_add(x_20, x_13);
lean_dec(x_13);
lean_dec(x_20);
x_22 = lean_nat_dec_lt(x_21, x_17);
if (x_22 == 0)
{
lean_dec(x_21);
lean_free_object(x_9);
lean_dec(x_17);
lean_free_object(x_7);
lean_dec(x_14);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_30; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_21, x_23);
lean_ctor_set(x_10, 0, x_24);
lean_inc(x_14);
lean_ctor_set(x_7, 0, x_14);
x_33 = l_Lean_Syntax_getArg(x_3, x_21);
x_34 = lean_box(0);
x_35 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(x_4, x_33, x_34);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_21);
lean_inc(x_5);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
lean_inc(x_33);
lean_inc_ref(x_38);
lean_inc_ref(x_4);
lean_inc_ref(x_6);
x_39 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(x_6, x_4, x_38, x_33, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec(x_33);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = lean_unbox(x_36);
lean_dec(x_36);
if (x_42 == 0)
{
lean_free_object(x_39);
lean_dec_ref(x_38);
lean_dec(x_33);
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set_tag(x_39, 0);
lean_ctor_set(x_39, 0, x_46);
x_30 = x_39;
goto block_32;
}
}
else
{
lean_object* x_47; 
lean_free_object(x_39);
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec(x_33);
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
lean_dec_ref(x_41);
x_30 = x_47;
goto block_32;
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = lean_unbox(x_36);
lean_dec(x_36);
if (x_49 == 0)
{
lean_dec_ref(x_38);
lean_dec(x_33);
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_33);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_38);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_30 = x_54;
goto block_32;
}
}
else
{
lean_object* x_55; 
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec(x_33);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec_ref(x_48);
x_30 = x_55;
goto block_32;
}
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_21);
goto _start;
}
block_29:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(x_1, x_25);
lean_dec_ref(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_8 = x_27;
goto _start;
}
block_32:
{
if (lean_obj_tag(x_8) == 0)
{
x_25 = x_30;
goto block_29;
}
else
{
lean_dec_ref(x_8);
if (x_2 == 0)
{
x_25 = x_30;
goto block_29;
}
else
{
lean_object* x_31; 
lean_dec_ref(x_30);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_31 = lean_box(0);
return x_31;
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_10, 0);
lean_inc(x_57);
lean_dec(x_10);
x_58 = lean_nat_add(x_57, x_13);
lean_dec(x_13);
lean_dec(x_57);
x_59 = lean_nat_dec_lt(x_58, x_17);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_58);
lean_free_object(x_9);
lean_dec(x_17);
lean_free_object(x_7);
lean_dec(x_14);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_8);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_69; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_58, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_9, 0, x_63);
lean_inc(x_14);
lean_ctor_set(x_7, 0, x_14);
x_72 = l_Lean_Syntax_getArg(x_3, x_58);
x_73 = lean_box(0);
x_74 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(x_4, x_72, x_73);
if (lean_obj_tag(x_74) == 1)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
lean_inc(x_3);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_3);
lean_ctor_set(x_76, 1, x_58);
lean_inc(x_5);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_5);
lean_inc(x_72);
lean_inc_ref(x_77);
lean_inc_ref(x_4);
lean_inc_ref(x_6);
x_78 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(x_6, x_4, x_77, x_72, x_73);
if (lean_obj_tag(x_78) == 0)
{
lean_dec_ref(x_77);
lean_dec(x_75);
lean_dec(x_72);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_81; 
x_81 = lean_unbox(x_75);
lean_dec(x_75);
if (x_81 == 0)
{
lean_dec(x_80);
lean_dec_ref(x_77);
lean_dec(x_72);
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_72);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_77);
if (lean_is_scalar(x_80)) {
 x_86 = lean_alloc_ctor(0, 1, 0);
} else {
 x_86 = x_80;
 lean_ctor_set_tag(x_86, 0);
}
lean_ctor_set(x_86, 0, x_85);
x_69 = x_86;
goto block_71;
}
}
else
{
lean_object* x_87; 
lean_dec(x_80);
lean_dec_ref(x_77);
lean_dec(x_75);
lean_dec(x_72);
x_87 = lean_ctor_get(x_79, 0);
lean_inc(x_87);
lean_dec_ref(x_79);
x_69 = x_87;
goto block_71;
}
}
}
else
{
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_58);
goto _start;
}
block_68:
{
lean_object* x_65; lean_object* x_66; 
x_65 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(x_1, x_64);
lean_dec_ref(x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_8 = x_66;
goto _start;
}
block_71:
{
if (lean_obj_tag(x_8) == 0)
{
x_64 = x_69;
goto block_68;
}
else
{
lean_dec_ref(x_8);
if (x_2 == 0)
{
x_64 = x_69;
goto block_68;
}
else
{
lean_object* x_70; 
lean_dec_ref(x_69);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_70 = lean_box(0);
return x_70;
}
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_9, 1);
lean_inc(x_89);
lean_dec(x_9);
x_90 = lean_ctor_get(x_10, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_91 = x_10;
} else {
 lean_dec_ref(x_10);
 x_91 = lean_box(0);
}
x_92 = lean_nat_add(x_90, x_13);
lean_dec(x_13);
lean_dec(x_90);
x_93 = lean_nat_dec_lt(x_92, x_89);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_92);
lean_dec(x_89);
lean_free_object(x_7);
lean_dec(x_14);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_91)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_91;
}
lean_ctor_set(x_94, 0, x_8);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_104; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_92, x_95);
if (lean_is_scalar(x_91)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_91;
}
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_89);
lean_inc(x_14);
lean_ctor_set(x_7, 2, x_98);
lean_ctor_set(x_7, 0, x_14);
x_107 = l_Lean_Syntax_getArg(x_3, x_92);
x_108 = lean_box(0);
x_109 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(x_4, x_107, x_108);
if (lean_obj_tag(x_109) == 1)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
lean_inc(x_3);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_3);
lean_ctor_set(x_111, 1, x_92);
lean_inc(x_5);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_5);
lean_inc(x_107);
lean_inc_ref(x_112);
lean_inc_ref(x_4);
lean_inc_ref(x_6);
x_113 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(x_6, x_4, x_112, x_107, x_108);
if (lean_obj_tag(x_113) == 0)
{
lean_dec_ref(x_112);
lean_dec(x_110);
lean_dec(x_107);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_116; 
x_116 = lean_unbox(x_110);
lean_dec(x_110);
if (x_116 == 0)
{
lean_dec(x_115);
lean_dec_ref(x_112);
lean_dec(x_107);
goto _start;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_107);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_112);
if (lean_is_scalar(x_115)) {
 x_121 = lean_alloc_ctor(0, 1, 0);
} else {
 x_121 = x_115;
 lean_ctor_set_tag(x_121, 0);
}
lean_ctor_set(x_121, 0, x_120);
x_104 = x_121;
goto block_106;
}
}
else
{
lean_object* x_122; 
lean_dec(x_115);
lean_dec_ref(x_112);
lean_dec(x_110);
lean_dec(x_107);
x_122 = lean_ctor_get(x_114, 0);
lean_inc(x_122);
lean_dec_ref(x_114);
x_104 = x_122;
goto block_106;
}
}
}
else
{
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_92);
goto _start;
}
block_103:
{
lean_object* x_100; lean_object* x_101; 
x_100 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(x_1, x_99);
lean_dec_ref(x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_8 = x_101;
goto _start;
}
block_106:
{
if (lean_obj_tag(x_8) == 0)
{
x_99 = x_104;
goto block_103;
}
else
{
lean_dec_ref(x_8);
if (x_2 == 0)
{
x_99 = x_104;
goto block_103;
}
else
{
lean_object* x_105; 
lean_dec_ref(x_104);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_105 = lean_box(0);
return x_105;
}
}
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_124 = lean_ctor_get(x_7, 0);
x_125 = lean_ctor_get(x_7, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_7);
x_126 = lean_ctor_get(x_9, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_127 = x_9;
} else {
 lean_dec_ref(x_9);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_10, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_129 = x_10;
} else {
 lean_dec_ref(x_10);
 x_129 = lean_box(0);
}
x_130 = lean_nat_add(x_128, x_124);
lean_dec(x_124);
lean_dec(x_128);
x_131 = lean_nat_dec_lt(x_130, x_126);
if (x_131 == 0)
{
lean_object* x_132; 
lean_dec(x_130);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_129;
}
lean_ctor_set(x_132, 0, x_8);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_143; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_nat_add(x_130, x_133);
if (lean_is_scalar(x_129)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_129;
}
lean_ctor_set(x_135, 0, x_134);
if (lean_is_scalar(x_127)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_127;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_126);
lean_inc(x_125);
x_137 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_137, 0, x_125);
lean_ctor_set(x_137, 1, x_125);
lean_ctor_set(x_137, 2, x_136);
x_146 = l_Lean_Syntax_getArg(x_3, x_130);
x_147 = lean_box(0);
x_148 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(x_4, x_146, x_147);
if (lean_obj_tag(x_148) == 1)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec_ref(x_148);
lean_inc(x_3);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_3);
lean_ctor_set(x_150, 1, x_130);
lean_inc(x_5);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_5);
lean_inc(x_146);
lean_inc_ref(x_151);
lean_inc_ref(x_4);
lean_inc_ref(x_6);
x_152 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(x_6, x_4, x_151, x_146, x_147);
if (lean_obj_tag(x_152) == 0)
{
lean_dec_ref(x_151);
lean_dec(x_149);
lean_dec(x_146);
lean_dec_ref(x_137);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
if (lean_obj_tag(x_153) == 0)
{
uint8_t x_155; 
x_155 = lean_unbox(x_149);
lean_dec(x_149);
if (x_155 == 0)
{
lean_dec(x_154);
lean_dec_ref(x_151);
lean_dec(x_146);
x_7 = x_137;
goto _start;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_146);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_151);
if (lean_is_scalar(x_154)) {
 x_160 = lean_alloc_ctor(0, 1, 0);
} else {
 x_160 = x_154;
 lean_ctor_set_tag(x_160, 0);
}
lean_ctor_set(x_160, 0, x_159);
x_143 = x_160;
goto block_145;
}
}
else
{
lean_object* x_161; 
lean_dec(x_154);
lean_dec_ref(x_151);
lean_dec(x_149);
lean_dec(x_146);
x_161 = lean_ctor_get(x_153, 0);
lean_inc(x_161);
lean_dec_ref(x_153);
x_143 = x_161;
goto block_145;
}
}
}
else
{
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_130);
x_7 = x_137;
goto _start;
}
block_142:
{
lean_object* x_139; lean_object* x_140; 
x_139 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(x_1, x_138);
lean_dec_ref(x_138);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_7 = x_137;
x_8 = x_140;
goto _start;
}
block_145:
{
if (lean_obj_tag(x_8) == 0)
{
x_138 = x_143;
goto block_142;
}
else
{
lean_dec_ref(x_8);
if (x_2 == 0)
{
x_138 = x_143;
goto block_142;
}
else
{
lean_object* x_144; 
lean_dec_ref(x_143);
lean_dec_ref(x_137);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_144 = lean_box(0);
return x_144;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_6 = l_Lean_Syntax_getKind(x_4);
x_7 = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3));
x_8 = lean_name_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Syntax_getNumArgs(x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(x_4, x_9, x_2, x_3, x_1, x_8, x_10, x_12);
lean_dec(x_9);
if (lean_obj_tag(x_13) == 0)
{
return x_11;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_56; 
lean_dec(x_5);
x_20 = lean_unsigned_to_nat(0u);
x_45 = l_Lean_Syntax_getArg(x_4, x_20);
lean_inc(x_45);
x_46 = l_Lean_Syntax_getKind(x_45);
x_47 = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6));
x_48 = lean_name_eq(x_46, x_47);
lean_dec(x_46);
if (x_48 == 0)
{
x_56 = x_20;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_unsigned_to_nat(1u);
x_56 = x_76;
goto block_75;
}
block_35:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_box(0);
x_25 = l_Lean_Syntax_getNumArgs(x_22);
x_26 = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4));
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_27);
x_30 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(x_23, x_8, x_22, x_2, x_21, x_1, x_29, x_24);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_23);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
lean_ctor_set(x_30, 0, x_23);
return x_30;
}
else
{
lean_object* x_34; 
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_23);
return x_34;
}
}
else
{
lean_dec_ref(x_31);
lean_dec(x_23);
return x_30;
}
}
}
block_44:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_20);
lean_inc(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
x_42 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_39);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_21 = x_37;
x_22 = x_38;
x_23 = x_43;
goto block_35;
}
block_55:
{
if (x_48 == 0)
{
lean_object* x_53; uint8_t x_54; 
lean_inc_ref(x_1);
x_53 = lean_apply_1(x_1, x_49);
x_54 = lean_unbox(x_53);
x_36 = x_52;
x_37 = x_50;
x_38 = x_51;
x_39 = x_54;
goto block_44;
}
else
{
lean_dec(x_49);
x_36 = x_52;
x_37 = x_50;
x_38 = x_51;
x_39 = x_8;
goto block_44;
}
}
block_75:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
lean_inc(x_56);
lean_inc(x_45);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_20);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_3);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Syntax_getArg(x_45, x_56);
lean_dec(x_56);
lean_dec(x_45);
x_62 = l_Lean_Syntax_getArg(x_61, x_20);
x_63 = 0;
x_64 = l_Lean_Syntax_getPos_x3f(x_62, x_63);
lean_dec(x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_box(0);
x_21 = x_60;
x_22 = x_61;
x_23 = x_65;
goto block_35;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = l_Lean_Syntax_getNumArgs(x_61);
x_68 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0));
lean_inc_ref(x_2);
x_69 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(x_67, x_61, x_2, x_20, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_67, x_71);
lean_dec(x_67);
x_73 = lean_nat_shiftr(x_72, x_71);
lean_dec(x_72);
x_49 = x_66;
x_50 = x_60;
x_51 = x_61;
x_52 = x_73;
goto block_55;
}
else
{
lean_object* x_74; 
lean_dec(x_67);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec_ref(x_70);
x_49 = x_66;
x_50 = x_60;
x_51 = x_61;
x_52 = x_74;
goto block_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_26; 
x_26 = lean_nat_dec_lt(x_7, x_2);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_8);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 1);
x_31 = l_Lean_Syntax_getArg(x_1, x_7);
lean_inc(x_30);
x_32 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(x_3, x_31, x_30);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_32);
lean_inc(x_7);
lean_inc(x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 0, x_1);
lean_inc(x_4);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_4);
lean_inc(x_30);
lean_inc_ref(x_3);
lean_inc_ref(x_5);
x_34 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(x_5, x_3, x_33, x_31, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_35 = lean_box(0);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec_ref(x_34);
if (lean_obj_tag(x_36) == 1)
{
if (lean_obj_tag(x_29) == 0)
{
if (x_6 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(x_1, x_7, x_26, x_36, x_30, x_37);
x_9 = x_38;
goto block_25;
}
else
{
lean_object* x_39; 
lean_dec_ref(x_36);
lean_dec(x_30);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_39 = lean_box(0);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec_ref(x_36);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_40 = lean_box(0);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(x_1, x_7, x_26, x_29, x_30, x_41);
x_9 = x_42;
goto block_25;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_32);
lean_dec(x_31);
lean_free_object(x_8);
x_43 = lean_box(0);
x_44 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(x_1, x_7, x_26, x_29, x_30, x_43);
x_9 = x_44;
goto block_25;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_8, 0);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_8);
x_47 = l_Lean_Syntax_getArg(x_1, x_7);
lean_inc(x_46);
x_48 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(x_3, x_47, x_46);
if (lean_obj_tag(x_48) == 1)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_48);
lean_inc(x_7);
lean_inc(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_7);
lean_inc(x_4);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_4);
lean_inc(x_46);
lean_inc_ref(x_3);
lean_inc_ref(x_5);
x_51 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(x_5, x_3, x_50, x_47, x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_52 = lean_box(0);
return x_52;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec_ref(x_51);
if (lean_obj_tag(x_53) == 1)
{
if (lean_obj_tag(x_45) == 0)
{
if (x_6 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_box(0);
x_55 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(x_1, x_7, x_26, x_53, x_46, x_54);
x_9 = x_55;
goto block_25;
}
else
{
lean_object* x_56; 
lean_dec_ref(x_53);
lean_dec(x_46);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_56 = lean_box(0);
return x_56;
}
}
else
{
lean_object* x_57; 
lean_dec_ref(x_53);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_57 = lean_box(0);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_53);
x_58 = lean_box(0);
x_59 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(x_1, x_7, x_26, x_45, x_46, x_58);
x_9 = x_59;
goto block_25;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_48);
lean_dec(x_47);
x_60 = lean_box(0);
x_61 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(x_1, x_7, x_26, x_45, x_46, x_60);
x_9 = x_61;
goto block_25;
}
}
}
block_25:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_9);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_7, x_15);
lean_dec(x_7);
x_7 = x_16;
x_8 = x_14;
goto _start;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_7, x_22);
lean_dec(x_7);
x_7 = x_23;
x_8 = x_21;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findTactic_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_5);
x_6 = lean_box(0);
x_7 = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(x_1, x_2, x_6, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
return x_4;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = lean_array_uget(x_7, x_9);
lean_inc(x_1);
x_18 = l_Lean_Elab_Info_updateContext_x3f(x_1, x_2);
lean_inc_ref(x_5);
x_19 = l_Lean_CodeAction_findInfoTree_x3f(x_3, x_4, x_18, x_17, x_5, x_6);
if (lean_obj_tag(x_19) == 1)
{
uint8_t x_20; 
lean_dec_ref(x_5);
lean_dec(x_1);
lean_inc_ref(x_19);
lean_ctor_set(x_10, 1, x_16);
lean_ctor_set(x_10, 0, x_19);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_10);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_14);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_19);
lean_free_object(x_10);
lean_dec(x_14);
x_27 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1));
x_28 = 1;
x_29 = lean_usize_add(x_9, x_28);
x_9 = x_29;
x_10 = x_27;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_dec(x_10);
x_32 = lean_box(0);
x_33 = lean_array_uget(x_7, x_9);
lean_inc(x_1);
x_34 = l_Lean_Elab_Info_updateContext_x3f(x_1, x_2);
lean_inc_ref(x_5);
x_35 = l_Lean_CodeAction_findInfoTree_x3f(x_3, x_4, x_34, x_33, x_5, x_6);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_5);
lean_dec(x_1);
lean_inc_ref(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; 
lean_dec(x_35);
lean_dec(x_31);
x_41 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1));
x_42 = 1;
x_43 = lean_usize_add(x_9, x_42);
x_9 = x_43;
x_10 = x_41;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = lean_array_uget(x_7, x_9);
lean_inc(x_1);
x_18 = l_Lean_Elab_Info_updateContext_x3f(x_1, x_2);
lean_inc_ref(x_5);
x_19 = l_Lean_CodeAction_findInfoTree_x3f(x_3, x_4, x_18, x_17, x_5, x_6);
if (lean_obj_tag(x_19) == 1)
{
uint8_t x_20; 
lean_dec_ref(x_5);
lean_dec(x_1);
lean_inc_ref(x_19);
lean_ctor_set(x_10, 1, x_16);
lean_ctor_set(x_10, 0, x_19);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_10);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_14);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
lean_dec(x_19);
lean_free_object(x_10);
lean_dec(x_14);
x_27 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1));
x_28 = 1;
x_29 = lean_usize_add(x_9, x_28);
x_30 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29, x_27);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_dec(x_10);
x_32 = lean_box(0);
x_33 = lean_array_uget(x_7, x_9);
lean_inc(x_1);
x_34 = l_Lean_Elab_Info_updateContext_x3f(x_1, x_2);
lean_inc_ref(x_5);
x_35 = l_Lean_CodeAction_findInfoTree_x3f(x_3, x_4, x_34, x_33, x_5, x_6);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_5);
lean_dec(x_1);
lean_inc_ref(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
lean_dec(x_35);
lean_dec(x_31);
x_41 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1));
x_42 = 1;
x_43 = lean_usize_add(x_9, x_42);
x_44 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_43, x_41);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_7);
lean_inc_ref(x_8);
lean_inc_ref(x_5);
lean_inc(x_1);
x_11 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_8);
lean_dec_ref(x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_5);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec_ref(x_10);
lean_dec_ref(x_5);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
lean_free_object(x_11);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_array_size(x_10);
x_20 = 0;
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_19, x_20, x_18);
lean_dec_ref(x_10);
if (lean_obj_tag(x_21) == 0)
{
return x_17;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_inc_ref(x_24);
lean_free_object(x_21);
lean_dec(x_23);
return x_24;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_26, 0);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_inc_ref(x_27);
lean_dec(x_26);
return x_27;
}
}
}
}
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_11, 0);
lean_inc(x_30);
lean_dec(x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_10);
lean_dec_ref(x_5);
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec_ref(x_30);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_array_size(x_10);
x_37 = 0;
x_38 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_36, x_37, x_35);
lean_dec_ref(x_10);
if (lean_obj_tag(x_38) == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_39, 0);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_inc_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
return x_41;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_4);
x_9 = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(x_7, x_3);
x_3 = x_9;
x_4 = x_8;
goto _start;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_19; uint8_t x_20; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_3, 0);
x_29 = l_Lean_Elab_Info_stx(x_11);
x_30 = l_Lean_Syntax_getRange_x3f(x_29, x_6);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Syntax_getKind(x_29);
x_33 = lean_name_eq(x_32, x_1);
lean_dec(x_32);
if (x_33 == 0)
{
lean_dec(x_31);
x_20 = x_33;
goto block_28;
}
else
{
uint8_t x_34; 
x_34 = l_Lean_Syntax_instBEqRange_beq(x_31, x_2);
lean_dec(x_31);
x_20 = x_34;
goto block_28;
}
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_dec_ref(x_4);
goto block_18;
}
block_28:
{
if (x_20 == 0)
{
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_dec_ref(x_4);
goto block_18;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_inc_ref(x_5);
lean_inc_ref(x_11);
lean_inc(x_19);
x_21 = lean_apply_2(x_5, x_19, x_11);
x_22 = lean_unbox(x_21);
if (x_22 == 0)
{
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_dec_ref(x_4);
goto block_18;
}
else
{
uint8_t x_23; 
lean_inc(x_19);
lean_dec_ref(x_5);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_3, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_3, 0, x_25);
return x_3;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_4);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
}
else
{
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_dec_ref(x_4);
goto block_18;
}
block_18:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0));
x_15 = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(x_3, x_11, x_1, x_2, x_5, x_6, x_12, x_14);
lean_dec_ref(x_11);
if (lean_obj_tag(x_15) == 0)
{
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
return x_13;
}
else
{
return x_17;
}
}
}
}
default: 
{
lean_object* x_35; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_35 = lean_box(0);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = lean_array_uget(x_7, x_9);
lean_inc(x_1);
x_18 = l_Lean_Elab_Info_updateContext_x3f(x_1, x_2);
lean_inc_ref(x_5);
x_19 = l_Lean_CodeAction_findInfoTree_x3f(x_3, x_4, x_18, x_17, x_5, x_6);
if (lean_obj_tag(x_19) == 1)
{
uint8_t x_20; 
lean_dec_ref(x_5);
lean_dec(x_1);
lean_inc_ref(x_19);
lean_ctor_set(x_10, 1, x_16);
lean_ctor_set(x_10, 0, x_19);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_10);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_14);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_10);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_14);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_19);
lean_free_object(x_10);
lean_dec(x_14);
x_29 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1));
x_30 = 1;
x_31 = lean_usize_add(x_9, x_30);
x_9 = x_31;
x_10 = x_29;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = lean_box(0);
x_35 = lean_array_uget(x_7, x_9);
lean_inc(x_1);
x_36 = l_Lean_Elab_Info_updateContext_x3f(x_1, x_2);
lean_inc_ref(x_5);
x_37 = l_Lean_CodeAction_findInfoTree_x3f(x_3, x_4, x_36, x_35, x_5, x_6);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_5);
lean_dec(x_1);
lean_inc_ref(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_39;
 lean_ctor_set_tag(x_40, 0);
}
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_33);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_37);
lean_dec(x_33);
x_44 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1));
x_45 = 1;
x_46 = lean_usize_add(x_9, x_45);
x_9 = x_46;
x_10 = x_44;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = lean_array_uget(x_7, x_9);
lean_inc(x_1);
x_18 = l_Lean_Elab_Info_updateContext_x3f(x_1, x_2);
lean_inc_ref(x_5);
x_19 = l_Lean_CodeAction_findInfoTree_x3f(x_3, x_4, x_18, x_17, x_5, x_6);
if (lean_obj_tag(x_19) == 1)
{
uint8_t x_20; 
lean_dec_ref(x_5);
lean_dec(x_1);
lean_inc_ref(x_19);
lean_ctor_set(x_10, 1, x_16);
lean_ctor_set(x_10, 0, x_19);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_10);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_14);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_10);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_14);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
lean_dec(x_19);
lean_free_object(x_10);
lean_dec(x_14);
x_29 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0));
x_30 = 1;
x_31 = lean_usize_add(x_9, x_30);
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = lean_box(0);
x_35 = lean_array_uget(x_7, x_9);
lean_inc(x_1);
x_36 = l_Lean_Elab_Info_updateContext_x3f(x_1, x_2);
lean_inc_ref(x_5);
x_37 = l_Lean_CodeAction_findInfoTree_x3f(x_3, x_4, x_36, x_35, x_5, x_6);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_5);
lean_dec(x_1);
lean_inc_ref(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_39;
 lean_ctor_set_tag(x_40, 0);
}
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_33);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
lean_dec(x_37);
lean_dec(x_33);
x_44 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0));
x_45 = 1;
x_46 = lean_usize_add(x_9, x_45);
x_47 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_46, x_44);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_array_size(x_11);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_14, x_15, x_13);
lean_dec_ref(x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_free_object(x_8);
return x_12;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_20);
lean_ctor_set(x_16, 0, x_8);
return x_16;
}
else
{
lean_inc_ref(x_19);
lean_free_object(x_16);
lean_dec(x_18);
lean_free_object(x_8);
return x_19;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_21, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_8);
return x_24;
}
else
{
lean_inc_ref(x_22);
lean_dec(x_21);
lean_free_object(x_8);
return x_22;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
x_28 = lean_array_size(x_25);
x_29 = 0;
x_30 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_25, x_28, x_29, x_27);
lean_dec_ref(x_25);
if (lean_obj_tag(x_30) == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
if (lean_is_scalar(x_32)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_32;
}
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_inc_ref(x_33);
lean_dec(x_32);
lean_dec(x_31);
return x_33;
}
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_9);
x_41 = lean_array_size(x_38);
x_42 = 0;
x_43 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_38, x_41, x_42, x_40);
lean_dec_ref(x_38);
if (lean_obj_tag(x_43) == 0)
{
lean_free_object(x_8);
return x_39;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_45, 0);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_ctor_set(x_8, 0, x_47);
lean_ctor_set(x_43, 0, x_8);
return x_43;
}
else
{
lean_inc_ref(x_46);
lean_free_object(x_43);
lean_dec(x_45);
lean_free_object(x_8);
return x_46;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_ctor_get(x_48, 0);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_ctor_set(x_8, 0, x_50);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_8);
return x_51;
}
else
{
lean_inc_ref(x_49);
lean_dec(x_48);
lean_free_object(x_8);
return x_49;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_8, 0);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_9);
x_55 = lean_array_size(x_52);
x_56 = 0;
x_57 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_52, x_55, x_56, x_54);
lean_dec_ref(x_52);
if (lean_obj_tag(x_57) == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_58, 0);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
else
{
lean_inc_ref(x_60);
lean_dec(x_59);
lean_dec(x_58);
return x_60;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_10, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_8, x_10);
lean_inc(x_15);
lean_inc_ref(x_5);
lean_inc(x_1);
x_18 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_free_object(x_11);
lean_dec(x_15);
lean_dec_ref(x_5);
lean_dec(x_1);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_11, 0, x_18);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
lean_ctor_set(x_11, 0, x_18);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_11);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec_ref(x_18);
lean_dec(x_15);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec_ref(x_20);
x_25 = lean_box(0);
lean_ctor_set(x_11, 1, x_24);
lean_ctor_set(x_11, 0, x_25);
x_26 = 1;
x_27 = lean_usize_add(x_10, x_26);
x_10 = x_27;
goto _start;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_array_uget(x_8, x_10);
lean_inc(x_29);
lean_inc_ref(x_5);
lean_inc(x_1);
x_31 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_30, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec_ref(x_5);
lean_dec(x_1);
x_32 = lean_box(0);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_5);
lean_dec(x_1);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_34 = x_33;
} else {
 lean_dec_ref(x_33);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_29);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_34;
 lean_ctor_set_tag(x_36, 1);
}
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
lean_dec_ref(x_31);
lean_dec(x_29);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec_ref(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = 1;
x_41 = lean_usize_add(x_10, x_40);
x_10 = x_41;
x_11 = x_39;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_6);
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_13, x_14, x_11);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
x_10 = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_6);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_12, x_13, x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_6);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_12, x_13, x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_6);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_12, x_13, x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_6);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_12, x_13, x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
x_11 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
x_8 = l_Lean_CodeAction_findInfoTree_x3f(x_1, x_2, x_3, x_4, x_5, x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_instInhabitedRequestError_default;
x_2 = lean_alloc_closure((void*)(l_instInhabitedEST___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0;
x_5 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_2(x_6, x_2, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_10) == 3)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_11, 1);
x_13 = 1;
x_14 = l_Lean_Syntax_getPos_x3f(x_12, x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Syntax_getTailPos_x3f(x_12, x_13);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_nat_dec_le(x_15, x_1);
lean_dec(x_15);
if (x_18 == 0)
{
lean_dec(x_17);
x_6 = x_18;
goto block_9;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_2, x_17);
lean_dec(x_17);
x_6 = x_19;
goto block_9;
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
block_9:
{
if (x_6 == 0)
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_array_push(x_5, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_CodeAction_cmdCodeActionProvider___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_7, x_6);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_uget(x_5, x_7);
lean_inc_ref(x_9);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_20 = lean_apply_6(x_19, x_1, x_2, x_3, x_4, x_9, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Array_append___redArg(x_8, x_21);
lean_dec(x_21);
x_11 = x_22;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_dec_ref(x_20);
x_11 = x_8;
x_12 = lean_box(0);
goto block_16;
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_7, x_13);
x_7 = x_14;
x_8 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(x_1, x_2, x_3, x_4, x_5, x_11, x_12, x_8, x_9);
lean_dec_ref(x_5);
return x_13;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2));
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_unsigned_to_nat(185u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1));
x_5 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_16; lean_object* x_17; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_6, x_5);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_array_uget(x_4, x_6);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_28) == 3)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
x_42 = l_Lean_Syntax_getKind(x_41);
x_43 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_32, x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_array_size(x_44);
x_46 = 0;
lean_inc_ref(x_8);
lean_inc_ref(x_27);
lean_inc(x_29);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_47 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(x_2, x_3, x_29, x_27, x_44, x_45, x_46, x_7, x_8);
lean_dec(x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc_ref(x_8);
x_33 = x_48;
x_34 = x_8;
x_35 = lean_box(0);
goto block_40;
}
else
{
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_47;
}
}
else
{
lean_dec(x_43);
lean_inc_ref(x_8);
x_33 = x_7;
x_34 = x_8;
x_35 = lean_box(0);
goto block_40;
}
block_40:
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = lean_array_size(x_31);
x_37 = 0;
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_38 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(x_2, x_3, x_29, x_27, x_31, x_36, x_37, x_33, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_10 = x_39;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_38;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_26);
lean_inc_ref(x_8);
x_16 = x_8;
x_17 = lean_box(0);
goto block_23;
}
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_inc_ref(x_8);
x_16 = x_8;
x_17 = lean_box(0);
goto block_23;
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_6, x_12);
x_6 = x_13;
x_7 = x_10;
goto _start;
}
block_23:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3;
x_19 = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(x_18, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_dec_ref(x_19);
x_10 = x_7;
x_11 = lean_box(0);
goto block_15;
}
else
{
uint8_t x_20; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_16; lean_object* x_17; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_6, x_5);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_array_uget(x_4, x_6);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_28) == 3)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get(x_3, 1);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
x_42 = l_Lean_Syntax_getKind(x_41);
x_43 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_32, x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_array_size(x_44);
x_46 = 0;
lean_inc_ref(x_8);
lean_inc_ref(x_27);
lean_inc(x_29);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_47 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(x_1, x_2, x_29, x_27, x_44, x_45, x_46, x_7, x_8);
lean_dec(x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc_ref(x_8);
x_33 = x_48;
x_34 = x_8;
x_35 = lean_box(0);
goto block_40;
}
else
{
lean_dec(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_47;
}
}
else
{
lean_dec(x_43);
lean_inc_ref(x_8);
x_33 = x_7;
x_34 = x_8;
x_35 = lean_box(0);
goto block_40;
}
block_40:
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = lean_array_size(x_31);
x_37 = 0;
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_38 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(x_1, x_2, x_29, x_27, x_31, x_36, x_37, x_33, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_10 = x_39;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_38;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_26);
lean_inc_ref(x_8);
x_16 = x_8;
x_17 = lean_box(0);
goto block_23;
}
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_inc_ref(x_8);
x_16 = x_8;
x_17 = lean_box(0);
goto block_23;
}
}
block_15:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_usize_add(x_6, x_12);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(x_3, x_1, x_2, x_4, x_5, x_13, x_10, x_8);
return x_14;
}
block_23:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3;
x_19 = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(x_18, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_dec_ref(x_19);
x_10 = x_7;
x_11 = lean_box(0);
goto block_15;
}
else
{
uint8_t x_20; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_CodeAction_instInhabitedCommandCodeActions_default;
x_2 = l_Lean_CodeAction_cmdCodeActionProvider___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_5 = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_CodeAction_cmdCodeActionExt;
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_CodeAction_cmdCodeActionProvider___closed__1;
x_17 = l_Lean_Server_Snapshots_Snapshot_env(x_2);
x_18 = lean_box(0);
x_19 = l_Lean_PersistentEnvExtension_getState___redArg(x_16, x_13, x_17, x_15, x_18);
lean_dec(x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc_ref(x_11);
x_21 = l_Lean_FileMap_lspPosToUtf8Pos(x_10, x_11);
lean_inc_ref(x_12);
x_22 = l_Lean_FileMap_lspPosToUtf8Pos(x_10, x_12);
lean_dec_ref(x_10);
x_23 = lean_alloc_closure((void*)(l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed), 5, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
x_24 = l_Lean_CodeAction_cmdCodeActionProvider___closed__2;
lean_inc_ref(x_2);
x_25 = l_Lean_Server_Snapshots_Snapshot_infoTree(x_2);
x_26 = l_Lean_Elab_InfoTree_foldInfoTree___redArg(x_24, x_23, x_25);
x_27 = lean_array_size(x_26);
x_28 = 0;
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(x_1, x_2, x_20, x_26, x_27, x_28, x_24, x_3);
lean_dec(x_26);
lean_dec(x_20);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_CodeAction_cmdCodeActionProvider(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1));
x_3 = lean_alloc_closure((void*)(l_Lean_CodeAction_cmdCodeActionProvider___boxed), 4, 0);
x_4 = l_Lean_Server_addBuiltinCodeActionProvider(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
return x_2;
}
}
lean_object* initialize_Std_Data_Iterators_Producers_Range(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Combinators_StepSize(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinTerm(uint8_t builtin);
lean_object* initialize_Lean_Elab_BuiltinNotation(uint8_t builtin);
lean_object* initialize_Lean_Server_CodeActions_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_CodeActions_Provider(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Producers_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinNotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_CodeActions_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CodeAction_holeCodeActionProvider___closed__0 = _init_l_Lean_CodeAction_holeCodeActionProvider___closed__0();
lean_mark_persistent(l_Lean_CodeAction_holeCodeActionProvider___closed__0);
l_Lean_CodeAction_holeCodeActionProvider___closed__1 = _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1();
lean_mark_persistent(l_Lean_CodeAction_holeCodeActionProvider___closed__1);
l_Lean_CodeAction_holeCodeActionProvider___closed__2 = _init_l_Lean_CodeAction_holeCodeActionProvider___closed__2();
lean_mark_persistent(l_Lean_CodeAction_holeCodeActionProvider___closed__2);
l_Lean_CodeAction_holeCodeActionProvider___closed__3 = _init_l_Lean_CodeAction_holeCodeActionProvider___closed__3();
lean_mark_persistent(l_Lean_CodeAction_holeCodeActionProvider___closed__3);
if (builtin) {res = l_Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0 = _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
l_Lean_CodeAction_cmdCodeActionProvider___closed__0 = _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0();
lean_mark_persistent(l_Lean_CodeAction_cmdCodeActionProvider___closed__0);
l_Lean_CodeAction_cmdCodeActionProvider___closed__1 = _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1();
lean_mark_persistent(l_Lean_CodeAction_cmdCodeActionProvider___closed__1);
l_Lean_CodeAction_cmdCodeActionProvider___closed__2 = _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__2();
lean_mark_persistent(l_Lean_CodeAction_cmdCodeActionProvider___closed__2);
if (builtin) {res = l_Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
