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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_CodeAction_instInhabitedCommandCodeActions_default;
lean_object* l_Array_instInhabited___redArg();
extern lean_object* l_Lean_CodeAction_cmdCodeActionExt;
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfoTree___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_instInhabitedRequestError_default;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_CodeAction_holeCodeActionExt;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Server_addBuiltinCodeActionProvider(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_CodeAction_holeCodeActionProvider___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_holeCodeActionProvider___closed__0;
static lean_once_cell_t l_Lean_CodeAction_holeCodeActionProvider___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_holeCodeActionProvider___closed__1;
static const lean_array_object l_Lean_CodeAction_holeCodeActionProvider___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___closed__2 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___closed__2_value;
static const lean_array_object l_Lean_CodeAction_holeCodeActionProvider___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___closed__3 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "CodeAction"};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value;
static const lean_string_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "holeCodeActionProvider"};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 156, 186, 144, 130, 73, 162, 22)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(136, 16, 220, 55, 95, 189, 101, 35)}};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeqBracketed"};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(142, 80, 121, 250, 245, 54, 71, 145)}};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0;
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_CodeAction_cmdCodeActionProvider___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_cmdCodeActionProvider___closed__0;
static const lean_array_object l_Lean_CodeAction_cmdCodeActionProvider___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CodeAction_cmdCodeActionProvider___closed__1 = (const lean_object*)&l_Lean_CodeAction_cmdCodeActionProvider___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cmdCodeActionProvider"};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 156, 186, 144, 130, 73, 162, 22)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 13, 245, 170, 192, 34, 91, 12)}};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(lean_object* v___y_1_){
_start:
{
lean_object* v_doc_3_; lean_object* v___x_4_; 
v_doc_3_ = lean_ctor_get(v___y_1_, 1);
lean_inc_ref(v_doc_3_);
v___x_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4_, 0, v_doc_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0___boxed(lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v___y_5_);
lean_dec_ref(v___y_5_);
return v_res_7_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
else
{
lean_object* v_head_11_; lean_object* v_tail_12_; uint8_t v___x_13_; 
v_head_11_ = lean_ctor_get(v_x_9_, 0);
v_tail_12_ = lean_ctor_get(v_x_9_, 1);
v___x_13_ = lean_name_eq(v_a_8_, v_head_11_);
if (v___x_13_ == 0)
{
v_x_9_ = v_tail_12_;
goto _start;
}
else
{
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1___boxed(lean_object* v_a_15_, lean_object* v_x_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(v_a_15_, v_x_16_);
lean_dec(v_x_16_);
lean_dec(v_a_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0(lean_object* v___x_49_, lean_object* v___x_50_, lean_object* v_ctx_51_, lean_object* v_info_52_, lean_object* v_result_53_){
_start:
{
if (lean_obj_tag(v_info_52_) == 1)
{
lean_object* v_i_54_; lean_object* v_toElabInfo_55_; lean_object* v_elaborator_56_; lean_object* v_stx_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_73_; 
v_i_54_ = lean_ctor_get(v_info_52_, 0);
lean_inc_ref(v_i_54_);
lean_dec_ref_known(v_info_52_, 1);
v_toElabInfo_55_ = lean_ctor_get(v_i_54_, 0);
lean_inc_ref(v_toElabInfo_55_);
v_elaborator_56_ = lean_ctor_get(v_toElabInfo_55_, 0);
v_stx_57_ = lean_ctor_get(v_toElabInfo_55_, 1);
v_isSharedCheck_73_ = !lean_is_exclusive(v_toElabInfo_55_);
if (v_isSharedCheck_73_ == 0)
{
v___x_59_ = v_toElabInfo_55_;
v_isShared_60_ = v_isSharedCheck_73_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_stx_57_);
lean_inc(v_elaborator_56_);
lean_dec(v_toElabInfo_55_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_73_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = ((lean_object*)(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11));
v___x_62_ = l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(v_elaborator_56_, v___x_61_);
lean_dec(v_elaborator_56_);
if (v___x_62_ == 0)
{
lean_del_object(v___x_59_);
lean_dec(v_stx_57_);
lean_dec_ref(v_i_54_);
lean_dec_ref(v_ctx_51_);
return v_result_53_;
}
else
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Syntax_getPos_x3f(v_stx_57_, v___x_62_);
if (lean_obj_tag(v___x_63_) == 1)
{
lean_object* v_val_64_; lean_object* v___x_65_; 
v_val_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_val_64_);
lean_dec_ref_known(v___x_63_, 1);
v___x_65_ = l_Lean_Syntax_getTailPos_x3f(v_stx_57_, v___x_62_);
lean_dec(v_stx_57_);
if (lean_obj_tag(v___x_65_) == 1)
{
lean_object* v_val_66_; uint8_t v___x_67_; 
v_val_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_val_66_);
lean_dec_ref_known(v___x_65_, 1);
v___x_67_ = lean_nat_dec_le(v_val_64_, v___x_49_);
lean_dec(v_val_64_);
if (v___x_67_ == 0)
{
lean_dec(v_val_66_);
lean_del_object(v___x_59_);
lean_dec_ref(v_i_54_);
lean_dec_ref(v_ctx_51_);
return v_result_53_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = lean_nat_dec_le(v___x_50_, v_val_66_);
lean_dec(v_val_66_);
if (v___x_68_ == 0)
{
lean_del_object(v___x_59_);
lean_dec_ref(v_i_54_);
lean_dec_ref(v_ctx_51_);
return v_result_53_;
}
else
{
lean_object* v___x_70_; 
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v_i_54_);
lean_ctor_set(v___x_59_, 0, v_ctx_51_);
v___x_70_ = v___x_59_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_ctx_51_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v_i_54_);
v___x_70_ = v_reuseFailAlloc_72_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; 
v___x_71_ = lean_array_push(v_result_53_, v___x_70_);
return v___x_71_;
}
}
}
}
else
{
lean_dec(v___x_65_);
lean_dec(v_val_64_);
lean_del_object(v___x_59_);
lean_dec_ref(v_i_54_);
lean_dec_ref(v_ctx_51_);
return v_result_53_;
}
}
else
{
lean_dec(v___x_63_);
lean_del_object(v___x_59_);
lean_dec(v_stx_57_);
lean_dec_ref(v_i_54_);
lean_dec_ref(v_ctx_51_);
return v_result_53_;
}
}
}
}
else
{
lean_dec_ref(v_info_52_);
lean_dec_ref(v_ctx_51_);
return v_result_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed(lean_object* v___x_74_, lean_object* v___x_75_, lean_object* v_ctx_76_, lean_object* v_info_77_, lean_object* v_result_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_CodeAction_holeCodeActionProvider___lam__0(v___x_74_, v___x_75_, v_ctx_76_, v_info_77_, v_result_78_);
lean_dec(v___x_75_);
lean_dec(v___x_74_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(lean_object* v_params_80_, lean_object* v_snap_81_, lean_object* v_fst_82_, lean_object* v_snd_83_, lean_object* v_as_84_, size_t v_i_85_, size_t v_stop_86_, lean_object* v_b_87_, lean_object* v___y_88_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lean_usize_dec_eq(v_i_85_, v_stop_86_);
if (v___x_90_ == 0)
{
lean_object* v___x_1568__overap_91_; lean_object* v___x_92_; 
v___x_1568__overap_91_ = lean_array_uget_borrowed(v_as_84_, v_i_85_);
lean_inc(v___x_1568__overap_91_);
lean_inc_ref(v___y_88_);
lean_inc_ref(v_snd_83_);
lean_inc_ref(v_fst_82_);
lean_inc_ref(v_snap_81_);
lean_inc_ref(v_params_80_);
v___x_92_ = lean_apply_6(v___x_1568__overap_91_, v_params_80_, v_snap_81_, v_fst_82_, v_snd_83_, v___y_88_, lean_box(0));
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_94_; size_t v___x_95_; size_t v___x_96_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_a_93_);
lean_dec_ref_known(v___x_92_, 1);
v___x_94_ = l_Array_append___redArg(v_b_87_, v_a_93_);
lean_dec(v_a_93_);
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_add(v_i_85_, v___x_95_);
v_i_85_ = v___x_96_;
v_b_87_ = v___x_94_;
goto _start;
}
else
{
lean_dec_ref(v_b_87_);
lean_dec_ref(v_snd_83_);
lean_dec_ref(v_fst_82_);
lean_dec_ref(v_snap_81_);
lean_dec_ref(v_params_80_);
return v___x_92_;
}
}
else
{
lean_object* v___x_98_; 
lean_dec_ref(v_snd_83_);
lean_dec_ref(v_fst_82_);
lean_dec_ref(v_snap_81_);
lean_dec_ref(v_params_80_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v_b_87_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2___boxed(lean_object* v_params_99_, lean_object* v_snap_100_, lean_object* v_fst_101_, lean_object* v_snd_102_, lean_object* v_as_103_, lean_object* v_i_104_, lean_object* v_stop_105_, lean_object* v_b_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
size_t v_i_boxed_109_; size_t v_stop_boxed_110_; lean_object* v_res_111_; 
v_i_boxed_109_ = lean_unbox_usize(v_i_104_);
lean_dec(v_i_104_);
v_stop_boxed_110_ = lean_unbox_usize(v_stop_105_);
lean_dec(v_stop_105_);
v_res_111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_99_, v_snap_100_, v_fst_101_, v_snd_102_, v_as_103_, v_i_boxed_109_, v_stop_boxed_110_, v_b_106_, v___y_107_);
lean_dec_ref(v___y_107_);
lean_dec_ref(v_as_103_);
return v_res_111_;
}
}
static lean_object* _init_l_Lean_CodeAction_holeCodeActionProvider___closed__0(void){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Array_instInhabited___redArg();
return v___x_112_;
}
}
static lean_object* _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_obj_once(&l_Lean_CodeAction_holeCodeActionProvider___closed__0, &l_Lean_CodeAction_holeCodeActionProvider___closed__0_once, _init_l_Lean_CodeAction_holeCodeActionProvider___closed__0);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider(lean_object* v_params_119_, lean_object* v_snap_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_168_; 
v___x_123_ = lean_obj_once(&l_Lean_CodeAction_holeCodeActionProvider___closed__1, &l_Lean_CodeAction_holeCodeActionProvider___closed__1_once, _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1);
v___x_124_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v_a_121_);
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_168_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_168_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_168_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v_toEditableDocumentCore_129_; lean_object* v_meta_130_; lean_object* v_range_131_; lean_object* v_text_132_; lean_object* v_start_133_; lean_object* v_end_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___f_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_toEditableDocumentCore_129_ = lean_ctor_get(v_a_125_, 0);
lean_inc_ref(v_toEditableDocumentCore_129_);
lean_dec(v_a_125_);
v_meta_130_ = lean_ctor_get(v_toEditableDocumentCore_129_, 0);
lean_inc_ref(v_meta_130_);
lean_dec_ref(v_toEditableDocumentCore_129_);
v_range_131_ = lean_ctor_get(v_params_119_, 3);
v_text_132_ = lean_ctor_get(v_meta_130_, 3);
lean_inc_ref(v_text_132_);
lean_dec_ref(v_meta_130_);
v_start_133_ = lean_ctor_get(v_range_131_, 0);
v_end_134_ = lean_ctor_get(v_range_131_, 1);
lean_inc_ref(v_start_133_);
v___x_135_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_132_, v_start_133_);
lean_inc_ref(v_end_134_);
v___x_136_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_132_, v_end_134_);
lean_dec_ref(v_text_132_);
v___f_137_ = lean_alloc_closure((void*)(l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed), 5, 2);
lean_closure_set(v___f_137_, 0, v___x_136_);
lean_closure_set(v___f_137_, 1, v___x_135_);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = ((lean_object*)(l_Lean_CodeAction_holeCodeActionProvider___closed__2));
lean_inc_ref(v_snap_120_);
v___x_140_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_120_);
v___x_141_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_137_, v___x_139_, v___x_140_);
v___x_142_ = lean_array_get_size(v___x_141_);
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_nat_dec_eq(v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_146_; 
lean_dec(v___x_141_);
lean_dec_ref(v_snap_120_);
lean_dec_ref(v_params_119_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_139_);
v___x_146_ = v___x_127_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_139_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
else
{
lean_object* v___x_148_; lean_object* v_fst_149_; lean_object* v_snd_150_; lean_object* v___x_151_; lean_object* v_toEnvExtension_152_; lean_object* v_asyncMode_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v_snd_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_148_ = lean_array_fget(v___x_141_, v___x_138_);
lean_dec(v___x_141_);
v_fst_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_fst_149_);
v_snd_150_ = lean_ctor_get(v___x_148_, 1);
lean_inc(v_snd_150_);
lean_dec(v___x_148_);
v___x_151_ = l_Lean_CodeAction_holeCodeActionExt;
v_toEnvExtension_152_ = lean_ctor_get(v___x_151_, 0);
v_asyncMode_153_ = lean_ctor_get(v_toEnvExtension_152_, 2);
v___x_154_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_120_);
v___x_155_ = lean_box(0);
v___x_156_ = 0;
v___x_157_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_123_, v___x_151_, v___x_154_, v_asyncMode_153_, v___x_155_, v___x_156_);
v_snd_158_ = lean_ctor_get(v___x_157_, 1);
lean_inc(v_snd_158_);
lean_dec(v___x_157_);
v___x_159_ = ((lean_object*)(l_Lean_CodeAction_holeCodeActionProvider___closed__3));
v___x_160_ = lean_array_get_size(v_snd_158_);
v___x_161_ = lean_nat_dec_lt(v___x_138_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_163_; 
lean_dec(v_snd_158_);
lean_dec(v_snd_150_);
lean_dec(v_fst_149_);
lean_dec_ref(v_snap_120_);
lean_dec_ref(v_params_119_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_159_);
v___x_163_ = v___x_127_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_159_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
else
{
size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; 
lean_del_object(v___x_127_);
v___x_165_ = ((size_t)0ULL);
v___x_166_ = lean_usize_of_nat(v___x_160_);
v___x_167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_119_, v_snap_120_, v_fst_149_, v_snd_150_, v_snd_158_, v___x_165_, v___x_166_, v___x_159_, v_a_121_);
lean_dec(v_snd_158_);
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___boxed(lean_object* v_params_169_, lean_object* v_snap_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_CodeAction_holeCodeActionProvider(v_params_169_, v_snap_170_, v_a_171_);
lean_dec_ref(v_a_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1(){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2));
v___x_182_ = lean_alloc_closure((void*)(l_Lean_CodeAction_holeCodeActionProvider___boxed), 4, 0);
v___x_183_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___boxed(lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx___impl(lean_object* v_x_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_tag_nat(v_x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx___impl___boxed(lean_object* v_x_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_CodeAction_FindTacticResult_ctorIdx___impl(v_x_188_);
lean_dec_ref(v_x_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(lean_object* v_t_190_, lean_object* v_k_191_){
_start:
{
if (lean_obj_tag(v_t_190_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_193_; 
v_a_192_ = lean_ctor_get(v_t_190_, 0);
lean_inc(v_a_192_);
lean_dec_ref_known(v_t_190_, 1);
v___x_193_ = lean_apply_1(v_k_191_, v_a_192_);
return v___x_193_;
}
else
{
uint8_t v_preferred_194_; lean_object* v_insertIdx_195_; lean_object* v_a_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_preferred_194_ = lean_ctor_get_uint8(v_t_190_, sizeof(void*)*2);
v_insertIdx_195_ = lean_ctor_get(v_t_190_, 0);
lean_inc(v_insertIdx_195_);
v_a_196_ = lean_ctor_get(v_t_190_, 1);
lean_inc(v_a_196_);
lean_dec_ref_known(v_t_190_, 2);
v___x_197_ = lean_box(v_preferred_194_);
v___x_198_ = lean_apply_3(v_k_191_, v___x_197_, v_insertIdx_195_, v_a_196_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim(lean_object* v_motive_199_, lean_object* v_ctorIdx_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_k_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_201_, v_k_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___boxed(lean_object* v_motive_205_, lean_object* v_ctorIdx_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_k_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_CodeAction_FindTacticResult_ctorElim(v_motive_205_, v_ctorIdx_206_, v_t_207_, v_h_208_, v_k_209_);
lean_dec(v_ctorIdx_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim___redArg(lean_object* v_t_211_, lean_object* v_tactic_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_211_, v_tactic_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim(lean_object* v_motive_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_tactic_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_215_, v_tactic_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim___redArg(lean_object* v_t_219_, lean_object* v_tacticSeq_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_219_, v_tacticSeq_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim(lean_object* v_motive_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_tacticSeq_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_223_, v_tacticSeq_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(lean_object* v_range_227_, lean_object* v_stx_228_, lean_object* v_prev_x3f_229_){
_start:
{
uint8_t v___x_230_; lean_object* v___x_231_; 
v___x_230_ = 1;
v___x_231_ = l_Lean_Syntax_getPos_x3f(v_stx_228_, v___x_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; 
lean_dec(v_prev_x3f_229_);
v___x_232_ = lean_box(0);
return v___x_232_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_264_; 
v_val_233_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_264_ == 0)
{
v___x_235_ = v___x_231_;
v_isShared_236_ = v_isSharedCheck_264_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_val_233_);
lean_dec(v___x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_264_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___y_238_; 
if (lean_obj_tag(v_prev_x3f_229_) == 0)
{
lean_inc(v_val_233_);
v___y_238_ = v_val_233_;
goto v___jp_237_;
}
else
{
lean_object* v_val_263_; 
v_val_263_ = lean_ctor_get(v_prev_x3f_229_, 0);
lean_inc(v_val_263_);
lean_dec_ref_known(v_prev_x3f_229_, 1);
v___y_238_ = v_val_263_;
goto v___jp_237_;
}
v___jp_237_:
{
lean_object* v_start_239_; lean_object* v_stop_240_; uint8_t v___x_241_; 
v_start_239_ = lean_ctor_get(v_range_227_, 0);
v_stop_240_ = lean_ctor_get(v_range_227_, 1);
v___x_241_ = lean_nat_dec_le(v___y_238_, v_start_239_);
lean_dec(v___y_238_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
lean_del_object(v___x_235_);
lean_dec(v_val_233_);
v___x_242_ = lean_box(0);
return v___x_242_;
}
else
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Syntax_getTailInfo(v_stx_228_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_trailing_244_; lean_object* v_endPos_245_; lean_object* v_startPos_246_; lean_object* v_stopPos_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v_trailing_244_ = lean_ctor_get(v___x_243_, 2);
lean_inc_ref(v_trailing_244_);
v_endPos_245_ = lean_ctor_get(v___x_243_, 3);
lean_inc(v_endPos_245_);
lean_dec_ref_known(v___x_243_, 4);
v_startPos_246_ = lean_ctor_get(v_trailing_244_, 1);
lean_inc(v_startPos_246_);
v_stopPos_247_ = lean_ctor_get(v_trailing_244_, 2);
lean_inc(v_stopPos_247_);
lean_dec_ref(v_trailing_244_);
v___x_248_ = lean_nat_sub(v_stopPos_247_, v_startPos_246_);
lean_dec(v_startPos_246_);
lean_dec(v_stopPos_247_);
v___x_249_ = lean_nat_add(v_endPos_245_, v___x_248_);
lean_dec(v___x_248_);
v___x_250_ = lean_nat_dec_le(v_stop_240_, v___x_249_);
lean_dec(v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
lean_dec(v_endPos_245_);
lean_del_object(v___x_235_);
lean_dec(v_val_233_);
v___x_251_ = lean_box(0);
return v___x_251_;
}
else
{
uint8_t v___x_252_; 
v___x_252_ = lean_nat_dec_le(v_val_233_, v_start_239_);
lean_dec(v_val_233_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_255_; 
lean_dec(v_endPos_245_);
v___x_253_ = lean_box(v___x_252_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_253_);
v___x_255_ = v___x_235_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
else
{
uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_257_ = lean_nat_dec_le(v_stop_240_, v_endPos_245_);
lean_dec(v_endPos_245_);
v___x_258_ = lean_box(v___x_257_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_258_);
v___x_260_ = v___x_235_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v___x_262_; 
lean_dec(v___x_243_);
lean_del_object(v___x_235_);
lean_dec(v_val_233_);
v___x_262_ = lean_box(0);
return v___x_262_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit___boxed(lean_object* v_range_265_, lean_object* v_stx_266_, lean_object* v_prev_x3f_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_265_, v_stx_266_, v_prev_x3f_267_);
lean_dec(v_stx_266_);
lean_dec_ref(v_range_265_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(lean_object* v_r_u2081_269_, lean_object* v_r_u2082_270_){
_start:
{
if (lean_obj_tag(v_r_u2081_269_) == 1)
{
lean_object* v_val_271_; 
v_val_271_ = lean_ctor_get(v_r_u2081_269_, 0);
if (lean_obj_tag(v_val_271_) == 1)
{
uint8_t v_preferred_272_; 
v_preferred_272_ = lean_ctor_get_uint8(v_val_271_, sizeof(void*)*2);
if (v_preferred_272_ == 1)
{
if (lean_obj_tag(v_r_u2082_270_) == 1)
{
uint8_t v_preferred_273_; 
v_preferred_273_ = lean_ctor_get_uint8(v_r_u2082_270_, sizeof(void*)*2);
if (v_preferred_273_ == 0)
{
lean_inc_ref(v_val_271_);
return v_val_271_;
}
else
{
lean_inc_ref(v_r_u2082_270_);
return v_r_u2082_270_;
}
}
else
{
lean_inc_ref(v_r_u2082_270_);
return v_r_u2082_270_;
}
}
else
{
lean_inc_ref(v_r_u2082_270_);
return v_r_u2082_270_;
}
}
else
{
lean_inc_ref(v_r_u2082_270_);
return v_r_u2082_270_;
}
}
else
{
lean_inc_ref(v_r_u2082_270_);
return v_r_u2082_270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge___boxed(lean_object* v_r_u2081_274_, lean_object* v_r_u2082_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(v_r_u2081_274_, v_r_u2082_275_);
lean_dec_ref(v_r_u2082_275_);
lean_dec(v_r_u2081_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(lean_object* v_upperBound_280_, lean_object* v___x_281_, lean_object* v_range_282_, lean_object* v_a_283_, lean_object* v_b_284_){
_start:
{
lean_object* v_a_286_; uint8_t v___x_290_; 
v___x_290_ = lean_nat_dec_lt(v_a_283_, v_upperBound_280_);
if (v___x_290_ == 0)
{
lean_dec(v_a_283_);
lean_dec_ref(v_range_282_);
lean_inc_ref(v_b_284_);
return v_b_284_;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; lean_object* v___x_297_; 
v___x_291_ = lean_box(0);
v___x_292_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0));
v___x_293_ = lean_unsigned_to_nat(2u);
v___x_294_ = lean_nat_mul(v___x_293_, v_a_283_);
v___x_295_ = l_Lean_Syntax_getArg(v___x_281_, v___x_294_);
lean_dec(v___x_294_);
v___x_296_ = 0;
v___x_297_ = l_Lean_Syntax_getPos_x3f(v___x_295_, v___x_296_);
lean_dec(v___x_295_);
if (lean_obj_tag(v___x_297_) == 1)
{
lean_object* v_val_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_318_; 
v_val_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_318_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_318_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_val_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_318_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_stop_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_stop_302_ = lean_ctor_get(v_range_282_, 1);
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_add(v_stop_302_, v___x_303_);
v___x_305_ = lean_nat_dec_le(v___x_304_, v_val_298_);
lean_dec(v_val_298_);
lean_dec(v___x_304_);
if (v___x_305_ == 0)
{
lean_del_object(v___x_300_);
v_a_286_ = v___x_292_;
goto v___jp_285_;
}
else
{
lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_315_; 
v_isSharedCheck_315_ = !lean_is_exclusive(v_range_282_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; lean_object* v_unused_317_; 
v_unused_316_ = lean_ctor_get(v_range_282_, 1);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_range_282_, 0);
lean_dec(v_unused_317_);
v___x_307_ = v_range_282_;
v_isShared_308_ = v_isSharedCheck_315_;
goto v_resetjp_306_;
}
else
{
lean_dec(v_range_282_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_315_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v_a_283_);
v___x_310_ = v___x_300_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_283_);
v___x_310_ = v_reuseFailAlloc_314_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_312_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_291_);
lean_ctor_set(v___x_307_, 0, v___x_310_);
v___x_312_ = v___x_307_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_291_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
}
else
{
lean_dec(v___x_297_);
v_a_286_ = v___x_292_;
goto v___jp_285_;
}
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_add(v_a_283_, v___x_287_);
lean_dec(v_a_283_);
v_a_283_ = v___x_288_;
v_b_284_ = v_a_286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___boxed(lean_object* v_upperBound_319_, lean_object* v___x_320_, lean_object* v_range_321_, lean_object* v_a_322_, lean_object* v_b_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_319_, v___x_320_, v_range_321_, v_a_322_, v_b_323_);
lean_dec_ref(v_b_323_);
lean_dec(v___x_320_);
lean_dec(v_upperBound_319_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(lean_object* v_stx_325_, lean_object* v_a_326_, uint8_t v___x_327_, lean_object* v_snd_328_, lean_object* v_____r_329_, lean_object* v_childRes_330_){
_start:
{
lean_object* v___y_332_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = l_Lean_Syntax_getArg(v_stx_325_, v_a_326_);
v___x_337_ = l_Lean_Syntax_getTailPos_x3f(v___x_336_, v___x_327_);
lean_dec(v___x_336_);
if (lean_obj_tag(v___x_337_) == 0)
{
v___y_332_ = v_snd_328_;
goto v___jp_331_;
}
else
{
lean_dec(v_snd_328_);
v___y_332_ = v___x_337_;
goto v___jp_331_;
}
v___jp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v_childRes_330_);
lean_ctor_set(v___x_333_, 1, v___y_332_);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0___boxed(lean_object* v_stx_338_, lean_object* v_a_339_, lean_object* v___x_340_, lean_object* v_snd_341_, lean_object* v_____r_342_, lean_object* v_childRes_343_){
_start:
{
uint8_t v___x_3788__boxed_344_; lean_object* v_res_345_; 
v___x_3788__boxed_344_ = lean_unbox(v___x_340_);
v_res_345_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_338_, v_a_339_, v___x_3788__boxed_344_, v_snd_341_, v_____r_342_, v_childRes_343_);
lean_dec(v_a_339_);
lean_dec(v_stx_338_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(lean_object* v___y_356_, lean_object* v___x_357_, lean_object* v_range_358_, lean_object* v___x_359_, lean_object* v_preferred_360_, lean_object* v_a_361_, lean_object* v_b_362_){
_start:
{
lean_object* v_inner_363_; lean_object* v_next_364_; 
v_inner_363_ = lean_ctor_get(v_a_361_, 2);
lean_inc(v_inner_363_);
v_next_364_ = lean_ctor_get(v_inner_363_, 0);
lean_inc(v_next_364_);
if (lean_obj_tag(v_next_364_) == 0)
{
lean_object* v___x_365_; 
lean_dec(v_inner_363_);
lean_dec_ref(v_a_361_);
lean_dec_ref(v_preferred_360_);
lean_dec(v___x_359_);
lean_dec_ref(v_range_358_);
lean_dec(v___x_357_);
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v_b_362_);
return v___x_365_;
}
else
{
lean_object* v_nextIdx_366_; lean_object* v_n_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_426_; 
v_nextIdx_366_ = lean_ctor_get(v_a_361_, 0);
v_n_367_ = lean_ctor_get(v_a_361_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v_a_361_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; 
v_unused_427_ = lean_ctor_get(v_a_361_, 2);
lean_dec(v_unused_427_);
v___x_369_ = v_a_361_;
v_isShared_370_ = v_isSharedCheck_426_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_n_367_);
lean_inc(v_nextIdx_366_);
lean_dec(v_a_361_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_426_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v_upperBound_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_424_; 
v_upperBound_371_ = lean_ctor_get(v_inner_363_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v_inner_363_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_inner_363_, 0);
lean_dec(v_unused_425_);
v___x_373_ = v_inner_363_;
v_isShared_374_ = v_isSharedCheck_424_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_upperBound_371_);
lean_dec(v_inner_363_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_424_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_val_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_423_; 
v_val_375_ = lean_ctor_get(v_next_364_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_next_364_);
if (v_isSharedCheck_423_ == 0)
{
v___x_377_ = v_next_364_;
v_isShared_378_ = v_isSharedCheck_423_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_val_375_);
lean_dec(v_next_364_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_423_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = lean_nat_add(v_val_375_, v_nextIdx_366_);
lean_dec(v_nextIdx_366_);
lean_dec(v_val_375_);
v___x_380_ = lean_nat_dec_lt(v___x_379_, v_upperBound_371_);
if (v___x_380_ == 0)
{
lean_object* v___x_382_; 
lean_dec(v___x_379_);
lean_del_object(v___x_373_);
lean_dec(v_upperBound_371_);
lean_del_object(v___x_369_);
lean_dec(v_n_367_);
lean_dec_ref(v_preferred_360_);
lean_dec(v___x_359_);
lean_dec_ref(v_range_358_);
lean_dec(v___x_357_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v_b_362_);
v___x_382_ = v___x_377_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_b_362_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = lean_nat_add(v___x_379_, v___x_384_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_385_);
v___x_387_ = v___x_377_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_422_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_387_);
v___x_389_ = v___x_373_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_upperBound_371_);
v___x_389_ = v_reuseFailAlloc_421_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_391_; 
lean_inc(v_n_367_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 2, v___x_389_);
lean_ctor_set(v___x_369_, 0, v_n_367_);
v___x_391_ = v___x_369_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_n_367_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_n_367_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v___x_389_);
v___x_391_ = v_reuseFailAlloc_420_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v_val_393_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = l_Lean_Syntax_getArg(v___x_357_, v___x_379_);
v___x_399_ = lean_box(0);
v___x_400_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_358_, v___x_398_, v___x_399_);
if (lean_obj_tag(v___x_400_) == 1)
{
lean_object* v_val_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_val_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v___x_400_, 1);
lean_inc(v___x_357_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_357_);
lean_ctor_set(v___x_402_, 1, v___x_379_);
lean_inc(v___x_359_);
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_359_);
lean_inc(v___x_398_);
lean_inc_ref(v___x_403_);
lean_inc_ref(v_range_358_);
lean_inc_ref(v_preferred_360_);
v___x_404_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_360_, v_range_358_, v___x_403_, v___x_398_, v___x_399_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_dec_ref_known(v___x_403_, 2);
lean_dec(v_val_401_);
lean_dec(v___x_398_);
lean_dec_ref(v___x_391_);
lean_dec(v_b_362_);
lean_dec_ref(v_preferred_360_);
lean_dec(v___x_359_);
lean_dec_ref(v_range_358_);
lean_dec(v___x_357_);
return v___x_404_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_418_; 
v_val_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_418_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_418_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_val_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_418_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
if (lean_obj_tag(v_val_405_) == 0)
{
uint8_t v___x_409_; 
v___x_409_ = lean_unbox(v_val_401_);
lean_dec(v_val_401_);
if (v___x_409_ == 0)
{
lean_del_object(v___x_407_);
lean_dec_ref_known(v___x_403_, 2);
lean_dec(v___x_398_);
v_a_361_ = v___x_391_;
goto _start;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_398_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___x_403_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 0);
lean_ctor_set(v___x_407_, 0, v___x_413_);
v___x_415_ = v___x_407_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
v_val_393_ = v___x_415_;
goto v___jp_392_;
}
}
}
else
{
lean_object* v_val_417_; 
lean_del_object(v___x_407_);
lean_dec_ref_known(v___x_403_, 2);
lean_dec(v_val_401_);
lean_dec(v___x_398_);
v_val_417_ = lean_ctor_get(v_val_405_, 0);
lean_inc(v_val_417_);
lean_dec_ref_known(v_val_405_, 1);
v_val_393_ = v_val_417_;
goto v___jp_392_;
}
}
}
}
else
{
lean_dec(v___x_400_);
lean_dec(v___x_398_);
lean_dec(v___x_379_);
v_a_361_ = v___x_391_;
goto _start;
}
v___jp_392_:
{
if (lean_obj_tag(v_b_362_) == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(v___y_356_, v_val_393_);
lean_dec_ref(v_val_393_);
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
v_a_361_ = v___x_391_;
v_b_362_ = v___x_395_;
goto _start;
}
else
{
lean_object* v___x_397_; 
lean_dec_ref_known(v_b_362_, 1);
lean_dec_ref(v_val_393_);
lean_dec_ref(v___x_391_);
lean_dec_ref(v_preferred_360_);
lean_dec(v___x_359_);
lean_dec_ref(v_range_358_);
lean_dec(v___x_357_);
v___x_397_ = lean_box(0);
return v___x_397_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(lean_object* v_preferred_434_, lean_object* v_range_435_, lean_object* v_stack_436_, lean_object* v_stx_437_, lean_object* v_prev_x3f_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
lean_inc(v_stx_437_);
v___x_439_ = l_Lean_Syntax_getKind(v_stx_437_);
v___x_440_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3));
v___x_441_ = lean_name_eq(v___x_439_, v___x_440_);
lean_dec(v___x_439_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_childRes_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_442_ = l_Lean_Syntax_getNumArgs(v_stx_437_);
v___x_443_ = lean_unsigned_to_nat(0u);
v_childRes_444_ = lean_box(0);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_childRes_444_);
lean_ctor_set(v___x_445_, 1, v_prev_x3f_438_);
v___x_446_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v___x_442_, v_stx_437_, v_range_435_, v_stack_436_, v_preferred_434_, v___x_443_, v___x_445_);
lean_dec(v___x_442_);
if (lean_obj_tag(v___x_446_) == 0)
{
return v_childRes_444_;
}
else
{
lean_object* v_val_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
v_val_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_val_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_fst_451_; lean_object* v___x_453_; 
v_fst_451_ = lean_ctor_get(v_val_447_, 0);
lean_inc(v_fst_451_);
lean_dec(v_val_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v_fst_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_fst_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v___x_456_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; uint8_t v___y_481_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v_bracket_489_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_498_; 
lean_dec(v_prev_x3f_438_);
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_486_ = l_Lean_Syntax_getArg(v_stx_437_, v___x_456_);
lean_inc(v___x_486_);
v___x_487_ = l_Lean_Syntax_getKind(v___x_486_);
v___x_488_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6));
v_bracket_489_ = lean_name_eq(v___x_487_, v___x_488_);
lean_dec(v___x_487_);
if (v_bracket_489_ == 0)
{
v___y_498_ = v___x_456_;
goto v___jp_497_;
}
else
{
lean_object* v___x_517_; 
v___x_517_ = lean_unsigned_to_nat(1u);
v___y_498_ = v___x_517_;
goto v___jp_497_;
}
v___jp_457_:
{
lean_object* v_childRes_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_childRes_461_ = lean_box(0);
v___x_462_ = l_Lean_Syntax_getNumArgs(v___y_459_);
v___x_463_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4));
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_462_);
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_466_, 0, v___x_456_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
lean_ctor_set(v___x_466_, 2, v___x_464_);
v___x_467_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_460_, v___y_459_, v_range_435_, v___y_458_, v_preferred_434_, v___x_466_, v_childRes_461_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_dec(v___y_460_);
return v___x_467_;
}
else
{
lean_object* v_val_468_; 
v_val_468_ = lean_ctor_get(v___x_467_, 0);
if (lean_obj_tag(v_val_468_) == 0)
{
lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; 
v_unused_476_ = lean_ctor_get(v___x_467_, 0);
lean_dec(v_unused_476_);
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___y_460_);
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___y_460_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
else
{
lean_dec(v___y_460_);
return v___x_467_;
}
}
}
v___jp_477_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_inc(v___y_480_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v___y_480_);
lean_ctor_set(v___x_482_, 1, v___x_456_);
lean_inc(v___y_479_);
v___x_483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___y_479_);
v___x_484_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_484_, 0, v___y_478_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*2, v___y_481_);
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
v___y_458_ = v___y_479_;
v___y_459_ = v___y_480_;
v___y_460_ = v___x_485_;
goto v___jp_457_;
}
v___jp_490_:
{
if (v_bracket_489_ == 0)
{
lean_object* v___x_495_; uint8_t v___x_496_; 
lean_inc_ref(v_preferred_434_);
v___x_495_ = lean_apply_1(v_preferred_434_, v___y_491_);
v___x_496_ = lean_unbox(v___x_495_);
v___y_478_ = v___y_494_;
v___y_479_ = v___y_492_;
v___y_480_ = v___y_493_;
v___y_481_ = v___x_496_;
goto v___jp_477_;
}
else
{
lean_dec(v___y_491_);
v___y_478_ = v___y_494_;
v___y_479_ = v___y_492_;
v___y_480_ = v___y_493_;
v___y_481_ = v___x_441_;
goto v___jp_477_;
}
}
v___jp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; 
lean_inc(v___y_498_);
lean_inc(v___x_486_);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_486_);
lean_ctor_set(v___x_499_, 1, v___y_498_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_stx_437_);
lean_ctor_set(v___x_500_, 1, v___x_456_);
v___x_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v_stack_436_);
v___x_502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_499_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = l_Lean_Syntax_getArg(v___x_486_, v___y_498_);
lean_dec(v___y_498_);
lean_dec(v___x_486_);
v___x_504_ = l_Lean_Syntax_getArg(v___x_503_, v___x_456_);
v___x_505_ = 0;
v___x_506_ = l_Lean_Syntax_getPos_x3f(v___x_504_, v___x_505_);
lean_dec(v___x_504_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v___x_507_; 
v___x_507_ = lean_box(0);
v___y_458_ = v___x_502_;
v___y_459_ = v___x_503_;
v___y_460_ = v___x_507_;
goto v___jp_457_;
}
else
{
lean_object* v_val_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_fst_512_; 
v_val_508_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_val_508_);
lean_dec_ref_known(v___x_506_, 1);
v___x_509_ = l_Lean_Syntax_getNumArgs(v___x_503_);
v___x_510_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0));
lean_inc_ref(v_range_435_);
v___x_511_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v___x_509_, v___x_503_, v_range_435_, v___x_456_, v___x_510_);
v_fst_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_fst_512_);
lean_dec_ref(v___x_511_);
if (lean_obj_tag(v_fst_512_) == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_add(v___x_509_, v___x_513_);
lean_dec(v___x_509_);
v___x_515_ = lean_nat_shiftr(v___x_514_, v___x_513_);
lean_dec(v___x_514_);
v___y_491_ = v_val_508_;
v___y_492_ = v___x_502_;
v___y_493_ = v___x_503_;
v___y_494_ = v___x_515_;
goto v___jp_490_;
}
else
{
lean_object* v_val_516_; 
lean_dec(v___x_509_);
v_val_516_ = lean_ctor_get(v_fst_512_, 0);
lean_inc(v_val_516_);
lean_dec_ref_known(v_fst_512_, 1);
v___y_491_ = v_val_508_;
v___y_492_ = v___x_502_;
v___y_493_ = v___x_503_;
v___y_494_ = v_val_516_;
goto v___jp_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(lean_object* v_upperBound_518_, lean_object* v_stx_519_, lean_object* v_range_520_, lean_object* v_stack_521_, lean_object* v_preferred_522_, lean_object* v_a_523_, lean_object* v_b_524_){
_start:
{
lean_object* v___y_526_; uint8_t v___x_541_; 
v___x_541_ = lean_nat_dec_lt(v_a_523_, v_upperBound_518_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
lean_dec(v_a_523_);
lean_dec_ref(v_preferred_522_);
lean_dec(v_stack_521_);
lean_dec_ref(v_range_520_);
lean_dec(v_stx_519_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v_b_524_);
return v___x_542_;
}
else
{
lean_object* v_fst_543_; lean_object* v_snd_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_564_; 
v_fst_543_ = lean_ctor_get(v_b_524_, 0);
v_snd_544_ = lean_ctor_get(v_b_524_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_b_524_);
if (v_isSharedCheck_564_ == 0)
{
v___x_546_ = v_b_524_;
v_isShared_547_ = v_isSharedCheck_564_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_snd_544_);
lean_inc(v_fst_543_);
lean_dec(v_b_524_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_564_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = l_Lean_Syntax_getArg(v_stx_519_, v_a_523_);
lean_inc(v_snd_544_);
v___x_549_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_520_, v___x_548_, v_snd_544_);
if (lean_obj_tag(v___x_549_) == 1)
{
lean_object* v___x_551_; 
lean_dec_ref_known(v___x_549_, 1);
lean_inc(v_a_523_);
lean_inc(v_stx_519_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v_a_523_);
lean_ctor_set(v___x_546_, 0, v_stx_519_);
v___x_551_ = v___x_546_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_stx_519_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_a_523_);
v___x_551_ = v_reuseFailAlloc_561_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_inc(v_stack_521_);
v___x_552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v_stack_521_);
lean_inc(v_snd_544_);
lean_inc_ref(v_range_520_);
lean_inc_ref(v_preferred_522_);
v___x_553_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_522_, v_range_520_, v___x_552_, v___x_548_, v_snd_544_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v___x_554_; 
lean_dec(v_snd_544_);
lean_dec(v_fst_543_);
lean_dec(v_a_523_);
lean_dec_ref(v_preferred_522_);
lean_dec(v_stack_521_);
lean_dec_ref(v_range_520_);
lean_dec(v_stx_519_);
v___x_554_ = lean_box(0);
return v___x_554_;
}
else
{
lean_object* v_val_555_; 
v_val_555_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_val_555_);
lean_dec_ref_known(v___x_553_, 1);
if (lean_obj_tag(v_val_555_) == 1)
{
if (lean_obj_tag(v_fst_543_) == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_box(0);
v___x_557_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_519_, v_a_523_, v___x_541_, v_snd_544_, v___x_556_, v_val_555_);
v___y_526_ = v___x_557_;
goto v___jp_525_;
}
else
{
lean_object* v___x_558_; 
lean_dec_ref_known(v_fst_543_, 1);
lean_dec_ref_known(v_val_555_, 1);
lean_dec(v_snd_544_);
lean_dec(v_a_523_);
lean_dec_ref(v_preferred_522_);
lean_dec(v_stack_521_);
lean_dec_ref(v_range_520_);
lean_dec(v_stx_519_);
v___x_558_ = lean_box(0);
return v___x_558_;
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v_val_555_);
v___x_559_ = lean_box(0);
v___x_560_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_519_, v_a_523_, v___x_541_, v_snd_544_, v___x_559_, v_fst_543_);
v___y_526_ = v___x_560_;
goto v___jp_525_;
}
}
}
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v___x_549_);
lean_dec(v___x_548_);
lean_del_object(v___x_546_);
v___x_562_ = lean_box(0);
v___x_563_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_519_, v_a_523_, v___x_541_, v_snd_544_, v___x_562_, v_fst_543_);
v___y_526_ = v___x_563_;
goto v___jp_525_;
}
}
}
v___jp_525_:
{
if (lean_obj_tag(v___y_526_) == 0)
{
lean_object* v___x_527_; 
lean_dec(v_a_523_);
lean_dec_ref(v_preferred_522_);
lean_dec(v_stack_521_);
lean_dec_ref(v_range_520_);
lean_dec(v_stx_519_);
v___x_527_ = lean_box(0);
return v___x_527_;
}
else
{
lean_object* v_val_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_540_; 
v_val_528_ = lean_ctor_get(v___y_526_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___y_526_);
if (v_isSharedCheck_540_ == 0)
{
v___x_530_ = v___y_526_;
v_isShared_531_ = v_isSharedCheck_540_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_val_528_);
lean_dec(v___y_526_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_540_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
if (lean_obj_tag(v_val_528_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; 
lean_dec(v_a_523_);
lean_dec_ref(v_preferred_522_);
lean_dec(v_stack_521_);
lean_dec_ref(v_range_520_);
lean_dec(v_stx_519_);
v_a_532_ = lean_ctor_get(v_val_528_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v_val_528_, 1);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v_a_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
lean_del_object(v___x_530_);
v_a_536_ = lean_ctor_get(v_val_528_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v_val_528_, 1);
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_add(v_a_523_, v___x_537_);
lean_dec(v_a_523_);
v_a_523_ = v___x_538_;
v_b_524_ = v_a_536_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_565_, lean_object* v_stx_566_, lean_object* v_range_567_, lean_object* v_stack_568_, lean_object* v_preferred_569_, lean_object* v_a_570_, lean_object* v_b_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_565_, v_stx_566_, v_range_567_, v_stack_568_, v_preferred_569_, v_a_570_, v_b_571_);
lean_dec(v_upperBound_565_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg___boxed(lean_object* v___y_573_, lean_object* v___x_574_, lean_object* v_range_575_, lean_object* v___x_576_, lean_object* v_preferred_577_, lean_object* v_a_578_, lean_object* v_b_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_573_, v___x_574_, v_range_575_, v___x_576_, v_preferred_577_, v_a_578_, v_b_579_);
lean_dec(v___y_573_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(lean_object* v_upperBound_581_, lean_object* v_stx_582_, lean_object* v_range_583_, lean_object* v_stack_584_, lean_object* v_preferred_585_, lean_object* v_inst_586_, lean_object* v_R_587_, lean_object* v_a_588_, lean_object* v_b_589_, lean_object* v_c_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_581_, v_stx_582_, v_range_583_, v_stack_584_, v_preferred_585_, v_a_588_, v_b_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___boxed(lean_object* v_upperBound_592_, lean_object* v_stx_593_, lean_object* v_range_594_, lean_object* v_stack_595_, lean_object* v_preferred_596_, lean_object* v_inst_597_, lean_object* v_R_598_, lean_object* v_a_599_, lean_object* v_b_600_, lean_object* v_c_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(v_upperBound_592_, v_stx_593_, v_range_594_, v_stack_595_, v_preferred_596_, v_inst_597_, v_R_598_, v_a_599_, v_b_600_, v_c_601_);
lean_dec(v_upperBound_592_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(lean_object* v___y_603_, lean_object* v___x_604_, lean_object* v_range_605_, lean_object* v___x_606_, lean_object* v_preferred_607_, lean_object* v_inst_608_, lean_object* v_R_609_, lean_object* v_a_610_, lean_object* v_b_611_, lean_object* v_c_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_603_, v___x_604_, v_range_605_, v___x_606_, v_preferred_607_, v_a_610_, v_b_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___boxed(lean_object* v___y_614_, lean_object* v___x_615_, lean_object* v_range_616_, lean_object* v___x_617_, lean_object* v_preferred_618_, lean_object* v_inst_619_, lean_object* v_R_620_, lean_object* v_a_621_, lean_object* v_b_622_, lean_object* v_c_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(v___y_614_, v___x_615_, v_range_616_, v___x_617_, v_preferred_618_, v_inst_619_, v_R_620_, v_a_621_, v_b_622_, v_c_623_);
lean_dec(v___y_614_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(lean_object* v_upperBound_625_, lean_object* v___x_626_, lean_object* v_range_627_, lean_object* v_inst_628_, lean_object* v_R_629_, lean_object* v_a_630_, lean_object* v_b_631_, lean_object* v_c_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_625_, v___x_626_, v_range_627_, v_a_630_, v_b_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___boxed(lean_object* v_upperBound_634_, lean_object* v___x_635_, lean_object* v_range_636_, lean_object* v_inst_637_, lean_object* v_R_638_, lean_object* v_a_639_, lean_object* v_b_640_, lean_object* v_c_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(v_upperBound_634_, v___x_635_, v_range_636_, v_inst_637_, v_R_638_, v_a_639_, v_b_640_, v_c_641_);
lean_dec_ref(v_b_640_);
lean_dec(v___x_635_);
lean_dec(v_upperBound_634_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findTactic_x3f(lean_object* v_preferred_643_, lean_object* v_range_644_, lean_object* v_root_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_box(0);
v___x_647_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_644_, v_root_645_, v___x_646_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_dec(v_root_645_);
lean_dec_ref(v_range_644_);
lean_dec_ref(v_preferred_643_);
return v___x_646_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec_ref_known(v___x_647_, 1);
v___x_648_ = lean_box(0);
v___x_649_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_643_, v_range_644_, v___x_648_, v_root_645_, v___x_646_);
if (lean_obj_tag(v___x_649_) == 0)
{
return v___x_646_;
}
else
{
lean_object* v_val_650_; 
v_val_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v___x_649_, 1);
return v_val_650_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(lean_object* v_ctx_x3f_663_, lean_object* v_i_664_, lean_object* v_kind_665_, lean_object* v_tgtRange_666_, lean_object* v_f_667_, uint8_t v_canonicalOnly_668_, lean_object* v_as_669_, size_t v_sz_670_, size_t v_i_671_, lean_object* v_b_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = lean_usize_dec_lt(v_i_671_, v_sz_670_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_dec_ref(v_f_667_);
lean_dec(v_ctx_x3f_663_);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_b_672_);
return v___x_674_;
}
else
{
lean_object* v_snd_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_700_; 
v_snd_675_ = lean_ctor_get(v_b_672_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v_b_672_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; 
v_unused_701_ = lean_ctor_get(v_b_672_, 0);
lean_dec(v_unused_701_);
v___x_677_ = v_b_672_;
v_isShared_678_ = v_isSharedCheck_700_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_snd_675_);
lean_dec(v_b_672_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_700_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v_a_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_679_ = lean_box(0);
v_a_680_ = lean_array_uget_borrowed(v_as_669_, v_i_671_);
lean_inc(v_ctx_x3f_663_);
v___x_681_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_663_, v_i_664_);
lean_inc_ref(v_f_667_);
lean_inc(v_a_680_);
v___x_682_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_665_, v_tgtRange_666_, v___x_681_, v_a_680_, v_f_667_, v_canonicalOnly_668_);
if (lean_obj_tag(v___x_682_) == 1)
{
lean_object* v___x_684_; 
lean_dec_ref(v_f_667_);
lean_dec(v_ctx_x3f_663_);
lean_inc_ref(v___x_682_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v___x_679_);
lean_ctor_set(v___x_677_, 0, v___x_682_);
v___x_684_ = v___x_677_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_679_);
v___x_684_ = v_reuseFailAlloc_695_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_693_; 
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; 
v_unused_694_ = lean_ctor_get(v___x_682_, 0);
lean_dec(v_unused_694_);
v___x_686_ = v___x_682_;
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
else
{
lean_dec(v___x_682_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_684_);
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_684_);
v___x_689_ = v_reuseFailAlloc_692_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_snd_675_);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
}
}
else
{
lean_object* v___x_696_; size_t v___x_697_; size_t v___x_698_; 
lean_dec(v___x_682_);
lean_del_object(v___x_677_);
lean_dec(v_snd_675_);
v___x_696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1));
v___x_697_ = ((size_t)1ULL);
v___x_698_ = lean_usize_add(v_i_671_, v___x_697_);
v_i_671_ = v___x_698_;
v_b_672_ = v___x_696_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(lean_object* v_ctx_x3f_702_, lean_object* v_i_703_, lean_object* v_kind_704_, lean_object* v_tgtRange_705_, lean_object* v_f_706_, uint8_t v_canonicalOnly_707_, lean_object* v_as_708_, size_t v_sz_709_, size_t v_i_710_, lean_object* v_b_711_){
_start:
{
uint8_t v___x_712_; 
v___x_712_ = lean_usize_dec_lt(v_i_710_, v_sz_709_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec_ref(v_f_706_);
lean_dec(v_ctx_x3f_702_);
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v_b_711_);
return v___x_713_;
}
else
{
lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_739_; 
v_snd_714_ = lean_ctor_get(v_b_711_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_b_711_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; 
v_unused_740_ = lean_ctor_get(v_b_711_, 0);
lean_dec(v_unused_740_);
v___x_716_ = v_b_711_;
v_isShared_717_ = v_isSharedCheck_739_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_dec(v_b_711_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_739_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_718_ = lean_box(0);
v_a_719_ = lean_array_uget_borrowed(v_as_708_, v_i_710_);
lean_inc(v_ctx_x3f_702_);
v___x_720_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_702_, v_i_703_);
lean_inc_ref(v_f_706_);
lean_inc(v_a_719_);
v___x_721_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_704_, v_tgtRange_705_, v___x_720_, v_a_719_, v_f_706_, v_canonicalOnly_707_);
if (lean_obj_tag(v___x_721_) == 1)
{
lean_object* v___x_723_; 
lean_dec_ref(v_f_706_);
lean_dec(v_ctx_x3f_702_);
lean_inc_ref(v___x_721_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v___x_718_);
lean_ctor_set(v___x_716_, 0, v___x_721_);
v___x_723_ = v___x_716_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_718_);
v___x_723_ = v_reuseFailAlloc_734_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_732_; 
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v___x_721_, 0);
lean_dec(v_unused_733_);
v___x_725_ = v___x_721_;
v_isShared_726_ = v_isSharedCheck_732_;
goto v_resetjp_724_;
}
else
{
lean_dec(v___x_721_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_732_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_723_);
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_723_);
v___x_728_ = v_reuseFailAlloc_731_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v_snd_714_);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
}
}
else
{
lean_object* v___x_735_; size_t v___x_736_; size_t v___x_737_; lean_object* v___x_738_; 
lean_dec(v___x_721_);
lean_del_object(v___x_716_);
lean_dec(v_snd_714_);
v___x_735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1));
v___x_736_ = ((size_t)1ULL);
v___x_737_ = lean_usize_add(v_i_710_, v___x_736_);
v___x_738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_702_, v_i_703_, v_kind_704_, v_tgtRange_705_, v_f_706_, v_canonicalOnly_707_, v_as_708_, v_sz_709_, v___x_737_, v___x_735_);
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(lean_object* v_ctx_x3f_741_, lean_object* v_i_742_, lean_object* v_kind_743_, lean_object* v_tgtRange_744_, lean_object* v_f_745_, uint8_t v_canonicalOnly_746_, lean_object* v_t_747_, lean_object* v_init_748_){
_start:
{
lean_object* v_root_749_; lean_object* v_tail_750_; lean_object* v___x_751_; 
v_root_749_ = lean_ctor_get(v_t_747_, 0);
v_tail_750_ = lean_ctor_get(v_t_747_, 1);
lean_inc_ref(v_f_745_);
lean_inc(v_ctx_x3f_741_);
lean_inc_ref(v_init_748_);
v___x_751_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_748_, v_ctx_x3f_741_, v_i_742_, v_kind_743_, v_tgtRange_744_, v_f_745_, v_canonicalOnly_746_, v_root_749_, v_init_748_);
lean_dec_ref(v_init_748_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v___x_752_; 
lean_dec_ref(v_f_745_);
lean_dec(v_ctx_x3f_741_);
v___x_752_ = lean_box(0);
return v___x_752_;
}
else
{
lean_object* v_val_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_777_; 
v_val_753_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_777_ == 0)
{
v___x_755_ = v___x_751_;
v_isShared_756_ = v_isSharedCheck_777_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_val_753_);
lean_dec(v___x_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_777_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
if (lean_obj_tag(v_val_753_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_759_; 
lean_dec_ref(v_f_745_);
lean_dec(v_ctx_x3f_741_);
v_a_757_ = lean_ctor_get(v_val_753_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v_val_753_, 1);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_a_757_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_762_; lean_object* v___x_763_; size_t v_sz_764_; size_t v___x_765_; lean_object* v___x_766_; 
lean_del_object(v___x_755_);
v_a_761_ = lean_ctor_get(v_val_753_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v_val_753_, 1);
v___x_762_ = lean_box(0);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v_a_761_);
v_sz_764_ = lean_array_size(v_tail_750_);
v___x_765_ = ((size_t)0ULL);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_741_, v_i_742_, v_kind_743_, v_tgtRange_744_, v_f_745_, v_canonicalOnly_746_, v_tail_750_, v_sz_764_, v___x_765_, v___x_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
return v___x_762_;
}
else
{
lean_object* v_val_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_776_; 
v_val_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_776_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_776_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_val_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_776_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_fst_771_; 
v_fst_771_ = lean_ctor_get(v_val_767_, 0);
if (lean_obj_tag(v_fst_771_) == 0)
{
lean_object* v_snd_772_; lean_object* v___x_774_; 
v_snd_772_ = lean_ctor_get(v_val_767_, 1);
lean_inc(v_snd_772_);
lean_dec(v_val_767_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v_snd_772_);
v___x_774_ = v___x_769_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_snd_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
else
{
lean_inc_ref(v_fst_771_);
lean_del_object(v___x_769_);
lean_dec(v_val_767_);
return v_fst_771_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f(lean_object* v_kind_778_, lean_object* v_tgtRange_779_, lean_object* v_ctx_x3f_780_, lean_object* v_t_781_, lean_object* v_f_782_, uint8_t v_canonicalOnly_783_){
_start:
{
switch(lean_obj_tag(v_t_781_))
{
case 0:
{
lean_object* v_i_784_; lean_object* v_t_785_; lean_object* v___x_786_; 
v_i_784_ = lean_ctor_get(v_t_781_, 0);
lean_inc_ref(v_i_784_);
v_t_785_ = lean_ctor_get(v_t_781_, 1);
lean_inc_ref(v_t_785_);
lean_dec_ref_known(v_t_781_, 2);
v___x_786_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_784_, v_ctx_x3f_780_);
v_ctx_x3f_780_ = v___x_786_;
v_t_781_ = v_t_785_;
goto _start;
}
case 1:
{
lean_object* v_i_788_; lean_object* v_children_789_; 
v_i_788_ = lean_ctor_get(v_t_781_, 0);
v_children_789_ = lean_ctor_get(v_t_781_, 1);
if (lean_obj_tag(v_ctx_x3f_780_) == 1)
{
lean_object* v_val_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_val_796_ = lean_ctor_get(v_ctx_x3f_780_, 0);
v___x_797_ = l_Lean_Elab_Info_stx(v_i_788_);
v___x_798_ = l_Lean_Syntax_getRange_x3f(v___x_797_, v_canonicalOnly_783_);
if (lean_obj_tag(v___x_798_) == 1)
{
lean_object* v_val_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_812_; 
v_val_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_812_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_812_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_val_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_812_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = l_Lean_Syntax_getKind(v___x_797_);
v___x_804_ = lean_name_eq(v___x_803_, v_kind_778_);
lean_dec(v___x_803_);
if (v___x_804_ == 0)
{
lean_inc_ref(v_children_789_);
lean_inc_ref(v_i_788_);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref_known(v_t_781_, 2);
goto v___jp_790_;
}
else
{
uint8_t v___x_805_; 
v___x_805_ = l_Lean_Syntax_instBEqRange_beq(v_val_799_, v_tgtRange_779_);
lean_dec(v_val_799_);
if (v___x_805_ == 0)
{
lean_inc_ref(v_children_789_);
lean_inc_ref(v_i_788_);
lean_del_object(v___x_801_);
lean_dec_ref_known(v_t_781_, 2);
goto v___jp_790_;
}
else
{
lean_object* v___x_806_; uint8_t v___x_807_; 
lean_inc_ref(v_f_782_);
lean_inc_ref(v_i_788_);
lean_inc(v_val_796_);
v___x_806_ = lean_apply_2(v_f_782_, v_val_796_, v_i_788_);
v___x_807_ = lean_unbox(v___x_806_);
if (v___x_807_ == 0)
{
lean_inc_ref(v_children_789_);
lean_inc_ref(v_i_788_);
lean_del_object(v___x_801_);
lean_dec_ref_known(v_t_781_, 2);
goto v___jp_790_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_inc(v_val_796_);
lean_dec_ref_known(v_ctx_x3f_780_, 1);
lean_dec_ref(v_f_782_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v_val_796_);
lean_ctor_set(v___x_808_, 1, v_t_781_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_808_);
v___x_810_ = v___x_801_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
else
{
lean_inc_ref(v_children_789_);
lean_inc_ref(v_i_788_);
lean_dec(v___x_798_);
lean_dec(v___x_797_);
lean_dec_ref_known(v_t_781_, 2);
goto v___jp_790_;
}
}
else
{
lean_inc_ref(v_children_789_);
lean_inc_ref(v_i_788_);
lean_dec_ref_known(v_t_781_, 2);
goto v___jp_790_;
}
v___jp_790_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = lean_box(0);
v___x_792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0));
v___x_793_ = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(v_ctx_x3f_780_, v_i_788_, v_kind_778_, v_tgtRange_779_, v_f_782_, v_canonicalOnly_783_, v_children_789_, v___x_792_);
lean_dec_ref(v_children_789_);
lean_dec_ref(v_i_788_);
if (lean_obj_tag(v___x_793_) == 0)
{
return v___x_791_;
}
else
{
lean_object* v_val_794_; lean_object* v_fst_795_; 
v_val_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_val_794_);
lean_dec_ref_known(v___x_793_, 1);
v_fst_795_ = lean_ctor_get(v_val_794_, 0);
lean_inc(v_fst_795_);
lean_dec(v_val_794_);
if (lean_obj_tag(v_fst_795_) == 0)
{
return v___x_791_;
}
else
{
return v_fst_795_;
}
}
}
}
default: 
{
lean_object* v___x_813_; 
lean_dec_ref(v_f_782_);
lean_dec_ref(v_t_781_);
lean_dec(v_ctx_x3f_780_);
v___x_813_ = lean_box(0);
return v___x_813_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_ctx_x3f_823_, lean_object* v_i_824_, lean_object* v_kind_825_, lean_object* v_tgtRange_826_, lean_object* v_f_827_, uint8_t v_canonicalOnly_828_, lean_object* v_as_829_, size_t v_sz_830_, size_t v_i_831_, lean_object* v_b_832_){
_start:
{
uint8_t v___x_833_; 
v___x_833_ = lean_usize_dec_lt(v_i_831_, v_sz_830_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_dec_ref(v_f_827_);
lean_dec(v_ctx_x3f_823_);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v_b_832_);
return v___x_834_;
}
else
{
lean_object* v_snd_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_861_; 
v_snd_835_ = lean_ctor_get(v_b_832_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v_b_832_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v_b_832_, 0);
lean_dec(v_unused_862_);
v___x_837_ = v_b_832_;
v_isShared_838_ = v_isSharedCheck_861_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_snd_835_);
lean_dec(v_b_832_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_861_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v_a_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_839_ = lean_box(0);
v_a_840_ = lean_array_uget_borrowed(v_as_829_, v_i_831_);
lean_inc(v_ctx_x3f_823_);
v___x_841_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_823_, v_i_824_);
lean_inc_ref(v_f_827_);
lean_inc(v_a_840_);
v___x_842_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_825_, v_tgtRange_826_, v___x_841_, v_a_840_, v_f_827_, v_canonicalOnly_828_);
if (lean_obj_tag(v___x_842_) == 1)
{
lean_object* v___x_844_; 
lean_dec_ref(v_f_827_);
lean_dec(v_ctx_x3f_823_);
lean_inc_ref(v___x_842_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_839_);
lean_ctor_set(v___x_837_, 0, v___x_842_);
v___x_844_ = v___x_837_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_839_);
v___x_844_ = v_reuseFailAlloc_856_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_854_; 
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v___x_842_, 0);
lean_dec(v_unused_855_);
v___x_846_ = v___x_842_;
v_isShared_847_ = v_isSharedCheck_854_;
goto v_resetjp_845_;
}
else
{
lean_dec(v___x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_854_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 0);
lean_ctor_set(v___x_846_, 0, v___x_844_);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_844_);
v___x_849_ = v_reuseFailAlloc_853_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v_snd_835_);
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
}
}
else
{
lean_object* v___x_857_; size_t v___x_858_; size_t v___x_859_; 
lean_dec(v___x_842_);
lean_del_object(v___x_837_);
lean_dec(v_snd_835_);
v___x_857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_858_ = ((size_t)1ULL);
v___x_859_ = lean_usize_add(v_i_831_, v___x_858_);
v_i_831_ = v___x_859_;
v_b_832_ = v___x_857_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(lean_object* v_ctx_x3f_863_, lean_object* v_i_864_, lean_object* v_kind_865_, lean_object* v_tgtRange_866_, lean_object* v_f_867_, uint8_t v_canonicalOnly_868_, lean_object* v_as_869_, size_t v_sz_870_, size_t v_i_871_, lean_object* v_b_872_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = lean_usize_dec_lt(v_i_871_, v_sz_870_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec_ref(v_f_867_);
lean_dec(v_ctx_x3f_863_);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v_b_872_);
return v___x_874_;
}
else
{
lean_object* v_snd_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_901_; 
v_snd_875_ = lean_ctor_get(v_b_872_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v_b_872_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v_b_872_, 0);
lean_dec(v_unused_902_);
v___x_877_ = v_b_872_;
v_isShared_878_ = v_isSharedCheck_901_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_snd_875_);
lean_dec(v_b_872_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_901_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v_a_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_879_ = lean_box(0);
v_a_880_ = lean_array_uget_borrowed(v_as_869_, v_i_871_);
lean_inc(v_ctx_x3f_863_);
v___x_881_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_863_, v_i_864_);
lean_inc_ref(v_f_867_);
lean_inc(v_a_880_);
v___x_882_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_865_, v_tgtRange_866_, v___x_881_, v_a_880_, v_f_867_, v_canonicalOnly_868_);
if (lean_obj_tag(v___x_882_) == 1)
{
lean_object* v___x_884_; 
lean_dec_ref(v_f_867_);
lean_dec(v_ctx_x3f_863_);
lean_inc_ref(v___x_882_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 1, v___x_879_);
lean_ctor_set(v___x_877_, 0, v___x_882_);
v___x_884_ = v___x_877_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_879_);
v___x_884_ = v_reuseFailAlloc_896_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_894_; 
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v___x_882_, 0);
lean_dec(v_unused_895_);
v___x_886_ = v___x_882_;
v_isShared_887_ = v_isSharedCheck_894_;
goto v_resetjp_885_;
}
else
{
lean_dec(v___x_882_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_894_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_884_);
v___x_889_ = v_reuseFailAlloc_893_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v_snd_875_);
v___x_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
}
}
else
{
lean_object* v___x_897_; size_t v___x_898_; size_t v___x_899_; lean_object* v___x_900_; 
lean_dec(v___x_882_);
lean_del_object(v___x_877_);
lean_dec(v_snd_875_);
v___x_897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0));
v___x_898_ = ((size_t)1ULL);
v___x_899_ = lean_usize_add(v_i_871_, v___x_898_);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_863_, v_i_864_, v_kind_865_, v_tgtRange_866_, v_f_867_, v_canonicalOnly_868_, v_as_869_, v_sz_870_, v___x_899_, v___x_897_);
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(lean_object* v_init_903_, lean_object* v_ctx_x3f_904_, lean_object* v_i_905_, lean_object* v_kind_906_, lean_object* v_tgtRange_907_, lean_object* v_f_908_, uint8_t v_canonicalOnly_909_, lean_object* v_n_910_, lean_object* v_b_911_){
_start:
{
if (lean_obj_tag(v_n_910_) == 0)
{
lean_object* v_cs_912_; lean_object* v___x_913_; lean_object* v___x_914_; size_t v_sz_915_; size_t v___x_916_; lean_object* v___x_917_; 
v_cs_912_ = lean_ctor_get(v_n_910_, 0);
v___x_913_ = lean_box(0);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v_b_911_);
v_sz_915_ = lean_array_size(v_cs_912_);
v___x_916_ = ((size_t)0ULL);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_903_, v_ctx_x3f_904_, v_i_905_, v_kind_906_, v_tgtRange_907_, v_f_908_, v_canonicalOnly_909_, v_cs_912_, v_sz_915_, v___x_916_, v___x_914_);
if (lean_obj_tag(v___x_917_) == 0)
{
return v___x_913_;
}
else
{
lean_object* v_val_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_928_; 
v_val_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_928_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_928_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_val_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_928_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_fst_922_; 
v_fst_922_ = lean_ctor_get(v_val_918_, 0);
if (lean_obj_tag(v_fst_922_) == 0)
{
lean_object* v_snd_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v_snd_923_ = lean_ctor_get(v_val_918_, 1);
lean_inc(v_snd_923_);
lean_dec(v_val_918_);
v___x_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_924_, 0, v_snd_923_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_924_);
v___x_926_ = v___x_920_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
else
{
lean_inc_ref(v_fst_922_);
lean_del_object(v___x_920_);
lean_dec(v_val_918_);
return v_fst_922_;
}
}
}
}
else
{
lean_object* v_vs_929_; lean_object* v___x_930_; lean_object* v___x_931_; size_t v_sz_932_; size_t v___x_933_; lean_object* v___x_934_; 
v_vs_929_ = lean_ctor_get(v_n_910_, 0);
v___x_930_ = lean_box(0);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v_b_911_);
v_sz_932_ = lean_array_size(v_vs_929_);
v___x_933_ = ((size_t)0ULL);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_904_, v_i_905_, v_kind_906_, v_tgtRange_907_, v_f_908_, v_canonicalOnly_909_, v_vs_929_, v_sz_932_, v___x_933_, v___x_931_);
if (lean_obj_tag(v___x_934_) == 0)
{
return v___x_930_;
}
else
{
lean_object* v_val_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_945_; 
v_val_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_945_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_val_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_fst_939_; 
v_fst_939_ = lean_ctor_get(v_val_935_, 0);
if (lean_obj_tag(v_fst_939_) == 0)
{
lean_object* v_snd_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v_snd_940_ = lean_ctor_get(v_val_935_, 1);
lean_inc(v_snd_940_);
lean_dec(v_val_935_);
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v_snd_940_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_941_);
v___x_943_ = v___x_937_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
else
{
lean_inc_ref(v_fst_939_);
lean_del_object(v___x_937_);
lean_dec(v_val_935_);
return v_fst_939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(lean_object* v_init_946_, lean_object* v_ctx_x3f_947_, lean_object* v_i_948_, lean_object* v_kind_949_, lean_object* v_tgtRange_950_, lean_object* v_f_951_, uint8_t v_canonicalOnly_952_, lean_object* v_as_953_, size_t v_sz_954_, size_t v_i_955_, lean_object* v_b_956_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = lean_usize_dec_lt(v_i_955_, v_sz_954_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
lean_dec_ref(v_f_951_);
lean_dec(v_ctx_x3f_947_);
v___x_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_958_, 0, v_b_956_);
return v___x_958_;
}
else
{
lean_object* v_snd_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_986_; 
v_snd_959_ = lean_ctor_get(v_b_956_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v_b_956_);
if (v_isSharedCheck_986_ == 0)
{
lean_object* v_unused_987_; 
v_unused_987_ = lean_ctor_get(v_b_956_, 0);
lean_dec(v_unused_987_);
v___x_961_ = v_b_956_;
v_isShared_962_ = v_isSharedCheck_986_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_snd_959_);
lean_dec(v_b_956_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_986_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_a_963_; lean_object* v___x_964_; 
v_a_963_ = lean_array_uget_borrowed(v_as_953_, v_i_955_);
lean_inc(v_snd_959_);
lean_inc_ref(v_f_951_);
lean_inc(v_ctx_x3f_947_);
v___x_964_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_946_, v_ctx_x3f_947_, v_i_948_, v_kind_949_, v_tgtRange_950_, v_f_951_, v_canonicalOnly_952_, v_a_963_, v_snd_959_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v___x_965_; 
lean_del_object(v___x_961_);
lean_dec(v_snd_959_);
lean_dec_ref(v_f_951_);
lean_dec(v_ctx_x3f_947_);
v___x_965_ = lean_box(0);
return v___x_965_;
}
else
{
lean_object* v_val_966_; 
v_val_966_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_val_966_);
if (lean_obj_tag(v_val_966_) == 0)
{
lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v_f_951_);
lean_dec(v_ctx_x3f_947_);
v_isSharedCheck_976_ = !lean_is_exclusive(v_val_966_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v_val_966_, 0);
lean_dec(v_unused_977_);
v___x_968_ = v_val_966_;
v_isShared_969_ = v_isSharedCheck_976_;
goto v_resetjp_967_;
}
else
{
lean_dec(v_val_966_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_976_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_964_);
v___x_971_ = v___x_961_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_snd_959_);
v___x_971_ = v_reuseFailAlloc_975_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_973_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 1);
lean_ctor_set(v___x_968_, 0, v___x_971_);
v___x_973_ = v___x_968_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
lean_dec_ref_known(v___x_964_, 1);
lean_dec(v_snd_959_);
v_a_978_ = lean_ctor_get(v_val_966_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v_val_966_, 1);
v___x_979_ = lean_box(0);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v_a_978_);
lean_ctor_set(v___x_961_, 0, v___x_979_);
v___x_981_ = v___x_961_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_a_978_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
size_t v___x_982_; size_t v___x_983_; 
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_add(v_i_955_, v___x_982_);
v_i_955_ = v___x_983_;
v_b_956_ = v___x_981_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_988_, lean_object* v_ctx_x3f_989_, lean_object* v_i_990_, lean_object* v_kind_991_, lean_object* v_tgtRange_992_, lean_object* v_f_993_, lean_object* v_canonicalOnly_994_, lean_object* v_as_995_, lean_object* v_sz_996_, lean_object* v_i_997_, lean_object* v_b_998_){
_start:
{
uint8_t v_canonicalOnly_boxed_999_; size_t v_sz_boxed_1000_; size_t v_i_boxed_1001_; lean_object* v_res_1002_; 
v_canonicalOnly_boxed_999_ = lean_unbox(v_canonicalOnly_994_);
v_sz_boxed_1000_ = lean_unbox_usize(v_sz_996_);
lean_dec(v_sz_996_);
v_i_boxed_1001_ = lean_unbox_usize(v_i_997_);
lean_dec(v_i_997_);
v_res_1002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_988_, v_ctx_x3f_989_, v_i_990_, v_kind_991_, v_tgtRange_992_, v_f_993_, v_canonicalOnly_boxed_999_, v_as_995_, v_sz_boxed_1000_, v_i_boxed_1001_, v_b_998_);
lean_dec_ref(v_as_995_);
lean_dec_ref(v_tgtRange_992_);
lean_dec(v_kind_991_);
lean_dec_ref(v_i_990_);
lean_dec_ref(v_init_988_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0___boxed(lean_object* v_ctx_x3f_1003_, lean_object* v_i_1004_, lean_object* v_kind_1005_, lean_object* v_tgtRange_1006_, lean_object* v_f_1007_, lean_object* v_canonicalOnly_1008_, lean_object* v_t_1009_, lean_object* v_init_1010_){
_start:
{
uint8_t v_canonicalOnly_boxed_1011_; lean_object* v_res_1012_; 
v_canonicalOnly_boxed_1011_ = lean_unbox(v_canonicalOnly_1008_);
v_res_1012_ = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(v_ctx_x3f_1003_, v_i_1004_, v_kind_1005_, v_tgtRange_1006_, v_f_1007_, v_canonicalOnly_boxed_1011_, v_t_1009_, v_init_1010_);
lean_dec_ref(v_t_1009_);
lean_dec_ref(v_tgtRange_1006_);
lean_dec(v_kind_1005_);
lean_dec_ref(v_i_1004_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___boxed(lean_object* v_ctx_x3f_1013_, lean_object* v_i_1014_, lean_object* v_kind_1015_, lean_object* v_tgtRange_1016_, lean_object* v_f_1017_, lean_object* v_canonicalOnly_1018_, lean_object* v_as_1019_, lean_object* v_sz_1020_, lean_object* v_i_1021_, lean_object* v_b_1022_){
_start:
{
uint8_t v_canonicalOnly_boxed_1023_; size_t v_sz_boxed_1024_; size_t v_i_boxed_1025_; lean_object* v_res_1026_; 
v_canonicalOnly_boxed_1023_ = lean_unbox(v_canonicalOnly_1018_);
v_sz_boxed_1024_ = lean_unbox_usize(v_sz_1020_);
lean_dec(v_sz_1020_);
v_i_boxed_1025_ = lean_unbox_usize(v_i_1021_);
lean_dec(v_i_1021_);
v_res_1026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_1013_, v_i_1014_, v_kind_1015_, v_tgtRange_1016_, v_f_1017_, v_canonicalOnly_boxed_1023_, v_as_1019_, v_sz_boxed_1024_, v_i_boxed_1025_, v_b_1022_);
lean_dec_ref(v_as_1019_);
lean_dec_ref(v_tgtRange_1016_);
lean_dec(v_kind_1015_);
lean_dec_ref(v_i_1014_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_ctx_x3f_1027_, lean_object* v_i_1028_, lean_object* v_kind_1029_, lean_object* v_tgtRange_1030_, lean_object* v_f_1031_, lean_object* v_canonicalOnly_1032_, lean_object* v_as_1033_, lean_object* v_sz_1034_, lean_object* v_i_1035_, lean_object* v_b_1036_){
_start:
{
uint8_t v_canonicalOnly_boxed_1037_; size_t v_sz_boxed_1038_; size_t v_i_boxed_1039_; lean_object* v_res_1040_; 
v_canonicalOnly_boxed_1037_ = lean_unbox(v_canonicalOnly_1032_);
v_sz_boxed_1038_ = lean_unbox_usize(v_sz_1034_);
lean_dec(v_sz_1034_);
v_i_boxed_1039_ = lean_unbox_usize(v_i_1035_);
lean_dec(v_i_1035_);
v_res_1040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_1027_, v_i_1028_, v_kind_1029_, v_tgtRange_1030_, v_f_1031_, v_canonicalOnly_boxed_1037_, v_as_1033_, v_sz_boxed_1038_, v_i_boxed_1039_, v_b_1036_);
lean_dec_ref(v_as_1033_);
lean_dec_ref(v_tgtRange_1030_);
lean_dec(v_kind_1029_);
lean_dec_ref(v_i_1028_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_ctx_x3f_1041_, lean_object* v_i_1042_, lean_object* v_kind_1043_, lean_object* v_tgtRange_1044_, lean_object* v_f_1045_, lean_object* v_canonicalOnly_1046_, lean_object* v_as_1047_, lean_object* v_sz_1048_, lean_object* v_i_1049_, lean_object* v_b_1050_){
_start:
{
uint8_t v_canonicalOnly_boxed_1051_; size_t v_sz_boxed_1052_; size_t v_i_boxed_1053_; lean_object* v_res_1054_; 
v_canonicalOnly_boxed_1051_ = lean_unbox(v_canonicalOnly_1046_);
v_sz_boxed_1052_ = lean_unbox_usize(v_sz_1048_);
lean_dec(v_sz_1048_);
v_i_boxed_1053_ = lean_unbox_usize(v_i_1049_);
lean_dec(v_i_1049_);
v_res_1054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_1041_, v_i_1042_, v_kind_1043_, v_tgtRange_1044_, v_f_1045_, v_canonicalOnly_boxed_1051_, v_as_1047_, v_sz_boxed_1052_, v_i_boxed_1053_, v_b_1050_);
lean_dec_ref(v_as_1047_);
lean_dec_ref(v_tgtRange_1044_);
lean_dec(v_kind_1043_);
lean_dec_ref(v_i_1042_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_ctx_x3f_1055_, lean_object* v_i_1056_, lean_object* v_kind_1057_, lean_object* v_tgtRange_1058_, lean_object* v_f_1059_, lean_object* v_canonicalOnly_1060_, lean_object* v_as_1061_, lean_object* v_sz_1062_, lean_object* v_i_1063_, lean_object* v_b_1064_){
_start:
{
uint8_t v_canonicalOnly_boxed_1065_; size_t v_sz_boxed_1066_; size_t v_i_boxed_1067_; lean_object* v_res_1068_; 
v_canonicalOnly_boxed_1065_ = lean_unbox(v_canonicalOnly_1060_);
v_sz_boxed_1066_ = lean_unbox_usize(v_sz_1062_);
lean_dec(v_sz_1062_);
v_i_boxed_1067_ = lean_unbox_usize(v_i_1063_);
lean_dec(v_i_1063_);
v_res_1068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_1055_, v_i_1056_, v_kind_1057_, v_tgtRange_1058_, v_f_1059_, v_canonicalOnly_boxed_1065_, v_as_1061_, v_sz_boxed_1066_, v_i_boxed_1067_, v_b_1064_);
lean_dec_ref(v_as_1061_);
lean_dec_ref(v_tgtRange_1058_);
lean_dec(v_kind_1057_);
lean_dec_ref(v_i_1056_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0___boxed(lean_object* v_init_1069_, lean_object* v_ctx_x3f_1070_, lean_object* v_i_1071_, lean_object* v_kind_1072_, lean_object* v_tgtRange_1073_, lean_object* v_f_1074_, lean_object* v_canonicalOnly_1075_, lean_object* v_n_1076_, lean_object* v_b_1077_){
_start:
{
uint8_t v_canonicalOnly_boxed_1078_; lean_object* v_res_1079_; 
v_canonicalOnly_boxed_1078_ = lean_unbox(v_canonicalOnly_1075_);
v_res_1079_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_1069_, v_ctx_x3f_1070_, v_i_1071_, v_kind_1072_, v_tgtRange_1073_, v_f_1074_, v_canonicalOnly_boxed_1078_, v_n_1076_, v_b_1077_);
lean_dec_ref(v_n_1076_);
lean_dec_ref(v_tgtRange_1073_);
lean_dec(v_kind_1072_);
lean_dec_ref(v_i_1071_);
lean_dec_ref(v_init_1069_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f___boxed(lean_object* v_kind_1080_, lean_object* v_tgtRange_1081_, lean_object* v_ctx_x3f_1082_, lean_object* v_t_1083_, lean_object* v_f_1084_, lean_object* v_canonicalOnly_1085_){
_start:
{
uint8_t v_canonicalOnly_boxed_1086_; lean_object* v_res_1087_; 
v_canonicalOnly_boxed_1086_ = lean_unbox(v_canonicalOnly_1085_);
v_res_1087_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_1080_, v_tgtRange_1081_, v_ctx_x3f_1082_, v_t_1083_, v_f_1084_, v_canonicalOnly_boxed_1086_);
lean_dec_ref(v_tgtRange_1081_);
lean_dec(v_kind_1080_);
return v_res_1087_;
}
}
static lean_object* _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_1089_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_1089_, 0, lean_box(0));
lean_closure_set(v___x_1089_, 1, lean_box(0));
lean_closure_set(v___x_1089_, 2, v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(lean_object* v_msg_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; lean_object* v___f_1094_; lean_object* v___x_3969__overap_1095_; lean_object* v___x_1096_; 
v___x_1093_ = lean_obj_once(&l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0, &l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0_once, _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0);
v___f_1094_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1094_, 0, v___x_1093_);
v___x_3969__overap_1095_ = lean_panic_fn_borrowed(v___f_1094_, v_msg_1090_);
lean_dec_ref(v___f_1094_);
lean_inc_ref(v___y_1091_);
v___x_1096_ = lean_apply_2(v___x_3969__overap_1095_, v___y_1091_, lean_box(0));
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___boxed(lean_object* v_msg_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v_msg_1097_, v___y_1098_);
lean_dec_ref(v___y_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0(lean_object* v___x_1101_, lean_object* v___x_1102_, lean_object* v_ctx_1103_, lean_object* v_node_1104_, lean_object* v_result_1105_){
_start:
{
if (lean_obj_tag(v_node_1104_) == 1)
{
lean_object* v_i_1106_; 
v_i_1106_ = lean_ctor_get(v_node_1104_, 0);
if (lean_obj_tag(v_i_1106_) == 3)
{
lean_object* v_i_1107_; lean_object* v_stx_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1123_; 
v_i_1107_ = lean_ctor_get(v_i_1106_, 0);
lean_inc_ref(v_i_1107_);
v_stx_1108_ = lean_ctor_get(v_i_1107_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_i_1107_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_i_1107_, 0);
lean_dec(v_unused_1124_);
v___x_1110_ = v_i_1107_;
v_isShared_1111_ = v_isSharedCheck_1123_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_stx_1108_);
lean_dec(v_i_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1123_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
uint8_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = 1;
v___x_1113_ = l_Lean_Syntax_getPos_x3f(v_stx_1108_, v___x_1112_);
if (lean_obj_tag(v___x_1113_) == 1)
{
lean_object* v_val_1114_; lean_object* v___x_1115_; 
v_val_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v___x_1113_, 1);
v___x_1115_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1108_, v___x_1112_);
lean_dec(v_stx_1108_);
if (lean_obj_tag(v___x_1115_) == 1)
{
lean_object* v_val_1116_; uint8_t v___x_1117_; 
v_val_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_val_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = lean_nat_dec_le(v_val_1114_, v___x_1101_);
lean_dec(v_val_1114_);
if (v___x_1117_ == 0)
{
lean_dec(v_val_1116_);
lean_del_object(v___x_1110_);
lean_dec_ref_known(v_node_1104_, 2);
lean_dec_ref(v_ctx_1103_);
return v_result_1105_;
}
else
{
uint8_t v___x_1118_; 
v___x_1118_ = lean_nat_dec_le(v___x_1102_, v_val_1116_);
lean_dec(v_val_1116_);
if (v___x_1118_ == 0)
{
lean_del_object(v___x_1110_);
lean_dec_ref_known(v_node_1104_, 2);
lean_dec_ref(v_ctx_1103_);
return v_result_1105_;
}
else
{
lean_object* v___x_1120_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 1, v_node_1104_);
lean_ctor_set(v___x_1110_, 0, v_ctx_1103_);
v___x_1120_ = v___x_1110_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_ctx_1103_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_node_1104_);
v___x_1120_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_array_push(v_result_1105_, v___x_1120_);
return v___x_1121_;
}
}
}
}
else
{
lean_dec(v___x_1115_);
lean_dec(v_val_1114_);
lean_del_object(v___x_1110_);
lean_dec_ref_known(v_node_1104_, 2);
lean_dec_ref(v_ctx_1103_);
return v_result_1105_;
}
}
else
{
lean_dec(v___x_1113_);
lean_del_object(v___x_1110_);
lean_dec(v_stx_1108_);
lean_dec_ref_known(v_node_1104_, 2);
lean_dec_ref(v_ctx_1103_);
return v_result_1105_;
}
}
}
else
{
lean_dec_ref_known(v_node_1104_, 2);
lean_dec_ref(v_ctx_1103_);
return v_result_1105_;
}
}
else
{
lean_dec_ref(v_node_1104_);
lean_dec_ref(v_ctx_1103_);
return v_result_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed(lean_object* v___x_1125_, lean_object* v___x_1126_, lean_object* v_ctx_1127_, lean_object* v_node_1128_, lean_object* v_result_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_CodeAction_cmdCodeActionProvider___lam__0(v___x_1125_, v___x_1126_, v_ctx_1127_, v_node_1128_, v_result_1129_);
lean_dec(v___x_1126_);
lean_dec(v___x_1125_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(lean_object* v_params_1131_, lean_object* v_snap_1132_, lean_object* v_fst_1133_, lean_object* v_snd_1134_, lean_object* v_as_1135_, size_t v_sz_1136_, size_t v_i_1137_, lean_object* v_b_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_snd_1142_; uint8_t v___x_1146_; 
v___x_1146_ = lean_usize_dec_lt(v_i_1137_, v_sz_1136_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
lean_dec_ref(v_snd_1134_);
lean_dec_ref(v_fst_1133_);
lean_dec_ref(v_snap_1132_);
lean_dec_ref(v_params_1131_);
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_b_1138_);
return v___x_1147_;
}
else
{
lean_object* v___x_4591__overap_1148_; lean_object* v___x_1149_; 
v___x_4591__overap_1148_ = lean_array_uget_borrowed(v_as_1135_, v_i_1137_);
lean_inc(v___x_4591__overap_1148_);
lean_inc_ref(v___y_1139_);
lean_inc_ref(v_snd_1134_);
lean_inc_ref(v_fst_1133_);
lean_inc_ref(v_snap_1132_);
lean_inc_ref(v_params_1131_);
v___x_1149_ = lean_apply_6(v___x_4591__overap_1148_, v_params_1131_, v_snap_1132_, v_fst_1133_, v_snd_1134_, v___y_1139_, lean_box(0));
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1151_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v___x_1151_ = l_Array_append___redArg(v_b_1138_, v_a_1150_);
lean_dec(v_a_1150_);
v_snd_1142_ = v___x_1151_;
goto v___jp_1141_;
}
else
{
lean_dec_ref_known(v___x_1149_, 1);
v_snd_1142_ = v_b_1138_;
goto v___jp_1141_;
}
}
v___jp_1141_:
{
size_t v___x_1143_; size_t v___x_1144_; 
v___x_1143_ = ((size_t)1ULL);
v___x_1144_ = lean_usize_add(v_i_1137_, v___x_1143_);
v_i_1137_ = v___x_1144_;
v_b_1138_ = v_snd_1142_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1___boxed(lean_object* v_params_1152_, lean_object* v_snap_1153_, lean_object* v_fst_1154_, lean_object* v_snd_1155_, lean_object* v_as_1156_, lean_object* v_sz_1157_, lean_object* v_i_1158_, lean_object* v_b_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
size_t v_sz_boxed_1162_; size_t v_i_boxed_1163_; lean_object* v_res_1164_; 
v_sz_boxed_1162_ = lean_unbox_usize(v_sz_1157_);
lean_dec(v_sz_1157_);
v_i_boxed_1163_ = lean_unbox_usize(v_i_1158_);
lean_dec(v_i_1158_);
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1152_, v_snap_1153_, v_fst_1154_, v_snd_1155_, v_as_1156_, v_sz_boxed_1162_, v_i_boxed_1163_, v_b_1159_, v___y_1160_);
lean_dec_ref(v___y_1160_);
lean_dec_ref(v_as_1156_);
return v_res_1164_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2));
v___x_1169_ = lean_unsigned_to_nat(48u);
v___x_1170_ = lean_unsigned_to_nat(185u);
v___x_1171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1));
v___x_1172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0));
v___x_1173_ = l_mkPanicMessageWithDecl(v___x_1172_, v___x_1171_, v___x_1170_, v___x_1169_, v___x_1168_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(lean_object* v___x_1174_, lean_object* v_params_1175_, lean_object* v_snap_1176_, lean_object* v_as_1177_, size_t v_sz_1178_, size_t v_i_1179_, lean_object* v_b_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_a_1184_; lean_object* v___y_1189_; uint8_t v___x_1200_; 
v___x_1200_ = lean_usize_dec_lt(v_i_1179_, v_sz_1178_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
lean_dec_ref(v_snap_1176_);
lean_dec_ref(v_params_1175_);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_b_1180_);
return v___x_1201_;
}
else
{
lean_object* v_a_1202_; lean_object* v_snd_1203_; 
v_a_1202_ = lean_array_uget_borrowed(v_as_1177_, v_i_1179_);
v_snd_1203_ = lean_ctor_get(v_a_1202_, 1);
if (lean_obj_tag(v_snd_1203_) == 1)
{
lean_object* v_i_1204_; 
v_i_1204_ = lean_ctor_get(v_snd_1203_, 0);
if (lean_obj_tag(v_i_1204_) == 3)
{
lean_object* v_fst_1205_; lean_object* v_i_1206_; lean_object* v_onAnyCmd_1207_; lean_object* v_onCmd_1208_; lean_object* v_out_1210_; lean_object* v___y_1211_; lean_object* v_stx_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_fst_1205_ = lean_ctor_get(v_a_1202_, 0);
v_i_1206_ = lean_ctor_get(v_i_1204_, 0);
v_onAnyCmd_1207_ = lean_ctor_get(v___x_1174_, 0);
v_onCmd_1208_ = lean_ctor_get(v___x_1174_, 1);
v_stx_1216_ = lean_ctor_get(v_i_1206_, 1);
lean_inc(v_stx_1216_);
v___x_1217_ = l_Lean_Syntax_getKind(v_stx_1216_);
v___x_1218_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_1208_, v___x_1217_);
lean_dec(v___x_1217_);
if (lean_obj_tag(v___x_1218_) == 1)
{
lean_object* v_val_1219_; size_t v_sz_1220_; size_t v___x_1221_; lean_object* v___x_1222_; 
v_val_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_val_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v_sz_1220_ = lean_array_size(v_val_1219_);
v___x_1221_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1203_);
lean_inc(v_fst_1205_);
lean_inc_ref(v_snap_1176_);
lean_inc_ref(v_params_1175_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1175_, v_snap_1176_, v_fst_1205_, v_snd_1203_, v_val_1219_, v_sz_1220_, v___x_1221_, v_b_1180_, v___y_1181_);
lean_dec(v_val_1219_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v_out_1210_ = v_a_1223_;
v___y_1211_ = v___y_1181_;
goto v___jp_1209_;
}
else
{
lean_dec_ref(v_snap_1176_);
lean_dec_ref(v_params_1175_);
return v___x_1222_;
}
}
else
{
lean_dec(v___x_1218_);
v_out_1210_ = v_b_1180_;
v___y_1211_ = v___y_1181_;
goto v___jp_1209_;
}
v___jp_1209_:
{
size_t v_sz_1212_; size_t v___x_1213_; lean_object* v___x_1214_; 
v_sz_1212_ = lean_array_size(v_onAnyCmd_1207_);
v___x_1213_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1203_);
lean_inc(v_fst_1205_);
lean_inc_ref(v_snap_1176_);
lean_inc_ref(v_params_1175_);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1175_, v_snap_1176_, v_fst_1205_, v_snd_1203_, v_onAnyCmd_1207_, v_sz_1212_, v___x_1213_, v_out_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v_a_1184_ = v_a_1215_;
goto v___jp_1183_;
}
else
{
lean_dec_ref(v_snap_1176_);
lean_dec_ref(v_params_1175_);
return v___x_1214_;
}
}
}
else
{
v___y_1189_ = v___y_1181_;
goto v___jp_1188_;
}
}
else
{
v___y_1189_ = v___y_1181_;
goto v___jp_1188_;
}
}
v___jp_1183_:
{
size_t v___x_1185_; size_t v___x_1186_; 
v___x_1185_ = ((size_t)1ULL);
v___x_1186_ = lean_usize_add(v_i_1179_, v___x_1185_);
v_i_1179_ = v___x_1186_;
v_b_1180_ = v_a_1184_;
goto _start;
}
v___jp_1188_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
v___x_1191_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v___x_1190_, v___y_1189_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_dec_ref_known(v___x_1191_, 1);
v_a_1184_ = v_b_1180_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v_b_1180_);
lean_dec_ref(v_snap_1176_);
lean_dec_ref(v_params_1175_);
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___boxed(lean_object* v___x_1224_, lean_object* v_params_1225_, lean_object* v_snap_1226_, lean_object* v_as_1227_, lean_object* v_sz_1228_, lean_object* v_i_1229_, lean_object* v_b_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
size_t v_sz_boxed_1233_; size_t v_i_boxed_1234_; lean_object* v_res_1235_; 
v_sz_boxed_1233_ = lean_unbox_usize(v_sz_1228_);
lean_dec(v_sz_1228_);
v_i_boxed_1234_ = lean_unbox_usize(v_i_1229_);
lean_dec(v_i_1229_);
v_res_1235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_1224_, v_params_1225_, v_snap_1226_, v_as_1227_, v_sz_boxed_1233_, v_i_boxed_1234_, v_b_1230_, v___y_1231_);
lean_dec_ref(v___y_1231_);
lean_dec_ref(v_as_1227_);
lean_dec_ref(v___x_1224_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(lean_object* v_params_1236_, lean_object* v_snap_1237_, lean_object* v___x_1238_, lean_object* v_as_1239_, size_t v_sz_1240_, size_t v_i_1241_, lean_object* v_b_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_a_1246_; lean_object* v___y_1251_; uint8_t v___x_1262_; 
v___x_1262_ = lean_usize_dec_lt(v_i_1241_, v_sz_1240_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
lean_dec_ref(v_snap_1237_);
lean_dec_ref(v_params_1236_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_b_1242_);
return v___x_1263_;
}
else
{
lean_object* v_a_1264_; lean_object* v_snd_1265_; 
v_a_1264_ = lean_array_uget_borrowed(v_as_1239_, v_i_1241_);
v_snd_1265_ = lean_ctor_get(v_a_1264_, 1);
if (lean_obj_tag(v_snd_1265_) == 1)
{
lean_object* v_i_1266_; 
v_i_1266_ = lean_ctor_get(v_snd_1265_, 0);
if (lean_obj_tag(v_i_1266_) == 3)
{
lean_object* v_fst_1267_; lean_object* v_i_1268_; lean_object* v_onAnyCmd_1269_; lean_object* v_onCmd_1270_; lean_object* v_out_1272_; lean_object* v___y_1273_; lean_object* v_stx_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_fst_1267_ = lean_ctor_get(v_a_1264_, 0);
v_i_1268_ = lean_ctor_get(v_i_1266_, 0);
v_onAnyCmd_1269_ = lean_ctor_get(v___x_1238_, 0);
v_onCmd_1270_ = lean_ctor_get(v___x_1238_, 1);
v_stx_1278_ = lean_ctor_get(v_i_1268_, 1);
lean_inc(v_stx_1278_);
v___x_1279_ = l_Lean_Syntax_getKind(v_stx_1278_);
v___x_1280_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_1270_, v___x_1279_);
lean_dec(v___x_1279_);
if (lean_obj_tag(v___x_1280_) == 1)
{
lean_object* v_val_1281_; size_t v_sz_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
v_val_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v_sz_1282_ = lean_array_size(v_val_1281_);
v___x_1283_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1265_);
lean_inc(v_fst_1267_);
lean_inc_ref(v_snap_1237_);
lean_inc_ref(v_params_1236_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1236_, v_snap_1237_, v_fst_1267_, v_snd_1265_, v_val_1281_, v_sz_1282_, v___x_1283_, v_b_1242_, v___y_1243_);
lean_dec(v_val_1281_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v_out_1272_ = v_a_1285_;
v___y_1273_ = v___y_1243_;
goto v___jp_1271_;
}
else
{
lean_dec_ref(v_snap_1237_);
lean_dec_ref(v_params_1236_);
return v___x_1284_;
}
}
else
{
lean_dec(v___x_1280_);
v_out_1272_ = v_b_1242_;
v___y_1273_ = v___y_1243_;
goto v___jp_1271_;
}
v___jp_1271_:
{
size_t v_sz_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v_sz_1274_ = lean_array_size(v_onAnyCmd_1269_);
v___x_1275_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1265_);
lean_inc(v_fst_1267_);
lean_inc_ref(v_snap_1237_);
lean_inc_ref(v_params_1236_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1236_, v_snap_1237_, v_fst_1267_, v_snd_1265_, v_onAnyCmd_1269_, v_sz_1274_, v___x_1275_, v_out_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v_a_1246_ = v_a_1277_;
goto v___jp_1245_;
}
else
{
lean_dec_ref(v_snap_1237_);
lean_dec_ref(v_params_1236_);
return v___x_1276_;
}
}
}
else
{
v___y_1251_ = v___y_1243_;
goto v___jp_1250_;
}
}
else
{
v___y_1251_ = v___y_1243_;
goto v___jp_1250_;
}
}
v___jp_1245_:
{
size_t v___x_1247_; size_t v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = lean_usize_add(v_i_1241_, v___x_1247_);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_1238_, v_params_1236_, v_snap_1237_, v_as_1239_, v_sz_1240_, v___x_1248_, v_a_1246_, v___y_1243_);
return v___x_1249_;
}
v___jp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
v___x_1253_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v___x_1252_, v___y_1251_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_dec_ref_known(v___x_1253_, 1);
v_a_1246_ = v_b_1242_;
goto v___jp_1245_;
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v_b_1242_);
lean_dec_ref(v_snap_1237_);
lean_dec_ref(v_params_1236_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2___boxed(lean_object* v_params_1286_, lean_object* v_snap_1287_, lean_object* v___x_1288_, lean_object* v_as_1289_, lean_object* v_sz_1290_, lean_object* v_i_1291_, lean_object* v_b_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
size_t v_sz_boxed_1295_; size_t v_i_boxed_1296_; lean_object* v_res_1297_; 
v_sz_boxed_1295_ = lean_unbox_usize(v_sz_1290_);
lean_dec(v_sz_1290_);
v_i_boxed_1296_ = lean_unbox_usize(v_i_1291_);
lean_dec(v_i_1291_);
v_res_1297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_1286_, v_snap_1287_, v___x_1288_, v_as_1289_, v_sz_boxed_1295_, v_i_boxed_1296_, v_b_1292_, v___y_1293_);
lean_dec_ref(v___y_1293_);
lean_dec_ref(v_as_1289_);
lean_dec_ref(v___x_1288_);
return v_res_1297_;
}
}
static lean_object* _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = l_Lean_CodeAction_instInhabitedCommandCodeActions_default;
v___x_1299_ = lean_obj_once(&l_Lean_CodeAction_holeCodeActionProvider___closed__0, &l_Lean_CodeAction_holeCodeActionProvider___closed__0_once, _init_l_Lean_CodeAction_holeCodeActionProvider___closed__0);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider(lean_object* v_params_1303_, lean_object* v_snap_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v_a_1309_; lean_object* v_toEditableDocumentCore_1310_; lean_object* v_meta_1311_; lean_object* v_range_1312_; lean_object* v_text_1313_; lean_object* v_start_1314_; lean_object* v_end_1315_; lean_object* v___x_1316_; lean_object* v_toEnvExtension_1317_; lean_object* v_asyncMode_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; lean_object* v___x_1322_; lean_object* v_snd_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___f_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; size_t v_sz_1330_; size_t v___x_1331_; lean_object* v___x_1332_; 
v___x_1307_ = lean_obj_once(&l_Lean_CodeAction_cmdCodeActionProvider___closed__0, &l_Lean_CodeAction_cmdCodeActionProvider___closed__0_once, _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0);
v___x_1308_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v_a_1305_);
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref(v___x_1308_);
v_toEditableDocumentCore_1310_ = lean_ctor_get(v_a_1309_, 0);
lean_inc_ref(v_toEditableDocumentCore_1310_);
lean_dec(v_a_1309_);
v_meta_1311_ = lean_ctor_get(v_toEditableDocumentCore_1310_, 0);
lean_inc_ref(v_meta_1311_);
lean_dec_ref(v_toEditableDocumentCore_1310_);
v_range_1312_ = lean_ctor_get(v_params_1303_, 3);
v_text_1313_ = lean_ctor_get(v_meta_1311_, 3);
lean_inc_ref(v_text_1313_);
lean_dec_ref(v_meta_1311_);
v_start_1314_ = lean_ctor_get(v_range_1312_, 0);
v_end_1315_ = lean_ctor_get(v_range_1312_, 1);
v___x_1316_ = l_Lean_CodeAction_cmdCodeActionExt;
v_toEnvExtension_1317_ = lean_ctor_get(v___x_1316_, 0);
v_asyncMode_1318_ = lean_ctor_get(v_toEnvExtension_1317_, 2);
v___x_1319_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1304_);
v___x_1320_ = lean_box(0);
v___x_1321_ = 0;
v___x_1322_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1307_, v___x_1316_, v___x_1319_, v_asyncMode_1318_, v___x_1320_, v___x_1321_);
v_snd_1323_ = lean_ctor_get(v___x_1322_, 1);
lean_inc(v_snd_1323_);
lean_dec(v___x_1322_);
lean_inc_ref(v_start_1314_);
v___x_1324_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1313_, v_start_1314_);
lean_inc_ref(v_end_1315_);
v___x_1325_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1313_, v_end_1315_);
lean_dec_ref(v_text_1313_);
v___f_1326_ = lean_alloc_closure((void*)(l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1326_, 0, v___x_1325_);
lean_closure_set(v___f_1326_, 1, v___x_1324_);
v___x_1327_ = ((lean_object*)(l_Lean_CodeAction_cmdCodeActionProvider___closed__1));
lean_inc_ref(v_snap_1304_);
v___x_1328_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_1304_);
v___x_1329_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v___x_1327_, v___f_1326_, v___x_1328_);
v_sz_1330_ = lean_array_size(v___x_1329_);
v___x_1331_ = ((size_t)0ULL);
v___x_1332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_1303_, v_snap_1304_, v_snd_1323_, v___x_1329_, v_sz_1330_, v___x_1331_, v___x_1327_, v_a_1305_);
lean_dec(v___x_1329_);
lean_dec(v_snd_1323_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___boxed(lean_object* v_params_1333_, lean_object* v_snap_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_CodeAction_cmdCodeActionProvider(v_params_1333_, v_snap_1334_, v_a_1335_);
lean_dec_ref(v_a_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1(){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1));
v___x_1345_ = lean_alloc_closure((void*)(l_Lean_CodeAction_cmdCodeActionProvider___boxed), 4, 0);
v___x_1346_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_1344_, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___boxed(lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
return v_res_1348_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Producers_Range(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_StepSize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinNotation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_CodeActions_Attr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_CodeActions_Provider(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_Iterators_Producers_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinTerm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinNotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_CodeActions_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_CodeActions_Provider(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Server_CodeActions_Provider(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_CodeActions_Provider(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_CodeActions_Provider(builtin);
}
#ifdef __cplusplus
}
#endif
