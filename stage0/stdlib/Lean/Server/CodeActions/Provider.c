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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeqBracketed"};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(142, 80, 121, 250, 245, 54, 71, 145)}};
static const lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6 = (const lean_object*)&l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(lean_object* v___y_1_){
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
LEAN_EXPORT void l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1_ = stack[0].m_obj;
lean_object* v_res_5_;
v_res_5_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v___y_1_);
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0___boxed(lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v___y_6_);
lean_dec_ref(v___y_6_);
return v_res_8_;
}
}
uint8_t l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(lean_object* v_a_9_, lean_object* v_x_10_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
else
{
lean_object* v_head_12_; lean_object* v_tail_13_; uint8_t v___x_14_; 
v_head_12_ = lean_ctor_get(v_x_10_, 0);
v_tail_13_ = lean_ctor_get(v_x_10_, 1);
v___x_14_ = lean_name_eq(v_a_9_, v_head_12_);
if (v___x_14_ == 0)
{
v_x_10_ = v_tail_13_;
goto _start;
}
else
{
return v___x_14_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_9_ = stack[0].m_obj;
lean_object* v_x_10_ = stack[1].m_obj;
uint8_t v_res_16_;
v_res_16_ = l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(v_a_9_, v_x_10_);
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1___boxed(lean_object* v_a_17_, lean_object* v_x_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(v_a_17_, v_x_18_);
lean_dec(v_x_18_);
lean_dec(v_a_17_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0(lean_object* v___x_51_, lean_object* v___x_52_, lean_object* v_ctx_53_, lean_object* v_info_54_, lean_object* v_result_55_){
_start:
{
if (lean_obj_tag(v_info_54_) == 1)
{
lean_object* v_i_56_; uint8_t v___y_58_; lean_object* v_toElabInfo_61_; lean_object* v_elaborator_62_; lean_object* v_stx_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v_i_56_ = lean_ctor_get(v_info_54_, 0);
v_toElabInfo_61_ = lean_ctor_get(v_i_56_, 0);
v_elaborator_62_ = lean_ctor_get(v_toElabInfo_61_, 0);
v_stx_63_ = lean_ctor_get(v_toElabInfo_61_, 1);
v___x_64_ = ((lean_object*)(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11));
v___x_65_ = l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(v_elaborator_62_, v___x_64_);
if (v___x_65_ == 0)
{
lean_dec_ref(v_ctx_53_);
return v_result_55_;
}
else
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Syntax_getPos_x3f(v_stx_63_, v___x_65_);
if (lean_obj_tag(v___x_66_) == 1)
{
lean_object* v_val_67_; lean_object* v___x_68_; 
v_val_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_val_67_);
lean_dec_ref_known(v___x_66_, 1);
v___x_68_ = l_Lean_Syntax_getTailPos_x3f(v_stx_63_, v___x_65_);
if (lean_obj_tag(v___x_68_) == 1)
{
lean_object* v_val_69_; uint8_t v___x_70_; 
v_val_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_val_69_);
lean_dec_ref_known(v___x_68_, 1);
v___x_70_ = lean_nat_dec_le(v_val_67_, v___x_51_);
lean_dec(v_val_67_);
if (v___x_70_ == 0)
{
lean_dec(v_val_69_);
v___y_58_ = v___x_70_;
goto v___jp_57_;
}
else
{
uint8_t v___x_71_; 
v___x_71_ = lean_nat_dec_le(v___x_52_, v_val_69_);
lean_dec(v_val_69_);
v___y_58_ = v___x_71_;
goto v___jp_57_;
}
}
else
{
lean_dec(v___x_68_);
lean_dec(v_val_67_);
lean_dec_ref(v_ctx_53_);
return v_result_55_;
}
}
else
{
lean_dec(v___x_66_);
lean_dec_ref(v_ctx_53_);
return v_result_55_;
}
}
v___jp_57_:
{
if (v___y_58_ == 0)
{
lean_dec_ref(v_ctx_53_);
return v_result_55_;
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_inc_ref(v_i_56_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v_ctx_53_);
lean_ctor_set(v___x_59_, 1, v_i_56_);
v___x_60_ = lean_array_push(v_result_55_, v___x_59_);
return v___x_60_;
}
}
}
else
{
lean_dec_ref(v_ctx_53_);
return v_result_55_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed(lean_object* v___x_72_, lean_object* v___x_73_, lean_object* v_ctx_74_, lean_object* v_info_75_, lean_object* v_result_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_CodeAction_holeCodeActionProvider___lam__0(v___x_72_, v___x_73_, v_ctx_74_, v_info_75_, v_result_76_);
lean_dec_ref(v_info_75_);
lean_dec(v___x_73_);
lean_dec(v___x_72_);
return v_res_77_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(lean_object* v_params_78_, lean_object* v_snap_79_, lean_object* v_fst_80_, lean_object* v_snd_81_, lean_object* v_as_82_, size_t v_i_83_, size_t v_stop_84_, lean_object* v_b_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_a_89_; uint8_t v___x_93_; 
v___x_93_ = lean_usize_dec_eq(v_i_83_, v_stop_84_);
if (v___x_93_ == 0)
{
lean_object* v___x_1561__overap_94_; lean_object* v___x_95_; 
v___x_1561__overap_94_ = lean_array_uget_borrowed(v_as_82_, v_i_83_);
lean_inc(v___x_1561__overap_94_);
lean_inc_ref(v___y_86_);
lean_inc_ref(v_snd_81_);
lean_inc_ref(v_fst_80_);
lean_inc_ref(v_snap_79_);
lean_inc_ref(v_params_78_);
v___x_95_ = lean_apply_6(v___x_1561__overap_94_, v_params_78_, v_snap_79_, v_fst_80_, v_snd_81_, v___y_86_, lean_box(0));
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_97_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_95_, 1);
v___x_97_ = l_Array_append___redArg(v_b_85_, v_a_96_);
lean_dec(v_a_96_);
v_a_89_ = v___x_97_;
goto v___jp_88_;
}
else
{
lean_dec_ref(v_b_85_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_98_; 
v_a_98_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_95_, 1);
v_a_89_ = v_a_98_;
goto v___jp_88_;
}
else
{
lean_dec_ref(v_snd_81_);
lean_dec_ref(v_fst_80_);
lean_dec_ref(v_snap_79_);
lean_dec_ref(v_params_78_);
return v___x_95_;
}
}
}
else
{
lean_object* v___x_99_; 
lean_dec_ref(v_snd_81_);
lean_dec_ref(v_fst_80_);
lean_dec_ref(v_snap_79_);
lean_dec_ref(v_params_78_);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v_b_85_);
return v___x_99_;
}
v___jp_88_:
{
size_t v___x_90_; size_t v___x_91_; 
v___x_90_ = ((size_t)1ULL);
v___x_91_ = lean_usize_add(v_i_83_, v___x_90_);
v_i_83_ = v___x_91_;
v_b_85_ = v_a_89_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_78_ = stack[0].m_obj;
lean_object* v_snap_79_ = stack[1].m_obj;
lean_object* v_fst_80_ = stack[2].m_obj;
lean_object* v_snd_81_ = stack[3].m_obj;
lean_object* v_as_82_ = stack[4].m_obj;
size_t v_i_83_ = stack[5].m_num;
size_t v_stop_84_ = stack[6].m_num;
lean_object* v_b_85_ = stack[7].m_obj;
lean_object* v___y_86_ = stack[8].m_obj;
lean_object* v_res_100_;
v_res_100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_78_, v_snap_79_, v_fst_80_, v_snd_81_, v_as_82_, v_i_83_, v_stop_84_, v_b_85_, v___y_86_);
stack->m_obj
 = v_res_100_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2___boxed(lean_object* v_params_101_, lean_object* v_snap_102_, lean_object* v_fst_103_, lean_object* v_snd_104_, lean_object* v_as_105_, lean_object* v_i_106_, lean_object* v_stop_107_, lean_object* v_b_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
size_t v_i_boxed_111_; size_t v_stop_boxed_112_; lean_object* v_res_113_; 
v_i_boxed_111_ = lean_unbox_usize(v_i_106_);
lean_dec(v_i_106_);
v_stop_boxed_112_ = lean_unbox_usize(v_stop_107_);
lean_dec(v_stop_107_);
v_res_113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_101_, v_snap_102_, v_fst_103_, v_snd_104_, v_as_105_, v_i_boxed_111_, v_stop_boxed_112_, v_b_108_, v___y_109_);
lean_dec_ref(v___y_109_);
lean_dec_ref(v_as_105_);
return v_res_113_;
}
}
static lean_object* _init_l_Lean_CodeAction_holeCodeActionProvider___closed__0(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Array_instInhabited___redArg();
return v___x_114_;
}
}
static lean_object* _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_obj_once(&l_Lean_CodeAction_holeCodeActionProvider___closed__0, &l_Lean_CodeAction_holeCodeActionProvider___closed__0_once, _init_l_Lean_CodeAction_holeCodeActionProvider___closed__0);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
return v___x_116_;
}
}
lean_object* l_Lean_CodeAction_holeCodeActionProvider(lean_object* v_params_121_, lean_object* v_snap_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_170_; 
v___x_125_ = lean_obj_once(&l_Lean_CodeAction_holeCodeActionProvider___closed__1, &l_Lean_CodeAction_holeCodeActionProvider___closed__1_once, _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1);
v___x_126_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v_a_123_);
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_170_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_170_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_170_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v_toEditableDocumentCore_131_; lean_object* v_meta_132_; lean_object* v_range_133_; lean_object* v_text_134_; lean_object* v_start_135_; lean_object* v_end_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___f_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_toEditableDocumentCore_131_ = lean_ctor_get(v_a_127_, 0);
lean_inc_ref(v_toEditableDocumentCore_131_);
lean_dec(v_a_127_);
v_meta_132_ = lean_ctor_get(v_toEditableDocumentCore_131_, 0);
lean_inc_ref(v_meta_132_);
lean_dec_ref(v_toEditableDocumentCore_131_);
v_range_133_ = lean_ctor_get(v_params_121_, 3);
v_text_134_ = lean_ctor_get(v_meta_132_, 3);
lean_inc_ref(v_text_134_);
lean_dec_ref(v_meta_132_);
v_start_135_ = lean_ctor_get(v_range_133_, 0);
v_end_136_ = lean_ctor_get(v_range_133_, 1);
lean_inc_ref(v_start_135_);
v___x_137_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_134_, v_start_135_);
lean_inc_ref(v_end_136_);
v___x_138_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_134_, v_end_136_);
lean_dec_ref(v_text_134_);
v___f_139_ = lean_alloc_closure((void*)(l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed), 5, 2);
lean_closure_set(v___f_139_, 0, v___x_138_);
lean_closure_set(v___f_139_, 1, v___x_137_);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = ((lean_object*)(l_Lean_CodeAction_holeCodeActionProvider___closed__2));
lean_inc_ref(v_snap_122_);
v___x_142_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_122_);
v___x_143_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_139_, v___x_141_, v___x_142_);
v___x_144_ = lean_array_get_size(v___x_143_);
v___x_145_ = lean_unsigned_to_nat(1u);
v___x_146_ = lean_nat_dec_eq(v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_148_; 
lean_dec(v___x_143_);
lean_dec_ref(v_snap_122_);
lean_dec_ref(v_params_121_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v___x_141_);
v___x_148_ = v___x_129_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_141_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
else
{
lean_object* v___x_150_; lean_object* v_fst_151_; lean_object* v_snd_152_; lean_object* v___x_153_; lean_object* v_toEnvExtension_154_; lean_object* v_asyncMode_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v_snd_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_150_ = lean_array_fget(v___x_143_, v___x_140_);
lean_dec(v___x_143_);
v_fst_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_fst_151_);
v_snd_152_ = lean_ctor_get(v___x_150_, 1);
lean_inc(v_snd_152_);
lean_dec(v___x_150_);
v___x_153_ = l_Lean_CodeAction_holeCodeActionExt;
v_toEnvExtension_154_ = lean_ctor_get(v___x_153_, 0);
v_asyncMode_155_ = lean_ctor_get(v_toEnvExtension_154_, 2);
v___x_156_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_122_);
v___x_157_ = lean_box(0);
v___x_158_ = 0;
v___x_159_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_125_, v___x_153_, v___x_156_, v_asyncMode_155_, v___x_157_, v___x_158_);
v_snd_160_ = lean_ctor_get(v___x_159_, 1);
lean_inc(v_snd_160_);
lean_dec(v___x_159_);
v___x_161_ = ((lean_object*)(l_Lean_CodeAction_holeCodeActionProvider___closed__3));
v___x_162_ = lean_array_get_size(v_snd_160_);
v___x_163_ = lean_nat_dec_lt(v___x_140_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_165_; 
lean_dec(v_snd_160_);
lean_dec(v_snd_152_);
lean_dec(v_fst_151_);
lean_dec_ref(v_snap_122_);
lean_dec_ref(v_params_121_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v___x_161_);
v___x_165_ = v___x_129_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_161_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
else
{
size_t v___x_167_; size_t v___x_168_; lean_object* v___x_169_; 
lean_del_object(v___x_129_);
v___x_167_ = ((size_t)0ULL);
v___x_168_ = lean_usize_of_nat(v___x_162_);
v___x_169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_121_, v_snap_122_, v_fst_151_, v_snd_152_, v_snd_160_, v___x_167_, v___x_168_, v___x_161_, v_a_123_);
lean_dec(v_snd_160_);
return v___x_169_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_CodeAction_holeCodeActionProvider_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_121_ = stack[0].m_obj;
lean_object* v_snap_122_ = stack[1].m_obj;
lean_object* v_a_123_ = stack[2].m_obj;
lean_object* v_res_171_;
v_res_171_ = l_Lean_CodeAction_holeCodeActionProvider(v_params_121_, v_snap_122_, v_a_123_);
stack->m_obj
 = v_res_171_;
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___boxed(lean_object* v_params_172_, lean_object* v_snap_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_CodeAction_holeCodeActionProvider(v_params_172_, v_snap_173_, v_a_174_);
lean_dec_ref(v_a_174_);
return v_res_176_;
}
}
lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1(){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2));
v___x_185_ = lean_alloc_closure((void*)(l_Lean_CodeAction_holeCodeActionProvider___boxed), 4, 0);
v___x_186_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_184_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT void l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_187_;
v_res_187_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
stack->m_obj
 = v_res_187_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___boxed(lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx___impl(lean_object* v_x_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_tag_nat(v_x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx___impl___boxed(lean_object* v_x_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_CodeAction_FindTacticResult_ctorIdx___impl(v_x_192_);
lean_dec_ref(v_x_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(lean_object* v_t_194_, lean_object* v_k_195_){
_start:
{
if (lean_obj_tag(v_t_194_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_197_; 
v_a_196_ = lean_ctor_get(v_t_194_, 0);
lean_inc(v_a_196_);
lean_dec_ref_known(v_t_194_, 1);
v___x_197_ = lean_apply_1(v_k_195_, v_a_196_);
return v___x_197_;
}
else
{
uint8_t v_preferred_198_; lean_object* v_insertIdx_199_; lean_object* v_a_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_preferred_198_ = lean_ctor_get_uint8(v_t_194_, sizeof(void*)*2);
v_insertIdx_199_ = lean_ctor_get(v_t_194_, 0);
lean_inc(v_insertIdx_199_);
v_a_200_ = lean_ctor_get(v_t_194_, 1);
lean_inc(v_a_200_);
lean_dec_ref_known(v_t_194_, 2);
v___x_201_ = lean_box(v_preferred_198_);
v___x_202_ = lean_apply_3(v_k_195_, v___x_201_, v_insertIdx_199_, v_a_200_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim(lean_object* v_motive_203_, lean_object* v_ctorIdx_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_k_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_205_, v_k_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___boxed(lean_object* v_motive_209_, lean_object* v_ctorIdx_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_k_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_CodeAction_FindTacticResult_ctorElim(v_motive_209_, v_ctorIdx_210_, v_t_211_, v_h_212_, v_k_213_);
lean_dec(v_ctorIdx_210_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim___redArg(lean_object* v_t_215_, lean_object* v_tactic_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_215_, v_tactic_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim(lean_object* v_motive_218_, lean_object* v_t_219_, lean_object* v_h_220_, lean_object* v_tactic_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_219_, v_tactic_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim___redArg(lean_object* v_t_223_, lean_object* v_tacticSeq_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_223_, v_tacticSeq_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim(lean_object* v_motive_226_, lean_object* v_t_227_, lean_object* v_h_228_, lean_object* v_tacticSeq_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_227_, v_tacticSeq_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(lean_object* v_range_231_, lean_object* v_stx_232_, lean_object* v_prev_x3f_233_){
_start:
{
uint8_t v___x_234_; lean_object* v___x_235_; 
v___x_234_ = 1;
v___x_235_ = l_Lean_Syntax_getPos_x3f(v_stx_232_, v___x_234_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v___x_236_; 
lean_dec(v_prev_x3f_233_);
v___x_236_ = lean_box(0);
return v___x_236_;
}
else
{
lean_object* v_val_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_268_; 
v_val_237_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_268_ == 0)
{
v___x_239_ = v___x_235_;
v_isShared_240_ = v_isSharedCheck_268_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_val_237_);
lean_dec(v___x_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_268_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___y_242_; 
if (lean_obj_tag(v_prev_x3f_233_) == 0)
{
lean_inc(v_val_237_);
v___y_242_ = v_val_237_;
goto v___jp_241_;
}
else
{
lean_object* v_val_267_; 
v_val_267_ = lean_ctor_get(v_prev_x3f_233_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v_prev_x3f_233_, 1);
v___y_242_ = v_val_267_;
goto v___jp_241_;
}
v___jp_241_:
{
lean_object* v_start_243_; lean_object* v_stop_244_; uint8_t v___x_245_; 
v_start_243_ = lean_ctor_get(v_range_231_, 0);
v_stop_244_ = lean_ctor_get(v_range_231_, 1);
v___x_245_ = lean_nat_dec_le(v___y_242_, v_start_243_);
lean_dec(v___y_242_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
v___x_246_ = lean_box(0);
return v___x_246_;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Syntax_getTailInfo(v_stx_232_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_trailing_248_; lean_object* v_endPos_249_; lean_object* v_startPos_250_; lean_object* v_stopPos_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v_trailing_248_ = lean_ctor_get(v___x_247_, 2);
lean_inc_ref(v_trailing_248_);
v_endPos_249_ = lean_ctor_get(v___x_247_, 3);
lean_inc(v_endPos_249_);
lean_dec_ref_known(v___x_247_, 4);
v_startPos_250_ = lean_ctor_get(v_trailing_248_, 1);
lean_inc(v_startPos_250_);
v_stopPos_251_ = lean_ctor_get(v_trailing_248_, 2);
lean_inc(v_stopPos_251_);
lean_dec_ref(v_trailing_248_);
v___x_252_ = lean_nat_sub(v_stopPos_251_, v_startPos_250_);
lean_dec(v_startPos_250_);
lean_dec(v_stopPos_251_);
v___x_253_ = lean_nat_add(v_endPos_249_, v___x_252_);
lean_dec(v___x_252_);
v___x_254_ = lean_nat_dec_le(v_stop_244_, v___x_253_);
lean_dec(v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v_endPos_249_);
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
v___x_255_ = lean_box(0);
return v___x_255_;
}
else
{
uint8_t v___x_256_; 
v___x_256_ = lean_nat_dec_le(v_val_237_, v_start_243_);
lean_dec(v_val_237_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_259_; 
lean_dec(v_endPos_249_);
v___x_257_ = lean_box(v___x_256_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_257_);
v___x_259_ = v___x_239_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
else
{
uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_261_ = lean_nat_dec_le(v_stop_244_, v_endPos_249_);
lean_dec(v_endPos_249_);
v___x_262_ = lean_box(v___x_261_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_262_);
v___x_264_ = v___x_239_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_object* v___x_266_; 
lean_dec(v___x_247_);
lean_del_object(v___x_239_);
lean_dec(v_val_237_);
v___x_266_ = lean_box(0);
return v___x_266_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit___boxed(lean_object* v_range_269_, lean_object* v_stx_270_, lean_object* v_prev_x3f_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_269_, v_stx_270_, v_prev_x3f_271_);
lean_dec(v_stx_270_);
lean_dec_ref(v_range_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(lean_object* v_r_u2081_273_, lean_object* v_r_u2082_274_){
_start:
{
if (lean_obj_tag(v_r_u2081_273_) == 1)
{
lean_object* v_val_275_; 
v_val_275_ = lean_ctor_get(v_r_u2081_273_, 0);
if (lean_obj_tag(v_val_275_) == 1)
{
uint8_t v_preferred_276_; 
v_preferred_276_ = lean_ctor_get_uint8(v_val_275_, sizeof(void*)*2);
if (v_preferred_276_ == 1)
{
if (lean_obj_tag(v_r_u2082_274_) == 1)
{
uint8_t v_preferred_277_; 
v_preferred_277_ = lean_ctor_get_uint8(v_r_u2082_274_, sizeof(void*)*2);
if (v_preferred_277_ == 0)
{
lean_inc_ref(v_val_275_);
return v_val_275_;
}
else
{
lean_inc_ref(v_r_u2082_274_);
return v_r_u2082_274_;
}
}
else
{
lean_inc_ref(v_r_u2082_274_);
return v_r_u2082_274_;
}
}
else
{
lean_inc_ref(v_r_u2082_274_);
return v_r_u2082_274_;
}
}
else
{
lean_inc_ref(v_r_u2082_274_);
return v_r_u2082_274_;
}
}
else
{
lean_inc_ref(v_r_u2082_274_);
return v_r_u2082_274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge___boxed(lean_object* v_r_u2081_278_, lean_object* v_r_u2082_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(v_r_u2081_278_, v_r_u2082_279_);
lean_dec_ref(v_r_u2082_279_);
lean_dec(v_r_u2081_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(lean_object* v_upperBound_284_, lean_object* v___x_285_, lean_object* v_range_286_, lean_object* v_a_287_, lean_object* v_b_288_){
_start:
{
lean_object* v_a_290_; uint8_t v___x_294_; 
v___x_294_ = lean_nat_dec_lt(v_a_287_, v_upperBound_284_);
if (v___x_294_ == 0)
{
lean_dec(v_a_287_);
lean_dec_ref(v_range_286_);
lean_inc_ref(v_b_288_);
return v_b_288_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; 
v___x_295_ = lean_box(0);
v___x_296_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0));
v___x_297_ = lean_unsigned_to_nat(2u);
v___x_298_ = lean_nat_mul(v___x_297_, v_a_287_);
v___x_299_ = l_Lean_Syntax_getArg(v___x_285_, v___x_298_);
lean_dec(v___x_298_);
v___x_300_ = 0;
v___x_301_ = l_Lean_Syntax_getPos_x3f(v___x_299_, v___x_300_);
lean_dec(v___x_299_);
if (lean_obj_tag(v___x_301_) == 1)
{
lean_object* v_val_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_322_; 
v_val_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_322_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_322_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_val_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_322_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v_stop_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_stop_306_ = lean_ctor_get(v_range_286_, 1);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_stop_306_, v___x_307_);
v___x_309_ = lean_nat_dec_le(v___x_308_, v_val_302_);
lean_dec(v_val_302_);
lean_dec(v___x_308_);
if (v___x_309_ == 0)
{
lean_del_object(v___x_304_);
v_a_290_ = v___x_296_;
goto v___jp_289_;
}
else
{
lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_319_; 
v_isSharedCheck_319_ = !lean_is_exclusive(v_range_286_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; lean_object* v_unused_321_; 
v_unused_320_ = lean_ctor_get(v_range_286_, 1);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_range_286_, 0);
lean_dec(v_unused_321_);
v___x_311_ = v_range_286_;
v_isShared_312_ = v_isSharedCheck_319_;
goto v_resetjp_310_;
}
else
{
lean_dec(v_range_286_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_319_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v_a_287_);
v___x_314_ = v___x_304_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_287_);
v___x_314_ = v_reuseFailAlloc_318_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_316_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_295_);
lean_ctor_set(v___x_311_, 0, v___x_314_);
v___x_316_ = v___x_311_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_295_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
}
else
{
lean_dec(v___x_301_);
v_a_290_ = v___x_296_;
goto v___jp_289_;
}
}
v___jp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_a_287_, v___x_291_);
lean_dec(v_a_287_);
v_a_287_ = v___x_292_;
v_b_288_ = v_a_290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___boxed(lean_object* v_upperBound_323_, lean_object* v___x_324_, lean_object* v_range_325_, lean_object* v_a_326_, lean_object* v_b_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_323_, v___x_324_, v_range_325_, v_a_326_, v_b_327_);
lean_dec_ref(v_b_327_);
lean_dec(v___x_324_);
lean_dec(v_upperBound_323_);
return v_res_328_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(lean_object* v_stx_329_, lean_object* v_a_330_, uint8_t v___x_331_, lean_object* v_snd_332_, lean_object* v_____r_333_, lean_object* v_childRes_334_){
_start:
{
lean_object* v___y_336_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = l_Lean_Syntax_getArg(v_stx_329_, v_a_330_);
v___x_341_ = l_Lean_Syntax_getTailPos_x3f(v___x_340_, v___x_331_);
lean_dec(v___x_340_);
if (lean_obj_tag(v___x_341_) == 0)
{
v___y_336_ = v_snd_332_;
goto v___jp_335_;
}
else
{
lean_dec(v_snd_332_);
v___y_336_ = v___x_341_;
goto v___jp_335_;
}
v___jp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v_childRes_334_);
lean_ctor_set(v___x_337_, 1, v___y_336_);
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_329_ = stack[0].m_obj;
lean_object* v_a_330_ = stack[1].m_obj;
uint8_t v___x_331_ = stack[2].m_num;
lean_object* v_snd_332_ = stack[3].m_obj;
lean_object* v_____r_333_ = stack[4].m_obj;
lean_object* v_childRes_334_ = stack[5].m_obj;
lean_object* v_res_342_;
v_res_342_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_329_, v_a_330_, v___x_331_, v_snd_332_, v_____r_333_, v_childRes_334_);
stack->m_obj
 = v_res_342_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0___boxed(lean_object* v_stx_343_, lean_object* v_a_344_, lean_object* v___x_345_, lean_object* v_snd_346_, lean_object* v_____r_347_, lean_object* v_childRes_348_){
_start:
{
uint8_t v___x_3830__boxed_349_; lean_object* v_res_350_; 
v___x_3830__boxed_349_ = lean_unbox(v___x_345_);
v_res_350_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_343_, v_a_344_, v___x_3830__boxed_349_, v_snd_346_, v_____r_347_, v_childRes_348_);
lean_dec(v_a_344_);
lean_dec(v_stx_343_);
return v_res_350_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(lean_object* v___y_361_, uint8_t v___x_362_, lean_object* v___x_363_, lean_object* v_range_364_, lean_object* v___x_365_, lean_object* v_preferred_366_, lean_object* v_a_367_, lean_object* v_b_368_){
_start:
{
lean_object* v_inner_369_; lean_object* v_next_370_; 
v_inner_369_ = lean_ctor_get(v_a_367_, 2);
lean_inc(v_inner_369_);
v_next_370_ = lean_ctor_get(v_inner_369_, 0);
lean_inc(v_next_370_);
if (lean_obj_tag(v_next_370_) == 0)
{
lean_object* v___x_371_; 
lean_dec(v_inner_369_);
lean_dec_ref(v_a_367_);
lean_dec_ref(v_preferred_366_);
lean_dec(v___x_365_);
lean_dec_ref(v_range_364_);
lean_dec(v___x_363_);
v___x_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_371_, 0, v_b_368_);
return v___x_371_;
}
else
{
lean_object* v_nextIdx_372_; lean_object* v_n_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_434_; 
v_nextIdx_372_ = lean_ctor_get(v_a_367_, 0);
v_n_373_ = lean_ctor_get(v_a_367_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_a_367_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v_a_367_, 2);
lean_dec(v_unused_435_);
v___x_375_ = v_a_367_;
v_isShared_376_ = v_isSharedCheck_434_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_n_373_);
lean_inc(v_nextIdx_372_);
lean_dec(v_a_367_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_434_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v_upperBound_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_432_; 
v_upperBound_377_ = lean_ctor_get(v_inner_369_, 1);
v_isSharedCheck_432_ = !lean_is_exclusive(v_inner_369_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v_inner_369_, 0);
lean_dec(v_unused_433_);
v___x_379_ = v_inner_369_;
v_isShared_380_ = v_isSharedCheck_432_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_upperBound_377_);
lean_dec(v_inner_369_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_432_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_val_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_431_; 
v_val_381_ = lean_ctor_get(v_next_370_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_next_370_);
if (v_isSharedCheck_431_ == 0)
{
v___x_383_ = v_next_370_;
v_isShared_384_ = v_isSharedCheck_431_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_val_381_);
lean_dec(v_next_370_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_431_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = lean_nat_add(v_val_381_, v_nextIdx_372_);
lean_dec(v_nextIdx_372_);
lean_dec(v_val_381_);
v___x_386_ = lean_nat_dec_lt(v___x_385_, v_upperBound_377_);
if (v___x_386_ == 0)
{
lean_object* v___x_388_; 
lean_dec(v___x_385_);
lean_del_object(v___x_379_);
lean_dec(v_upperBound_377_);
lean_del_object(v___x_375_);
lean_dec(v_n_373_);
lean_dec_ref(v_preferred_366_);
lean_dec(v___x_365_);
lean_dec_ref(v_range_364_);
lean_dec(v___x_363_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v_b_368_);
v___x_388_ = v___x_383_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_b_368_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_nat_add(v___x_385_, v___x_390_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_391_);
v___x_393_ = v___x_383_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_430_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_395_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_393_);
v___x_395_ = v___x_379_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_upperBound_377_);
v___x_395_ = v_reuseFailAlloc_429_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_397_; 
lean_inc(v_n_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 2, v___x_395_);
lean_ctor_set(v___x_375_, 0, v_n_373_);
v___x_397_ = v___x_375_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_n_373_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_n_373_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v___x_395_);
v___x_397_ = v_reuseFailAlloc_428_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___y_399_; lean_object* v_val_404_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = l_Lean_Syntax_getArg(v___x_363_, v___x_385_);
v___x_407_ = lean_box(0);
v___x_408_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_364_, v___x_406_, v___x_407_);
if (lean_obj_tag(v___x_408_) == 1)
{
lean_object* v_val_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_val_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_val_409_);
lean_dec_ref_known(v___x_408_, 1);
lean_inc(v___x_363_);
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_363_);
lean_ctor_set(v___x_410_, 1, v___x_385_);
lean_inc(v___x_365_);
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_365_);
lean_inc(v___x_406_);
lean_inc_ref(v___x_411_);
lean_inc_ref(v_range_364_);
lean_inc_ref(v_preferred_366_);
v___x_412_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_366_, v_range_364_, v___x_411_, v___x_406_, v___x_407_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_dec_ref_known(v___x_411_, 2);
lean_dec(v_val_409_);
lean_dec(v___x_406_);
lean_dec_ref(v___x_397_);
lean_dec(v_b_368_);
lean_dec_ref(v_preferred_366_);
lean_dec(v___x_365_);
lean_dec_ref(v_range_364_);
lean_dec(v___x_363_);
return v___x_412_;
}
else
{
lean_object* v_val_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_426_; 
v_val_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_426_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_426_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_val_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_426_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
if (lean_obj_tag(v_val_413_) == 0)
{
uint8_t v___x_417_; 
v___x_417_ = lean_unbox(v_val_409_);
lean_dec(v_val_409_);
if (v___x_417_ == 0)
{
lean_del_object(v___x_415_);
lean_dec_ref_known(v___x_411_, 2);
lean_dec(v___x_406_);
v_a_367_ = v___x_397_;
goto _start;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_406_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_411_);
if (v_isShared_416_ == 0)
{
lean_ctor_set_tag(v___x_415_, 0);
lean_ctor_set(v___x_415_, 0, v___x_421_);
v___x_423_ = v___x_415_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
v_val_404_ = v___x_423_;
goto v___jp_403_;
}
}
}
else
{
lean_object* v_val_425_; 
lean_del_object(v___x_415_);
lean_dec_ref_known(v___x_411_, 2);
lean_dec(v_val_409_);
lean_dec(v___x_406_);
v_val_425_ = lean_ctor_get(v_val_413_, 0);
lean_inc(v_val_425_);
lean_dec_ref_known(v_val_413_, 1);
v_val_404_ = v_val_425_;
goto v___jp_403_;
}
}
}
}
else
{
lean_dec(v___x_408_);
lean_dec(v___x_406_);
lean_dec(v___x_385_);
v_a_367_ = v___x_397_;
goto _start;
}
v___jp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(v___y_361_, v___y_399_);
lean_dec_ref(v___y_399_);
v___x_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
v_a_367_ = v___x_397_;
v_b_368_ = v___x_401_;
goto _start;
}
v___jp_403_:
{
if (lean_obj_tag(v_b_368_) == 0)
{
v___y_399_ = v_val_404_;
goto v___jp_398_;
}
else
{
lean_dec_ref_known(v_b_368_, 1);
if (v___x_362_ == 0)
{
v___y_399_ = v_val_404_;
goto v___jp_398_;
}
else
{
lean_object* v___x_405_; 
lean_dec_ref(v_val_404_);
lean_dec_ref(v___x_397_);
lean_dec_ref(v_preferred_366_);
lean_dec(v___x_365_);
lean_dec_ref(v_range_364_);
lean_dec(v___x_363_);
v___x_405_ = lean_box(0);
return v___x_405_;
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
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_361_ = stack[0].m_obj;
uint8_t v___x_362_ = stack[1].m_num;
lean_object* v___x_363_ = stack[2].m_obj;
lean_object* v_range_364_ = stack[3].m_obj;
lean_object* v___x_365_ = stack[4].m_obj;
lean_object* v_preferred_366_ = stack[5].m_obj;
lean_object* v_a_367_ = stack[6].m_obj;
lean_object* v_b_368_ = stack[7].m_obj;
lean_object* v_res_436_;
v_res_436_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_361_, v___x_362_, v___x_363_, v_range_364_, v___x_365_, v_preferred_366_, v_a_367_, v_b_368_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(lean_object* v_preferred_443_, lean_object* v_range_444_, lean_object* v_stack_445_, lean_object* v_stx_446_, lean_object* v_prev_x3f_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
lean_inc(v_stx_446_);
v___x_448_ = l_Lean_Syntax_getKind(v_stx_446_);
v___x_449_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3));
v___x_450_ = lean_name_eq(v___x_448_, v___x_449_);
lean_dec(v___x_448_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v_childRes_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_451_ = l_Lean_Syntax_getNumArgs(v_stx_446_);
v___x_452_ = lean_unsigned_to_nat(0u);
v_childRes_453_ = lean_box(0);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v_childRes_453_);
lean_ctor_set(v___x_454_, 1, v_prev_x3f_447_);
v___x_455_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v___x_451_, v_stx_446_, v_range_444_, v_stack_445_, v_preferred_443_, v___x_450_, v___x_452_, v___x_454_);
lean_dec(v___x_451_);
if (lean_obj_tag(v___x_455_) == 0)
{
return v_childRes_453_;
}
else
{
lean_object* v_val_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_val_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_val_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_fst_460_; lean_object* v___x_462_; 
v_fst_460_ = lean_ctor_get(v_val_456_, 0);
lean_inc(v_fst_460_);
lean_dec(v_val_456_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v_fst_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_fst_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v___x_465_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; uint8_t v___y_490_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v_bracket_498_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_507_; 
lean_dec(v_prev_x3f_447_);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_495_ = l_Lean_Syntax_getArg(v_stx_446_, v___x_465_);
lean_inc(v___x_495_);
v___x_496_ = l_Lean_Syntax_getKind(v___x_495_);
v___x_497_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6));
v_bracket_498_ = lean_name_eq(v___x_496_, v___x_497_);
lean_dec(v___x_496_);
if (v_bracket_498_ == 0)
{
v___y_507_ = v___x_465_;
goto v___jp_506_;
}
else
{
lean_object* v___x_526_; 
v___x_526_ = lean_unsigned_to_nat(1u);
v___y_507_ = v___x_526_;
goto v___jp_506_;
}
v___jp_466_:
{
lean_object* v_childRes_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_childRes_470_ = lean_box(0);
v___x_471_ = l_Lean_Syntax_getNumArgs(v___y_468_);
v___x_472_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4));
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v___x_471_);
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_475_, 0, v___x_465_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
lean_ctor_set(v___x_475_, 2, v___x_473_);
v___x_476_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_469_, v___x_450_, v___y_468_, v_range_444_, v___y_467_, v_preferred_443_, v___x_475_, v_childRes_470_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_dec(v___y_469_);
return v___x_476_;
}
else
{
lean_object* v_val_477_; 
v_val_477_ = lean_ctor_get(v___x_476_, 0);
if (lean_obj_tag(v_val_477_) == 0)
{
lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; 
v_unused_485_ = lean_ctor_get(v___x_476_, 0);
lean_dec(v_unused_485_);
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___y_469_);
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___y_469_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_dec(v___y_469_);
return v___x_476_;
}
}
}
v___jp_486_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
lean_inc(v___y_489_);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v___y_489_);
lean_ctor_set(v___x_491_, 1, v___x_465_);
lean_inc(v___y_487_);
v___x_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___y_487_);
v___x_493_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_493_, 0, v___y_488_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*2, v___y_490_);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
v___y_467_ = v___y_487_;
v___y_468_ = v___y_489_;
v___y_469_ = v___x_494_;
goto v___jp_466_;
}
v___jp_499_:
{
if (v_bracket_498_ == 0)
{
lean_object* v___x_504_; uint8_t v___x_505_; 
lean_inc_ref(v_preferred_443_);
v___x_504_ = lean_apply_1(v_preferred_443_, v___y_501_);
v___x_505_ = lean_unbox(v___x_504_);
v___y_487_ = v___y_500_;
v___y_488_ = v___y_503_;
v___y_489_ = v___y_502_;
v___y_490_ = v___x_505_;
goto v___jp_486_;
}
else
{
lean_dec(v___y_501_);
v___y_487_ = v___y_500_;
v___y_488_ = v___y_503_;
v___y_489_ = v___y_502_;
v___y_490_ = v___x_450_;
goto v___jp_486_;
}
}
v___jp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; 
lean_inc(v___y_507_);
lean_inc(v___x_495_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_495_);
lean_ctor_set(v___x_508_, 1, v___y_507_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_stx_446_);
lean_ctor_set(v___x_509_, 1, v___x_465_);
v___x_510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v_stack_445_);
v___x_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_508_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = l_Lean_Syntax_getArg(v___x_495_, v___y_507_);
lean_dec(v___y_507_);
lean_dec(v___x_495_);
v___x_513_ = l_Lean_Syntax_getArg(v___x_512_, v___x_465_);
v___x_514_ = 0;
v___x_515_ = l_Lean_Syntax_getPos_x3f(v___x_513_, v___x_514_);
lean_dec(v___x_513_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_box(0);
v___y_467_ = v___x_511_;
v___y_468_ = v___x_512_;
v___y_469_ = v___x_516_;
goto v___jp_466_;
}
else
{
lean_object* v_val_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v_fst_521_; 
v_val_517_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v___x_515_, 1);
v___x_518_ = l_Lean_Syntax_getNumArgs(v___x_512_);
v___x_519_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0));
lean_inc_ref(v_range_444_);
v___x_520_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v___x_518_, v___x_512_, v_range_444_, v___x_465_, v___x_519_);
v_fst_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_fst_521_);
lean_dec_ref(v___x_520_);
if (lean_obj_tag(v_fst_521_) == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v___x_518_, v___x_522_);
lean_dec(v___x_518_);
v___x_524_ = lean_nat_shiftr(v___x_523_, v___x_522_);
lean_dec(v___x_523_);
v___y_500_ = v___x_511_;
v___y_501_ = v_val_517_;
v___y_502_ = v___x_512_;
v___y_503_ = v___x_524_;
goto v___jp_499_;
}
else
{
lean_object* v_val_525_; 
lean_dec(v___x_518_);
v_val_525_ = lean_ctor_get(v_fst_521_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v_fst_521_, 1);
v___y_500_ = v___x_511_;
v___y_501_ = v_val_517_;
v___y_502_ = v___x_512_;
v___y_503_ = v_val_525_;
goto v___jp_499_;
}
}
}
}
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(lean_object* v_upperBound_527_, lean_object* v_stx_528_, lean_object* v_range_529_, lean_object* v_stack_530_, lean_object* v_preferred_531_, uint8_t v___x_532_, lean_object* v_a_533_, lean_object* v_b_534_){
_start:
{
lean_object* v___y_536_; uint8_t v___x_551_; 
v___x_551_ = lean_nat_dec_lt(v_a_533_, v_upperBound_527_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
lean_dec(v_a_533_);
lean_dec_ref(v_preferred_531_);
lean_dec(v_stack_530_);
lean_dec_ref(v_range_529_);
lean_dec(v_stx_528_);
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v_b_534_);
return v___x_552_;
}
else
{
lean_object* v_fst_553_; lean_object* v_snd_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_575_; 
v_fst_553_ = lean_ctor_get(v_b_534_, 0);
v_snd_554_ = lean_ctor_get(v_b_534_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_b_534_);
if (v_isSharedCheck_575_ == 0)
{
v___x_556_ = v_b_534_;
v_isShared_557_ = v_isSharedCheck_575_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_snd_554_);
lean_inc(v_fst_553_);
lean_dec(v_b_534_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_575_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = l_Lean_Syntax_getArg(v_stx_528_, v_a_533_);
lean_inc(v_snd_554_);
v___x_559_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_529_, v___x_558_, v_snd_554_);
if (lean_obj_tag(v___x_559_) == 1)
{
lean_object* v___x_561_; 
lean_dec_ref_known(v___x_559_, 1);
lean_inc(v_a_533_);
lean_inc(v_stx_528_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v_a_533_);
lean_ctor_set(v___x_556_, 0, v_stx_528_);
v___x_561_ = v___x_556_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_stx_528_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_a_533_);
v___x_561_ = v_reuseFailAlloc_572_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_inc(v_stack_530_);
v___x_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v_stack_530_);
lean_inc(v_snd_554_);
lean_inc_ref(v_range_529_);
lean_inc_ref(v_preferred_531_);
v___x_563_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_531_, v_range_529_, v___x_562_, v___x_558_, v_snd_554_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v___x_564_; 
lean_dec(v_snd_554_);
lean_dec(v_fst_553_);
lean_dec(v_a_533_);
lean_dec_ref(v_preferred_531_);
lean_dec(v_stack_530_);
lean_dec_ref(v_range_529_);
lean_dec(v_stx_528_);
v___x_564_ = lean_box(0);
return v___x_564_;
}
else
{
lean_object* v_val_565_; 
v_val_565_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_val_565_);
lean_dec_ref_known(v___x_563_, 1);
if (lean_obj_tag(v_val_565_) == 1)
{
if (lean_obj_tag(v_fst_553_) == 0)
{
if (v___x_532_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_box(0);
v___x_567_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_528_, v_a_533_, v___x_551_, v_snd_554_, v___x_566_, v_val_565_);
v___y_536_ = v___x_567_;
goto v___jp_535_;
}
else
{
lean_object* v___x_568_; 
lean_dec_ref_known(v_val_565_, 1);
lean_dec(v_snd_554_);
lean_dec(v_a_533_);
lean_dec_ref(v_preferred_531_);
lean_dec(v_stack_530_);
lean_dec_ref(v_range_529_);
lean_dec(v_stx_528_);
v___x_568_ = lean_box(0);
return v___x_568_;
}
}
else
{
lean_object* v___x_569_; 
lean_dec_ref_known(v_fst_553_, 1);
lean_dec_ref_known(v_val_565_, 1);
lean_dec(v_snd_554_);
lean_dec(v_a_533_);
lean_dec_ref(v_preferred_531_);
lean_dec(v_stack_530_);
lean_dec_ref(v_range_529_);
lean_dec(v_stx_528_);
v___x_569_ = lean_box(0);
return v___x_569_;
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_val_565_);
v___x_570_ = lean_box(0);
v___x_571_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_528_, v_a_533_, v___x_551_, v_snd_554_, v___x_570_, v_fst_553_);
v___y_536_ = v___x_571_;
goto v___jp_535_;
}
}
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___x_559_);
lean_dec(v___x_558_);
lean_del_object(v___x_556_);
v___x_573_ = lean_box(0);
v___x_574_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_528_, v_a_533_, v___x_551_, v_snd_554_, v___x_573_, v_fst_553_);
v___y_536_ = v___x_574_;
goto v___jp_535_;
}
}
}
v___jp_535_:
{
if (lean_obj_tag(v___y_536_) == 0)
{
lean_object* v___x_537_; 
lean_dec(v_a_533_);
lean_dec_ref(v_preferred_531_);
lean_dec(v_stack_530_);
lean_dec_ref(v_range_529_);
lean_dec(v_stx_528_);
v___x_537_ = lean_box(0);
return v___x_537_;
}
else
{
lean_object* v_val_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_550_; 
v_val_538_ = lean_ctor_get(v___y_536_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___y_536_);
if (v_isSharedCheck_550_ == 0)
{
v___x_540_ = v___y_536_;
v_isShared_541_ = v_isSharedCheck_550_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_val_538_);
lean_dec(v___y_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_550_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
if (lean_obj_tag(v_val_538_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_544_; 
lean_dec(v_a_533_);
lean_dec_ref(v_preferred_531_);
lean_dec(v_stack_530_);
lean_dec_ref(v_range_529_);
lean_dec(v_stx_528_);
v_a_542_ = lean_ctor_get(v_val_538_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v_val_538_, 1);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v_a_542_);
v___x_544_ = v___x_540_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_del_object(v___x_540_);
v_a_546_ = lean_ctor_get(v_val_538_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v_val_538_, 1);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_add(v_a_533_, v___x_547_);
lean_dec(v_a_533_);
v_a_533_ = v___x_548_;
v_b_534_ = v_a_546_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_527_ = stack[0].m_obj;
lean_object* v_stx_528_ = stack[1].m_obj;
lean_object* v_range_529_ = stack[2].m_obj;
lean_object* v_stack_530_ = stack[3].m_obj;
lean_object* v_preferred_531_ = stack[4].m_obj;
uint8_t v___x_532_ = stack[5].m_num;
lean_object* v_a_533_ = stack[6].m_obj;
lean_object* v_b_534_ = stack[7].m_obj;
lean_object* v_res_576_;
v_res_576_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_527_, v_stx_528_, v_range_529_, v_stack_530_, v_preferred_531_, v___x_532_, v_a_533_, v_b_534_);
stack->m_obj
 = v_res_576_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_577_, lean_object* v_stx_578_, lean_object* v_range_579_, lean_object* v_stack_580_, lean_object* v_preferred_581_, lean_object* v___x_582_, lean_object* v_a_583_, lean_object* v_b_584_){
_start:
{
uint8_t v___x_3883__boxed_585_; lean_object* v_res_586_; 
v___x_3883__boxed_585_ = lean_unbox(v___x_582_);
v_res_586_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_577_, v_stx_578_, v_range_579_, v_stack_580_, v_preferred_581_, v___x_3883__boxed_585_, v_a_583_, v_b_584_);
lean_dec(v_upperBound_577_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg___boxed(lean_object* v___y_587_, lean_object* v___x_588_, lean_object* v___x_589_, lean_object* v_range_590_, lean_object* v___x_591_, lean_object* v_preferred_592_, lean_object* v_a_593_, lean_object* v_b_594_){
_start:
{
uint8_t v___x_3914__boxed_595_; lean_object* v_res_596_; 
v___x_3914__boxed_595_ = lean_unbox(v___x_588_);
v_res_596_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_587_, v___x_3914__boxed_595_, v___x_589_, v_range_590_, v___x_591_, v_preferred_592_, v_a_593_, v_b_594_);
lean_dec(v___y_587_);
return v_res_596_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(lean_object* v_upperBound_597_, lean_object* v_stx_598_, lean_object* v_range_599_, lean_object* v_stack_600_, lean_object* v_preferred_601_, uint8_t v___x_602_, lean_object* v_inst_603_, lean_object* v_R_604_, lean_object* v_a_605_, lean_object* v_b_606_, lean_object* v_c_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_597_, v_stx_598_, v_range_599_, v_stack_600_, v_preferred_601_, v___x_602_, v_a_605_, v_b_606_);
return v___x_608_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_597_ = stack[0].m_obj;
lean_object* v_stx_598_ = stack[1].m_obj;
lean_object* v_range_599_ = stack[2].m_obj;
lean_object* v_stack_600_ = stack[3].m_obj;
lean_object* v_preferred_601_ = stack[4].m_obj;
uint8_t v___x_602_ = stack[5].m_num;
lean_object* v_a_605_ = stack[8].m_obj;
lean_object* v_b_606_ = stack[9].m_obj;
lean_object* v_res_609_;
v_res_609_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(v_upperBound_597_, v_stx_598_, v_range_599_, v_stack_600_, v_preferred_601_, v___x_602_, lean_box(0), lean_box(0), v_a_605_, v_b_606_, lean_box(0));
stack->m_obj
 = v_res_609_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___boxed(lean_object* v_upperBound_610_, lean_object* v_stx_611_, lean_object* v_range_612_, lean_object* v_stack_613_, lean_object* v_preferred_614_, lean_object* v___x_615_, lean_object* v_inst_616_, lean_object* v_R_617_, lean_object* v_a_618_, lean_object* v_b_619_, lean_object* v_c_620_){
_start:
{
uint8_t v___x_4489__boxed_621_; lean_object* v_res_622_; 
v___x_4489__boxed_621_ = lean_unbox(v___x_615_);
v_res_622_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(v_upperBound_610_, v_stx_611_, v_range_612_, v_stack_613_, v_preferred_614_, v___x_4489__boxed_621_, v_inst_616_, v_R_617_, v_a_618_, v_b_619_, v_c_620_);
lean_dec(v_upperBound_610_);
return v_res_622_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(lean_object* v___y_623_, uint8_t v___x_624_, lean_object* v___x_625_, lean_object* v_range_626_, lean_object* v___x_627_, lean_object* v_preferred_628_, lean_object* v_inst_629_, lean_object* v_R_630_, lean_object* v_a_631_, lean_object* v_b_632_, lean_object* v_c_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_623_, v___x_624_, v___x_625_, v_range_626_, v___x_627_, v_preferred_628_, v_a_631_, v_b_632_);
return v___x_634_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_623_ = stack[0].m_obj;
uint8_t v___x_624_ = stack[1].m_num;
lean_object* v___x_625_ = stack[2].m_obj;
lean_object* v_range_626_ = stack[3].m_obj;
lean_object* v___x_627_ = stack[4].m_obj;
lean_object* v_preferred_628_ = stack[5].m_obj;
lean_object* v_a_631_ = stack[8].m_obj;
lean_object* v_b_632_ = stack[9].m_obj;
lean_object* v_res_635_;
v_res_635_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(v___y_623_, v___x_624_, v___x_625_, v_range_626_, v___x_627_, v_preferred_628_, lean_box(0), lean_box(0), v_a_631_, v_b_632_, lean_box(0));
stack->m_obj
 = v_res_635_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___boxed(lean_object* v___y_636_, lean_object* v___x_637_, lean_object* v___x_638_, lean_object* v_range_639_, lean_object* v___x_640_, lean_object* v_preferred_641_, lean_object* v_inst_642_, lean_object* v_R_643_, lean_object* v_a_644_, lean_object* v_b_645_, lean_object* v_c_646_){
_start:
{
uint8_t v___x_4507__boxed_647_; lean_object* v_res_648_; 
v___x_4507__boxed_647_ = lean_unbox(v___x_637_);
v_res_648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(v___y_636_, v___x_4507__boxed_647_, v___x_638_, v_range_639_, v___x_640_, v_preferred_641_, v_inst_642_, v_R_643_, v_a_644_, v_b_645_, v_c_646_);
lean_dec(v___y_636_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(lean_object* v_upperBound_649_, lean_object* v___x_650_, lean_object* v_range_651_, lean_object* v_inst_652_, lean_object* v_R_653_, lean_object* v_a_654_, lean_object* v_b_655_, lean_object* v_c_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_649_, v___x_650_, v_range_651_, v_a_654_, v_b_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___boxed(lean_object* v_upperBound_658_, lean_object* v___x_659_, lean_object* v_range_660_, lean_object* v_inst_661_, lean_object* v_R_662_, lean_object* v_a_663_, lean_object* v_b_664_, lean_object* v_c_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(v_upperBound_658_, v___x_659_, v_range_660_, v_inst_661_, v_R_662_, v_a_663_, v_b_664_, v_c_665_);
lean_dec_ref(v_b_664_);
lean_dec(v___x_659_);
lean_dec(v_upperBound_658_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findTactic_x3f(lean_object* v_preferred_667_, lean_object* v_range_668_, lean_object* v_root_669_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_box(0);
v___x_671_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_668_, v_root_669_, v___x_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_dec(v_root_669_);
lean_dec_ref(v_range_668_);
lean_dec_ref(v_preferred_667_);
return v___x_670_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec_ref_known(v___x_671_, 1);
v___x_672_ = lean_box(0);
v___x_673_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_667_, v_range_668_, v___x_672_, v_root_669_, v___x_670_);
if (lean_obj_tag(v___x_673_) == 0)
{
return v___x_670_;
}
else
{
lean_object* v_val_674_; 
v_val_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v___x_673_, 1);
return v_val_674_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(lean_object* v_ctx_x3f_687_, lean_object* v_i_688_, lean_object* v_kind_689_, lean_object* v_tgtRange_690_, lean_object* v_f_691_, uint8_t v_canonicalOnly_692_, lean_object* v_as_693_, size_t v_sz_694_, size_t v_i_695_, lean_object* v_b_696_){
_start:
{
uint8_t v___x_697_; 
v___x_697_ = lean_usize_dec_lt(v_i_695_, v_sz_694_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
lean_dec_ref(v_f_691_);
lean_dec(v_ctx_x3f_687_);
v___x_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_698_, 0, v_b_696_);
return v___x_698_;
}
else
{
lean_object* v_snd_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_724_; 
v_snd_699_ = lean_ctor_get(v_b_696_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_b_696_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v_b_696_, 0);
lean_dec(v_unused_725_);
v___x_701_ = v_b_696_;
v_isShared_702_ = v_isSharedCheck_724_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_snd_699_);
lean_dec(v_b_696_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_724_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v_a_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_703_ = lean_box(0);
v_a_704_ = lean_array_uget_borrowed(v_as_693_, v_i_695_);
lean_inc(v_ctx_x3f_687_);
v___x_705_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_687_, v_i_688_);
lean_inc_ref(v_f_691_);
lean_inc(v_a_704_);
v___x_706_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_689_, v_tgtRange_690_, v___x_705_, v_a_704_, v_f_691_, v_canonicalOnly_692_);
if (lean_obj_tag(v___x_706_) == 1)
{
lean_object* v___x_708_; 
lean_dec_ref(v_f_691_);
lean_dec(v_ctx_x3f_687_);
lean_inc_ref(v___x_706_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_703_);
lean_ctor_set(v___x_701_, 0, v___x_706_);
v___x_708_ = v___x_701_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_703_);
v___x_708_ = v_reuseFailAlloc_719_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_717_; 
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; 
v_unused_718_ = lean_ctor_get(v___x_706_, 0);
lean_dec(v_unused_718_);
v___x_710_ = v___x_706_;
v_isShared_711_ = v_isSharedCheck_717_;
goto v_resetjp_709_;
}
else
{
lean_dec(v___x_706_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_717_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_708_);
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_708_);
v___x_713_ = v_reuseFailAlloc_716_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v_snd_699_);
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
}
}
else
{
lean_object* v___x_720_; size_t v___x_721_; size_t v___x_722_; 
lean_dec(v___x_706_);
lean_del_object(v___x_701_);
lean_dec(v_snd_699_);
v___x_720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1));
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_695_, v___x_721_);
v_i_695_ = v___x_722_;
v_b_696_ = v___x_720_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_x3f_687_ = stack[0].m_obj;
lean_object* v_i_688_ = stack[1].m_obj;
lean_object* v_kind_689_ = stack[2].m_obj;
lean_object* v_tgtRange_690_ = stack[3].m_obj;
lean_object* v_f_691_ = stack[4].m_obj;
uint8_t v_canonicalOnly_692_ = stack[5].m_num;
lean_object* v_as_693_ = stack[6].m_obj;
size_t v_sz_694_ = stack[7].m_num;
size_t v_i_695_ = stack[8].m_num;
lean_object* v_b_696_ = stack[9].m_obj;
lean_object* v_res_726_;
v_res_726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_687_, v_i_688_, v_kind_689_, v_tgtRange_690_, v_f_691_, v_canonicalOnly_692_, v_as_693_, v_sz_694_, v_i_695_, v_b_696_);
stack->m_obj
 = v_res_726_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(lean_object* v_ctx_x3f_727_, lean_object* v_i_728_, lean_object* v_kind_729_, lean_object* v_tgtRange_730_, lean_object* v_f_731_, uint8_t v_canonicalOnly_732_, lean_object* v_as_733_, size_t v_sz_734_, size_t v_i_735_, lean_object* v_b_736_){
_start:
{
uint8_t v___x_737_; 
v___x_737_ = lean_usize_dec_lt(v_i_735_, v_sz_734_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec_ref(v_f_731_);
lean_dec(v_ctx_x3f_727_);
v___x_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_738_, 0, v_b_736_);
return v___x_738_;
}
else
{
lean_object* v_snd_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_764_; 
v_snd_739_ = lean_ctor_get(v_b_736_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_b_736_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v_b_736_, 0);
lean_dec(v_unused_765_);
v___x_741_ = v_b_736_;
v_isShared_742_ = v_isSharedCheck_764_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_snd_739_);
lean_dec(v_b_736_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_764_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v_a_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_743_ = lean_box(0);
v_a_744_ = lean_array_uget_borrowed(v_as_733_, v_i_735_);
lean_inc(v_ctx_x3f_727_);
v___x_745_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_727_, v_i_728_);
lean_inc_ref(v_f_731_);
lean_inc(v_a_744_);
v___x_746_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_729_, v_tgtRange_730_, v___x_745_, v_a_744_, v_f_731_, v_canonicalOnly_732_);
if (lean_obj_tag(v___x_746_) == 1)
{
lean_object* v___x_748_; 
lean_dec_ref(v_f_731_);
lean_dec(v_ctx_x3f_727_);
lean_inc_ref(v___x_746_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_743_);
lean_ctor_set(v___x_741_, 0, v___x_746_);
v___x_748_ = v___x_741_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___x_743_);
v___x_748_ = v_reuseFailAlloc_759_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_757_; 
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v___x_746_, 0);
lean_dec(v_unused_758_);
v___x_750_ = v___x_746_;
v_isShared_751_ = v_isSharedCheck_757_;
goto v_resetjp_749_;
}
else
{
lean_dec(v___x_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_757_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_748_);
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_748_);
v___x_753_ = v_reuseFailAlloc_756_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v_snd_739_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
}
}
else
{
lean_object* v___x_760_; size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
lean_dec(v___x_746_);
lean_del_object(v___x_741_);
lean_dec(v_snd_739_);
v___x_760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1));
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_735_, v___x_761_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_727_, v_i_728_, v_kind_729_, v_tgtRange_730_, v_f_731_, v_canonicalOnly_732_, v_as_733_, v_sz_734_, v___x_762_, v___x_760_);
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_x3f_727_ = stack[0].m_obj;
lean_object* v_i_728_ = stack[1].m_obj;
lean_object* v_kind_729_ = stack[2].m_obj;
lean_object* v_tgtRange_730_ = stack[3].m_obj;
lean_object* v_f_731_ = stack[4].m_obj;
uint8_t v_canonicalOnly_732_ = stack[5].m_num;
lean_object* v_as_733_ = stack[6].m_obj;
size_t v_sz_734_ = stack[7].m_num;
size_t v_i_735_ = stack[8].m_num;
lean_object* v_b_736_ = stack[9].m_obj;
lean_object* v_res_766_;
v_res_766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_727_, v_i_728_, v_kind_729_, v_tgtRange_730_, v_f_731_, v_canonicalOnly_732_, v_as_733_, v_sz_734_, v_i_735_, v_b_736_);
stack->m_obj
 = v_res_766_;
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(lean_object* v_ctx_x3f_767_, lean_object* v_i_768_, lean_object* v_kind_769_, lean_object* v_tgtRange_770_, lean_object* v_f_771_, uint8_t v_canonicalOnly_772_, lean_object* v_t_773_, lean_object* v_init_774_){
_start:
{
lean_object* v_root_775_; lean_object* v_tail_776_; lean_object* v___x_777_; 
v_root_775_ = lean_ctor_get(v_t_773_, 0);
v_tail_776_ = lean_ctor_get(v_t_773_, 1);
lean_inc_ref(v_f_771_);
lean_inc(v_ctx_x3f_767_);
lean_inc_ref(v_init_774_);
v___x_777_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_774_, v_ctx_x3f_767_, v_i_768_, v_kind_769_, v_tgtRange_770_, v_f_771_, v_canonicalOnly_772_, v_root_775_, v_init_774_);
lean_dec_ref(v_init_774_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v___x_778_; 
lean_dec_ref(v_f_771_);
lean_dec(v_ctx_x3f_767_);
v___x_778_ = lean_box(0);
return v___x_778_;
}
else
{
lean_object* v_val_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_803_; 
v_val_779_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_803_ == 0)
{
v___x_781_ = v___x_777_;
v_isShared_782_ = v_isSharedCheck_803_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_val_779_);
lean_dec(v___x_777_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_803_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
if (lean_obj_tag(v_val_779_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; 
lean_dec_ref(v_f_771_);
lean_dec(v_ctx_x3f_767_);
v_a_783_ = lean_ctor_get(v_val_779_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v_val_779_, 1);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v_a_783_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v___x_789_; size_t v_sz_790_; size_t v___x_791_; lean_object* v___x_792_; 
lean_del_object(v___x_781_);
v_a_787_ = lean_ctor_get(v_val_779_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v_val_779_, 1);
v___x_788_ = lean_box(0);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v_a_787_);
v_sz_790_ = lean_array_size(v_tail_776_);
v___x_791_ = ((size_t)0ULL);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_767_, v_i_768_, v_kind_769_, v_tgtRange_770_, v_f_771_, v_canonicalOnly_772_, v_tail_776_, v_sz_790_, v___x_791_, v___x_789_);
if (lean_obj_tag(v___x_792_) == 0)
{
return v___x_788_;
}
else
{
lean_object* v_val_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_802_; 
v_val_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_802_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_802_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_val_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_802_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_fst_797_; 
v_fst_797_ = lean_ctor_get(v_val_793_, 0);
if (lean_obj_tag(v_fst_797_) == 0)
{
lean_object* v_snd_798_; lean_object* v___x_800_; 
v_snd_798_ = lean_ctor_get(v_val_793_, 1);
lean_inc(v_snd_798_);
lean_dec(v_val_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v_snd_798_);
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_snd_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
else
{
lean_inc_ref(v_fst_797_);
lean_del_object(v___x_795_);
lean_dec(v_val_793_);
return v_fst_797_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_x3f_767_ = stack[0].m_obj;
lean_object* v_i_768_ = stack[1].m_obj;
lean_object* v_kind_769_ = stack[2].m_obj;
lean_object* v_tgtRange_770_ = stack[3].m_obj;
lean_object* v_f_771_ = stack[4].m_obj;
uint8_t v_canonicalOnly_772_ = stack[5].m_num;
lean_object* v_t_773_ = stack[6].m_obj;
lean_object* v_init_774_ = stack[7].m_obj;
lean_object* v_res_804_;
v_res_804_ = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(v_ctx_x3f_767_, v_i_768_, v_kind_769_, v_tgtRange_770_, v_f_771_, v_canonicalOnly_772_, v_t_773_, v_init_774_);
stack->m_obj
 = v_res_804_;
}
lean_object* l_Lean_CodeAction_findInfoTree_x3f(lean_object* v_kind_805_, lean_object* v_tgtRange_806_, lean_object* v_ctx_x3f_807_, lean_object* v_t_808_, lean_object* v_f_809_, uint8_t v_canonicalOnly_810_){
_start:
{
switch(lean_obj_tag(v_t_808_))
{
case 0:
{
lean_object* v_i_811_; lean_object* v_t_812_; lean_object* v___x_813_; 
v_i_811_ = lean_ctor_get(v_t_808_, 0);
lean_inc_ref(v_i_811_);
v_t_812_ = lean_ctor_get(v_t_808_, 1);
lean_inc_ref(v_t_812_);
lean_dec_ref_known(v_t_808_, 2);
v___x_813_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_811_, v_ctx_x3f_807_);
v_ctx_x3f_807_ = v___x_813_;
v_t_808_ = v_t_812_;
goto _start;
}
case 1:
{
lean_object* v_i_815_; lean_object* v_children_816_; 
v_i_815_ = lean_ctor_get(v_t_808_, 0);
v_children_816_ = lean_ctor_get(v_t_808_, 1);
if (lean_obj_tag(v_ctx_x3f_807_) == 1)
{
lean_object* v_val_823_; uint8_t v___y_825_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_val_823_ = lean_ctor_get(v_ctx_x3f_807_, 0);
v___x_837_ = l_Lean_Elab_Info_stx(v_i_815_);
v___x_838_ = l_Lean_Syntax_getRange_x3f(v___x_837_, v_canonicalOnly_810_);
if (lean_obj_tag(v___x_838_) == 1)
{
lean_object* v_val_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_val_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_val_839_);
lean_dec_ref_known(v___x_838_, 1);
v___x_840_ = l_Lean_Syntax_getKind(v___x_837_);
v___x_841_ = lean_name_eq(v___x_840_, v_kind_805_);
lean_dec(v___x_840_);
if (v___x_841_ == 0)
{
lean_dec(v_val_839_);
v___y_825_ = v___x_841_;
goto v___jp_824_;
}
else
{
uint8_t v___x_842_; 
v___x_842_ = l_Lean_Syntax_instBEqRange_beq(v_val_839_, v_tgtRange_806_);
lean_dec(v_val_839_);
v___y_825_ = v___x_842_;
goto v___jp_824_;
}
}
else
{
lean_inc_ref(v_children_816_);
lean_inc_ref(v_i_815_);
lean_dec(v___x_838_);
lean_dec(v___x_837_);
lean_dec_ref_known(v_t_808_, 2);
goto v___jp_817_;
}
v___jp_824_:
{
if (v___y_825_ == 0)
{
lean_inc_ref(v_children_816_);
lean_inc_ref(v_i_815_);
lean_dec_ref_known(v_t_808_, 2);
goto v___jp_817_;
}
else
{
lean_object* v___x_826_; uint8_t v___x_827_; 
lean_inc_ref(v_f_809_);
lean_inc_ref(v_i_815_);
lean_inc(v_val_823_);
v___x_826_ = lean_apply_2(v_f_809_, v_val_823_, v_i_815_);
v___x_827_ = lean_unbox(v___x_826_);
if (v___x_827_ == 0)
{
lean_inc_ref(v_children_816_);
lean_inc_ref(v_i_815_);
lean_dec_ref_known(v_t_808_, 2);
goto v___jp_817_;
}
else
{
lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_835_; 
lean_inc(v_val_823_);
lean_dec_ref(v_f_809_);
v_isSharedCheck_835_ = !lean_is_exclusive(v_ctx_x3f_807_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v_ctx_x3f_807_, 0);
lean_dec(v_unused_836_);
v___x_829_ = v_ctx_x3f_807_;
v_isShared_830_ = v_isSharedCheck_835_;
goto v_resetjp_828_;
}
else
{
lean_dec(v_ctx_x3f_807_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_835_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_val_823_);
lean_ctor_set(v___x_831_, 1, v_t_808_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_831_);
v___x_833_ = v___x_829_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
}
else
{
lean_inc_ref(v_children_816_);
lean_inc_ref(v_i_815_);
lean_dec_ref_known(v_t_808_, 2);
goto v___jp_817_;
}
v___jp_817_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = lean_box(0);
v___x_819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0));
v___x_820_ = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(v_ctx_x3f_807_, v_i_815_, v_kind_805_, v_tgtRange_806_, v_f_809_, v_canonicalOnly_810_, v_children_816_, v___x_819_);
lean_dec_ref(v_children_816_);
lean_dec_ref(v_i_815_);
if (lean_obj_tag(v___x_820_) == 0)
{
return v___x_818_;
}
else
{
lean_object* v_val_821_; lean_object* v_fst_822_; 
v_val_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v___x_820_, 1);
v_fst_822_ = lean_ctor_get(v_val_821_, 0);
lean_inc(v_fst_822_);
lean_dec(v_val_821_);
if (lean_obj_tag(v_fst_822_) == 0)
{
return v___x_818_;
}
else
{
return v_fst_822_;
}
}
}
}
default: 
{
lean_object* v___x_843_; 
lean_dec_ref(v_f_809_);
lean_dec_ref(v_t_808_);
lean_dec(v_ctx_x3f_807_);
v___x_843_ = lean_box(0);
return v___x_843_;
}
}
}
}
LEAN_EXPORT void l_Lean_CodeAction_findInfoTree_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_805_ = stack[0].m_obj;
lean_object* v_tgtRange_806_ = stack[1].m_obj;
lean_object* v_ctx_x3f_807_ = stack[2].m_obj;
lean_object* v_t_808_ = stack[3].m_obj;
lean_object* v_f_809_ = stack[4].m_obj;
uint8_t v_canonicalOnly_810_ = stack[5].m_num;
lean_object* v_res_844_;
v_res_844_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_805_, v_tgtRange_806_, v_ctx_x3f_807_, v_t_808_, v_f_809_, v_canonicalOnly_810_);
stack->m_obj
 = v_res_844_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_ctx_x3f_854_, lean_object* v_i_855_, lean_object* v_kind_856_, lean_object* v_tgtRange_857_, lean_object* v_f_858_, uint8_t v_canonicalOnly_859_, lean_object* v_as_860_, size_t v_sz_861_, size_t v_i_862_, lean_object* v_b_863_){
_start:
{
uint8_t v___x_864_; 
v___x_864_ = lean_usize_dec_lt(v_i_862_, v_sz_861_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
lean_dec_ref(v_f_858_);
lean_dec(v_ctx_x3f_854_);
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v_b_863_);
return v___x_865_;
}
else
{
lean_object* v_snd_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_892_; 
v_snd_866_ = lean_ctor_get(v_b_863_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v_b_863_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_b_863_, 0);
lean_dec(v_unused_893_);
v___x_868_ = v_b_863_;
v_isShared_869_ = v_isSharedCheck_892_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_snd_866_);
lean_dec(v_b_863_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_892_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v_a_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_870_ = lean_box(0);
v_a_871_ = lean_array_uget_borrowed(v_as_860_, v_i_862_);
lean_inc(v_ctx_x3f_854_);
v___x_872_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_854_, v_i_855_);
lean_inc_ref(v_f_858_);
lean_inc(v_a_871_);
v___x_873_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_856_, v_tgtRange_857_, v___x_872_, v_a_871_, v_f_858_, v_canonicalOnly_859_);
if (lean_obj_tag(v___x_873_) == 1)
{
lean_object* v___x_875_; 
lean_dec_ref(v_f_858_);
lean_dec(v_ctx_x3f_854_);
lean_inc_ref(v___x_873_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___x_870_);
lean_ctor_set(v___x_868_, 0, v___x_873_);
v___x_875_ = v___x_868_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_870_);
v___x_875_ = v_reuseFailAlloc_887_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_885_; 
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v___x_873_, 0);
lean_dec(v_unused_886_);
v___x_877_ = v___x_873_;
v_isShared_878_ = v_isSharedCheck_885_;
goto v_resetjp_876_;
}
else
{
lean_dec(v___x_873_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_885_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set_tag(v___x_877_, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_875_);
v___x_880_ = v_reuseFailAlloc_884_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_snd_866_);
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
}
}
else
{
lean_object* v___x_888_; size_t v___x_889_; size_t v___x_890_; 
lean_dec(v___x_873_);
lean_del_object(v___x_868_);
lean_dec(v_snd_866_);
v___x_888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_889_ = ((size_t)1ULL);
v___x_890_ = lean_usize_add(v_i_862_, v___x_889_);
v_i_862_ = v___x_890_;
v_b_863_ = v___x_888_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_x3f_854_ = stack[0].m_obj;
lean_object* v_i_855_ = stack[1].m_obj;
lean_object* v_kind_856_ = stack[2].m_obj;
lean_object* v_tgtRange_857_ = stack[3].m_obj;
lean_object* v_f_858_ = stack[4].m_obj;
uint8_t v_canonicalOnly_859_ = stack[5].m_num;
lean_object* v_as_860_ = stack[6].m_obj;
size_t v_sz_861_ = stack[7].m_num;
size_t v_i_862_ = stack[8].m_num;
lean_object* v_b_863_ = stack[9].m_obj;
lean_object* v_res_894_;
v_res_894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_854_, v_i_855_, v_kind_856_, v_tgtRange_857_, v_f_858_, v_canonicalOnly_859_, v_as_860_, v_sz_861_, v_i_862_, v_b_863_);
stack->m_obj
 = v_res_894_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(lean_object* v_ctx_x3f_895_, lean_object* v_i_896_, lean_object* v_kind_897_, lean_object* v_tgtRange_898_, lean_object* v_f_899_, uint8_t v_canonicalOnly_900_, lean_object* v_as_901_, size_t v_sz_902_, size_t v_i_903_, lean_object* v_b_904_){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = lean_usize_dec_lt(v_i_903_, v_sz_902_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec_ref(v_f_899_);
lean_dec(v_ctx_x3f_895_);
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v_b_904_);
return v___x_906_;
}
else
{
lean_object* v_snd_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_933_; 
v_snd_907_ = lean_ctor_get(v_b_904_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_b_904_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; 
v_unused_934_ = lean_ctor_get(v_b_904_, 0);
lean_dec(v_unused_934_);
v___x_909_ = v_b_904_;
v_isShared_910_ = v_isSharedCheck_933_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_snd_907_);
lean_dec(v_b_904_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_933_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_911_ = lean_box(0);
v_a_912_ = lean_array_uget_borrowed(v_as_901_, v_i_903_);
lean_inc(v_ctx_x3f_895_);
v___x_913_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_895_, v_i_896_);
lean_inc_ref(v_f_899_);
lean_inc(v_a_912_);
v___x_914_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_897_, v_tgtRange_898_, v___x_913_, v_a_912_, v_f_899_, v_canonicalOnly_900_);
if (lean_obj_tag(v___x_914_) == 1)
{
lean_object* v___x_916_; 
lean_dec_ref(v_f_899_);
lean_dec(v_ctx_x3f_895_);
lean_inc_ref(v___x_914_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v___x_911_);
lean_ctor_set(v___x_909_, 0, v___x_914_);
v___x_916_ = v___x_909_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v___x_911_);
v___x_916_ = v_reuseFailAlloc_928_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_926_; 
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v___x_914_, 0);
lean_dec(v_unused_927_);
v___x_918_ = v___x_914_;
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
else
{
lean_dec(v___x_914_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_916_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v_snd_907_);
v___x_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
}
}
}
else
{
lean_object* v___x_929_; size_t v___x_930_; size_t v___x_931_; lean_object* v___x_932_; 
lean_dec(v___x_914_);
lean_del_object(v___x_909_);
lean_dec(v_snd_907_);
v___x_929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0));
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_add(v_i_903_, v___x_930_);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_895_, v_i_896_, v_kind_897_, v_tgtRange_898_, v_f_899_, v_canonicalOnly_900_, v_as_901_, v_sz_902_, v___x_931_, v___x_929_);
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_x3f_895_ = stack[0].m_obj;
lean_object* v_i_896_ = stack[1].m_obj;
lean_object* v_kind_897_ = stack[2].m_obj;
lean_object* v_tgtRange_898_ = stack[3].m_obj;
lean_object* v_f_899_ = stack[4].m_obj;
uint8_t v_canonicalOnly_900_ = stack[5].m_num;
lean_object* v_as_901_ = stack[6].m_obj;
size_t v_sz_902_ = stack[7].m_num;
size_t v_i_903_ = stack[8].m_num;
lean_object* v_b_904_ = stack[9].m_obj;
lean_object* v_res_935_;
v_res_935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_895_, v_i_896_, v_kind_897_, v_tgtRange_898_, v_f_899_, v_canonicalOnly_900_, v_as_901_, v_sz_902_, v_i_903_, v_b_904_);
stack->m_obj
 = v_res_935_;
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(lean_object* v_init_936_, lean_object* v_ctx_x3f_937_, lean_object* v_i_938_, lean_object* v_kind_939_, lean_object* v_tgtRange_940_, lean_object* v_f_941_, uint8_t v_canonicalOnly_942_, lean_object* v_n_943_, lean_object* v_b_944_){
_start:
{
if (lean_obj_tag(v_n_943_) == 0)
{
lean_object* v_cs_945_; lean_object* v___x_946_; lean_object* v___x_947_; size_t v_sz_948_; size_t v___x_949_; lean_object* v___x_950_; 
v_cs_945_ = lean_ctor_get(v_n_943_, 0);
v___x_946_ = lean_box(0);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_b_944_);
v_sz_948_ = lean_array_size(v_cs_945_);
v___x_949_ = ((size_t)0ULL);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_936_, v_ctx_x3f_937_, v_i_938_, v_kind_939_, v_tgtRange_940_, v_f_941_, v_canonicalOnly_942_, v_cs_945_, v_sz_948_, v___x_949_, v___x_947_);
if (lean_obj_tag(v___x_950_) == 0)
{
return v___x_946_;
}
else
{
lean_object* v_val_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_961_; 
v_val_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_961_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_961_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_val_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_961_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_fst_955_; 
v_fst_955_ = lean_ctor_get(v_val_951_, 0);
if (lean_obj_tag(v_fst_955_) == 0)
{
lean_object* v_snd_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v_snd_956_ = lean_ctor_get(v_val_951_, 1);
lean_inc(v_snd_956_);
lean_dec(v_val_951_);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v_snd_956_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_957_);
v___x_959_ = v___x_953_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
else
{
lean_inc_ref(v_fst_955_);
lean_del_object(v___x_953_);
lean_dec(v_val_951_);
return v_fst_955_;
}
}
}
}
else
{
lean_object* v_vs_962_; lean_object* v___x_963_; lean_object* v___x_964_; size_t v_sz_965_; size_t v___x_966_; lean_object* v___x_967_; 
v_vs_962_ = lean_ctor_get(v_n_943_, 0);
v___x_963_ = lean_box(0);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v_b_944_);
v_sz_965_ = lean_array_size(v_vs_962_);
v___x_966_ = ((size_t)0ULL);
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_937_, v_i_938_, v_kind_939_, v_tgtRange_940_, v_f_941_, v_canonicalOnly_942_, v_vs_962_, v_sz_965_, v___x_966_, v___x_964_);
if (lean_obj_tag(v___x_967_) == 0)
{
return v___x_963_;
}
else
{
lean_object* v_val_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_978_; 
v_val_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_978_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_978_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_val_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_978_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_fst_972_; 
v_fst_972_ = lean_ctor_get(v_val_968_, 0);
if (lean_obj_tag(v_fst_972_) == 0)
{
lean_object* v_snd_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v_snd_973_ = lean_ctor_get(v_val_968_, 1);
lean_inc(v_snd_973_);
lean_dec(v_val_968_);
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v_snd_973_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_974_);
v___x_976_ = v___x_970_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
else
{
lean_inc_ref(v_fst_972_);
lean_del_object(v___x_970_);
lean_dec(v_val_968_);
return v_fst_972_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_936_ = stack[0].m_obj;
lean_object* v_ctx_x3f_937_ = stack[1].m_obj;
lean_object* v_i_938_ = stack[2].m_obj;
lean_object* v_kind_939_ = stack[3].m_obj;
lean_object* v_tgtRange_940_ = stack[4].m_obj;
lean_object* v_f_941_ = stack[5].m_obj;
uint8_t v_canonicalOnly_942_ = stack[6].m_num;
lean_object* v_n_943_ = stack[7].m_obj;
lean_object* v_b_944_ = stack[8].m_obj;
lean_object* v_res_979_;
v_res_979_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_936_, v_ctx_x3f_937_, v_i_938_, v_kind_939_, v_tgtRange_940_, v_f_941_, v_canonicalOnly_942_, v_n_943_, v_b_944_);
stack->m_obj
 = v_res_979_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(lean_object* v_init_980_, lean_object* v_ctx_x3f_981_, lean_object* v_i_982_, lean_object* v_kind_983_, lean_object* v_tgtRange_984_, lean_object* v_f_985_, uint8_t v_canonicalOnly_986_, lean_object* v_as_987_, size_t v_sz_988_, size_t v_i_989_, lean_object* v_b_990_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = lean_usize_dec_lt(v_i_989_, v_sz_988_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_dec_ref(v_f_985_);
lean_dec(v_ctx_x3f_981_);
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v_b_990_);
return v___x_992_;
}
else
{
lean_object* v_snd_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1020_; 
v_snd_993_ = lean_ctor_get(v_b_990_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_b_990_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v_b_990_, 0);
lean_dec(v_unused_1021_);
v___x_995_ = v_b_990_;
v_isShared_996_ = v_isSharedCheck_1020_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_snd_993_);
lean_dec(v_b_990_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1020_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v_a_997_; lean_object* v___x_998_; 
v_a_997_ = lean_array_uget_borrowed(v_as_987_, v_i_989_);
lean_inc(v_snd_993_);
lean_inc_ref(v_f_985_);
lean_inc(v_ctx_x3f_981_);
v___x_998_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_980_, v_ctx_x3f_981_, v_i_982_, v_kind_983_, v_tgtRange_984_, v_f_985_, v_canonicalOnly_986_, v_a_997_, v_snd_993_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v___x_999_; 
lean_del_object(v___x_995_);
lean_dec(v_snd_993_);
lean_dec_ref(v_f_985_);
lean_dec(v_ctx_x3f_981_);
v___x_999_ = lean_box(0);
return v___x_999_;
}
else
{
lean_object* v_val_1000_; 
v_val_1000_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_val_1000_);
if (lean_obj_tag(v_val_1000_) == 0)
{
lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_f_985_);
lean_dec(v_ctx_x3f_981_);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_val_1000_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_val_1000_, 0);
lean_dec(v_unused_1011_);
v___x_1002_ = v_val_1000_;
v_isShared_1003_ = v_isSharedCheck_1010_;
goto v_resetjp_1001_;
}
else
{
lean_dec(v_val_1000_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1010_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_998_);
v___x_1005_ = v___x_995_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_snd_993_);
v___x_1005_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 1);
lean_ctor_set(v___x_1002_, 0, v___x_1005_);
v___x_1007_ = v___x_1002_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
lean_dec_ref_known(v___x_998_, 1);
lean_dec(v_snd_993_);
v_a_1012_ = lean_ctor_get(v_val_1000_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v_val_1000_, 1);
v___x_1013_ = lean_box(0);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v_a_1012_);
lean_ctor_set(v___x_995_, 0, v___x_1013_);
v___x_1015_ = v___x_995_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_a_1012_);
v___x_1015_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
size_t v___x_1016_; size_t v___x_1017_; 
v___x_1016_ = ((size_t)1ULL);
v___x_1017_ = lean_usize_add(v_i_989_, v___x_1016_);
v_i_989_ = v___x_1017_;
v_b_990_ = v___x_1015_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_980_ = stack[0].m_obj;
lean_object* v_ctx_x3f_981_ = stack[1].m_obj;
lean_object* v_i_982_ = stack[2].m_obj;
lean_object* v_kind_983_ = stack[3].m_obj;
lean_object* v_tgtRange_984_ = stack[4].m_obj;
lean_object* v_f_985_ = stack[5].m_obj;
uint8_t v_canonicalOnly_986_ = stack[6].m_num;
lean_object* v_as_987_ = stack[7].m_obj;
size_t v_sz_988_ = stack[8].m_num;
size_t v_i_989_ = stack[9].m_num;
lean_object* v_b_990_ = stack[10].m_obj;
lean_object* v_res_1022_;
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_980_, v_ctx_x3f_981_, v_i_982_, v_kind_983_, v_tgtRange_984_, v_f_985_, v_canonicalOnly_986_, v_as_987_, v_sz_988_, v_i_989_, v_b_990_);
stack->m_obj
 = v_res_1022_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1023_, lean_object* v_ctx_x3f_1024_, lean_object* v_i_1025_, lean_object* v_kind_1026_, lean_object* v_tgtRange_1027_, lean_object* v_f_1028_, lean_object* v_canonicalOnly_1029_, lean_object* v_as_1030_, lean_object* v_sz_1031_, lean_object* v_i_1032_, lean_object* v_b_1033_){
_start:
{
uint8_t v_canonicalOnly_boxed_1034_; size_t v_sz_boxed_1035_; size_t v_i_boxed_1036_; lean_object* v_res_1037_; 
v_canonicalOnly_boxed_1034_ = lean_unbox(v_canonicalOnly_1029_);
v_sz_boxed_1035_ = lean_unbox_usize(v_sz_1031_);
lean_dec(v_sz_1031_);
v_i_boxed_1036_ = lean_unbox_usize(v_i_1032_);
lean_dec(v_i_1032_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_1023_, v_ctx_x3f_1024_, v_i_1025_, v_kind_1026_, v_tgtRange_1027_, v_f_1028_, v_canonicalOnly_boxed_1034_, v_as_1030_, v_sz_boxed_1035_, v_i_boxed_1036_, v_b_1033_);
lean_dec_ref(v_as_1030_);
lean_dec_ref(v_tgtRange_1027_);
lean_dec(v_kind_1026_);
lean_dec_ref(v_i_1025_);
lean_dec_ref(v_init_1023_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0___boxed(lean_object* v_ctx_x3f_1038_, lean_object* v_i_1039_, lean_object* v_kind_1040_, lean_object* v_tgtRange_1041_, lean_object* v_f_1042_, lean_object* v_canonicalOnly_1043_, lean_object* v_t_1044_, lean_object* v_init_1045_){
_start:
{
uint8_t v_canonicalOnly_boxed_1046_; lean_object* v_res_1047_; 
v_canonicalOnly_boxed_1046_ = lean_unbox(v_canonicalOnly_1043_);
v_res_1047_ = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(v_ctx_x3f_1038_, v_i_1039_, v_kind_1040_, v_tgtRange_1041_, v_f_1042_, v_canonicalOnly_boxed_1046_, v_t_1044_, v_init_1045_);
lean_dec_ref(v_t_1044_);
lean_dec_ref(v_tgtRange_1041_);
lean_dec(v_kind_1040_);
lean_dec_ref(v_i_1039_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___boxed(lean_object* v_ctx_x3f_1048_, lean_object* v_i_1049_, lean_object* v_kind_1050_, lean_object* v_tgtRange_1051_, lean_object* v_f_1052_, lean_object* v_canonicalOnly_1053_, lean_object* v_as_1054_, lean_object* v_sz_1055_, lean_object* v_i_1056_, lean_object* v_b_1057_){
_start:
{
uint8_t v_canonicalOnly_boxed_1058_; size_t v_sz_boxed_1059_; size_t v_i_boxed_1060_; lean_object* v_res_1061_; 
v_canonicalOnly_boxed_1058_ = lean_unbox(v_canonicalOnly_1053_);
v_sz_boxed_1059_ = lean_unbox_usize(v_sz_1055_);
lean_dec(v_sz_1055_);
v_i_boxed_1060_ = lean_unbox_usize(v_i_1056_);
lean_dec(v_i_1056_);
v_res_1061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_1048_, v_i_1049_, v_kind_1050_, v_tgtRange_1051_, v_f_1052_, v_canonicalOnly_boxed_1058_, v_as_1054_, v_sz_boxed_1059_, v_i_boxed_1060_, v_b_1057_);
lean_dec_ref(v_as_1054_);
lean_dec_ref(v_tgtRange_1051_);
lean_dec(v_kind_1050_);
lean_dec_ref(v_i_1049_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_ctx_x3f_1062_, lean_object* v_i_1063_, lean_object* v_kind_1064_, lean_object* v_tgtRange_1065_, lean_object* v_f_1066_, lean_object* v_canonicalOnly_1067_, lean_object* v_as_1068_, lean_object* v_sz_1069_, lean_object* v_i_1070_, lean_object* v_b_1071_){
_start:
{
uint8_t v_canonicalOnly_boxed_1072_; size_t v_sz_boxed_1073_; size_t v_i_boxed_1074_; lean_object* v_res_1075_; 
v_canonicalOnly_boxed_1072_ = lean_unbox(v_canonicalOnly_1067_);
v_sz_boxed_1073_ = lean_unbox_usize(v_sz_1069_);
lean_dec(v_sz_1069_);
v_i_boxed_1074_ = lean_unbox_usize(v_i_1070_);
lean_dec(v_i_1070_);
v_res_1075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_1062_, v_i_1063_, v_kind_1064_, v_tgtRange_1065_, v_f_1066_, v_canonicalOnly_boxed_1072_, v_as_1068_, v_sz_boxed_1073_, v_i_boxed_1074_, v_b_1071_);
lean_dec_ref(v_as_1068_);
lean_dec_ref(v_tgtRange_1065_);
lean_dec(v_kind_1064_);
lean_dec_ref(v_i_1063_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_ctx_x3f_1076_, lean_object* v_i_1077_, lean_object* v_kind_1078_, lean_object* v_tgtRange_1079_, lean_object* v_f_1080_, lean_object* v_canonicalOnly_1081_, lean_object* v_as_1082_, lean_object* v_sz_1083_, lean_object* v_i_1084_, lean_object* v_b_1085_){
_start:
{
uint8_t v_canonicalOnly_boxed_1086_; size_t v_sz_boxed_1087_; size_t v_i_boxed_1088_; lean_object* v_res_1089_; 
v_canonicalOnly_boxed_1086_ = lean_unbox(v_canonicalOnly_1081_);
v_sz_boxed_1087_ = lean_unbox_usize(v_sz_1083_);
lean_dec(v_sz_1083_);
v_i_boxed_1088_ = lean_unbox_usize(v_i_1084_);
lean_dec(v_i_1084_);
v_res_1089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_1076_, v_i_1077_, v_kind_1078_, v_tgtRange_1079_, v_f_1080_, v_canonicalOnly_boxed_1086_, v_as_1082_, v_sz_boxed_1087_, v_i_boxed_1088_, v_b_1085_);
lean_dec_ref(v_as_1082_);
lean_dec_ref(v_tgtRange_1079_);
lean_dec(v_kind_1078_);
lean_dec_ref(v_i_1077_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_ctx_x3f_1090_, lean_object* v_i_1091_, lean_object* v_kind_1092_, lean_object* v_tgtRange_1093_, lean_object* v_f_1094_, lean_object* v_canonicalOnly_1095_, lean_object* v_as_1096_, lean_object* v_sz_1097_, lean_object* v_i_1098_, lean_object* v_b_1099_){
_start:
{
uint8_t v_canonicalOnly_boxed_1100_; size_t v_sz_boxed_1101_; size_t v_i_boxed_1102_; lean_object* v_res_1103_; 
v_canonicalOnly_boxed_1100_ = lean_unbox(v_canonicalOnly_1095_);
v_sz_boxed_1101_ = lean_unbox_usize(v_sz_1097_);
lean_dec(v_sz_1097_);
v_i_boxed_1102_ = lean_unbox_usize(v_i_1098_);
lean_dec(v_i_1098_);
v_res_1103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_1090_, v_i_1091_, v_kind_1092_, v_tgtRange_1093_, v_f_1094_, v_canonicalOnly_boxed_1100_, v_as_1096_, v_sz_boxed_1101_, v_i_boxed_1102_, v_b_1099_);
lean_dec_ref(v_as_1096_);
lean_dec_ref(v_tgtRange_1093_);
lean_dec(v_kind_1092_);
lean_dec_ref(v_i_1091_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0___boxed(lean_object* v_init_1104_, lean_object* v_ctx_x3f_1105_, lean_object* v_i_1106_, lean_object* v_kind_1107_, lean_object* v_tgtRange_1108_, lean_object* v_f_1109_, lean_object* v_canonicalOnly_1110_, lean_object* v_n_1111_, lean_object* v_b_1112_){
_start:
{
uint8_t v_canonicalOnly_boxed_1113_; lean_object* v_res_1114_; 
v_canonicalOnly_boxed_1113_ = lean_unbox(v_canonicalOnly_1110_);
v_res_1114_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_1104_, v_ctx_x3f_1105_, v_i_1106_, v_kind_1107_, v_tgtRange_1108_, v_f_1109_, v_canonicalOnly_boxed_1113_, v_n_1111_, v_b_1112_);
lean_dec_ref(v_n_1111_);
lean_dec_ref(v_tgtRange_1108_);
lean_dec(v_kind_1107_);
lean_dec_ref(v_i_1106_);
lean_dec_ref(v_init_1104_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f___boxed(lean_object* v_kind_1115_, lean_object* v_tgtRange_1116_, lean_object* v_ctx_x3f_1117_, lean_object* v_t_1118_, lean_object* v_f_1119_, lean_object* v_canonicalOnly_1120_){
_start:
{
uint8_t v_canonicalOnly_boxed_1121_; lean_object* v_res_1122_; 
v_canonicalOnly_boxed_1121_ = lean_unbox(v_canonicalOnly_1120_);
v_res_1122_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_1115_, v_tgtRange_1116_, v_ctx_x3f_1117_, v_t_1118_, v_f_1119_, v_canonicalOnly_boxed_1121_);
lean_dec_ref(v_tgtRange_1116_);
lean_dec(v_kind_1115_);
return v_res_1122_;
}
}
static lean_object* _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_1124_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_1124_, 0, lean_box(0));
lean_closure_set(v___x_1124_, 1, lean_box(0));
lean_closure_set(v___x_1124_, 2, v___x_1123_);
return v___x_1124_;
}
}
lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(lean_object* v_msg_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v___f_1129_; lean_object* v___x_3962__overap_1130_; lean_object* v___x_1131_; 
v___x_1128_ = lean_obj_once(&l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0, &l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0_once, _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0);
v___f_1129_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1129_, 0, v___x_1128_);
v___x_3962__overap_1130_ = lean_panic_fn_borrowed(v___f_1129_, v_msg_1125_);
lean_dec_ref(v___f_1129_);
lean_inc_ref(v___y_1126_);
v___x_1131_ = lean_apply_2(v___x_3962__overap_1130_, v___y_1126_, lean_box(0));
return v___x_1131_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1125_ = stack[0].m_obj;
lean_object* v___y_1126_ = stack[1].m_obj;
lean_object* v_res_1132_;
v_res_1132_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v_msg_1125_, v___y_1126_);
stack->m_obj
 = v_res_1132_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___boxed(lean_object* v_msg_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v_msg_1133_, v___y_1134_);
lean_dec_ref(v___y_1134_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0(lean_object* v___x_1137_, lean_object* v___x_1138_, lean_object* v_ctx_1139_, lean_object* v_node_1140_, lean_object* v_result_1141_){
_start:
{
uint8_t v___y_1143_; 
if (lean_obj_tag(v_node_1140_) == 1)
{
lean_object* v_i_1146_; 
v_i_1146_ = lean_ctor_get(v_node_1140_, 0);
if (lean_obj_tag(v_i_1146_) == 3)
{
lean_object* v_i_1147_; lean_object* v_stx_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; 
v_i_1147_ = lean_ctor_get(v_i_1146_, 0);
v_stx_1148_ = lean_ctor_get(v_i_1147_, 1);
v___x_1149_ = 1;
v___x_1150_ = l_Lean_Syntax_getPos_x3f(v_stx_1148_, v___x_1149_);
if (lean_obj_tag(v___x_1150_) == 1)
{
lean_object* v_val_1151_; lean_object* v___x_1152_; 
v_val_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_val_1151_);
lean_dec_ref_known(v___x_1150_, 1);
v___x_1152_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1148_, v___x_1149_);
if (lean_obj_tag(v___x_1152_) == 1)
{
lean_object* v_val_1153_; uint8_t v___x_1154_; 
v_val_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_val_1153_);
lean_dec_ref_known(v___x_1152_, 1);
v___x_1154_ = lean_nat_dec_le(v_val_1151_, v___x_1137_);
lean_dec(v_val_1151_);
if (v___x_1154_ == 0)
{
lean_dec(v_val_1153_);
v___y_1143_ = v___x_1154_;
goto v___jp_1142_;
}
else
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_nat_dec_le(v___x_1138_, v_val_1153_);
lean_dec(v_val_1153_);
v___y_1143_ = v___x_1155_;
goto v___jp_1142_;
}
}
else
{
lean_dec(v___x_1152_);
lean_dec(v_val_1151_);
lean_dec_ref_known(v_node_1140_, 2);
lean_dec_ref(v_ctx_1139_);
return v_result_1141_;
}
}
else
{
lean_dec(v___x_1150_);
lean_dec_ref_known(v_node_1140_, 2);
lean_dec_ref(v_ctx_1139_);
return v_result_1141_;
}
}
else
{
lean_dec_ref_known(v_node_1140_, 2);
lean_dec_ref(v_ctx_1139_);
return v_result_1141_;
}
}
else
{
lean_dec_ref(v_node_1140_);
lean_dec_ref(v_ctx_1139_);
return v_result_1141_;
}
v___jp_1142_:
{
if (v___y_1143_ == 0)
{
lean_dec_ref(v_node_1140_);
lean_dec_ref(v_ctx_1139_);
return v_result_1141_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_ctx_1139_);
lean_ctor_set(v___x_1144_, 1, v_node_1140_);
v___x_1145_ = lean_array_push(v_result_1141_, v___x_1144_);
return v___x_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed(lean_object* v___x_1156_, lean_object* v___x_1157_, lean_object* v_ctx_1158_, lean_object* v_node_1159_, lean_object* v_result_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_CodeAction_cmdCodeActionProvider___lam__0(v___x_1156_, v___x_1157_, v_ctx_1158_, v_node_1159_, v_result_1160_);
lean_dec(v___x_1157_);
lean_dec(v___x_1156_);
return v_res_1161_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(lean_object* v_params_1162_, lean_object* v_snap_1163_, lean_object* v_fst_1164_, lean_object* v_snd_1165_, lean_object* v_as_1166_, size_t v_sz_1167_, size_t v_i_1168_, lean_object* v_b_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_snd_1173_; uint8_t v___x_1177_; 
v___x_1177_ = lean_usize_dec_lt(v_i_1168_, v_sz_1167_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; 
lean_dec_ref(v_snd_1165_);
lean_dec_ref(v_fst_1164_);
lean_dec_ref(v_snap_1163_);
lean_dec_ref(v_params_1162_);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_b_1169_);
return v___x_1178_;
}
else
{
lean_object* v___x_4584__overap_1179_; lean_object* v___x_1180_; 
v___x_4584__overap_1179_ = lean_array_uget_borrowed(v_as_1166_, v_i_1168_);
lean_inc(v___x_4584__overap_1179_);
lean_inc_ref(v___y_1170_);
lean_inc_ref(v_snd_1165_);
lean_inc_ref(v_fst_1164_);
lean_inc_ref(v_snap_1163_);
lean_inc_ref(v_params_1162_);
v___x_1180_ = lean_apply_6(v___x_4584__overap_1179_, v_params_1162_, v_snap_1163_, v_fst_1164_, v_snd_1165_, v___y_1170_, lean_box(0));
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1182_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1182_ = l_Array_append___redArg(v_b_1169_, v_a_1181_);
lean_dec(v_a_1181_);
v_snd_1173_ = v___x_1182_;
goto v___jp_1172_;
}
else
{
lean_dec_ref_known(v___x_1180_, 1);
v_snd_1173_ = v_b_1169_;
goto v___jp_1172_;
}
}
v___jp_1172_:
{
size_t v___x_1174_; size_t v___x_1175_; 
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1168_, v___x_1174_);
v_i_1168_ = v___x_1175_;
v_b_1169_ = v_snd_1173_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_1162_ = stack[0].m_obj;
lean_object* v_snap_1163_ = stack[1].m_obj;
lean_object* v_fst_1164_ = stack[2].m_obj;
lean_object* v_snd_1165_ = stack[3].m_obj;
lean_object* v_as_1166_ = stack[4].m_obj;
size_t v_sz_1167_ = stack[5].m_num;
size_t v_i_1168_ = stack[6].m_num;
lean_object* v_b_1169_ = stack[7].m_obj;
lean_object* v___y_1170_ = stack[8].m_obj;
lean_object* v_res_1183_;
v_res_1183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1162_, v_snap_1163_, v_fst_1164_, v_snd_1165_, v_as_1166_, v_sz_1167_, v_i_1168_, v_b_1169_, v___y_1170_);
stack->m_obj
 = v_res_1183_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1___boxed(lean_object* v_params_1184_, lean_object* v_snap_1185_, lean_object* v_fst_1186_, lean_object* v_snd_1187_, lean_object* v_as_1188_, lean_object* v_sz_1189_, lean_object* v_i_1190_, lean_object* v_b_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
size_t v_sz_boxed_1194_; size_t v_i_boxed_1195_; lean_object* v_res_1196_; 
v_sz_boxed_1194_ = lean_unbox_usize(v_sz_1189_);
lean_dec(v_sz_1189_);
v_i_boxed_1195_ = lean_unbox_usize(v_i_1190_);
lean_dec(v_i_1190_);
v_res_1196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1184_, v_snap_1185_, v_fst_1186_, v_snd_1187_, v_as_1188_, v_sz_boxed_1194_, v_i_boxed_1195_, v_b_1191_, v___y_1192_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v_as_1188_);
return v_res_1196_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2));
v___x_1201_ = lean_unsigned_to_nat(48u);
v___x_1202_ = lean_unsigned_to_nat(185u);
v___x_1203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1));
v___x_1204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0));
v___x_1205_ = l_mkPanicMessageWithDecl(v___x_1204_, v___x_1203_, v___x_1202_, v___x_1201_, v___x_1200_);
return v___x_1205_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(lean_object* v___x_1206_, lean_object* v_params_1207_, lean_object* v_snap_1208_, lean_object* v_as_1209_, size_t v_sz_1210_, size_t v_i_1211_, lean_object* v_b_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_a_1216_; lean_object* v___y_1221_; uint8_t v___x_1232_; 
v___x_1232_ = lean_usize_dec_lt(v_i_1211_, v_sz_1210_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
lean_dec_ref(v_snap_1208_);
lean_dec_ref(v_params_1207_);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v_b_1212_);
return v___x_1233_;
}
else
{
lean_object* v_a_1234_; lean_object* v_snd_1235_; 
v_a_1234_ = lean_array_uget_borrowed(v_as_1209_, v_i_1211_);
v_snd_1235_ = lean_ctor_get(v_a_1234_, 1);
if (lean_obj_tag(v_snd_1235_) == 1)
{
lean_object* v_i_1236_; 
v_i_1236_ = lean_ctor_get(v_snd_1235_, 0);
if (lean_obj_tag(v_i_1236_) == 3)
{
lean_object* v_fst_1237_; lean_object* v_i_1238_; lean_object* v_onAnyCmd_1239_; lean_object* v_onCmd_1240_; lean_object* v_out_1242_; lean_object* v___y_1243_; lean_object* v_stx_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_fst_1237_ = lean_ctor_get(v_a_1234_, 0);
v_i_1238_ = lean_ctor_get(v_i_1236_, 0);
v_onAnyCmd_1239_ = lean_ctor_get(v___x_1206_, 0);
v_onCmd_1240_ = lean_ctor_get(v___x_1206_, 1);
v_stx_1248_ = lean_ctor_get(v_i_1238_, 1);
lean_inc(v_stx_1248_);
v___x_1249_ = l_Lean_Syntax_getKind(v_stx_1248_);
v___x_1250_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_1240_, v___x_1249_);
lean_dec(v___x_1249_);
if (lean_obj_tag(v___x_1250_) == 1)
{
lean_object* v_val_1251_; size_t v_sz_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v_val_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_val_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v_sz_1252_ = lean_array_size(v_val_1251_);
v___x_1253_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1235_);
lean_inc(v_fst_1237_);
lean_inc_ref(v_snap_1208_);
lean_inc_ref(v_params_1207_);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1207_, v_snap_1208_, v_fst_1237_, v_snd_1235_, v_val_1251_, v_sz_1252_, v___x_1253_, v_b_1212_, v___y_1213_);
lean_dec(v_val_1251_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v_out_1242_ = v_a_1255_;
v___y_1243_ = v___y_1213_;
goto v___jp_1241_;
}
else
{
lean_dec_ref(v_snap_1208_);
lean_dec_ref(v_params_1207_);
return v___x_1254_;
}
}
else
{
lean_dec(v___x_1250_);
v_out_1242_ = v_b_1212_;
v___y_1243_ = v___y_1213_;
goto v___jp_1241_;
}
v___jp_1241_:
{
size_t v_sz_1244_; size_t v___x_1245_; lean_object* v___x_1246_; 
v_sz_1244_ = lean_array_size(v_onAnyCmd_1239_);
v___x_1245_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1235_);
lean_inc(v_fst_1237_);
lean_inc_ref(v_snap_1208_);
lean_inc_ref(v_params_1207_);
v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1207_, v_snap_1208_, v_fst_1237_, v_snd_1235_, v_onAnyCmd_1239_, v_sz_1244_, v___x_1245_, v_out_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v_a_1216_ = v_a_1247_;
goto v___jp_1215_;
}
else
{
lean_dec_ref(v_snap_1208_);
lean_dec_ref(v_params_1207_);
return v___x_1246_;
}
}
}
else
{
v___y_1221_ = v___y_1213_;
goto v___jp_1220_;
}
}
else
{
v___y_1221_ = v___y_1213_;
goto v___jp_1220_;
}
}
v___jp_1215_:
{
size_t v___x_1217_; size_t v___x_1218_; 
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1211_, v___x_1217_);
v_i_1211_ = v___x_1218_;
v_b_1212_ = v_a_1216_;
goto _start;
}
v___jp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
v___x_1223_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v___x_1222_, v___y_1221_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_dec_ref_known(v___x_1223_, 1);
v_a_1216_ = v_b_1212_;
goto v___jp_1215_;
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec_ref(v_b_1212_);
lean_dec_ref(v_snap_1208_);
lean_dec_ref(v_params_1207_);
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1206_ = stack[0].m_obj;
lean_object* v_params_1207_ = stack[1].m_obj;
lean_object* v_snap_1208_ = stack[2].m_obj;
lean_object* v_as_1209_ = stack[3].m_obj;
size_t v_sz_1210_ = stack[4].m_num;
size_t v_i_1211_ = stack[5].m_num;
lean_object* v_b_1212_ = stack[6].m_obj;
lean_object* v___y_1213_ = stack[7].m_obj;
lean_object* v_res_1256_;
v_res_1256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_1206_, v_params_1207_, v_snap_1208_, v_as_1209_, v_sz_1210_, v_i_1211_, v_b_1212_, v___y_1213_);
stack->m_obj
 = v_res_1256_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___boxed(lean_object* v___x_1257_, lean_object* v_params_1258_, lean_object* v_snap_1259_, lean_object* v_as_1260_, lean_object* v_sz_1261_, lean_object* v_i_1262_, lean_object* v_b_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
size_t v_sz_boxed_1266_; size_t v_i_boxed_1267_; lean_object* v_res_1268_; 
v_sz_boxed_1266_ = lean_unbox_usize(v_sz_1261_);
lean_dec(v_sz_1261_);
v_i_boxed_1267_ = lean_unbox_usize(v_i_1262_);
lean_dec(v_i_1262_);
v_res_1268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_1257_, v_params_1258_, v_snap_1259_, v_as_1260_, v_sz_boxed_1266_, v_i_boxed_1267_, v_b_1263_, v___y_1264_);
lean_dec_ref(v___y_1264_);
lean_dec_ref(v_as_1260_);
lean_dec_ref(v___x_1257_);
return v_res_1268_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(lean_object* v_params_1269_, lean_object* v_snap_1270_, lean_object* v___x_1271_, lean_object* v_as_1272_, size_t v_sz_1273_, size_t v_i_1274_, lean_object* v_b_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_a_1279_; lean_object* v___y_1284_; uint8_t v___x_1295_; 
v___x_1295_ = lean_usize_dec_lt(v_i_1274_, v_sz_1273_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; 
lean_dec_ref(v_snap_1270_);
lean_dec_ref(v_params_1269_);
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_b_1275_);
return v___x_1296_;
}
else
{
lean_object* v_a_1297_; lean_object* v_snd_1298_; 
v_a_1297_ = lean_array_uget_borrowed(v_as_1272_, v_i_1274_);
v_snd_1298_ = lean_ctor_get(v_a_1297_, 1);
if (lean_obj_tag(v_snd_1298_) == 1)
{
lean_object* v_i_1299_; 
v_i_1299_ = lean_ctor_get(v_snd_1298_, 0);
if (lean_obj_tag(v_i_1299_) == 3)
{
lean_object* v_fst_1300_; lean_object* v_i_1301_; lean_object* v_onAnyCmd_1302_; lean_object* v_onCmd_1303_; lean_object* v_out_1305_; lean_object* v___y_1306_; lean_object* v_stx_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_fst_1300_ = lean_ctor_get(v_a_1297_, 0);
v_i_1301_ = lean_ctor_get(v_i_1299_, 0);
v_onAnyCmd_1302_ = lean_ctor_get(v___x_1271_, 0);
v_onCmd_1303_ = lean_ctor_get(v___x_1271_, 1);
v_stx_1311_ = lean_ctor_get(v_i_1301_, 1);
lean_inc(v_stx_1311_);
v___x_1312_ = l_Lean_Syntax_getKind(v_stx_1311_);
v___x_1313_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_1303_, v___x_1312_);
lean_dec(v___x_1312_);
if (lean_obj_tag(v___x_1313_) == 1)
{
lean_object* v_val_1314_; size_t v_sz_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v_val_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_val_1314_);
lean_dec_ref_known(v___x_1313_, 1);
v_sz_1315_ = lean_array_size(v_val_1314_);
v___x_1316_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1298_);
lean_inc(v_fst_1300_);
lean_inc_ref(v_snap_1270_);
lean_inc_ref(v_params_1269_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1269_, v_snap_1270_, v_fst_1300_, v_snd_1298_, v_val_1314_, v_sz_1315_, v___x_1316_, v_b_1275_, v___y_1276_);
lean_dec(v_val_1314_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v_out_1305_ = v_a_1318_;
v___y_1306_ = v___y_1276_;
goto v___jp_1304_;
}
else
{
lean_dec_ref(v_snap_1270_);
lean_dec_ref(v_params_1269_);
return v___x_1317_;
}
}
else
{
lean_dec(v___x_1313_);
v_out_1305_ = v_b_1275_;
v___y_1306_ = v___y_1276_;
goto v___jp_1304_;
}
v___jp_1304_:
{
size_t v_sz_1307_; size_t v___x_1308_; lean_object* v___x_1309_; 
v_sz_1307_ = lean_array_size(v_onAnyCmd_1302_);
v___x_1308_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1298_);
lean_inc(v_fst_1300_);
lean_inc_ref(v_snap_1270_);
lean_inc_ref(v_params_1269_);
v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1269_, v_snap_1270_, v_fst_1300_, v_snd_1298_, v_onAnyCmd_1302_, v_sz_1307_, v___x_1308_, v_out_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v_a_1279_ = v_a_1310_;
goto v___jp_1278_;
}
else
{
lean_dec_ref(v_snap_1270_);
lean_dec_ref(v_params_1269_);
return v___x_1309_;
}
}
}
else
{
v___y_1284_ = v___y_1276_;
goto v___jp_1283_;
}
}
else
{
v___y_1284_ = v___y_1276_;
goto v___jp_1283_;
}
}
v___jp_1278_:
{
size_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_add(v_i_1274_, v___x_1280_);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_1271_, v_params_1269_, v_snap_1270_, v_as_1272_, v_sz_1273_, v___x_1281_, v_a_1279_, v___y_1276_);
return v___x_1282_;
}
v___jp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
v___x_1286_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v___x_1285_, v___y_1284_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_dec_ref_known(v___x_1286_, 1);
v_a_1279_ = v_b_1275_;
goto v___jp_1278_;
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v_b_1275_);
lean_dec_ref(v_snap_1270_);
lean_dec_ref(v_params_1269_);
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_1269_ = stack[0].m_obj;
lean_object* v_snap_1270_ = stack[1].m_obj;
lean_object* v___x_1271_ = stack[2].m_obj;
lean_object* v_as_1272_ = stack[3].m_obj;
size_t v_sz_1273_ = stack[4].m_num;
size_t v_i_1274_ = stack[5].m_num;
lean_object* v_b_1275_ = stack[6].m_obj;
lean_object* v___y_1276_ = stack[7].m_obj;
lean_object* v_res_1319_;
v_res_1319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_1269_, v_snap_1270_, v___x_1271_, v_as_1272_, v_sz_1273_, v_i_1274_, v_b_1275_, v___y_1276_);
stack->m_obj
 = v_res_1319_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2___boxed(lean_object* v_params_1320_, lean_object* v_snap_1321_, lean_object* v___x_1322_, lean_object* v_as_1323_, lean_object* v_sz_1324_, lean_object* v_i_1325_, lean_object* v_b_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
size_t v_sz_boxed_1329_; size_t v_i_boxed_1330_; lean_object* v_res_1331_; 
v_sz_boxed_1329_ = lean_unbox_usize(v_sz_1324_);
lean_dec(v_sz_1324_);
v_i_boxed_1330_ = lean_unbox_usize(v_i_1325_);
lean_dec(v_i_1325_);
v_res_1331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_1320_, v_snap_1321_, v___x_1322_, v_as_1323_, v_sz_boxed_1329_, v_i_boxed_1330_, v_b_1326_, v___y_1327_);
lean_dec_ref(v___y_1327_);
lean_dec_ref(v_as_1323_);
lean_dec_ref(v___x_1322_);
return v_res_1331_;
}
}
static lean_object* _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = l_Lean_CodeAction_instInhabitedCommandCodeActions_default;
v___x_1333_ = lean_obj_once(&l_Lean_CodeAction_holeCodeActionProvider___closed__0, &l_Lean_CodeAction_holeCodeActionProvider___closed__0_once, _init_l_Lean_CodeAction_holeCodeActionProvider___closed__0);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1332_);
return v___x_1334_;
}
}
lean_object* l_Lean_CodeAction_cmdCodeActionProvider(lean_object* v_params_1337_, lean_object* v_snap_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v_a_1343_; lean_object* v_toEditableDocumentCore_1344_; lean_object* v_meta_1345_; lean_object* v_range_1346_; lean_object* v_text_1347_; lean_object* v_start_1348_; lean_object* v_end_1349_; lean_object* v___x_1350_; lean_object* v_toEnvExtension_1351_; lean_object* v_asyncMode_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; lean_object* v_snd_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___f_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; size_t v_sz_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
v___x_1341_ = lean_obj_once(&l_Lean_CodeAction_cmdCodeActionProvider___closed__0, &l_Lean_CodeAction_cmdCodeActionProvider___closed__0_once, _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0);
v___x_1342_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v_a_1339_);
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref(v___x_1342_);
v_toEditableDocumentCore_1344_ = lean_ctor_get(v_a_1343_, 0);
lean_inc_ref(v_toEditableDocumentCore_1344_);
lean_dec(v_a_1343_);
v_meta_1345_ = lean_ctor_get(v_toEditableDocumentCore_1344_, 0);
lean_inc_ref(v_meta_1345_);
lean_dec_ref(v_toEditableDocumentCore_1344_);
v_range_1346_ = lean_ctor_get(v_params_1337_, 3);
v_text_1347_ = lean_ctor_get(v_meta_1345_, 3);
lean_inc_ref(v_text_1347_);
lean_dec_ref(v_meta_1345_);
v_start_1348_ = lean_ctor_get(v_range_1346_, 0);
v_end_1349_ = lean_ctor_get(v_range_1346_, 1);
v___x_1350_ = l_Lean_CodeAction_cmdCodeActionExt;
v_toEnvExtension_1351_ = lean_ctor_get(v___x_1350_, 0);
v_asyncMode_1352_ = lean_ctor_get(v_toEnvExtension_1351_, 2);
v___x_1353_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1338_);
v___x_1354_ = lean_box(0);
v___x_1355_ = 0;
v___x_1356_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1341_, v___x_1350_, v___x_1353_, v_asyncMode_1352_, v___x_1354_, v___x_1355_);
v_snd_1357_ = lean_ctor_get(v___x_1356_, 1);
lean_inc(v_snd_1357_);
lean_dec(v___x_1356_);
lean_inc_ref(v_start_1348_);
v___x_1358_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1347_, v_start_1348_);
lean_inc_ref(v_end_1349_);
v___x_1359_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1347_, v_end_1349_);
lean_dec_ref(v_text_1347_);
v___f_1360_ = lean_alloc_closure((void*)(l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1360_, 0, v___x_1359_);
lean_closure_set(v___f_1360_, 1, v___x_1358_);
v___x_1361_ = ((lean_object*)(l_Lean_CodeAction_cmdCodeActionProvider___closed__1));
lean_inc_ref(v_snap_1338_);
v___x_1362_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_1338_);
v___x_1363_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v___x_1361_, v___f_1360_, v___x_1362_);
v_sz_1364_ = lean_array_size(v___x_1363_);
v___x_1365_ = ((size_t)0ULL);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_1337_, v_snap_1338_, v_snd_1357_, v___x_1363_, v_sz_1364_, v___x_1365_, v___x_1361_, v_a_1339_);
lean_dec(v___x_1363_);
lean_dec(v_snd_1357_);
return v___x_1366_;
}
}
LEAN_EXPORT void l_Lean_CodeAction_cmdCodeActionProvider_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_1337_ = stack[0].m_obj;
lean_object* v_snap_1338_ = stack[1].m_obj;
lean_object* v_a_1339_ = stack[2].m_obj;
lean_object* v_res_1367_;
v_res_1367_ = l_Lean_CodeAction_cmdCodeActionProvider(v_params_1337_, v_snap_1338_, v_a_1339_);
stack->m_obj
 = v_res_1367_;
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___boxed(lean_object* v_params_1368_, lean_object* v_snap_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_CodeAction_cmdCodeActionProvider(v_params_1368_, v_snap_1369_, v_a_1370_);
lean_dec_ref(v_a_1370_);
return v_res_1372_;
}
}
lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1(){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1379_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1));
v___x_1380_ = lean_alloc_closure((void*)(l_Lean_CodeAction_cmdCodeActionProvider___boxed), 4, 0);
v___x_1381_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_1379_, v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT void l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1382_;
v_res_1382_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
stack->m_obj
 = v_res_1382_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___boxed(lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
return v_res_1384_;
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
