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
extern lean_object* l_Lean_CodeAction_cmdCodeActionExt;
extern lean_object* l_Lean_CodeAction_instInhabitedCommandCodeActions_default;
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Lean_CodeAction_holeCodeActionProvider___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CodeAction_holeCodeActionProvider___closed__0 = (const lean_object*)&l_Lean_CodeAction_holeCodeActionProvider___closed__0_value;
static lean_once_cell_t l_Lean_CodeAction_holeCodeActionProvider___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_holeCodeActionProvider___closed__1;
static lean_once_cell_t l_Lean_CodeAction_holeCodeActionProvider___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_holeCodeActionProvider___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_CodeAction_cmdCodeActionProvider___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CodeAction_cmdCodeActionProvider___closed__1;
static const lean_array_object l_Lean_CodeAction_cmdCodeActionProvider___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CodeAction_cmdCodeActionProvider___closed__2 = (const lean_object*)&l_Lean_CodeAction_cmdCodeActionProvider___closed__2_value;
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
lean_object* v_i_54_; uint8_t v___y_56_; lean_object* v_toElabInfo_59_; lean_object* v_elaborator_60_; lean_object* v_stx_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v_i_54_ = lean_ctor_get(v_info_52_, 0);
v_toElabInfo_59_ = lean_ctor_get(v_i_54_, 0);
v_elaborator_60_ = lean_ctor_get(v_toElabInfo_59_, 0);
v_stx_61_ = lean_ctor_get(v_toElabInfo_59_, 1);
v___x_62_ = ((lean_object*)(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11));
v___x_63_ = l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(v_elaborator_60_, v___x_62_);
if (v___x_63_ == 0)
{
lean_dec_ref(v_ctx_51_);
return v_result_53_;
}
else
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Syntax_getPos_x3f(v_stx_61_, v___x_63_);
if (lean_obj_tag(v___x_64_) == 1)
{
lean_object* v_val_65_; lean_object* v___x_66_; 
v_val_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_val_65_);
lean_dec_ref_known(v___x_64_, 1);
v___x_66_ = l_Lean_Syntax_getTailPos_x3f(v_stx_61_, v___x_63_);
if (lean_obj_tag(v___x_66_) == 1)
{
lean_object* v_val_67_; uint8_t v___x_68_; 
v_val_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_val_67_);
lean_dec_ref_known(v___x_66_, 1);
v___x_68_ = lean_nat_dec_le(v_val_65_, v___x_49_);
lean_dec(v_val_65_);
if (v___x_68_ == 0)
{
lean_dec(v_val_67_);
v___y_56_ = v___x_68_;
goto v___jp_55_;
}
else
{
uint8_t v___x_69_; 
v___x_69_ = lean_nat_dec_le(v___x_50_, v_val_67_);
lean_dec(v_val_67_);
v___y_56_ = v___x_69_;
goto v___jp_55_;
}
}
else
{
lean_dec(v___x_66_);
lean_dec(v_val_65_);
lean_dec_ref(v_ctx_51_);
return v_result_53_;
}
}
else
{
lean_dec(v___x_64_);
lean_dec_ref(v_ctx_51_);
return v_result_53_;
}
}
v___jp_55_:
{
if (v___y_56_ == 0)
{
lean_dec_ref(v_ctx_51_);
return v_result_53_;
}
else
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_inc_ref(v_i_54_);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v_ctx_51_);
lean_ctor_set(v___x_57_, 1, v_i_54_);
v___x_58_ = lean_array_push(v_result_53_, v___x_57_);
return v___x_58_;
}
}
}
else
{
lean_dec_ref(v_ctx_51_);
return v_result_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed(lean_object* v___x_70_, lean_object* v___x_71_, lean_object* v_ctx_72_, lean_object* v_info_73_, lean_object* v_result_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_CodeAction_holeCodeActionProvider___lam__0(v___x_70_, v___x_71_, v_ctx_72_, v_info_73_, v_result_74_);
lean_dec_ref(v_info_73_);
lean_dec(v___x_71_);
lean_dec(v___x_70_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(lean_object* v_params_76_, lean_object* v_snap_77_, lean_object* v_fst_78_, lean_object* v_snd_79_, lean_object* v_as_80_, size_t v_i_81_, size_t v_stop_82_, lean_object* v_b_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_a_87_; uint8_t v___x_91_; 
v___x_91_ = lean_usize_dec_eq(v_i_81_, v_stop_82_);
if (v___x_91_ == 0)
{
lean_object* v___x_1554__overap_92_; lean_object* v___x_93_; 
v___x_1554__overap_92_ = lean_array_uget_borrowed(v_as_80_, v_i_81_);
lean_inc(v___x_1554__overap_92_);
lean_inc_ref(v___y_84_);
lean_inc_ref(v_snd_79_);
lean_inc_ref(v_fst_78_);
lean_inc_ref(v_snap_77_);
lean_inc_ref(v_params_76_);
v___x_93_ = lean_apply_6(v___x_1554__overap_92_, v_params_76_, v_snap_77_, v_fst_78_, v_snd_79_, v___y_84_, lean_box(0));
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_95_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_94_);
lean_dec_ref_known(v___x_93_, 1);
v___x_95_ = l_Array_append___redArg(v_b_83_, v_a_94_);
lean_dec(v_a_94_);
v_a_87_ = v___x_95_;
goto v___jp_86_;
}
else
{
lean_dec_ref(v_b_83_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_96_; 
v_a_96_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_93_, 1);
v_a_87_ = v_a_96_;
goto v___jp_86_;
}
else
{
lean_dec_ref(v_snd_79_);
lean_dec_ref(v_fst_78_);
lean_dec_ref(v_snap_77_);
lean_dec_ref(v_params_76_);
return v___x_93_;
}
}
}
else
{
lean_object* v___x_97_; 
lean_dec_ref(v_snd_79_);
lean_dec_ref(v_fst_78_);
lean_dec_ref(v_snap_77_);
lean_dec_ref(v_params_76_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v_b_83_);
return v___x_97_;
}
v___jp_86_:
{
size_t v___x_88_; size_t v___x_89_; 
v___x_88_ = ((size_t)1ULL);
v___x_89_ = lean_usize_add(v_i_81_, v___x_88_);
v_i_81_ = v___x_89_;
v_b_83_ = v_a_87_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2___boxed(lean_object* v_params_98_, lean_object* v_snap_99_, lean_object* v_fst_100_, lean_object* v_snd_101_, lean_object* v_as_102_, lean_object* v_i_103_, lean_object* v_stop_104_, lean_object* v_b_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
size_t v_i_boxed_108_; size_t v_stop_boxed_109_; lean_object* v_res_110_; 
v_i_boxed_108_ = lean_unbox_usize(v_i_103_);
lean_dec(v_i_103_);
v_stop_boxed_109_ = lean_unbox_usize(v_stop_104_);
lean_dec(v_stop_104_);
v_res_110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_98_, v_snap_99_, v_fst_100_, v_snd_101_, v_as_102_, v_i_boxed_108_, v_stop_boxed_109_, v_b_105_, v___y_106_);
lean_dec_ref(v___y_106_);
lean_dec_ref(v_as_102_);
return v_res_110_;
}
}
static lean_object* _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Array_instInhabited(lean_box(0));
return v___x_113_;
}
}
static lean_object* _init_l_Lean_CodeAction_holeCodeActionProvider___closed__2(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_obj_once(&l_Lean_CodeAction_holeCodeActionProvider___closed__1, &l_Lean_CodeAction_holeCodeActionProvider___closed__1_once, _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider(lean_object* v_params_118_, lean_object* v_snap_119_, lean_object* v_a_120_){
_start:
{
lean_object* v___x_122_; lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_166_; 
v___x_122_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v_a_120_);
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_166_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_166_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_166_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v_toEditableDocumentCore_127_; lean_object* v_meta_128_; lean_object* v_range_129_; lean_object* v_text_130_; lean_object* v_start_131_; lean_object* v_end_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___f_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_toEditableDocumentCore_127_ = lean_ctor_get(v_a_123_, 0);
lean_inc_ref(v_toEditableDocumentCore_127_);
lean_dec(v_a_123_);
v_meta_128_ = lean_ctor_get(v_toEditableDocumentCore_127_, 0);
lean_inc_ref(v_meta_128_);
lean_dec_ref(v_toEditableDocumentCore_127_);
v_range_129_ = lean_ctor_get(v_params_118_, 3);
v_text_130_ = lean_ctor_get(v_meta_128_, 3);
lean_inc_ref(v_text_130_);
lean_dec_ref(v_meta_128_);
v_start_131_ = lean_ctor_get(v_range_129_, 0);
v_end_132_ = lean_ctor_get(v_range_129_, 1);
lean_inc_ref(v_start_131_);
v___x_133_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_130_, v_start_131_);
lean_inc_ref(v_end_132_);
v___x_134_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_130_, v_end_132_);
lean_dec_ref(v_text_130_);
v___f_135_ = lean_alloc_closure((void*)(l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed), 5, 2);
lean_closure_set(v___f_135_, 0, v___x_134_);
lean_closure_set(v___f_135_, 1, v___x_133_);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = ((lean_object*)(l_Lean_CodeAction_holeCodeActionProvider___closed__0));
lean_inc_ref(v_snap_119_);
v___x_138_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_119_);
v___x_139_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_135_, v___x_137_, v___x_138_);
v___x_140_ = lean_array_get_size(v___x_139_);
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = lean_nat_dec_eq(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_144_; 
lean_dec(v___x_139_);
lean_dec_ref(v_snap_119_);
lean_dec_ref(v_params_118_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_137_);
v___x_144_ = v___x_125_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_137_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
else
{
lean_object* v___x_146_; lean_object* v_fst_147_; lean_object* v_snd_148_; lean_object* v___x_149_; lean_object* v_toEnvExtension_150_; lean_object* v_asyncMode_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_snd_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_146_ = lean_array_fget(v___x_139_, v___x_136_);
lean_dec(v___x_139_);
v_fst_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_fst_147_);
v_snd_148_ = lean_ctor_get(v___x_146_, 1);
lean_inc(v_snd_148_);
lean_dec(v___x_146_);
v___x_149_ = l_Lean_CodeAction_holeCodeActionExt;
v_toEnvExtension_150_ = lean_ctor_get(v___x_149_, 0);
v_asyncMode_151_ = lean_ctor_get(v_toEnvExtension_150_, 2);
v___x_152_ = lean_obj_once(&l_Lean_CodeAction_holeCodeActionProvider___closed__2, &l_Lean_CodeAction_holeCodeActionProvider___closed__2_once, _init_l_Lean_CodeAction_holeCodeActionProvider___closed__2);
v___x_153_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_119_);
v___x_154_ = lean_box(0);
v___x_155_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_152_, v___x_149_, v___x_153_, v_asyncMode_151_, v___x_154_);
v_snd_156_ = lean_ctor_get(v___x_155_, 1);
lean_inc(v_snd_156_);
lean_dec(v___x_155_);
v___x_157_ = ((lean_object*)(l_Lean_CodeAction_holeCodeActionProvider___closed__3));
v___x_158_ = lean_array_get_size(v_snd_156_);
v___x_159_ = lean_nat_dec_lt(v___x_136_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_161_; 
lean_dec(v_snd_156_);
lean_dec(v_snd_148_);
lean_dec(v_fst_147_);
lean_dec_ref(v_snap_119_);
lean_dec_ref(v_params_118_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_157_);
v___x_161_ = v___x_125_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_157_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
else
{
size_t v___x_163_; size_t v___x_164_; lean_object* v___x_165_; 
lean_del_object(v___x_125_);
v___x_163_ = ((size_t)0ULL);
v___x_164_ = lean_usize_of_nat(v___x_158_);
v___x_165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_118_, v_snap_119_, v_fst_147_, v_snd_148_, v_snd_156_, v___x_163_, v___x_164_, v___x_157_, v_a_120_);
lean_dec(v_snd_156_);
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___boxed(lean_object* v_params_167_, lean_object* v_snap_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_CodeAction_holeCodeActionProvider(v_params_167_, v_snap_168_, v_a_169_);
lean_dec_ref(v_a_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1(){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2));
v___x_180_ = lean_alloc_closure((void*)(l_Lean_CodeAction_holeCodeActionProvider___boxed), 4, 0);
v___x_181_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_179_, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___boxed(lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx(lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_unsigned_to_nat(0u);
return v___x_185_;
}
else
{
lean_object* v___x_186_; 
v___x_186_ = lean_unsigned_to_nat(1u);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx___boxed(lean_object* v_x_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_CodeAction_FindTacticResult_ctorIdx(v_x_187_);
lean_dec_ref(v_x_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(lean_object* v_t_189_, lean_object* v_k_190_){
_start:
{
if (lean_obj_tag(v_t_189_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_192_; 
v_a_191_ = lean_ctor_get(v_t_189_, 0);
lean_inc(v_a_191_);
lean_dec_ref_known(v_t_189_, 1);
v___x_192_ = lean_apply_1(v_k_190_, v_a_191_);
return v___x_192_;
}
else
{
uint8_t v_preferred_193_; lean_object* v_insertIdx_194_; lean_object* v_a_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_preferred_193_ = lean_ctor_get_uint8(v_t_189_, sizeof(void*)*2);
v_insertIdx_194_ = lean_ctor_get(v_t_189_, 0);
lean_inc(v_insertIdx_194_);
v_a_195_ = lean_ctor_get(v_t_189_, 1);
lean_inc(v_a_195_);
lean_dec_ref_known(v_t_189_, 2);
v___x_196_ = lean_box(v_preferred_193_);
v___x_197_ = lean_apply_3(v_k_190_, v___x_196_, v_insertIdx_194_, v_a_195_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim(lean_object* v_motive_198_, lean_object* v_ctorIdx_199_, lean_object* v_t_200_, lean_object* v_h_201_, lean_object* v_k_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_200_, v_k_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___boxed(lean_object* v_motive_204_, lean_object* v_ctorIdx_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_k_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_CodeAction_FindTacticResult_ctorElim(v_motive_204_, v_ctorIdx_205_, v_t_206_, v_h_207_, v_k_208_);
lean_dec(v_ctorIdx_205_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim___redArg(lean_object* v_t_210_, lean_object* v_tactic_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_210_, v_tactic_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim(lean_object* v_motive_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_tactic_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_214_, v_tactic_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim___redArg(lean_object* v_t_218_, lean_object* v_tacticSeq_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_218_, v_tacticSeq_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim(lean_object* v_motive_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_tacticSeq_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_222_, v_tacticSeq_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(lean_object* v_range_226_, lean_object* v_stx_227_, lean_object* v_prev_x3f_228_){
_start:
{
uint8_t v___x_229_; lean_object* v___x_230_; 
v___x_229_ = 1;
v___x_230_ = l_Lean_Syntax_getPos_x3f(v_stx_227_, v___x_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v___x_231_; 
lean_dec(v_prev_x3f_228_);
v___x_231_ = lean_box(0);
return v___x_231_;
}
else
{
lean_object* v_val_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_263_; 
v_val_232_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_263_ == 0)
{
v___x_234_ = v___x_230_;
v_isShared_235_ = v_isSharedCheck_263_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_val_232_);
lean_dec(v___x_230_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_263_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___y_237_; 
if (lean_obj_tag(v_prev_x3f_228_) == 0)
{
lean_inc(v_val_232_);
v___y_237_ = v_val_232_;
goto v___jp_236_;
}
else
{
lean_object* v_val_262_; 
v_val_262_ = lean_ctor_get(v_prev_x3f_228_, 0);
lean_inc(v_val_262_);
lean_dec_ref_known(v_prev_x3f_228_, 1);
v___y_237_ = v_val_262_;
goto v___jp_236_;
}
v___jp_236_:
{
lean_object* v_start_238_; lean_object* v_stop_239_; uint8_t v___x_240_; 
v_start_238_ = lean_ctor_get(v_range_226_, 0);
v_stop_239_ = lean_ctor_get(v_range_226_, 1);
v___x_240_ = lean_nat_dec_le(v___y_237_, v_start_238_);
lean_dec(v___y_237_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
lean_del_object(v___x_234_);
lean_dec(v_val_232_);
v___x_241_ = lean_box(0);
return v___x_241_;
}
else
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Syntax_getTailInfo(v_stx_227_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_trailing_243_; lean_object* v_endPos_244_; lean_object* v_startPos_245_; lean_object* v_stopPos_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_trailing_243_ = lean_ctor_get(v___x_242_, 2);
lean_inc_ref(v_trailing_243_);
v_endPos_244_ = lean_ctor_get(v___x_242_, 3);
lean_inc(v_endPos_244_);
lean_dec_ref_known(v___x_242_, 4);
v_startPos_245_ = lean_ctor_get(v_trailing_243_, 1);
lean_inc(v_startPos_245_);
v_stopPos_246_ = lean_ctor_get(v_trailing_243_, 2);
lean_inc(v_stopPos_246_);
lean_dec_ref(v_trailing_243_);
v___x_247_ = lean_nat_sub(v_stopPos_246_, v_startPos_245_);
lean_dec(v_startPos_245_);
lean_dec(v_stopPos_246_);
v___x_248_ = lean_nat_add(v_endPos_244_, v___x_247_);
lean_dec(v___x_247_);
v___x_249_ = lean_nat_dec_le(v_stop_239_, v___x_248_);
lean_dec(v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v_endPos_244_);
lean_del_object(v___x_234_);
lean_dec(v_val_232_);
v___x_250_ = lean_box(0);
return v___x_250_;
}
else
{
uint8_t v___x_251_; 
v___x_251_ = lean_nat_dec_le(v_val_232_, v_start_238_);
lean_dec(v_val_232_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_254_; 
lean_dec(v_endPos_244_);
v___x_252_ = lean_box(v___x_251_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_252_);
v___x_254_ = v___x_234_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
else
{
uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_256_ = lean_nat_dec_le(v_stop_239_, v_endPos_244_);
lean_dec(v_endPos_244_);
v___x_257_ = lean_box(v___x_256_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_257_);
v___x_259_ = v___x_234_;
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
}
}
else
{
lean_object* v___x_261_; 
lean_dec(v___x_242_);
lean_del_object(v___x_234_);
lean_dec(v_val_232_);
v___x_261_ = lean_box(0);
return v___x_261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit___boxed(lean_object* v_range_264_, lean_object* v_stx_265_, lean_object* v_prev_x3f_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_264_, v_stx_265_, v_prev_x3f_266_);
lean_dec(v_stx_265_);
lean_dec_ref(v_range_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(lean_object* v_r_u2081_268_, lean_object* v_r_u2082_269_){
_start:
{
if (lean_obj_tag(v_r_u2081_268_) == 1)
{
lean_object* v_val_270_; 
v_val_270_ = lean_ctor_get(v_r_u2081_268_, 0);
if (lean_obj_tag(v_val_270_) == 1)
{
uint8_t v_preferred_271_; 
v_preferred_271_ = lean_ctor_get_uint8(v_val_270_, sizeof(void*)*2);
if (v_preferred_271_ == 1)
{
if (lean_obj_tag(v_r_u2082_269_) == 1)
{
uint8_t v_preferred_272_; 
v_preferred_272_ = lean_ctor_get_uint8(v_r_u2082_269_, sizeof(void*)*2);
if (v_preferred_272_ == 0)
{
lean_inc_ref(v_val_270_);
return v_val_270_;
}
else
{
lean_inc_ref(v_r_u2082_269_);
return v_r_u2082_269_;
}
}
else
{
lean_inc_ref(v_r_u2082_269_);
return v_r_u2082_269_;
}
}
else
{
lean_inc_ref(v_r_u2082_269_);
return v_r_u2082_269_;
}
}
else
{
lean_inc_ref(v_r_u2082_269_);
return v_r_u2082_269_;
}
}
else
{
lean_inc_ref(v_r_u2082_269_);
return v_r_u2082_269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge___boxed(lean_object* v_r_u2081_273_, lean_object* v_r_u2082_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(v_r_u2081_273_, v_r_u2082_274_);
lean_dec_ref(v_r_u2082_274_);
lean_dec(v_r_u2081_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(lean_object* v_upperBound_279_, lean_object* v___x_280_, lean_object* v_range_281_, lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
lean_object* v_a_285_; uint8_t v___x_289_; 
v___x_289_ = lean_nat_dec_lt(v_a_282_, v_upperBound_279_);
if (v___x_289_ == 0)
{
lean_dec(v_a_282_);
lean_dec_ref(v_range_281_);
lean_inc_ref(v_b_283_);
return v_b_283_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; 
v___x_290_ = lean_box(0);
v___x_291_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0));
v___x_292_ = lean_unsigned_to_nat(2u);
v___x_293_ = lean_nat_mul(v___x_292_, v_a_282_);
v___x_294_ = l_Lean_Syntax_getArg(v___x_280_, v___x_293_);
lean_dec(v___x_293_);
v___x_295_ = 0;
v___x_296_ = l_Lean_Syntax_getPos_x3f(v___x_294_, v___x_295_);
lean_dec(v___x_294_);
if (lean_obj_tag(v___x_296_) == 1)
{
lean_object* v_val_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_317_; 
v_val_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_317_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_317_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_val_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_317_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v_stop_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_stop_301_ = lean_ctor_get(v_range_281_, 1);
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v_stop_301_, v___x_302_);
v___x_304_ = lean_nat_dec_le(v___x_303_, v_val_297_);
lean_dec(v_val_297_);
lean_dec(v___x_303_);
if (v___x_304_ == 0)
{
lean_del_object(v___x_299_);
v_a_285_ = v___x_291_;
goto v___jp_284_;
}
else
{
lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_314_; 
v_isSharedCheck_314_ = !lean_is_exclusive(v_range_281_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; lean_object* v_unused_316_; 
v_unused_315_ = lean_ctor_get(v_range_281_, 1);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_range_281_, 0);
lean_dec(v_unused_316_);
v___x_306_ = v_range_281_;
v_isShared_307_ = v_isSharedCheck_314_;
goto v_resetjp_305_;
}
else
{
lean_dec(v_range_281_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_314_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v_a_282_);
v___x_309_ = v___x_299_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_282_);
v___x_309_ = v_reuseFailAlloc_313_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v___x_290_);
lean_ctor_set(v___x_306_, 0, v___x_309_);
v___x_311_ = v___x_306_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v___x_290_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
}
else
{
lean_dec(v___x_296_);
v_a_285_ = v___x_291_;
goto v___jp_284_;
}
}
v___jp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_a_282_, v___x_286_);
lean_dec(v_a_282_);
v_a_282_ = v___x_287_;
v_b_283_ = v_a_285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___boxed(lean_object* v_upperBound_318_, lean_object* v___x_319_, lean_object* v_range_320_, lean_object* v_a_321_, lean_object* v_b_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_318_, v___x_319_, v_range_320_, v_a_321_, v_b_322_);
lean_dec_ref(v_b_322_);
lean_dec(v___x_319_);
lean_dec(v_upperBound_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(lean_object* v_stx_324_, lean_object* v_a_325_, uint8_t v___x_326_, lean_object* v_snd_327_, lean_object* v_____r_328_, lean_object* v_childRes_329_){
_start:
{
lean_object* v___y_331_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = l_Lean_Syntax_getArg(v_stx_324_, v_a_325_);
v___x_336_ = l_Lean_Syntax_getTailPos_x3f(v___x_335_, v___x_326_);
lean_dec(v___x_335_);
if (lean_obj_tag(v___x_336_) == 0)
{
v___y_331_ = v_snd_327_;
goto v___jp_330_;
}
else
{
lean_dec(v_snd_327_);
v___y_331_ = v___x_336_;
goto v___jp_330_;
}
v___jp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_childRes_329_);
lean_ctor_set(v___x_332_, 1, v___y_331_);
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0___boxed(lean_object* v_stx_337_, lean_object* v_a_338_, lean_object* v___x_339_, lean_object* v_snd_340_, lean_object* v_____r_341_, lean_object* v_childRes_342_){
_start:
{
uint8_t v___x_3799__boxed_343_; lean_object* v_res_344_; 
v___x_3799__boxed_343_ = lean_unbox(v___x_339_);
v_res_344_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_337_, v_a_338_, v___x_3799__boxed_343_, v_snd_340_, v_____r_341_, v_childRes_342_);
lean_dec(v_a_338_);
lean_dec(v_stx_337_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(lean_object* v___y_355_, uint8_t v___x_356_, lean_object* v___x_357_, lean_object* v_range_358_, lean_object* v___x_359_, lean_object* v_preferred_360_, lean_object* v_a_361_, lean_object* v_b_362_){
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
lean_object* v_nextIdx_366_; lean_object* v_n_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_428_; 
v_nextIdx_366_ = lean_ctor_get(v_a_361_, 0);
v_n_367_ = lean_ctor_get(v_a_361_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_a_361_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; 
v_unused_429_ = lean_ctor_get(v_a_361_, 2);
lean_dec(v_unused_429_);
v___x_369_ = v_a_361_;
v_isShared_370_ = v_isSharedCheck_428_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_n_367_);
lean_inc(v_nextIdx_366_);
lean_dec(v_a_361_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_428_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v_upperBound_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_426_; 
v_upperBound_371_ = lean_ctor_get(v_inner_363_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v_inner_363_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; 
v_unused_427_ = lean_ctor_get(v_inner_363_, 0);
lean_dec(v_unused_427_);
v___x_373_ = v_inner_363_;
v_isShared_374_ = v_isSharedCheck_426_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_upperBound_371_);
lean_dec(v_inner_363_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_426_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_val_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_425_; 
v_val_375_ = lean_ctor_get(v_next_364_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_next_364_);
if (v_isSharedCheck_425_ == 0)
{
v___x_377_ = v_next_364_;
v_isShared_378_ = v_isSharedCheck_425_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_val_375_);
lean_dec(v_next_364_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_425_;
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
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_424_;
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
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_upperBound_371_);
v___x_389_ = v_reuseFailAlloc_423_;
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
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_n_367_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_n_367_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v___x_389_);
v___x_391_ = v_reuseFailAlloc_422_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___y_393_; lean_object* v_val_398_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = l_Lean_Syntax_getArg(v___x_357_, v___x_379_);
v___x_401_ = lean_box(0);
v___x_402_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_358_, v___x_400_, v___x_401_);
if (lean_obj_tag(v___x_402_) == 1)
{
lean_object* v_val_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_val_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v___x_402_, 1);
lean_inc(v___x_357_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_357_);
lean_ctor_set(v___x_404_, 1, v___x_379_);
lean_inc(v___x_359_);
v___x_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_359_);
lean_inc(v___x_400_);
lean_inc_ref(v___x_405_);
lean_inc_ref(v_range_358_);
lean_inc_ref(v_preferred_360_);
v___x_406_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_360_, v_range_358_, v___x_405_, v___x_400_, v___x_401_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_dec_ref_known(v___x_405_, 2);
lean_dec(v_val_403_);
lean_dec(v___x_400_);
lean_dec_ref(v___x_391_);
lean_dec(v_b_362_);
lean_dec_ref(v_preferred_360_);
lean_dec(v___x_359_);
lean_dec_ref(v_range_358_);
lean_dec(v___x_357_);
return v___x_406_;
}
else
{
lean_object* v_val_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_420_; 
v_val_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_420_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_420_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_val_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_420_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
if (lean_obj_tag(v_val_407_) == 0)
{
uint8_t v___x_411_; 
v___x_411_ = lean_unbox(v_val_403_);
lean_dec(v_val_403_);
if (v___x_411_ == 0)
{
lean_del_object(v___x_409_);
lean_dec_ref_known(v___x_405_, 2);
lean_dec(v___x_400_);
v_a_361_ = v___x_391_;
goto _start;
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_400_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___x_405_);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 0);
lean_ctor_set(v___x_409_, 0, v___x_415_);
v___x_417_ = v___x_409_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
v_val_398_ = v___x_417_;
goto v___jp_397_;
}
}
}
else
{
lean_object* v_val_419_; 
lean_del_object(v___x_409_);
lean_dec_ref_known(v___x_405_, 2);
lean_dec(v_val_403_);
lean_dec(v___x_400_);
v_val_419_ = lean_ctor_get(v_val_407_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v_val_407_, 1);
v_val_398_ = v_val_419_;
goto v___jp_397_;
}
}
}
}
else
{
lean_dec(v___x_402_);
lean_dec(v___x_400_);
lean_dec(v___x_379_);
v_a_361_ = v___x_391_;
goto _start;
}
v___jp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(v___y_355_, v___y_393_);
lean_dec_ref(v___y_393_);
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
v_a_361_ = v___x_391_;
v_b_362_ = v___x_395_;
goto _start;
}
v___jp_397_:
{
if (lean_obj_tag(v_b_362_) == 0)
{
v___y_393_ = v_val_398_;
goto v___jp_392_;
}
else
{
lean_dec_ref_known(v_b_362_, 1);
if (v___x_356_ == 0)
{
v___y_393_ = v_val_398_;
goto v___jp_392_;
}
else
{
lean_object* v___x_399_; 
lean_dec_ref(v_val_398_);
lean_dec_ref(v___x_391_);
lean_dec_ref(v_preferred_360_);
lean_dec(v___x_359_);
lean_dec_ref(v_range_358_);
lean_dec(v___x_357_);
v___x_399_ = lean_box(0);
return v___x_399_;
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
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(lean_object* v_preferred_436_, lean_object* v_range_437_, lean_object* v_stack_438_, lean_object* v_stx_439_, lean_object* v_prev_x3f_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
lean_inc(v_stx_439_);
v___x_441_ = l_Lean_Syntax_getKind(v_stx_439_);
v___x_442_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3));
v___x_443_ = lean_name_eq(v___x_441_, v___x_442_);
lean_dec(v___x_441_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_childRes_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_444_ = l_Lean_Syntax_getNumArgs(v_stx_439_);
v___x_445_ = lean_unsigned_to_nat(0u);
v_childRes_446_ = lean_box(0);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v_childRes_446_);
lean_ctor_set(v___x_447_, 1, v_prev_x3f_440_);
v___x_448_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v___x_444_, v_stx_439_, v_range_437_, v_stack_438_, v_preferred_436_, v___x_443_, v___x_445_, v___x_447_);
lean_dec(v___x_444_);
if (lean_obj_tag(v___x_448_) == 0)
{
return v_childRes_446_;
}
else
{
lean_object* v_val_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_457_; 
v_val_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_457_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_val_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v_fst_453_; lean_object* v___x_455_; 
v_fst_453_ = lean_ctor_get(v_val_449_, 0);
lean_inc(v_fst_453_);
lean_dec(v_val_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v_fst_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_fst_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v___x_458_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; uint8_t v___y_483_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v_bracket_491_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_500_; 
lean_dec(v_prev_x3f_440_);
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_488_ = l_Lean_Syntax_getArg(v_stx_439_, v___x_458_);
lean_inc(v___x_488_);
v___x_489_ = l_Lean_Syntax_getKind(v___x_488_);
v___x_490_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6));
v_bracket_491_ = lean_name_eq(v___x_489_, v___x_490_);
lean_dec(v___x_489_);
if (v_bracket_491_ == 0)
{
v___y_500_ = v___x_458_;
goto v___jp_499_;
}
else
{
lean_object* v___x_519_; 
v___x_519_ = lean_unsigned_to_nat(1u);
v___y_500_ = v___x_519_;
goto v___jp_499_;
}
v___jp_459_:
{
lean_object* v_childRes_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_childRes_463_ = lean_box(0);
v___x_464_ = l_Lean_Syntax_getNumArgs(v___y_461_);
v___x_465_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4));
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v___x_464_);
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_468_, 0, v___x_458_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
lean_ctor_set(v___x_468_, 2, v___x_466_);
v___x_469_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_462_, v___x_443_, v___y_461_, v_range_437_, v___y_460_, v_preferred_436_, v___x_468_, v_childRes_463_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_dec(v___y_462_);
return v___x_469_;
}
else
{
lean_object* v_val_470_; 
v_val_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_val_470_);
if (lean_obj_tag(v_val_470_) == 0)
{
lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v___x_469_, 0);
lean_dec(v_unused_478_);
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___y_462_);
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___y_462_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
else
{
lean_dec_ref_known(v_val_470_, 1);
lean_dec(v___y_462_);
return v___x_469_;
}
}
}
v___jp_479_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_inc(v___y_482_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___y_482_);
lean_ctor_set(v___x_484_, 1, v___x_458_);
lean_inc(v___y_480_);
v___x_485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___y_480_);
v___x_486_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_486_, 0, v___y_481_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*2, v___y_483_);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
v___y_460_ = v___y_480_;
v___y_461_ = v___y_482_;
v___y_462_ = v___x_487_;
goto v___jp_459_;
}
v___jp_492_:
{
if (v_bracket_491_ == 0)
{
lean_object* v___x_497_; uint8_t v___x_498_; 
lean_inc_ref(v_preferred_436_);
v___x_497_ = lean_apply_1(v_preferred_436_, v___y_495_);
v___x_498_ = lean_unbox(v___x_497_);
v___y_480_ = v___y_493_;
v___y_481_ = v___y_496_;
v___y_482_ = v___y_494_;
v___y_483_ = v___x_498_;
goto v___jp_479_;
}
else
{
lean_dec(v___y_495_);
v___y_480_ = v___y_493_;
v___y_481_ = v___y_496_;
v___y_482_ = v___y_494_;
v___y_483_ = v___x_443_;
goto v___jp_479_;
}
}
v___jp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; 
lean_inc(v___y_500_);
lean_inc(v___x_488_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_488_);
lean_ctor_set(v___x_501_, 1, v___y_500_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v_stx_439_);
lean_ctor_set(v___x_502_, 1, v___x_458_);
v___x_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v_stack_438_);
v___x_504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_501_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = l_Lean_Syntax_getArg(v___x_488_, v___y_500_);
lean_dec(v___y_500_);
lean_dec(v___x_488_);
v___x_506_ = l_Lean_Syntax_getArg(v___x_505_, v___x_458_);
v___x_507_ = 0;
v___x_508_ = l_Lean_Syntax_getPos_x3f(v___x_506_, v___x_507_);
lean_dec(v___x_506_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v___x_509_; 
v___x_509_ = lean_box(0);
v___y_460_ = v___x_504_;
v___y_461_ = v___x_505_;
v___y_462_ = v___x_509_;
goto v___jp_459_;
}
else
{
lean_object* v_val_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_fst_514_; 
v_val_510_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v___x_508_, 1);
v___x_511_ = l_Lean_Syntax_getNumArgs(v___x_505_);
v___x_512_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0));
lean_inc_ref(v_range_437_);
v___x_513_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v___x_511_, v___x_505_, v_range_437_, v___x_458_, v___x_512_);
v_fst_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_fst_514_);
lean_dec_ref(v___x_513_);
if (lean_obj_tag(v_fst_514_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_add(v___x_511_, v___x_515_);
lean_dec(v___x_511_);
v___x_517_ = lean_nat_shiftr(v___x_516_, v___x_515_);
lean_dec(v___x_516_);
v___y_493_ = v___x_504_;
v___y_494_ = v___x_505_;
v___y_495_ = v_val_510_;
v___y_496_ = v___x_517_;
goto v___jp_492_;
}
else
{
lean_object* v_val_518_; 
lean_dec(v___x_511_);
v_val_518_ = lean_ctor_get(v_fst_514_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v_fst_514_, 1);
v___y_493_ = v___x_504_;
v___y_494_ = v___x_505_;
v___y_495_ = v_val_510_;
v___y_496_ = v_val_518_;
goto v___jp_492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(lean_object* v_upperBound_520_, lean_object* v_stx_521_, lean_object* v_range_522_, lean_object* v_stack_523_, lean_object* v_preferred_524_, uint8_t v___x_525_, lean_object* v_a_526_, lean_object* v_b_527_){
_start:
{
lean_object* v___y_529_; uint8_t v___x_544_; 
v___x_544_ = lean_nat_dec_lt(v_a_526_, v_upperBound_520_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; 
lean_dec(v_a_526_);
lean_dec_ref(v_preferred_524_);
lean_dec(v_stack_523_);
lean_dec_ref(v_range_522_);
lean_dec(v_stx_521_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v_b_527_);
return v___x_545_;
}
else
{
lean_object* v_fst_546_; lean_object* v_snd_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_568_; 
v_fst_546_ = lean_ctor_get(v_b_527_, 0);
v_snd_547_ = lean_ctor_get(v_b_527_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_b_527_);
if (v_isSharedCheck_568_ == 0)
{
v___x_549_ = v_b_527_;
v_isShared_550_ = v_isSharedCheck_568_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_snd_547_);
lean_inc(v_fst_546_);
lean_dec(v_b_527_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_568_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = l_Lean_Syntax_getArg(v_stx_521_, v_a_526_);
lean_inc(v_snd_547_);
v___x_552_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_522_, v___x_551_, v_snd_547_);
if (lean_obj_tag(v___x_552_) == 1)
{
lean_object* v___x_554_; 
lean_dec_ref_known(v___x_552_, 1);
lean_inc(v_a_526_);
lean_inc(v_stx_521_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v_a_526_);
lean_ctor_set(v___x_549_, 0, v_stx_521_);
v___x_554_ = v___x_549_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_stx_521_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_a_526_);
v___x_554_ = v_reuseFailAlloc_565_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_inc(v_stack_523_);
v___x_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v_stack_523_);
lean_inc(v_snd_547_);
lean_inc_ref(v_range_522_);
lean_inc_ref(v_preferred_524_);
v___x_556_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_524_, v_range_522_, v___x_555_, v___x_551_, v_snd_547_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v___x_557_; 
lean_dec(v_snd_547_);
lean_dec(v_fst_546_);
lean_dec(v_a_526_);
lean_dec_ref(v_preferred_524_);
lean_dec(v_stack_523_);
lean_dec_ref(v_range_522_);
lean_dec(v_stx_521_);
v___x_557_ = lean_box(0);
return v___x_557_;
}
else
{
lean_object* v_val_558_; 
v_val_558_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_val_558_);
lean_dec_ref_known(v___x_556_, 1);
if (lean_obj_tag(v_val_558_) == 1)
{
if (lean_obj_tag(v_fst_546_) == 0)
{
if (v___x_525_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_box(0);
v___x_560_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_521_, v_a_526_, v___x_544_, v_snd_547_, v___x_559_, v_val_558_);
v___y_529_ = v___x_560_;
goto v___jp_528_;
}
else
{
lean_object* v___x_561_; 
lean_dec_ref_known(v_val_558_, 1);
lean_dec(v_snd_547_);
lean_dec(v_a_526_);
lean_dec_ref(v_preferred_524_);
lean_dec(v_stack_523_);
lean_dec_ref(v_range_522_);
lean_dec(v_stx_521_);
v___x_561_ = lean_box(0);
return v___x_561_;
}
}
else
{
lean_object* v___x_562_; 
lean_dec_ref_known(v_fst_546_, 1);
lean_dec_ref_known(v_val_558_, 1);
lean_dec(v_snd_547_);
lean_dec(v_a_526_);
lean_dec_ref(v_preferred_524_);
lean_dec(v_stack_523_);
lean_dec_ref(v_range_522_);
lean_dec(v_stx_521_);
v___x_562_ = lean_box(0);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v_val_558_);
v___x_563_ = lean_box(0);
v___x_564_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_521_, v_a_526_, v___x_544_, v_snd_547_, v___x_563_, v_fst_546_);
v___y_529_ = v___x_564_;
goto v___jp_528_;
}
}
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec(v___x_552_);
lean_dec(v___x_551_);
lean_del_object(v___x_549_);
v___x_566_ = lean_box(0);
v___x_567_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_521_, v_a_526_, v___x_544_, v_snd_547_, v___x_566_, v_fst_546_);
v___y_529_ = v___x_567_;
goto v___jp_528_;
}
}
}
v___jp_528_:
{
if (lean_obj_tag(v___y_529_) == 0)
{
lean_object* v___x_530_; 
lean_dec(v_a_526_);
lean_dec_ref(v_preferred_524_);
lean_dec(v_stack_523_);
lean_dec_ref(v_range_522_);
lean_dec(v_stx_521_);
v___x_530_ = lean_box(0);
return v___x_530_;
}
else
{
lean_object* v_val_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_543_; 
v_val_531_ = lean_ctor_get(v___y_529_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___y_529_);
if (v_isSharedCheck_543_ == 0)
{
v___x_533_ = v___y_529_;
v_isShared_534_ = v_isSharedCheck_543_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_val_531_);
lean_dec(v___y_529_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_543_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
if (lean_obj_tag(v_val_531_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; 
lean_dec(v_a_526_);
lean_dec_ref(v_preferred_524_);
lean_dec(v_stack_523_);
lean_dec_ref(v_range_522_);
lean_dec(v_stx_521_);
v_a_535_ = lean_ctor_get(v_val_531_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v_val_531_, 1);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v_a_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
lean_del_object(v___x_533_);
v_a_539_ = lean_ctor_get(v_val_531_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v_val_531_, 1);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_add(v_a_526_, v___x_540_);
lean_dec(v_a_526_);
v_a_526_ = v___x_541_;
v_b_527_ = v_a_539_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_569_, lean_object* v_stx_570_, lean_object* v_range_571_, lean_object* v_stack_572_, lean_object* v_preferred_573_, lean_object* v___x_574_, lean_object* v_a_575_, lean_object* v_b_576_){
_start:
{
uint8_t v___x_3841__boxed_577_; lean_object* v_res_578_; 
v___x_3841__boxed_577_ = lean_unbox(v___x_574_);
v_res_578_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_569_, v_stx_570_, v_range_571_, v_stack_572_, v_preferred_573_, v___x_3841__boxed_577_, v_a_575_, v_b_576_);
lean_dec(v_upperBound_569_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg___boxed(lean_object* v___y_579_, lean_object* v___x_580_, lean_object* v___x_581_, lean_object* v_range_582_, lean_object* v___x_583_, lean_object* v_preferred_584_, lean_object* v_a_585_, lean_object* v_b_586_){
_start:
{
uint8_t v___x_3872__boxed_587_; lean_object* v_res_588_; 
v___x_3872__boxed_587_ = lean_unbox(v___x_580_);
v_res_588_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_579_, v___x_3872__boxed_587_, v___x_581_, v_range_582_, v___x_583_, v_preferred_584_, v_a_585_, v_b_586_);
lean_dec(v___y_579_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(lean_object* v_upperBound_589_, lean_object* v_stx_590_, lean_object* v_range_591_, lean_object* v_stack_592_, lean_object* v_preferred_593_, uint8_t v___x_594_, lean_object* v_inst_595_, lean_object* v_R_596_, lean_object* v_a_597_, lean_object* v_b_598_, lean_object* v_c_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_589_, v_stx_590_, v_range_591_, v_stack_592_, v_preferred_593_, v___x_594_, v_a_597_, v_b_598_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___boxed(lean_object* v_upperBound_601_, lean_object* v_stx_602_, lean_object* v_range_603_, lean_object* v_stack_604_, lean_object* v_preferred_605_, lean_object* v___x_606_, lean_object* v_inst_607_, lean_object* v_R_608_, lean_object* v_a_609_, lean_object* v_b_610_, lean_object* v_c_611_){
_start:
{
uint8_t v___x_4244__boxed_612_; lean_object* v_res_613_; 
v___x_4244__boxed_612_ = lean_unbox(v___x_606_);
v_res_613_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(v_upperBound_601_, v_stx_602_, v_range_603_, v_stack_604_, v_preferred_605_, v___x_4244__boxed_612_, v_inst_607_, v_R_608_, v_a_609_, v_b_610_, v_c_611_);
lean_dec(v_upperBound_601_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(lean_object* v___y_614_, uint8_t v___x_615_, lean_object* v___x_616_, lean_object* v_range_617_, lean_object* v___x_618_, lean_object* v_preferred_619_, lean_object* v_inst_620_, lean_object* v_R_621_, lean_object* v_a_622_, lean_object* v_b_623_, lean_object* v_c_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_614_, v___x_615_, v___x_616_, v_range_617_, v___x_618_, v_preferred_619_, v_a_622_, v_b_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___boxed(lean_object* v___y_626_, lean_object* v___x_627_, lean_object* v___x_628_, lean_object* v_range_629_, lean_object* v___x_630_, lean_object* v_preferred_631_, lean_object* v_inst_632_, lean_object* v_R_633_, lean_object* v_a_634_, lean_object* v_b_635_, lean_object* v_c_636_){
_start:
{
uint8_t v___x_4255__boxed_637_; lean_object* v_res_638_; 
v___x_4255__boxed_637_ = lean_unbox(v___x_627_);
v_res_638_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(v___y_626_, v___x_4255__boxed_637_, v___x_628_, v_range_629_, v___x_630_, v_preferred_631_, v_inst_632_, v_R_633_, v_a_634_, v_b_635_, v_c_636_);
lean_dec(v___y_626_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(lean_object* v_upperBound_639_, lean_object* v___x_640_, lean_object* v_range_641_, lean_object* v_inst_642_, lean_object* v_R_643_, lean_object* v_a_644_, lean_object* v_b_645_, lean_object* v_c_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_639_, v___x_640_, v_range_641_, v_a_644_, v_b_645_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___boxed(lean_object* v_upperBound_648_, lean_object* v___x_649_, lean_object* v_range_650_, lean_object* v_inst_651_, lean_object* v_R_652_, lean_object* v_a_653_, lean_object* v_b_654_, lean_object* v_c_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(v_upperBound_648_, v___x_649_, v_range_650_, v_inst_651_, v_R_652_, v_a_653_, v_b_654_, v_c_655_);
lean_dec_ref(v_b_654_);
lean_dec(v___x_649_);
lean_dec(v_upperBound_648_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findTactic_x3f(lean_object* v_preferred_657_, lean_object* v_range_658_, lean_object* v_root_659_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_box(0);
v___x_661_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_658_, v_root_659_, v___x_660_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_dec(v_root_659_);
lean_dec_ref(v_range_658_);
lean_dec_ref(v_preferred_657_);
return v___x_660_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec_ref_known(v___x_661_, 1);
v___x_662_ = lean_box(0);
v___x_663_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_657_, v_range_658_, v___x_662_, v_root_659_, v___x_660_);
if (lean_obj_tag(v___x_663_) == 0)
{
return v___x_660_;
}
else
{
lean_object* v_val_664_; 
v_val_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v___x_663_, 1);
return v_val_664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(lean_object* v_ctx_x3f_677_, lean_object* v_i_678_, lean_object* v_kind_679_, lean_object* v_tgtRange_680_, lean_object* v_f_681_, uint8_t v_canonicalOnly_682_, lean_object* v_as_683_, size_t v_sz_684_, size_t v_i_685_, lean_object* v_b_686_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = lean_usize_dec_lt(v_i_685_, v_sz_684_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
lean_dec_ref(v_f_681_);
lean_dec(v_ctx_x3f_677_);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v_b_686_);
return v___x_688_;
}
else
{
lean_object* v_snd_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_714_; 
v_snd_689_ = lean_ctor_get(v_b_686_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_b_686_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v_b_686_, 0);
lean_dec(v_unused_715_);
v___x_691_ = v_b_686_;
v_isShared_692_ = v_isSharedCheck_714_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_snd_689_);
lean_dec(v_b_686_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_714_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_693_ = lean_box(0);
v_a_694_ = lean_array_uget_borrowed(v_as_683_, v_i_685_);
lean_inc(v_ctx_x3f_677_);
v___x_695_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_677_, v_i_678_);
lean_inc_ref(v_f_681_);
lean_inc(v_a_694_);
v___x_696_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_679_, v_tgtRange_680_, v___x_695_, v_a_694_, v_f_681_, v_canonicalOnly_682_);
if (lean_obj_tag(v___x_696_) == 1)
{
lean_object* v___x_698_; 
lean_dec_ref(v_f_681_);
lean_dec(v_ctx_x3f_677_);
lean_inc_ref(v___x_696_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v___x_693_);
lean_ctor_set(v___x_691_, 0, v___x_696_);
v___x_698_ = v___x_691_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_693_);
v___x_698_ = v_reuseFailAlloc_709_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_707_; 
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v___x_696_, 0);
lean_dec(v_unused_708_);
v___x_700_ = v___x_696_;
v_isShared_701_ = v_isSharedCheck_707_;
goto v_resetjp_699_;
}
else
{
lean_dec(v___x_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_707_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_698_);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_698_);
v___x_703_ = v_reuseFailAlloc_706_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_snd_689_);
v___x_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
}
}
else
{
lean_object* v___x_710_; size_t v___x_711_; size_t v___x_712_; 
lean_dec(v___x_696_);
lean_del_object(v___x_691_);
lean_dec(v_snd_689_);
v___x_710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1));
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_add(v_i_685_, v___x_711_);
v_i_685_ = v___x_712_;
v_b_686_ = v___x_710_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(lean_object* v_ctx_x3f_716_, lean_object* v_i_717_, lean_object* v_kind_718_, lean_object* v_tgtRange_719_, lean_object* v_f_720_, uint8_t v_canonicalOnly_721_, lean_object* v_as_722_, size_t v_sz_723_, size_t v_i_724_, lean_object* v_b_725_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = lean_usize_dec_lt(v_i_724_, v_sz_723_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec_ref(v_f_720_);
lean_dec(v_ctx_x3f_716_);
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v_b_725_);
return v___x_727_;
}
else
{
lean_object* v_snd_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_753_; 
v_snd_728_ = lean_ctor_get(v_b_725_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_b_725_);
if (v_isSharedCheck_753_ == 0)
{
lean_object* v_unused_754_; 
v_unused_754_ = lean_ctor_get(v_b_725_, 0);
lean_dec(v_unused_754_);
v___x_730_ = v_b_725_;
v_isShared_731_ = v_isSharedCheck_753_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_snd_728_);
lean_dec(v_b_725_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_753_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v_a_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_732_ = lean_box(0);
v_a_733_ = lean_array_uget_borrowed(v_as_722_, v_i_724_);
lean_inc(v_ctx_x3f_716_);
v___x_734_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_716_, v_i_717_);
lean_inc_ref(v_f_720_);
lean_inc(v_a_733_);
v___x_735_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_718_, v_tgtRange_719_, v___x_734_, v_a_733_, v_f_720_, v_canonicalOnly_721_);
if (lean_obj_tag(v___x_735_) == 1)
{
lean_object* v___x_737_; 
lean_dec_ref(v_f_720_);
lean_dec(v_ctx_x3f_716_);
lean_inc_ref(v___x_735_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_732_);
lean_ctor_set(v___x_730_, 0, v___x_735_);
v___x_737_ = v___x_730_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_732_);
v___x_737_ = v_reuseFailAlloc_748_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_746_; 
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v___x_735_, 0);
lean_dec(v_unused_747_);
v___x_739_ = v___x_735_;
v_isShared_740_ = v_isSharedCheck_746_;
goto v_resetjp_738_;
}
else
{
lean_dec(v___x_735_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_746_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_737_);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_737_);
v___x_742_ = v_reuseFailAlloc_745_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v_snd_728_);
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
}
}
else
{
lean_object* v___x_749_; size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
lean_dec(v___x_735_);
lean_del_object(v___x_730_);
lean_dec(v_snd_728_);
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1));
v___x_750_ = ((size_t)1ULL);
v___x_751_ = lean_usize_add(v_i_724_, v___x_750_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_716_, v_i_717_, v_kind_718_, v_tgtRange_719_, v_f_720_, v_canonicalOnly_721_, v_as_722_, v_sz_723_, v___x_751_, v___x_749_);
return v___x_752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(lean_object* v_ctx_x3f_755_, lean_object* v_i_756_, lean_object* v_kind_757_, lean_object* v_tgtRange_758_, lean_object* v_f_759_, uint8_t v_canonicalOnly_760_, lean_object* v_t_761_, lean_object* v_init_762_){
_start:
{
lean_object* v_root_763_; lean_object* v_tail_764_; lean_object* v___x_765_; 
v_root_763_ = lean_ctor_get(v_t_761_, 0);
v_tail_764_ = lean_ctor_get(v_t_761_, 1);
lean_inc_ref(v_f_759_);
lean_inc(v_ctx_x3f_755_);
lean_inc_ref(v_init_762_);
v___x_765_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_762_, v_ctx_x3f_755_, v_i_756_, v_kind_757_, v_tgtRange_758_, v_f_759_, v_canonicalOnly_760_, v_root_763_, v_init_762_);
lean_dec_ref(v_init_762_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v___x_766_; 
lean_dec_ref(v_f_759_);
lean_dec(v_ctx_x3f_755_);
v___x_766_ = lean_box(0);
return v___x_766_;
}
else
{
lean_object* v_val_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_791_; 
v_val_767_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_791_ == 0)
{
v___x_769_ = v___x_765_;
v_isShared_770_ = v_isSharedCheck_791_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_val_767_);
lean_dec(v___x_765_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_791_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
if (lean_obj_tag(v_val_767_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; 
lean_dec_ref(v_f_759_);
lean_dec(v_ctx_x3f_755_);
v_a_771_ = lean_ctor_get(v_val_767_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v_val_767_, 1);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v_a_771_);
v___x_773_ = v___x_769_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_776_; lean_object* v___x_777_; size_t v_sz_778_; size_t v___x_779_; lean_object* v___x_780_; 
lean_del_object(v___x_769_);
v_a_775_ = lean_ctor_get(v_val_767_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v_val_767_, 1);
v___x_776_ = lean_box(0);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v_a_775_);
v_sz_778_ = lean_array_size(v_tail_764_);
v___x_779_ = ((size_t)0ULL);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_755_, v_i_756_, v_kind_757_, v_tgtRange_758_, v_f_759_, v_canonicalOnly_760_, v_tail_764_, v_sz_778_, v___x_779_, v___x_777_);
if (lean_obj_tag(v___x_780_) == 0)
{
return v___x_776_;
}
else
{
lean_object* v_val_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_790_; 
v_val_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_790_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_790_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_val_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_790_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_fst_785_; 
v_fst_785_ = lean_ctor_get(v_val_781_, 0);
if (lean_obj_tag(v_fst_785_) == 0)
{
lean_object* v_snd_786_; lean_object* v___x_788_; 
v_snd_786_ = lean_ctor_get(v_val_781_, 1);
lean_inc(v_snd_786_);
lean_dec(v_val_781_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v_snd_786_);
v___x_788_ = v___x_783_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_snd_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
else
{
lean_inc_ref(v_fst_785_);
lean_del_object(v___x_783_);
lean_dec(v_val_781_);
return v_fst_785_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f(lean_object* v_kind_792_, lean_object* v_tgtRange_793_, lean_object* v_ctx_x3f_794_, lean_object* v_t_795_, lean_object* v_f_796_, uint8_t v_canonicalOnly_797_){
_start:
{
switch(lean_obj_tag(v_t_795_))
{
case 0:
{
lean_object* v_i_798_; lean_object* v_t_799_; lean_object* v___x_800_; 
v_i_798_ = lean_ctor_get(v_t_795_, 0);
lean_inc_ref(v_i_798_);
v_t_799_ = lean_ctor_get(v_t_795_, 1);
lean_inc_ref(v_t_799_);
lean_dec_ref_known(v_t_795_, 2);
v___x_800_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_798_, v_ctx_x3f_794_);
v_ctx_x3f_794_ = v___x_800_;
v_t_795_ = v_t_799_;
goto _start;
}
case 1:
{
lean_object* v_i_802_; lean_object* v_children_803_; 
v_i_802_ = lean_ctor_get(v_t_795_, 0);
v_children_803_ = lean_ctor_get(v_t_795_, 1);
if (lean_obj_tag(v_ctx_x3f_794_) == 1)
{
lean_object* v_val_810_; uint8_t v___y_812_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_val_810_ = lean_ctor_get(v_ctx_x3f_794_, 0);
v___x_824_ = l_Lean_Elab_Info_stx(v_i_802_);
v___x_825_ = l_Lean_Syntax_getRange_x3f(v___x_824_, v_canonicalOnly_797_);
if (lean_obj_tag(v___x_825_) == 1)
{
lean_object* v_val_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_val_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v___x_825_, 1);
v___x_827_ = l_Lean_Syntax_getKind(v___x_824_);
v___x_828_ = lean_name_eq(v___x_827_, v_kind_792_);
lean_dec(v___x_827_);
if (v___x_828_ == 0)
{
lean_dec(v_val_826_);
v___y_812_ = v___x_828_;
goto v___jp_811_;
}
else
{
uint8_t v___x_829_; 
v___x_829_ = l_Lean_Syntax_instBEqRange_beq(v_val_826_, v_tgtRange_793_);
lean_dec(v_val_826_);
v___y_812_ = v___x_829_;
goto v___jp_811_;
}
}
else
{
lean_inc_ref(v_children_803_);
lean_inc_ref(v_i_802_);
lean_dec(v___x_825_);
lean_dec(v___x_824_);
lean_dec_ref_known(v_t_795_, 2);
goto v___jp_804_;
}
v___jp_811_:
{
if (v___y_812_ == 0)
{
lean_inc_ref(v_children_803_);
lean_inc_ref(v_i_802_);
lean_dec_ref_known(v_t_795_, 2);
goto v___jp_804_;
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
lean_inc_ref(v_f_796_);
lean_inc_ref(v_i_802_);
lean_inc(v_val_810_);
v___x_813_ = lean_apply_2(v_f_796_, v_val_810_, v_i_802_);
v___x_814_ = lean_unbox(v___x_813_);
if (v___x_814_ == 0)
{
lean_inc_ref(v_children_803_);
lean_inc_ref(v_i_802_);
lean_dec_ref_known(v_t_795_, 2);
goto v___jp_804_;
}
else
{
lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_822_; 
lean_inc(v_val_810_);
lean_dec_ref(v_f_796_);
v_isSharedCheck_822_ = !lean_is_exclusive(v_ctx_x3f_794_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_ctx_x3f_794_, 0);
lean_dec(v_unused_823_);
v___x_816_ = v_ctx_x3f_794_;
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
else
{
lean_dec(v_ctx_x3f_794_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_val_810_);
lean_ctor_set(v___x_818_, 1, v_t_795_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_818_);
v___x_820_ = v___x_816_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
}
else
{
lean_inc_ref(v_children_803_);
lean_inc_ref(v_i_802_);
lean_dec_ref_known(v_t_795_, 2);
goto v___jp_804_;
}
v___jp_804_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = lean_box(0);
v___x_806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0));
v___x_807_ = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(v_ctx_x3f_794_, v_i_802_, v_kind_792_, v_tgtRange_793_, v_f_796_, v_canonicalOnly_797_, v_children_803_, v___x_806_);
lean_dec_ref(v_children_803_);
lean_dec_ref(v_i_802_);
if (lean_obj_tag(v___x_807_) == 0)
{
return v___x_805_;
}
else
{
lean_object* v_val_808_; lean_object* v_fst_809_; 
v_val_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_val_808_);
lean_dec_ref_known(v___x_807_, 1);
v_fst_809_ = lean_ctor_get(v_val_808_, 0);
lean_inc(v_fst_809_);
lean_dec(v_val_808_);
if (lean_obj_tag(v_fst_809_) == 0)
{
return v___x_805_;
}
else
{
return v_fst_809_;
}
}
}
}
default: 
{
lean_object* v___x_830_; 
lean_dec_ref(v_f_796_);
lean_dec_ref(v_t_795_);
lean_dec(v_ctx_x3f_794_);
v___x_830_ = lean_box(0);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_ctx_x3f_840_, lean_object* v_i_841_, lean_object* v_kind_842_, lean_object* v_tgtRange_843_, lean_object* v_f_844_, uint8_t v_canonicalOnly_845_, lean_object* v_as_846_, size_t v_sz_847_, size_t v_i_848_, lean_object* v_b_849_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = lean_usize_dec_lt(v_i_848_, v_sz_847_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_dec_ref(v_f_844_);
lean_dec(v_ctx_x3f_840_);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v_b_849_);
return v___x_851_;
}
else
{
lean_object* v_snd_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_878_; 
v_snd_852_ = lean_ctor_get(v_b_849_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_b_849_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; 
v_unused_879_ = lean_ctor_get(v_b_849_, 0);
lean_dec(v_unused_879_);
v___x_854_ = v_b_849_;
v_isShared_855_ = v_isSharedCheck_878_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_snd_852_);
lean_dec(v_b_849_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_878_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_856_ = lean_box(0);
v_a_857_ = lean_array_uget_borrowed(v_as_846_, v_i_848_);
lean_inc(v_ctx_x3f_840_);
v___x_858_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_840_, v_i_841_);
lean_inc_ref(v_f_844_);
lean_inc(v_a_857_);
v___x_859_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_842_, v_tgtRange_843_, v___x_858_, v_a_857_, v_f_844_, v_canonicalOnly_845_);
if (lean_obj_tag(v___x_859_) == 1)
{
lean_object* v___x_861_; 
lean_dec_ref(v_f_844_);
lean_dec(v_ctx_x3f_840_);
lean_inc_ref(v___x_859_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_856_);
lean_ctor_set(v___x_854_, 0, v___x_859_);
v___x_861_ = v___x_854_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_856_);
v___x_861_ = v_reuseFailAlloc_873_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_871_; 
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_859_, 0);
lean_dec(v_unused_872_);
v___x_863_ = v___x_859_;
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
else
{
lean_dec(v___x_859_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_871_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_861_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v_snd_852_);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
}
}
else
{
lean_object* v___x_874_; size_t v___x_875_; size_t v___x_876_; 
lean_dec(v___x_859_);
lean_del_object(v___x_854_);
lean_dec(v_snd_852_);
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_add(v_i_848_, v___x_875_);
v_i_848_ = v___x_876_;
v_b_849_ = v___x_874_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(lean_object* v_ctx_x3f_880_, lean_object* v_i_881_, lean_object* v_kind_882_, lean_object* v_tgtRange_883_, lean_object* v_f_884_, uint8_t v_canonicalOnly_885_, lean_object* v_as_886_, size_t v_sz_887_, size_t v_i_888_, lean_object* v_b_889_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = lean_usize_dec_lt(v_i_888_, v_sz_887_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_dec_ref(v_f_884_);
lean_dec(v_ctx_x3f_880_);
v___x_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_891_, 0, v_b_889_);
return v___x_891_;
}
else
{
lean_object* v_snd_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_918_; 
v_snd_892_ = lean_ctor_get(v_b_889_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_b_889_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v_b_889_, 0);
lean_dec(v_unused_919_);
v___x_894_ = v_b_889_;
v_isShared_895_ = v_isSharedCheck_918_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_snd_892_);
lean_dec(v_b_889_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_918_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_896_ = lean_box(0);
v_a_897_ = lean_array_uget_borrowed(v_as_886_, v_i_888_);
lean_inc(v_ctx_x3f_880_);
v___x_898_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_880_, v_i_881_);
lean_inc_ref(v_f_884_);
lean_inc(v_a_897_);
v___x_899_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_882_, v_tgtRange_883_, v___x_898_, v_a_897_, v_f_884_, v_canonicalOnly_885_);
if (lean_obj_tag(v___x_899_) == 1)
{
lean_object* v___x_901_; 
lean_dec_ref(v_f_884_);
lean_dec(v_ctx_x3f_880_);
lean_inc_ref(v___x_899_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v___x_896_);
lean_ctor_set(v___x_894_, 0, v___x_899_);
v___x_901_ = v___x_894_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_896_);
v___x_901_ = v_reuseFailAlloc_913_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_911_; 
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v___x_899_, 0);
lean_dec(v_unused_912_);
v___x_903_ = v___x_899_;
v_isShared_904_ = v_isSharedCheck_911_;
goto v_resetjp_902_;
}
else
{
lean_dec(v___x_899_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_911_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set_tag(v___x_903_, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_901_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v_snd_892_);
v___x_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
}
}
else
{
lean_object* v___x_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; 
lean_dec(v___x_899_);
lean_del_object(v___x_894_);
lean_dec(v_snd_892_);
v___x_914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0));
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_888_, v___x_915_);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_880_, v_i_881_, v_kind_882_, v_tgtRange_883_, v_f_884_, v_canonicalOnly_885_, v_as_886_, v_sz_887_, v___x_916_, v___x_914_);
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(lean_object* v_init_920_, lean_object* v_ctx_x3f_921_, lean_object* v_i_922_, lean_object* v_kind_923_, lean_object* v_tgtRange_924_, lean_object* v_f_925_, uint8_t v_canonicalOnly_926_, lean_object* v_n_927_, lean_object* v_b_928_){
_start:
{
if (lean_obj_tag(v_n_927_) == 0)
{
lean_object* v_cs_929_; lean_object* v___x_930_; lean_object* v___x_931_; size_t v_sz_932_; size_t v___x_933_; lean_object* v___x_934_; 
v_cs_929_ = lean_ctor_get(v_n_927_, 0);
v___x_930_ = lean_box(0);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v_b_928_);
v_sz_932_ = lean_array_size(v_cs_929_);
v___x_933_ = ((size_t)0ULL);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_920_, v_ctx_x3f_921_, v_i_922_, v_kind_923_, v_tgtRange_924_, v_f_925_, v_canonicalOnly_926_, v_cs_929_, v_sz_932_, v___x_933_, v___x_931_);
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
else
{
lean_object* v_vs_946_; lean_object* v___x_947_; lean_object* v___x_948_; size_t v_sz_949_; size_t v___x_950_; lean_object* v___x_951_; 
v_vs_946_ = lean_ctor_get(v_n_927_, 0);
v___x_947_ = lean_box(0);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v_b_928_);
v_sz_949_ = lean_array_size(v_vs_946_);
v___x_950_ = ((size_t)0ULL);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_921_, v_i_922_, v_kind_923_, v_tgtRange_924_, v_f_925_, v_canonicalOnly_926_, v_vs_946_, v_sz_949_, v___x_950_, v___x_948_);
if (lean_obj_tag(v___x_951_) == 0)
{
return v___x_947_;
}
else
{
lean_object* v_val_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_962_; 
v_val_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_962_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_962_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_val_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_962_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_fst_956_; 
v_fst_956_ = lean_ctor_get(v_val_952_, 0);
if (lean_obj_tag(v_fst_956_) == 0)
{
lean_object* v_snd_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v_snd_957_ = lean_ctor_get(v_val_952_, 1);
lean_inc(v_snd_957_);
lean_dec(v_val_952_);
v___x_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_958_, 0, v_snd_957_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_958_);
v___x_960_ = v___x_954_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
else
{
lean_inc_ref(v_fst_956_);
lean_del_object(v___x_954_);
lean_dec(v_val_952_);
return v_fst_956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(lean_object* v_init_963_, lean_object* v_ctx_x3f_964_, lean_object* v_i_965_, lean_object* v_kind_966_, lean_object* v_tgtRange_967_, lean_object* v_f_968_, uint8_t v_canonicalOnly_969_, lean_object* v_as_970_, size_t v_sz_971_, size_t v_i_972_, lean_object* v_b_973_){
_start:
{
uint8_t v___x_974_; 
v___x_974_ = lean_usize_dec_lt(v_i_972_, v_sz_971_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
lean_dec_ref(v_f_968_);
lean_dec(v_ctx_x3f_964_);
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v_b_973_);
return v___x_975_;
}
else
{
lean_object* v_snd_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1003_; 
v_snd_976_ = lean_ctor_get(v_b_973_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_b_973_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v_b_973_, 0);
lean_dec(v_unused_1004_);
v___x_978_ = v_b_973_;
v_isShared_979_ = v_isSharedCheck_1003_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_snd_976_);
lean_dec(v_b_973_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1003_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_980_ = lean_array_uget_borrowed(v_as_970_, v_i_972_);
lean_inc(v_snd_976_);
lean_inc_ref(v_f_968_);
lean_inc(v_ctx_x3f_964_);
v___x_981_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_963_, v_ctx_x3f_964_, v_i_965_, v_kind_966_, v_tgtRange_967_, v_f_968_, v_canonicalOnly_969_, v_a_980_, v_snd_976_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v___x_982_; 
lean_del_object(v___x_978_);
lean_dec(v_snd_976_);
lean_dec_ref(v_f_968_);
lean_dec(v_ctx_x3f_964_);
v___x_982_ = lean_box(0);
return v___x_982_;
}
else
{
lean_object* v_val_983_; 
v_val_983_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_val_983_);
if (lean_obj_tag(v_val_983_) == 0)
{
lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_993_; 
lean_dec_ref(v_f_968_);
lean_dec(v_ctx_x3f_964_);
v_isSharedCheck_993_ = !lean_is_exclusive(v_val_983_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v_val_983_, 0);
lean_dec(v_unused_994_);
v___x_985_ = v_val_983_;
v_isShared_986_ = v_isSharedCheck_993_;
goto v_resetjp_984_;
}
else
{
lean_dec(v_val_983_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_993_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_981_);
v___x_988_ = v___x_978_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_snd_976_);
v___x_988_ = v_reuseFailAlloc_992_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 1);
lean_ctor_set(v___x_985_, 0, v___x_988_);
v___x_990_ = v___x_985_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
lean_dec_ref_known(v___x_981_, 1);
lean_dec(v_snd_976_);
v_a_995_ = lean_ctor_get(v_val_983_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v_val_983_, 1);
v___x_996_ = lean_box(0);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v_a_995_);
lean_ctor_set(v___x_978_, 0, v___x_996_);
v___x_998_ = v___x_978_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_a_995_);
v___x_998_ = v_reuseFailAlloc_1002_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
size_t v___x_999_; size_t v___x_1000_; 
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_add(v_i_972_, v___x_999_);
v_i_972_ = v___x_1000_;
v_b_973_ = v___x_998_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1005_, lean_object* v_ctx_x3f_1006_, lean_object* v_i_1007_, lean_object* v_kind_1008_, lean_object* v_tgtRange_1009_, lean_object* v_f_1010_, lean_object* v_canonicalOnly_1011_, lean_object* v_as_1012_, lean_object* v_sz_1013_, lean_object* v_i_1014_, lean_object* v_b_1015_){
_start:
{
uint8_t v_canonicalOnly_boxed_1016_; size_t v_sz_boxed_1017_; size_t v_i_boxed_1018_; lean_object* v_res_1019_; 
v_canonicalOnly_boxed_1016_ = lean_unbox(v_canonicalOnly_1011_);
v_sz_boxed_1017_ = lean_unbox_usize(v_sz_1013_);
lean_dec(v_sz_1013_);
v_i_boxed_1018_ = lean_unbox_usize(v_i_1014_);
lean_dec(v_i_1014_);
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_1005_, v_ctx_x3f_1006_, v_i_1007_, v_kind_1008_, v_tgtRange_1009_, v_f_1010_, v_canonicalOnly_boxed_1016_, v_as_1012_, v_sz_boxed_1017_, v_i_boxed_1018_, v_b_1015_);
lean_dec_ref(v_as_1012_);
lean_dec_ref(v_tgtRange_1009_);
lean_dec(v_kind_1008_);
lean_dec_ref(v_i_1007_);
lean_dec_ref(v_init_1005_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0___boxed(lean_object* v_ctx_x3f_1020_, lean_object* v_i_1021_, lean_object* v_kind_1022_, lean_object* v_tgtRange_1023_, lean_object* v_f_1024_, lean_object* v_canonicalOnly_1025_, lean_object* v_t_1026_, lean_object* v_init_1027_){
_start:
{
uint8_t v_canonicalOnly_boxed_1028_; lean_object* v_res_1029_; 
v_canonicalOnly_boxed_1028_ = lean_unbox(v_canonicalOnly_1025_);
v_res_1029_ = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(v_ctx_x3f_1020_, v_i_1021_, v_kind_1022_, v_tgtRange_1023_, v_f_1024_, v_canonicalOnly_boxed_1028_, v_t_1026_, v_init_1027_);
lean_dec_ref(v_t_1026_);
lean_dec_ref(v_tgtRange_1023_);
lean_dec(v_kind_1022_);
lean_dec_ref(v_i_1021_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___boxed(lean_object* v_ctx_x3f_1030_, lean_object* v_i_1031_, lean_object* v_kind_1032_, lean_object* v_tgtRange_1033_, lean_object* v_f_1034_, lean_object* v_canonicalOnly_1035_, lean_object* v_as_1036_, lean_object* v_sz_1037_, lean_object* v_i_1038_, lean_object* v_b_1039_){
_start:
{
uint8_t v_canonicalOnly_boxed_1040_; size_t v_sz_boxed_1041_; size_t v_i_boxed_1042_; lean_object* v_res_1043_; 
v_canonicalOnly_boxed_1040_ = lean_unbox(v_canonicalOnly_1035_);
v_sz_boxed_1041_ = lean_unbox_usize(v_sz_1037_);
lean_dec(v_sz_1037_);
v_i_boxed_1042_ = lean_unbox_usize(v_i_1038_);
lean_dec(v_i_1038_);
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_1030_, v_i_1031_, v_kind_1032_, v_tgtRange_1033_, v_f_1034_, v_canonicalOnly_boxed_1040_, v_as_1036_, v_sz_boxed_1041_, v_i_boxed_1042_, v_b_1039_);
lean_dec_ref(v_as_1036_);
lean_dec_ref(v_tgtRange_1033_);
lean_dec(v_kind_1032_);
lean_dec_ref(v_i_1031_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_ctx_x3f_1044_, lean_object* v_i_1045_, lean_object* v_kind_1046_, lean_object* v_tgtRange_1047_, lean_object* v_f_1048_, lean_object* v_canonicalOnly_1049_, lean_object* v_as_1050_, lean_object* v_sz_1051_, lean_object* v_i_1052_, lean_object* v_b_1053_){
_start:
{
uint8_t v_canonicalOnly_boxed_1054_; size_t v_sz_boxed_1055_; size_t v_i_boxed_1056_; lean_object* v_res_1057_; 
v_canonicalOnly_boxed_1054_ = lean_unbox(v_canonicalOnly_1049_);
v_sz_boxed_1055_ = lean_unbox_usize(v_sz_1051_);
lean_dec(v_sz_1051_);
v_i_boxed_1056_ = lean_unbox_usize(v_i_1052_);
lean_dec(v_i_1052_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_1044_, v_i_1045_, v_kind_1046_, v_tgtRange_1047_, v_f_1048_, v_canonicalOnly_boxed_1054_, v_as_1050_, v_sz_boxed_1055_, v_i_boxed_1056_, v_b_1053_);
lean_dec_ref(v_as_1050_);
lean_dec_ref(v_tgtRange_1047_);
lean_dec(v_kind_1046_);
lean_dec_ref(v_i_1045_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_ctx_x3f_1058_, lean_object* v_i_1059_, lean_object* v_kind_1060_, lean_object* v_tgtRange_1061_, lean_object* v_f_1062_, lean_object* v_canonicalOnly_1063_, lean_object* v_as_1064_, lean_object* v_sz_1065_, lean_object* v_i_1066_, lean_object* v_b_1067_){
_start:
{
uint8_t v_canonicalOnly_boxed_1068_; size_t v_sz_boxed_1069_; size_t v_i_boxed_1070_; lean_object* v_res_1071_; 
v_canonicalOnly_boxed_1068_ = lean_unbox(v_canonicalOnly_1063_);
v_sz_boxed_1069_ = lean_unbox_usize(v_sz_1065_);
lean_dec(v_sz_1065_);
v_i_boxed_1070_ = lean_unbox_usize(v_i_1066_);
lean_dec(v_i_1066_);
v_res_1071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_1058_, v_i_1059_, v_kind_1060_, v_tgtRange_1061_, v_f_1062_, v_canonicalOnly_boxed_1068_, v_as_1064_, v_sz_boxed_1069_, v_i_boxed_1070_, v_b_1067_);
lean_dec_ref(v_as_1064_);
lean_dec_ref(v_tgtRange_1061_);
lean_dec(v_kind_1060_);
lean_dec_ref(v_i_1059_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_ctx_x3f_1072_, lean_object* v_i_1073_, lean_object* v_kind_1074_, lean_object* v_tgtRange_1075_, lean_object* v_f_1076_, lean_object* v_canonicalOnly_1077_, lean_object* v_as_1078_, lean_object* v_sz_1079_, lean_object* v_i_1080_, lean_object* v_b_1081_){
_start:
{
uint8_t v_canonicalOnly_boxed_1082_; size_t v_sz_boxed_1083_; size_t v_i_boxed_1084_; lean_object* v_res_1085_; 
v_canonicalOnly_boxed_1082_ = lean_unbox(v_canonicalOnly_1077_);
v_sz_boxed_1083_ = lean_unbox_usize(v_sz_1079_);
lean_dec(v_sz_1079_);
v_i_boxed_1084_ = lean_unbox_usize(v_i_1080_);
lean_dec(v_i_1080_);
v_res_1085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_1072_, v_i_1073_, v_kind_1074_, v_tgtRange_1075_, v_f_1076_, v_canonicalOnly_boxed_1082_, v_as_1078_, v_sz_boxed_1083_, v_i_boxed_1084_, v_b_1081_);
lean_dec_ref(v_as_1078_);
lean_dec_ref(v_tgtRange_1075_);
lean_dec(v_kind_1074_);
lean_dec_ref(v_i_1073_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0___boxed(lean_object* v_init_1086_, lean_object* v_ctx_x3f_1087_, lean_object* v_i_1088_, lean_object* v_kind_1089_, lean_object* v_tgtRange_1090_, lean_object* v_f_1091_, lean_object* v_canonicalOnly_1092_, lean_object* v_n_1093_, lean_object* v_b_1094_){
_start:
{
uint8_t v_canonicalOnly_boxed_1095_; lean_object* v_res_1096_; 
v_canonicalOnly_boxed_1095_ = lean_unbox(v_canonicalOnly_1092_);
v_res_1096_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_1086_, v_ctx_x3f_1087_, v_i_1088_, v_kind_1089_, v_tgtRange_1090_, v_f_1091_, v_canonicalOnly_boxed_1095_, v_n_1093_, v_b_1094_);
lean_dec_ref(v_n_1093_);
lean_dec_ref(v_tgtRange_1090_);
lean_dec(v_kind_1089_);
lean_dec_ref(v_i_1088_);
lean_dec_ref(v_init_1086_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f___boxed(lean_object* v_kind_1097_, lean_object* v_tgtRange_1098_, lean_object* v_ctx_x3f_1099_, lean_object* v_t_1100_, lean_object* v_f_1101_, lean_object* v_canonicalOnly_1102_){
_start:
{
uint8_t v_canonicalOnly_boxed_1103_; lean_object* v_res_1104_; 
v_canonicalOnly_boxed_1103_ = lean_unbox(v_canonicalOnly_1102_);
v_res_1104_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_1097_, v_tgtRange_1098_, v_ctx_x3f_1099_, v_t_1100_, v_f_1101_, v_canonicalOnly_boxed_1103_);
lean_dec_ref(v_tgtRange_1098_);
lean_dec(v_kind_1097_);
return v_res_1104_;
}
}
static lean_object* _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_1106_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_1106_, 0, lean_box(0));
lean_closure_set(v___x_1106_, 1, lean_box(0));
lean_closure_set(v___x_1106_, 2, v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(lean_object* v_msg_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v___f_1111_; lean_object* v___x_3957__overap_1112_; lean_object* v___x_1113_; 
v___x_1110_ = lean_obj_once(&l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0, &l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0_once, _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0);
v___f_1111_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1111_, 0, v___x_1110_);
v___x_3957__overap_1112_ = lean_panic_fn_borrowed(v___f_1111_, v_msg_1107_);
lean_dec_ref(v___f_1111_);
lean_inc_ref(v___y_1108_);
v___x_1113_ = lean_apply_2(v___x_3957__overap_1112_, v___y_1108_, lean_box(0));
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___boxed(lean_object* v_msg_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v_msg_1114_, v___y_1115_);
lean_dec_ref(v___y_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0(lean_object* v___x_1118_, lean_object* v___x_1119_, lean_object* v_ctx_1120_, lean_object* v_node_1121_, lean_object* v_result_1122_){
_start:
{
uint8_t v___y_1124_; 
if (lean_obj_tag(v_node_1121_) == 1)
{
lean_object* v_i_1127_; 
v_i_1127_ = lean_ctor_get(v_node_1121_, 0);
if (lean_obj_tag(v_i_1127_) == 3)
{
lean_object* v_i_1128_; lean_object* v_stx_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; 
v_i_1128_ = lean_ctor_get(v_i_1127_, 0);
v_stx_1129_ = lean_ctor_get(v_i_1128_, 1);
v___x_1130_ = 1;
v___x_1131_ = l_Lean_Syntax_getPos_x3f(v_stx_1129_, v___x_1130_);
if (lean_obj_tag(v___x_1131_) == 1)
{
lean_object* v_val_1132_; lean_object* v___x_1133_; 
v_val_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_val_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1133_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1129_, v___x_1130_);
if (lean_obj_tag(v___x_1133_) == 1)
{
lean_object* v_val_1134_; uint8_t v___x_1135_; 
v_val_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_val_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = lean_nat_dec_le(v_val_1132_, v___x_1118_);
lean_dec(v_val_1132_);
if (v___x_1135_ == 0)
{
lean_dec(v_val_1134_);
v___y_1124_ = v___x_1135_;
goto v___jp_1123_;
}
else
{
uint8_t v___x_1136_; 
v___x_1136_ = lean_nat_dec_le(v___x_1119_, v_val_1134_);
lean_dec(v_val_1134_);
v___y_1124_ = v___x_1136_;
goto v___jp_1123_;
}
}
else
{
lean_dec(v___x_1133_);
lean_dec(v_val_1132_);
lean_dec_ref_known(v_node_1121_, 2);
lean_dec_ref(v_ctx_1120_);
return v_result_1122_;
}
}
else
{
lean_dec(v___x_1131_);
lean_dec_ref_known(v_node_1121_, 2);
lean_dec_ref(v_ctx_1120_);
return v_result_1122_;
}
}
else
{
lean_dec_ref_known(v_node_1121_, 2);
lean_dec_ref(v_ctx_1120_);
return v_result_1122_;
}
}
else
{
lean_dec_ref(v_node_1121_);
lean_dec_ref(v_ctx_1120_);
return v_result_1122_;
}
v___jp_1123_:
{
if (v___y_1124_ == 0)
{
lean_dec_ref(v_node_1121_);
lean_dec_ref(v_ctx_1120_);
return v_result_1122_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_ctx_1120_);
lean_ctor_set(v___x_1125_, 1, v_node_1121_);
v___x_1126_ = lean_array_push(v_result_1122_, v___x_1125_);
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed(lean_object* v___x_1137_, lean_object* v___x_1138_, lean_object* v_ctx_1139_, lean_object* v_node_1140_, lean_object* v_result_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_CodeAction_cmdCodeActionProvider___lam__0(v___x_1137_, v___x_1138_, v_ctx_1139_, v_node_1140_, v_result_1141_);
lean_dec(v___x_1138_);
lean_dec(v___x_1137_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(lean_object* v_params_1143_, lean_object* v_snap_1144_, lean_object* v_fst_1145_, lean_object* v_snd_1146_, lean_object* v_as_1147_, size_t v_sz_1148_, size_t v_i_1149_, lean_object* v_b_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_snd_1154_; uint8_t v___x_1158_; 
v___x_1158_ = lean_usize_dec_lt(v_i_1149_, v_sz_1148_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_dec_ref(v_snd_1146_);
lean_dec_ref(v_fst_1145_);
lean_dec_ref(v_snap_1144_);
lean_dec_ref(v_params_1143_);
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_b_1150_);
return v___x_1159_;
}
else
{
lean_object* v___x_4579__overap_1160_; lean_object* v___x_1161_; 
v___x_4579__overap_1160_ = lean_array_uget_borrowed(v_as_1147_, v_i_1149_);
lean_inc(v___x_4579__overap_1160_);
lean_inc_ref(v___y_1151_);
lean_inc_ref(v_snd_1146_);
lean_inc_ref(v_fst_1145_);
lean_inc_ref(v_snap_1144_);
lean_inc_ref(v_params_1143_);
v___x_1161_ = lean_apply_6(v___x_4579__overap_1160_, v_params_1143_, v_snap_1144_, v_fst_1145_, v_snd_1146_, v___y_1151_, lean_box(0));
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
v___x_1163_ = l_Array_append___redArg(v_b_1150_, v_a_1162_);
lean_dec(v_a_1162_);
v_snd_1154_ = v___x_1163_;
goto v___jp_1153_;
}
else
{
lean_dec_ref_known(v___x_1161_, 1);
v_snd_1154_ = v_b_1150_;
goto v___jp_1153_;
}
}
v___jp_1153_:
{
size_t v___x_1155_; size_t v___x_1156_; 
v___x_1155_ = ((size_t)1ULL);
v___x_1156_ = lean_usize_add(v_i_1149_, v___x_1155_);
v_i_1149_ = v___x_1156_;
v_b_1150_ = v_snd_1154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1___boxed(lean_object* v_params_1164_, lean_object* v_snap_1165_, lean_object* v_fst_1166_, lean_object* v_snd_1167_, lean_object* v_as_1168_, lean_object* v_sz_1169_, lean_object* v_i_1170_, lean_object* v_b_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
size_t v_sz_boxed_1174_; size_t v_i_boxed_1175_; lean_object* v_res_1176_; 
v_sz_boxed_1174_ = lean_unbox_usize(v_sz_1169_);
lean_dec(v_sz_1169_);
v_i_boxed_1175_ = lean_unbox_usize(v_i_1170_);
lean_dec(v_i_1170_);
v_res_1176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1164_, v_snap_1165_, v_fst_1166_, v_snd_1167_, v_as_1168_, v_sz_boxed_1174_, v_i_boxed_1175_, v_b_1171_, v___y_1172_);
lean_dec_ref(v___y_1172_);
lean_dec_ref(v_as_1168_);
return v_res_1176_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2));
v___x_1181_ = lean_unsigned_to_nat(48u);
v___x_1182_ = lean_unsigned_to_nat(185u);
v___x_1183_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1));
v___x_1184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0));
v___x_1185_ = l_mkPanicMessageWithDecl(v___x_1184_, v___x_1183_, v___x_1182_, v___x_1181_, v___x_1180_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(lean_object* v___x_1186_, lean_object* v_params_1187_, lean_object* v_snap_1188_, lean_object* v_as_1189_, size_t v_sz_1190_, size_t v_i_1191_, lean_object* v_b_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_a_1196_; lean_object* v___y_1201_; uint8_t v___x_1212_; 
v___x_1212_ = lean_usize_dec_lt(v_i_1191_, v_sz_1190_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec_ref(v_snap_1188_);
lean_dec_ref(v_params_1187_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_b_1192_);
return v___x_1213_;
}
else
{
lean_object* v_a_1214_; lean_object* v_snd_1215_; 
v_a_1214_ = lean_array_uget_borrowed(v_as_1189_, v_i_1191_);
v_snd_1215_ = lean_ctor_get(v_a_1214_, 1);
if (lean_obj_tag(v_snd_1215_) == 1)
{
lean_object* v_i_1216_; 
v_i_1216_ = lean_ctor_get(v_snd_1215_, 0);
if (lean_obj_tag(v_i_1216_) == 3)
{
lean_object* v_fst_1217_; lean_object* v_i_1218_; lean_object* v_onAnyCmd_1219_; lean_object* v_onCmd_1220_; lean_object* v_out_1222_; lean_object* v___y_1223_; lean_object* v_stx_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_fst_1217_ = lean_ctor_get(v_a_1214_, 0);
v_i_1218_ = lean_ctor_get(v_i_1216_, 0);
v_onAnyCmd_1219_ = lean_ctor_get(v___x_1186_, 0);
v_onCmd_1220_ = lean_ctor_get(v___x_1186_, 1);
v_stx_1228_ = lean_ctor_get(v_i_1218_, 1);
lean_inc(v_stx_1228_);
v___x_1229_ = l_Lean_Syntax_getKind(v_stx_1228_);
v___x_1230_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_1220_, v___x_1229_);
lean_dec(v___x_1229_);
if (lean_obj_tag(v___x_1230_) == 1)
{
lean_object* v_val_1231_; size_t v_sz_1232_; size_t v___x_1233_; lean_object* v___x_1234_; 
v_val_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_val_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v_sz_1232_ = lean_array_size(v_val_1231_);
v___x_1233_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1215_);
lean_inc(v_fst_1217_);
lean_inc_ref(v_snap_1188_);
lean_inc_ref(v_params_1187_);
v___x_1234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1187_, v_snap_1188_, v_fst_1217_, v_snd_1215_, v_val_1231_, v_sz_1232_, v___x_1233_, v_b_1192_, v___y_1193_);
lean_dec(v_val_1231_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v_out_1222_ = v_a_1235_;
v___y_1223_ = v___y_1193_;
goto v___jp_1221_;
}
else
{
lean_dec_ref(v_snap_1188_);
lean_dec_ref(v_params_1187_);
return v___x_1234_;
}
}
else
{
lean_dec(v___x_1230_);
v_out_1222_ = v_b_1192_;
v___y_1223_ = v___y_1193_;
goto v___jp_1221_;
}
v___jp_1221_:
{
size_t v_sz_1224_; size_t v___x_1225_; lean_object* v___x_1226_; 
v_sz_1224_ = lean_array_size(v_onAnyCmd_1219_);
v___x_1225_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1215_);
lean_inc(v_fst_1217_);
lean_inc_ref(v_snap_1188_);
lean_inc_ref(v_params_1187_);
v___x_1226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1187_, v_snap_1188_, v_fst_1217_, v_snd_1215_, v_onAnyCmd_1219_, v_sz_1224_, v___x_1225_, v_out_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v_a_1196_ = v_a_1227_;
goto v___jp_1195_;
}
else
{
lean_dec_ref(v_snap_1188_);
lean_dec_ref(v_params_1187_);
return v___x_1226_;
}
}
}
else
{
v___y_1201_ = v___y_1193_;
goto v___jp_1200_;
}
}
else
{
v___y_1201_ = v___y_1193_;
goto v___jp_1200_;
}
}
v___jp_1195_:
{
size_t v___x_1197_; size_t v___x_1198_; 
v___x_1197_ = ((size_t)1ULL);
v___x_1198_ = lean_usize_add(v_i_1191_, v___x_1197_);
v_i_1191_ = v___x_1198_;
v_b_1192_ = v_a_1196_;
goto _start;
}
v___jp_1200_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
v___x_1203_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v___x_1202_, v___y_1201_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_dec_ref_known(v___x_1203_, 1);
v_a_1196_ = v_b_1192_;
goto v___jp_1195_;
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec_ref(v_b_1192_);
lean_dec_ref(v_snap_1188_);
lean_dec_ref(v_params_1187_);
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___boxed(lean_object* v___x_1236_, lean_object* v_params_1237_, lean_object* v_snap_1238_, lean_object* v_as_1239_, lean_object* v_sz_1240_, lean_object* v_i_1241_, lean_object* v_b_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
size_t v_sz_boxed_1245_; size_t v_i_boxed_1246_; lean_object* v_res_1247_; 
v_sz_boxed_1245_ = lean_unbox_usize(v_sz_1240_);
lean_dec(v_sz_1240_);
v_i_boxed_1246_ = lean_unbox_usize(v_i_1241_);
lean_dec(v_i_1241_);
v_res_1247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_1236_, v_params_1237_, v_snap_1238_, v_as_1239_, v_sz_boxed_1245_, v_i_boxed_1246_, v_b_1242_, v___y_1243_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v_as_1239_);
lean_dec_ref(v___x_1236_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(lean_object* v_params_1248_, lean_object* v_snap_1249_, lean_object* v___x_1250_, lean_object* v_as_1251_, size_t v_sz_1252_, size_t v_i_1253_, lean_object* v_b_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_a_1258_; lean_object* v___y_1263_; uint8_t v___x_1274_; 
v___x_1274_ = lean_usize_dec_lt(v_i_1253_, v_sz_1252_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
lean_dec_ref(v_snap_1249_);
lean_dec_ref(v_params_1248_);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_b_1254_);
return v___x_1275_;
}
else
{
lean_object* v_a_1276_; lean_object* v_snd_1277_; 
v_a_1276_ = lean_array_uget_borrowed(v_as_1251_, v_i_1253_);
v_snd_1277_ = lean_ctor_get(v_a_1276_, 1);
if (lean_obj_tag(v_snd_1277_) == 1)
{
lean_object* v_i_1278_; 
v_i_1278_ = lean_ctor_get(v_snd_1277_, 0);
if (lean_obj_tag(v_i_1278_) == 3)
{
lean_object* v_fst_1279_; lean_object* v_i_1280_; lean_object* v_onAnyCmd_1281_; lean_object* v_onCmd_1282_; lean_object* v_out_1284_; lean_object* v___y_1285_; lean_object* v_stx_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_fst_1279_ = lean_ctor_get(v_a_1276_, 0);
v_i_1280_ = lean_ctor_get(v_i_1278_, 0);
v_onAnyCmd_1281_ = lean_ctor_get(v___x_1250_, 0);
v_onCmd_1282_ = lean_ctor_get(v___x_1250_, 1);
v_stx_1290_ = lean_ctor_get(v_i_1280_, 1);
lean_inc(v_stx_1290_);
v___x_1291_ = l_Lean_Syntax_getKind(v_stx_1290_);
v___x_1292_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_1282_, v___x_1291_);
lean_dec(v___x_1291_);
if (lean_obj_tag(v___x_1292_) == 1)
{
lean_object* v_val_1293_; size_t v_sz_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v_val_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_val_1293_);
lean_dec_ref_known(v___x_1292_, 1);
v_sz_1294_ = lean_array_size(v_val_1293_);
v___x_1295_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1277_);
lean_inc(v_fst_1279_);
lean_inc_ref(v_snap_1249_);
lean_inc_ref(v_params_1248_);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1248_, v_snap_1249_, v_fst_1279_, v_snd_1277_, v_val_1293_, v_sz_1294_, v___x_1295_, v_b_1254_, v___y_1255_);
lean_dec(v_val_1293_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v_out_1284_ = v_a_1297_;
v___y_1285_ = v___y_1255_;
goto v___jp_1283_;
}
else
{
lean_dec_ref(v_snap_1249_);
lean_dec_ref(v_params_1248_);
return v___x_1296_;
}
}
else
{
lean_dec(v___x_1292_);
v_out_1284_ = v_b_1254_;
v___y_1285_ = v___y_1255_;
goto v___jp_1283_;
}
v___jp_1283_:
{
size_t v_sz_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v_sz_1286_ = lean_array_size(v_onAnyCmd_1281_);
v___x_1287_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1277_);
lean_inc(v_fst_1279_);
lean_inc_ref(v_snap_1249_);
lean_inc_ref(v_params_1248_);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1248_, v_snap_1249_, v_fst_1279_, v_snd_1277_, v_onAnyCmd_1281_, v_sz_1286_, v___x_1287_, v_out_1284_, v___y_1285_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v_a_1258_ = v_a_1289_;
goto v___jp_1257_;
}
else
{
lean_dec_ref(v_snap_1249_);
lean_dec_ref(v_params_1248_);
return v___x_1288_;
}
}
}
else
{
v___y_1263_ = v___y_1255_;
goto v___jp_1262_;
}
}
else
{
v___y_1263_ = v___y_1255_;
goto v___jp_1262_;
}
}
v___jp_1257_:
{
size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = ((size_t)1ULL);
v___x_1260_ = lean_usize_add(v_i_1253_, v___x_1259_);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_1250_, v_params_1248_, v_snap_1249_, v_as_1251_, v_sz_1252_, v___x_1260_, v_a_1258_, v___y_1255_);
return v___x_1261_;
}
v___jp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
v___x_1265_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v___x_1264_, v___y_1263_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_dec_ref_known(v___x_1265_, 1);
v_a_1258_ = v_b_1254_;
goto v___jp_1257_;
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_b_1254_);
lean_dec_ref(v_snap_1249_);
lean_dec_ref(v_params_1248_);
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2___boxed(lean_object* v_params_1298_, lean_object* v_snap_1299_, lean_object* v___x_1300_, lean_object* v_as_1301_, lean_object* v_sz_1302_, lean_object* v_i_1303_, lean_object* v_b_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
size_t v_sz_boxed_1307_; size_t v_i_boxed_1308_; lean_object* v_res_1309_; 
v_sz_boxed_1307_ = lean_unbox_usize(v_sz_1302_);
lean_dec(v_sz_1302_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1303_);
lean_dec(v_i_1303_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_1298_, v_snap_1299_, v___x_1300_, v_as_1301_, v_sz_boxed_1307_, v_i_boxed_1308_, v_b_1304_, v___y_1305_);
lean_dec_ref(v___y_1305_);
lean_dec_ref(v_as_1301_);
lean_dec_ref(v___x_1300_);
return v_res_1309_;
}
}
static lean_object* _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0(void){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Array_instInhabited(lean_box(0));
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = l_Lean_CodeAction_instInhabitedCommandCodeActions_default;
v___x_1312_ = lean_obj_once(&l_Lean_CodeAction_cmdCodeActionProvider___closed__0, &l_Lean_CodeAction_cmdCodeActionProvider___closed__0_once, _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v___x_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider(lean_object* v_params_1316_, lean_object* v_snap_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___x_1320_; lean_object* v_a_1321_; lean_object* v_toEditableDocumentCore_1322_; lean_object* v_meta_1323_; lean_object* v_range_1324_; lean_object* v_text_1325_; lean_object* v_start_1326_; lean_object* v_end_1327_; lean_object* v___x_1328_; lean_object* v_toEnvExtension_1329_; lean_object* v_asyncMode_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v_snd_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___f_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; size_t v_sz_1342_; size_t v___x_1343_; lean_object* v___x_1344_; 
v___x_1320_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v_a_1318_);
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref(v___x_1320_);
v_toEditableDocumentCore_1322_ = lean_ctor_get(v_a_1321_, 0);
lean_inc_ref(v_toEditableDocumentCore_1322_);
lean_dec(v_a_1321_);
v_meta_1323_ = lean_ctor_get(v_toEditableDocumentCore_1322_, 0);
lean_inc_ref(v_meta_1323_);
lean_dec_ref(v_toEditableDocumentCore_1322_);
v_range_1324_ = lean_ctor_get(v_params_1316_, 3);
v_text_1325_ = lean_ctor_get(v_meta_1323_, 3);
lean_inc_ref(v_text_1325_);
lean_dec_ref(v_meta_1323_);
v_start_1326_ = lean_ctor_get(v_range_1324_, 0);
v_end_1327_ = lean_ctor_get(v_range_1324_, 1);
v___x_1328_ = l_Lean_CodeAction_cmdCodeActionExt;
v_toEnvExtension_1329_ = lean_ctor_get(v___x_1328_, 0);
v_asyncMode_1330_ = lean_ctor_get(v_toEnvExtension_1329_, 2);
v___x_1331_ = lean_obj_once(&l_Lean_CodeAction_cmdCodeActionProvider___closed__1, &l_Lean_CodeAction_cmdCodeActionProvider___closed__1_once, _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1);
v___x_1332_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1317_);
v___x_1333_ = lean_box(0);
v___x_1334_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1331_, v___x_1328_, v___x_1332_, v_asyncMode_1330_, v___x_1333_);
v_snd_1335_ = lean_ctor_get(v___x_1334_, 1);
lean_inc(v_snd_1335_);
lean_dec(v___x_1334_);
lean_inc_ref(v_start_1326_);
v___x_1336_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1325_, v_start_1326_);
lean_inc_ref(v_end_1327_);
v___x_1337_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1325_, v_end_1327_);
lean_dec_ref(v_text_1325_);
v___f_1338_ = lean_alloc_closure((void*)(l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1338_, 0, v___x_1337_);
lean_closure_set(v___f_1338_, 1, v___x_1336_);
v___x_1339_ = ((lean_object*)(l_Lean_CodeAction_cmdCodeActionProvider___closed__2));
lean_inc_ref(v_snap_1317_);
v___x_1340_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_1317_);
v___x_1341_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v___x_1339_, v___f_1338_, v___x_1340_);
v_sz_1342_ = lean_array_size(v___x_1341_);
v___x_1343_ = ((size_t)0ULL);
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_1316_, v_snap_1317_, v_snd_1335_, v___x_1341_, v_sz_1342_, v___x_1343_, v___x_1339_, v_a_1318_);
lean_dec(v___x_1341_);
lean_dec(v_snd_1335_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___boxed(lean_object* v_params_1345_, lean_object* v_snap_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_CodeAction_cmdCodeActionProvider(v_params_1345_, v_snap_1346_, v_a_1347_);
lean_dec_ref(v_a_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1(){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1));
v___x_1357_ = lean_alloc_closure((void*)(l_Lean_CodeAction_cmdCodeActionProvider___boxed), 4, 0);
v___x_1358_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_1356_, v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___boxed(lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
return v_res_1360_;
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
