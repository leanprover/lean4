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
lean_dec_ref(v___x_64_);
v___x_66_ = l_Lean_Syntax_getTailPos_x3f(v_stx_61_, v___x_63_);
if (lean_obj_tag(v___x_66_) == 1)
{
lean_object* v_val_67_; uint8_t v___x_68_; 
v_val_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_val_67_);
lean_dec_ref(v___x_66_);
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
lean_object* v___x_1833__overap_92_; lean_object* v___x_93_; 
v___x_1833__overap_92_ = lean_array_uget_borrowed(v_as_80_, v_i_81_);
lean_inc(v___x_1833__overap_92_);
lean_inc_ref(v___y_84_);
lean_inc_ref(v_snd_79_);
lean_inc_ref(v_fst_78_);
lean_inc_ref(v_snap_77_);
lean_inc_ref(v_params_76_);
v___x_93_ = lean_apply_6(v___x_1833__overap_92_, v_params_76_, v_snap_77_, v_fst_78_, v_snd_79_, v___y_84_, lean_box(0));
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_95_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_94_);
lean_dec_ref(v___x_93_);
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
lean_dec_ref(v___x_93_);
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
lean_object* v___x_122_; lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_173_; 
v___x_122_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v_a_120_);
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_173_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_173_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_173_;
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
uint8_t v___x_163_; 
v___x_163_ = lean_nat_dec_le(v___x_158_, v___x_158_);
if (v___x_163_ == 0)
{
if (v___x_159_ == 0)
{
lean_object* v___x_165_; 
lean_dec(v_snd_156_);
lean_dec(v_snd_148_);
lean_dec(v_fst_147_);
lean_dec_ref(v_snap_119_);
lean_dec_ref(v_params_118_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_157_);
v___x_165_ = v___x_125_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_157_);
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
lean_del_object(v___x_125_);
v___x_167_ = ((size_t)0ULL);
v___x_168_ = lean_usize_of_nat(v___x_158_);
v___x_169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_118_, v_snap_119_, v_fst_147_, v_snd_148_, v_snd_156_, v___x_167_, v___x_168_, v___x_157_, v_a_120_);
lean_dec(v_snd_156_);
return v___x_169_;
}
}
else
{
size_t v___x_170_; size_t v___x_171_; lean_object* v___x_172_; 
lean_del_object(v___x_125_);
v___x_170_ = ((size_t)0ULL);
v___x_171_ = lean_usize_of_nat(v___x_158_);
v___x_172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_118_, v_snap_119_, v_fst_147_, v_snd_148_, v_snd_156_, v___x_170_, v___x_171_, v___x_157_, v_a_120_);
lean_dec(v_snd_156_);
return v___x_172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_holeCodeActionProvider___boxed(lean_object* v_params_174_, lean_object* v_snap_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_CodeAction_holeCodeActionProvider(v_params_174_, v_snap_175_, v_a_176_);
lean_dec_ref(v_a_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1(){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2));
v___x_187_ = lean_alloc_closure((void*)(l_Lean_CodeAction_holeCodeActionProvider___boxed), 4, 0);
v___x_188_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_186_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___boxed(lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx(lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
lean_object* v___x_192_; 
v___x_192_ = lean_unsigned_to_nat(0u);
return v___x_192_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = lean_unsigned_to_nat(1u);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorIdx___boxed(lean_object* v_x_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_CodeAction_FindTacticResult_ctorIdx(v_x_194_);
lean_dec_ref(v_x_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(lean_object* v_t_196_, lean_object* v_k_197_){
_start:
{
if (lean_obj_tag(v_t_196_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_199_; 
v_a_198_ = lean_ctor_get(v_t_196_, 0);
lean_inc(v_a_198_);
lean_dec_ref(v_t_196_);
v___x_199_ = lean_apply_1(v_k_197_, v_a_198_);
return v___x_199_;
}
else
{
uint8_t v_preferred_200_; lean_object* v_insertIdx_201_; lean_object* v_a_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_preferred_200_ = lean_ctor_get_uint8(v_t_196_, sizeof(void*)*2);
v_insertIdx_201_ = lean_ctor_get(v_t_196_, 0);
lean_inc(v_insertIdx_201_);
v_a_202_ = lean_ctor_get(v_t_196_, 1);
lean_inc(v_a_202_);
lean_dec_ref(v_t_196_);
v___x_203_ = lean_box(v_preferred_200_);
v___x_204_ = lean_apply_3(v_k_197_, v___x_203_, v_insertIdx_201_, v_a_202_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim(lean_object* v_motive_205_, lean_object* v_ctorIdx_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_k_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_207_, v_k_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_ctorElim___boxed(lean_object* v_motive_211_, lean_object* v_ctorIdx_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_k_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_CodeAction_FindTacticResult_ctorElim(v_motive_211_, v_ctorIdx_212_, v_t_213_, v_h_214_, v_k_215_);
lean_dec(v_ctorIdx_212_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim___redArg(lean_object* v_t_217_, lean_object* v_tactic_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_217_, v_tactic_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tactic_elim(lean_object* v_motive_220_, lean_object* v_t_221_, lean_object* v_h_222_, lean_object* v_tactic_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_221_, v_tactic_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim___redArg(lean_object* v_t_225_, lean_object* v_tacticSeq_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_225_, v_tacticSeq_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_FindTacticResult_tacticSeq_elim(lean_object* v_motive_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_tacticSeq_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_229_, v_tacticSeq_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(lean_object* v_range_233_, lean_object* v_stx_234_, lean_object* v_prev_x3f_235_){
_start:
{
uint8_t v___x_236_; lean_object* v___x_237_; 
v___x_236_ = 1;
v___x_237_ = l_Lean_Syntax_getPos_x3f(v_stx_234_, v___x_236_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v___x_238_; 
lean_dec(v_prev_x3f_235_);
v___x_238_ = lean_box(0);
return v___x_238_;
}
else
{
lean_object* v_val_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_270_; 
v_val_239_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_270_ == 0)
{
v___x_241_ = v___x_237_;
v_isShared_242_ = v_isSharedCheck_270_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_val_239_);
lean_dec(v___x_237_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_270_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___y_244_; 
if (lean_obj_tag(v_prev_x3f_235_) == 0)
{
lean_inc(v_val_239_);
v___y_244_ = v_val_239_;
goto v___jp_243_;
}
else
{
lean_object* v_val_269_; 
v_val_269_ = lean_ctor_get(v_prev_x3f_235_, 0);
lean_inc(v_val_269_);
lean_dec_ref(v_prev_x3f_235_);
v___y_244_ = v_val_269_;
goto v___jp_243_;
}
v___jp_243_:
{
lean_object* v_start_245_; lean_object* v_stop_246_; uint8_t v___x_247_; 
v_start_245_ = lean_ctor_get(v_range_233_, 0);
v_stop_246_ = lean_ctor_get(v_range_233_, 1);
v___x_247_ = lean_nat_dec_le(v___y_244_, v_start_245_);
lean_dec(v___y_244_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_del_object(v___x_241_);
lean_dec(v_val_239_);
v___x_248_ = lean_box(0);
return v___x_248_;
}
else
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_Syntax_getTailInfo(v_stx_234_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_trailing_250_; lean_object* v_endPos_251_; lean_object* v_startPos_252_; lean_object* v_stopPos_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_trailing_250_ = lean_ctor_get(v___x_249_, 2);
lean_inc_ref(v_trailing_250_);
v_endPos_251_ = lean_ctor_get(v___x_249_, 3);
lean_inc(v_endPos_251_);
lean_dec_ref(v___x_249_);
v_startPos_252_ = lean_ctor_get(v_trailing_250_, 1);
lean_inc(v_startPos_252_);
v_stopPos_253_ = lean_ctor_get(v_trailing_250_, 2);
lean_inc(v_stopPos_253_);
lean_dec_ref(v_trailing_250_);
v___x_254_ = lean_nat_sub(v_stopPos_253_, v_startPos_252_);
lean_dec(v_startPos_252_);
lean_dec(v_stopPos_253_);
v___x_255_ = lean_nat_add(v_endPos_251_, v___x_254_);
lean_dec(v___x_254_);
v___x_256_ = lean_nat_dec_le(v_stop_246_, v___x_255_);
lean_dec(v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
lean_dec(v_endPos_251_);
lean_del_object(v___x_241_);
lean_dec(v_val_239_);
v___x_257_ = lean_box(0);
return v___x_257_;
}
else
{
uint8_t v___x_258_; 
v___x_258_ = lean_nat_dec_le(v_val_239_, v_start_245_);
lean_dec(v_val_239_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_261_; 
lean_dec(v_endPos_251_);
v___x_259_ = lean_box(v___x_258_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_259_);
v___x_261_ = v___x_241_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
else
{
uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_263_ = lean_nat_dec_le(v_stop_246_, v_endPos_251_);
lean_dec(v_endPos_251_);
v___x_264_ = lean_box(v___x_263_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_264_);
v___x_266_ = v___x_241_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v___x_268_; 
lean_dec(v___x_249_);
lean_del_object(v___x_241_);
lean_dec(v_val_239_);
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit___boxed(lean_object* v_range_271_, lean_object* v_stx_272_, lean_object* v_prev_x3f_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_271_, v_stx_272_, v_prev_x3f_273_);
lean_dec(v_stx_272_);
lean_dec_ref(v_range_271_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(lean_object* v_r_u2081_275_, lean_object* v_r_u2082_276_){
_start:
{
if (lean_obj_tag(v_r_u2081_275_) == 1)
{
lean_object* v_val_277_; 
v_val_277_ = lean_ctor_get(v_r_u2081_275_, 0);
if (lean_obj_tag(v_val_277_) == 1)
{
uint8_t v_preferred_278_; 
v_preferred_278_ = lean_ctor_get_uint8(v_val_277_, sizeof(void*)*2);
if (v_preferred_278_ == 1)
{
if (lean_obj_tag(v_r_u2082_276_) == 1)
{
uint8_t v_preferred_279_; 
v_preferred_279_ = lean_ctor_get_uint8(v_r_u2082_276_, sizeof(void*)*2);
if (v_preferred_279_ == 0)
{
lean_inc_ref(v_val_277_);
return v_val_277_;
}
else
{
lean_inc_ref(v_r_u2082_276_);
return v_r_u2082_276_;
}
}
else
{
lean_inc_ref(v_r_u2082_276_);
return v_r_u2082_276_;
}
}
else
{
lean_inc_ref(v_r_u2082_276_);
return v_r_u2082_276_;
}
}
else
{
lean_inc_ref(v_r_u2082_276_);
return v_r_u2082_276_;
}
}
else
{
lean_inc_ref(v_r_u2082_276_);
return v_r_u2082_276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge___boxed(lean_object* v_r_u2081_280_, lean_object* v_r_u2082_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(v_r_u2081_280_, v_r_u2082_281_);
lean_dec_ref(v_r_u2082_281_);
lean_dec(v_r_u2081_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(lean_object* v_upperBound_286_, lean_object* v___x_287_, lean_object* v_range_288_, lean_object* v_a_289_, lean_object* v_b_290_){
_start:
{
lean_object* v_a_292_; uint8_t v___x_296_; 
v___x_296_ = lean_nat_dec_lt(v_a_289_, v_upperBound_286_);
if (v___x_296_ == 0)
{
lean_dec(v_a_289_);
lean_dec_ref(v_range_288_);
lean_inc_ref(v_b_290_);
return v_b_290_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; 
v___x_297_ = lean_box(0);
v___x_298_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0));
v___x_299_ = lean_unsigned_to_nat(2u);
v___x_300_ = lean_nat_mul(v___x_299_, v_a_289_);
v___x_301_ = l_Lean_Syntax_getArg(v___x_287_, v___x_300_);
lean_dec(v___x_300_);
v___x_302_ = 0;
v___x_303_ = l_Lean_Syntax_getPos_x3f(v___x_301_, v___x_302_);
lean_dec(v___x_301_);
if (lean_obj_tag(v___x_303_) == 1)
{
lean_object* v_val_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_322_; 
v_val_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_322_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_322_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_val_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_322_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_stop_308_; uint8_t v___x_309_; 
v_stop_308_ = lean_ctor_get(v_range_288_, 1);
v___x_309_ = lean_nat_dec_lt(v_stop_308_, v_val_304_);
lean_dec(v_val_304_);
if (v___x_309_ == 0)
{
lean_del_object(v___x_306_);
v_a_292_ = v___x_298_;
goto v___jp_291_;
}
else
{
lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_319_; 
v_isSharedCheck_319_ = !lean_is_exclusive(v_range_288_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; lean_object* v_unused_321_; 
v_unused_320_ = lean_ctor_get(v_range_288_, 1);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_range_288_, 0);
lean_dec(v_unused_321_);
v___x_311_ = v_range_288_;
v_isShared_312_ = v_isSharedCheck_319_;
goto v_resetjp_310_;
}
else
{
lean_dec(v_range_288_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_319_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v_a_289_);
v___x_314_ = v___x_306_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_289_);
v___x_314_ = v_reuseFailAlloc_318_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_316_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_297_);
lean_ctor_set(v___x_311_, 0, v___x_314_);
v___x_316_ = v___x_311_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_297_);
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
lean_dec(v___x_303_);
v_a_292_ = v___x_298_;
goto v___jp_291_;
}
}
v___jp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_a_289_, v___x_293_);
lean_dec(v_a_289_);
v_a_289_ = v___x_294_;
v_b_290_ = v_a_292_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(lean_object* v_stx_329_, lean_object* v_a_330_, uint8_t v___x_331_, lean_object* v_snd_332_, lean_object* v_____r_333_, lean_object* v_childRes_334_){
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0___boxed(lean_object* v_stx_342_, lean_object* v_a_343_, lean_object* v___x_344_, lean_object* v_snd_345_, lean_object* v_____r_346_, lean_object* v_childRes_347_){
_start:
{
uint8_t v___x_4618__boxed_348_; lean_object* v_res_349_; 
v___x_4618__boxed_348_ = lean_unbox(v___x_344_);
v_res_349_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_342_, v_a_343_, v___x_4618__boxed_348_, v_snd_345_, v_____r_346_, v_childRes_347_);
lean_dec(v_a_343_);
lean_dec(v_stx_342_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(lean_object* v___y_360_, uint8_t v___x_361_, lean_object* v___x_362_, lean_object* v_range_363_, lean_object* v___x_364_, lean_object* v_preferred_365_, lean_object* v_a_366_, lean_object* v_b_367_){
_start:
{
lean_object* v_inner_368_; lean_object* v_next_369_; 
v_inner_368_ = lean_ctor_get(v_a_366_, 2);
lean_inc(v_inner_368_);
v_next_369_ = lean_ctor_get(v_inner_368_, 0);
lean_inc(v_next_369_);
if (lean_obj_tag(v_next_369_) == 0)
{
lean_object* v___x_370_; 
lean_dec(v_inner_368_);
lean_dec_ref(v_a_366_);
lean_dec_ref(v_preferred_365_);
lean_dec(v___x_364_);
lean_dec_ref(v_range_363_);
lean_dec(v___x_362_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v_b_367_);
return v___x_370_;
}
else
{
lean_object* v_nextIdx_371_; lean_object* v_n_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_433_; 
v_nextIdx_371_ = lean_ctor_get(v_a_366_, 0);
v_n_372_ = lean_ctor_get(v_a_366_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_a_366_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v_a_366_, 2);
lean_dec(v_unused_434_);
v___x_374_ = v_a_366_;
v_isShared_375_ = v_isSharedCheck_433_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_n_372_);
lean_inc(v_nextIdx_371_);
lean_dec(v_a_366_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_433_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v_upperBound_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_431_; 
v_upperBound_376_ = lean_ctor_get(v_inner_368_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_inner_368_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v_inner_368_, 0);
lean_dec(v_unused_432_);
v___x_378_ = v_inner_368_;
v_isShared_379_ = v_isSharedCheck_431_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_upperBound_376_);
lean_dec(v_inner_368_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_431_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v_val_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_430_; 
v_val_380_ = lean_ctor_get(v_next_369_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v_next_369_);
if (v_isSharedCheck_430_ == 0)
{
v___x_382_ = v_next_369_;
v_isShared_383_ = v_isSharedCheck_430_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_val_380_);
lean_dec(v_next_369_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_430_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = lean_nat_add(v_val_380_, v_nextIdx_371_);
lean_dec(v_nextIdx_371_);
lean_dec(v_val_380_);
v___x_385_ = lean_nat_dec_lt(v___x_384_, v_upperBound_376_);
if (v___x_385_ == 0)
{
lean_object* v___x_387_; 
lean_dec(v___x_384_);
lean_del_object(v___x_378_);
lean_dec(v_upperBound_376_);
lean_del_object(v___x_374_);
lean_dec(v_n_372_);
lean_dec_ref(v_preferred_365_);
lean_dec(v___x_364_);
lean_dec_ref(v_range_363_);
lean_dec(v___x_362_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v_b_367_);
v___x_387_ = v___x_382_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_b_367_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_add(v___x_384_, v___x_389_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_390_);
v___x_392_ = v___x_382_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_429_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_392_);
v___x_394_ = v___x_378_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_upperBound_376_);
v___x_394_ = v_reuseFailAlloc_428_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
lean_inc(v_n_372_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 2, v___x_394_);
lean_ctor_set(v___x_374_, 0, v_n_372_);
v___x_396_ = v___x_374_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_n_372_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_n_372_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v___x_394_);
v___x_396_ = v_reuseFailAlloc_427_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___y_398_; lean_object* v_val_403_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = l_Lean_Syntax_getArg(v___x_362_, v___x_384_);
v___x_406_ = lean_box(0);
v___x_407_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_363_, v___x_405_, v___x_406_);
if (lean_obj_tag(v___x_407_) == 1)
{
lean_object* v_val_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_val_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_val_408_);
lean_dec_ref(v___x_407_);
lean_inc(v___x_362_);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_362_);
lean_ctor_set(v___x_409_, 1, v___x_384_);
lean_inc(v___x_364_);
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_364_);
lean_inc(v___x_405_);
lean_inc_ref(v___x_410_);
lean_inc_ref(v_range_363_);
lean_inc_ref(v_preferred_365_);
v___x_411_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_365_, v_range_363_, v___x_410_, v___x_405_, v___x_406_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_dec_ref(v___x_410_);
lean_dec(v_val_408_);
lean_dec(v___x_405_);
lean_dec_ref(v___x_396_);
lean_dec(v_b_367_);
lean_dec_ref(v_preferred_365_);
lean_dec(v___x_364_);
lean_dec_ref(v_range_363_);
lean_dec(v___x_362_);
return v___x_411_;
}
else
{
lean_object* v_val_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_425_; 
v_val_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_425_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_425_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_val_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_425_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
if (lean_obj_tag(v_val_412_) == 0)
{
uint8_t v___x_416_; 
v___x_416_ = lean_unbox(v_val_408_);
lean_dec(v_val_408_);
if (v___x_416_ == 0)
{
lean_del_object(v___x_414_);
lean_dec_ref(v___x_410_);
lean_dec(v___x_405_);
v_a_366_ = v___x_396_;
goto _start;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_405_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_410_);
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 0);
lean_ctor_set(v___x_414_, 0, v___x_420_);
v___x_422_ = v___x_414_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
v_val_403_ = v___x_422_;
goto v___jp_402_;
}
}
}
else
{
lean_object* v_val_424_; 
lean_del_object(v___x_414_);
lean_dec_ref(v___x_410_);
lean_dec(v_val_408_);
lean_dec(v___x_405_);
v_val_424_ = lean_ctor_get(v_val_412_, 0);
lean_inc(v_val_424_);
lean_dec_ref(v_val_412_);
v_val_403_ = v_val_424_;
goto v___jp_402_;
}
}
}
}
else
{
lean_dec(v___x_407_);
lean_dec(v___x_405_);
lean_dec(v___x_384_);
v_a_366_ = v___x_396_;
goto _start;
}
v___jp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(v___y_360_, v___y_398_);
lean_dec_ref(v___y_398_);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
v_a_366_ = v___x_396_;
v_b_367_ = v___x_400_;
goto _start;
}
v___jp_402_:
{
if (lean_obj_tag(v_b_367_) == 0)
{
v___y_398_ = v_val_403_;
goto v___jp_397_;
}
else
{
lean_dec_ref(v_b_367_);
if (v___x_361_ == 0)
{
v___y_398_ = v_val_403_;
goto v___jp_397_;
}
else
{
lean_object* v___x_404_; 
lean_dec_ref(v_val_403_);
lean_dec_ref(v___x_396_);
lean_dec_ref(v_preferred_365_);
lean_dec(v___x_364_);
lean_dec_ref(v_range_363_);
lean_dec(v___x_362_);
v___x_404_ = lean_box(0);
return v___x_404_;
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
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(lean_object* v_preferred_441_, lean_object* v_range_442_, lean_object* v_stack_443_, lean_object* v_stx_444_, lean_object* v_prev_x3f_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
lean_inc(v_stx_444_);
v___x_446_ = l_Lean_Syntax_getKind(v_stx_444_);
v___x_447_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3));
v___x_448_ = lean_name_eq(v___x_446_, v___x_447_);
lean_dec(v___x_446_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_childRes_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_449_ = l_Lean_Syntax_getNumArgs(v_stx_444_);
v___x_450_ = lean_unsigned_to_nat(0u);
v_childRes_451_ = lean_box(0);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v_childRes_451_);
lean_ctor_set(v___x_452_, 1, v_prev_x3f_445_);
v___x_453_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v___x_449_, v_stx_444_, v_range_442_, v_stack_443_, v_preferred_441_, v___x_448_, v___x_450_, v___x_452_);
lean_dec(v___x_449_);
if (lean_obj_tag(v___x_453_) == 0)
{
return v_childRes_451_;
}
else
{
lean_object* v_val_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_462_; 
v_val_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_462_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_462_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_val_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_462_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_fst_458_; lean_object* v___x_460_; 
v_fst_458_ = lean_ctor_get(v_val_454_, 0);
lean_inc(v_fst_458_);
lean_dec(v_val_454_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v_fst_458_);
v___x_460_ = v___x_456_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_fst_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v___x_463_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; uint8_t v___y_488_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v_bracket_496_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_505_; 
lean_dec(v_prev_x3f_445_);
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_493_ = l_Lean_Syntax_getArg(v_stx_444_, v___x_463_);
lean_inc(v___x_493_);
v___x_494_ = l_Lean_Syntax_getKind(v___x_493_);
v___x_495_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6));
v_bracket_496_ = lean_name_eq(v___x_494_, v___x_495_);
lean_dec(v___x_494_);
if (v_bracket_496_ == 0)
{
v___y_505_ = v___x_463_;
goto v___jp_504_;
}
else
{
lean_object* v___x_524_; 
v___x_524_ = lean_unsigned_to_nat(1u);
v___y_505_ = v___x_524_;
goto v___jp_504_;
}
v___jp_464_:
{
lean_object* v_childRes_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_childRes_468_ = lean_box(0);
v___x_469_ = l_Lean_Syntax_getNumArgs(v___y_465_);
v___x_470_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4));
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_473_, 0, v___x_463_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
lean_ctor_set(v___x_473_, 2, v___x_471_);
v___x_474_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_467_, v___x_448_, v___y_465_, v_range_442_, v___y_466_, v_preferred_441_, v___x_473_, v_childRes_468_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_dec(v___y_467_);
return v___x_474_;
}
else
{
lean_object* v_val_475_; 
v_val_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_475_);
if (lean_obj_tag(v_val_475_) == 0)
{
lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___x_474_, 0);
lean_dec(v_unused_483_);
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___y_467_);
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___y_467_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_dec_ref(v_val_475_);
lean_dec(v___y_467_);
return v___x_474_;
}
}
}
v___jp_484_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_inc(v___y_486_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___y_486_);
lean_ctor_set(v___x_489_, 1, v___x_463_);
lean_inc(v___y_487_);
v___x_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___y_487_);
v___x_491_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_491_, 0, v___y_485_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*2, v___y_488_);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
v___y_465_ = v___y_486_;
v___y_466_ = v___y_487_;
v___y_467_ = v___x_492_;
goto v___jp_464_;
}
v___jp_497_:
{
if (v_bracket_496_ == 0)
{
lean_object* v___x_502_; uint8_t v___x_503_; 
lean_inc_ref(v_preferred_441_);
v___x_502_ = lean_apply_1(v_preferred_441_, v___y_498_);
v___x_503_ = lean_unbox(v___x_502_);
v___y_485_ = v___y_501_;
v___y_486_ = v___y_499_;
v___y_487_ = v___y_500_;
v___y_488_ = v___x_503_;
goto v___jp_484_;
}
else
{
lean_dec(v___y_498_);
v___y_485_ = v___y_501_;
v___y_486_ = v___y_499_;
v___y_487_ = v___y_500_;
v___y_488_ = v___x_448_;
goto v___jp_484_;
}
}
v___jp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; lean_object* v___x_513_; 
lean_inc(v___y_505_);
lean_inc(v___x_493_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_493_);
lean_ctor_set(v___x_506_, 1, v___y_505_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_stx_444_);
lean_ctor_set(v___x_507_, 1, v___x_463_);
v___x_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v_stack_443_);
v___x_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_506_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = l_Lean_Syntax_getArg(v___x_493_, v___y_505_);
lean_dec(v___y_505_);
lean_dec(v___x_493_);
v___x_511_ = l_Lean_Syntax_getArg(v___x_510_, v___x_463_);
v___x_512_ = 0;
v___x_513_ = l_Lean_Syntax_getPos_x3f(v___x_511_, v___x_512_);
lean_dec(v___x_511_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_box(0);
v___y_465_ = v___x_510_;
v___y_466_ = v___x_509_;
v___y_467_ = v___x_514_;
goto v___jp_464_;
}
else
{
lean_object* v_val_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v_fst_519_; 
v_val_515_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_val_515_);
lean_dec_ref(v___x_513_);
v___x_516_ = l_Lean_Syntax_getNumArgs(v___x_510_);
v___x_517_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0));
lean_inc_ref(v_range_442_);
v___x_518_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v___x_516_, v___x_510_, v_range_442_, v___x_463_, v___x_517_);
v_fst_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_fst_519_);
lean_dec_ref(v___x_518_);
if (lean_obj_tag(v_fst_519_) == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_add(v___x_516_, v___x_520_);
lean_dec(v___x_516_);
v___x_522_ = lean_nat_shiftr(v___x_521_, v___x_520_);
lean_dec(v___x_521_);
v___y_498_ = v_val_515_;
v___y_499_ = v___x_510_;
v___y_500_ = v___x_509_;
v___y_501_ = v___x_522_;
goto v___jp_497_;
}
else
{
lean_object* v_val_523_; 
lean_dec(v___x_516_);
v_val_523_ = lean_ctor_get(v_fst_519_, 0);
lean_inc(v_val_523_);
lean_dec_ref(v_fst_519_);
v___y_498_ = v_val_515_;
v___y_499_ = v___x_510_;
v___y_500_ = v___x_509_;
v___y_501_ = v_val_523_;
goto v___jp_497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(lean_object* v_upperBound_525_, lean_object* v_stx_526_, lean_object* v_range_527_, lean_object* v_stack_528_, lean_object* v_preferred_529_, uint8_t v___x_530_, lean_object* v_a_531_, lean_object* v_b_532_){
_start:
{
lean_object* v___y_534_; uint8_t v___x_549_; 
v___x_549_ = lean_nat_dec_lt(v_a_531_, v_upperBound_525_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
lean_dec(v_a_531_);
lean_dec_ref(v_preferred_529_);
lean_dec(v_stack_528_);
lean_dec_ref(v_range_527_);
lean_dec(v_stx_526_);
v___x_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_550_, 0, v_b_532_);
return v___x_550_;
}
else
{
lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_573_; 
v_fst_551_ = lean_ctor_get(v_b_532_, 0);
v_snd_552_ = lean_ctor_get(v_b_532_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_b_532_);
if (v_isSharedCheck_573_ == 0)
{
v___x_554_ = v_b_532_;
v_isShared_555_ = v_isSharedCheck_573_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_snd_552_);
lean_inc(v_fst_551_);
lean_dec(v_b_532_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_573_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = l_Lean_Syntax_getArg(v_stx_526_, v_a_531_);
lean_inc(v_snd_552_);
v___x_557_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_527_, v___x_556_, v_snd_552_);
if (lean_obj_tag(v___x_557_) == 1)
{
lean_object* v___x_559_; 
lean_dec_ref(v___x_557_);
lean_inc(v_a_531_);
lean_inc(v_stx_526_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v_a_531_);
lean_ctor_set(v___x_554_, 0, v_stx_526_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_stx_526_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_a_531_);
v___x_559_ = v_reuseFailAlloc_570_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_inc(v_stack_528_);
v___x_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v_stack_528_);
lean_inc(v_snd_552_);
lean_inc_ref(v_range_527_);
lean_inc_ref(v_preferred_529_);
v___x_561_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_529_, v_range_527_, v___x_560_, v___x_556_, v_snd_552_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; 
lean_dec(v_snd_552_);
lean_dec(v_fst_551_);
lean_dec(v_a_531_);
lean_dec_ref(v_preferred_529_);
lean_dec(v_stack_528_);
lean_dec_ref(v_range_527_);
lean_dec(v_stx_526_);
v___x_562_ = lean_box(0);
return v___x_562_;
}
else
{
lean_object* v_val_563_; 
v_val_563_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_val_563_);
lean_dec_ref(v___x_561_);
if (lean_obj_tag(v_val_563_) == 1)
{
if (lean_obj_tag(v_fst_551_) == 0)
{
if (v___x_530_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_box(0);
v___x_565_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_526_, v_a_531_, v___x_549_, v_snd_552_, v___x_564_, v_val_563_);
v___y_534_ = v___x_565_;
goto v___jp_533_;
}
else
{
lean_object* v___x_566_; 
lean_dec_ref(v_val_563_);
lean_dec(v_snd_552_);
lean_dec(v_a_531_);
lean_dec_ref(v_preferred_529_);
lean_dec(v_stack_528_);
lean_dec_ref(v_range_527_);
lean_dec(v_stx_526_);
v___x_566_ = lean_box(0);
return v___x_566_;
}
}
else
{
lean_object* v___x_567_; 
lean_dec_ref(v_fst_551_);
lean_dec_ref(v_val_563_);
lean_dec(v_snd_552_);
lean_dec(v_a_531_);
lean_dec_ref(v_preferred_529_);
lean_dec(v_stack_528_);
lean_dec_ref(v_range_527_);
lean_dec(v_stx_526_);
v___x_567_ = lean_box(0);
return v___x_567_;
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec(v_val_563_);
v___x_568_ = lean_box(0);
v___x_569_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_526_, v_a_531_, v___x_549_, v_snd_552_, v___x_568_, v_fst_551_);
v___y_534_ = v___x_569_;
goto v___jp_533_;
}
}
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v___x_557_);
lean_dec(v___x_556_);
lean_del_object(v___x_554_);
v___x_571_ = lean_box(0);
v___x_572_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_526_, v_a_531_, v___x_549_, v_snd_552_, v___x_571_, v_fst_551_);
v___y_534_ = v___x_572_;
goto v___jp_533_;
}
}
}
v___jp_533_:
{
if (lean_obj_tag(v___y_534_) == 0)
{
lean_object* v___x_535_; 
lean_dec(v_a_531_);
lean_dec_ref(v_preferred_529_);
lean_dec(v_stack_528_);
lean_dec_ref(v_range_527_);
lean_dec(v_stx_526_);
v___x_535_ = lean_box(0);
return v___x_535_;
}
else
{
lean_object* v_val_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_548_; 
v_val_536_ = lean_ctor_get(v___y_534_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___y_534_);
if (v_isSharedCheck_548_ == 0)
{
v___x_538_ = v___y_534_;
v_isShared_539_ = v_isSharedCheck_548_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_val_536_);
lean_dec(v___y_534_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_548_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
if (lean_obj_tag(v_val_536_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; 
lean_dec(v_a_531_);
lean_dec_ref(v_preferred_529_);
lean_dec(v_stack_528_);
lean_dec_ref(v_range_527_);
lean_dec(v_stx_526_);
v_a_540_ = lean_ctor_get(v_val_536_, 0);
lean_inc(v_a_540_);
lean_dec_ref(v_val_536_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v_a_540_);
v___x_542_ = v___x_538_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
lean_del_object(v___x_538_);
v_a_544_ = lean_ctor_get(v_val_536_, 0);
lean_inc(v_a_544_);
lean_dec_ref(v_val_536_);
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_nat_add(v_a_531_, v___x_545_);
lean_dec(v_a_531_);
v_a_531_ = v___x_546_;
v_b_532_ = v_a_544_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_574_, lean_object* v_stx_575_, lean_object* v_range_576_, lean_object* v_stack_577_, lean_object* v_preferred_578_, lean_object* v___x_579_, lean_object* v_a_580_, lean_object* v_b_581_){
_start:
{
uint8_t v___x_4660__boxed_582_; lean_object* v_res_583_; 
v___x_4660__boxed_582_ = lean_unbox(v___x_579_);
v_res_583_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_574_, v_stx_575_, v_range_576_, v_stack_577_, v_preferred_578_, v___x_4660__boxed_582_, v_a_580_, v_b_581_);
lean_dec(v_upperBound_574_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg___boxed(lean_object* v___y_584_, lean_object* v___x_585_, lean_object* v___x_586_, lean_object* v_range_587_, lean_object* v___x_588_, lean_object* v_preferred_589_, lean_object* v_a_590_, lean_object* v_b_591_){
_start:
{
uint8_t v___x_4691__boxed_592_; lean_object* v_res_593_; 
v___x_4691__boxed_592_ = lean_unbox(v___x_585_);
v_res_593_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_584_, v___x_4691__boxed_592_, v___x_586_, v_range_587_, v___x_588_, v_preferred_589_, v_a_590_, v_b_591_);
lean_dec(v___y_584_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(lean_object* v_upperBound_594_, lean_object* v_stx_595_, lean_object* v_range_596_, lean_object* v_stack_597_, lean_object* v_preferred_598_, uint8_t v___x_599_, lean_object* v_inst_600_, lean_object* v_R_601_, lean_object* v_a_602_, lean_object* v_b_603_, lean_object* v_c_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_594_, v_stx_595_, v_range_596_, v_stack_597_, v_preferred_598_, v___x_599_, v_a_602_, v_b_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___boxed(lean_object* v_upperBound_606_, lean_object* v_stx_607_, lean_object* v_range_608_, lean_object* v_stack_609_, lean_object* v_preferred_610_, lean_object* v___x_611_, lean_object* v_inst_612_, lean_object* v_R_613_, lean_object* v_a_614_, lean_object* v_b_615_, lean_object* v_c_616_){
_start:
{
uint8_t v___x_5063__boxed_617_; lean_object* v_res_618_; 
v___x_5063__boxed_617_ = lean_unbox(v___x_611_);
v_res_618_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(v_upperBound_606_, v_stx_607_, v_range_608_, v_stack_609_, v_preferred_610_, v___x_5063__boxed_617_, v_inst_612_, v_R_613_, v_a_614_, v_b_615_, v_c_616_);
lean_dec(v_upperBound_606_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(lean_object* v___y_619_, uint8_t v___x_620_, lean_object* v___x_621_, lean_object* v_range_622_, lean_object* v___x_623_, lean_object* v_preferred_624_, lean_object* v_inst_625_, lean_object* v_R_626_, lean_object* v_a_627_, lean_object* v_b_628_, lean_object* v_c_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_619_, v___x_620_, v___x_621_, v_range_622_, v___x_623_, v_preferred_624_, v_a_627_, v_b_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___boxed(lean_object* v___y_631_, lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v_range_634_, lean_object* v___x_635_, lean_object* v_preferred_636_, lean_object* v_inst_637_, lean_object* v_R_638_, lean_object* v_a_639_, lean_object* v_b_640_, lean_object* v_c_641_){
_start:
{
uint8_t v___x_5074__boxed_642_; lean_object* v_res_643_; 
v___x_5074__boxed_642_ = lean_unbox(v___x_632_);
v_res_643_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(v___y_631_, v___x_5074__boxed_642_, v___x_633_, v_range_634_, v___x_635_, v_preferred_636_, v_inst_637_, v_R_638_, v_a_639_, v_b_640_, v_c_641_);
lean_dec(v___y_631_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(lean_object* v_upperBound_644_, lean_object* v___x_645_, lean_object* v_range_646_, lean_object* v_inst_647_, lean_object* v_R_648_, lean_object* v_a_649_, lean_object* v_b_650_, lean_object* v_c_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_644_, v___x_645_, v_range_646_, v_a_649_, v_b_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___boxed(lean_object* v_upperBound_653_, lean_object* v___x_654_, lean_object* v_range_655_, lean_object* v_inst_656_, lean_object* v_R_657_, lean_object* v_a_658_, lean_object* v_b_659_, lean_object* v_c_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(v_upperBound_653_, v___x_654_, v_range_655_, v_inst_656_, v_R_657_, v_a_658_, v_b_659_, v_c_660_);
lean_dec_ref(v_b_659_);
lean_dec(v___x_654_);
lean_dec(v_upperBound_653_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findTactic_x3f(lean_object* v_preferred_662_, lean_object* v_range_663_, lean_object* v_root_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_box(0);
v___x_666_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_663_, v_root_664_, v___x_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_dec(v_root_664_);
lean_dec_ref(v_range_663_);
lean_dec_ref(v_preferred_662_);
return v___x_665_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec_ref(v___x_666_);
v___x_667_ = lean_box(0);
v___x_668_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_662_, v_range_663_, v___x_667_, v_root_664_, v___x_665_);
if (lean_obj_tag(v___x_668_) == 0)
{
return v___x_665_;
}
else
{
lean_object* v_val_669_; 
v_val_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_val_669_);
lean_dec_ref(v___x_668_);
return v_val_669_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(lean_object* v_ctx_x3f_682_, lean_object* v_i_683_, lean_object* v_kind_684_, lean_object* v_tgtRange_685_, lean_object* v_f_686_, uint8_t v_canonicalOnly_687_, lean_object* v_as_688_, size_t v_sz_689_, size_t v_i_690_, lean_object* v_b_691_){
_start:
{
uint8_t v___x_692_; 
v___x_692_ = lean_usize_dec_lt(v_i_690_, v_sz_689_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
lean_dec_ref(v_f_686_);
lean_dec(v_ctx_x3f_682_);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v_b_691_);
return v___x_693_;
}
else
{
lean_object* v_snd_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_719_; 
v_snd_694_ = lean_ctor_get(v_b_691_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_b_691_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v_b_691_, 0);
lean_dec(v_unused_720_);
v___x_696_ = v_b_691_;
v_isShared_697_ = v_isSharedCheck_719_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snd_694_);
lean_dec(v_b_691_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_719_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v_a_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_698_ = lean_box(0);
v_a_699_ = lean_array_uget_borrowed(v_as_688_, v_i_690_);
lean_inc(v_ctx_x3f_682_);
v___x_700_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_682_, v_i_683_);
lean_inc_ref(v_f_686_);
lean_inc(v_a_699_);
v___x_701_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_684_, v_tgtRange_685_, v___x_700_, v_a_699_, v_f_686_, v_canonicalOnly_687_);
if (lean_obj_tag(v___x_701_) == 1)
{
lean_object* v___x_703_; 
lean_dec_ref(v_f_686_);
lean_dec(v_ctx_x3f_682_);
lean_inc_ref(v___x_701_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_698_);
lean_ctor_set(v___x_696_, 0, v___x_701_);
v___x_703_ = v___x_696_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_698_);
v___x_703_ = v_reuseFailAlloc_714_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_712_; 
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v___x_701_, 0);
lean_dec(v_unused_713_);
v___x_705_ = v___x_701_;
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
else
{
lean_dec(v___x_701_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_703_);
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_703_);
v___x_708_ = v_reuseFailAlloc_711_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v_snd_694_);
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
}
}
}
else
{
lean_object* v___x_715_; size_t v___x_716_; size_t v___x_717_; 
lean_dec(v___x_701_);
lean_del_object(v___x_696_);
lean_dec(v_snd_694_);
v___x_715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1));
v___x_716_ = ((size_t)1ULL);
v___x_717_ = lean_usize_add(v_i_690_, v___x_716_);
v_i_690_ = v___x_717_;
v_b_691_ = v___x_715_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(lean_object* v_ctx_x3f_721_, lean_object* v_i_722_, lean_object* v_kind_723_, lean_object* v_tgtRange_724_, lean_object* v_f_725_, uint8_t v_canonicalOnly_726_, lean_object* v_as_727_, size_t v_sz_728_, size_t v_i_729_, lean_object* v_b_730_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_lt(v_i_729_, v_sz_728_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
lean_dec_ref(v_f_725_);
lean_dec(v_ctx_x3f_721_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v_b_730_);
return v___x_732_;
}
else
{
lean_object* v_snd_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_758_; 
v_snd_733_ = lean_ctor_get(v_b_730_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_b_730_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v_b_730_, 0);
lean_dec(v_unused_759_);
v___x_735_ = v_b_730_;
v_isShared_736_ = v_isSharedCheck_758_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_snd_733_);
lean_dec(v_b_730_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_758_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v_a_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_737_ = lean_box(0);
v_a_738_ = lean_array_uget_borrowed(v_as_727_, v_i_729_);
lean_inc(v_ctx_x3f_721_);
v___x_739_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_721_, v_i_722_);
lean_inc_ref(v_f_725_);
lean_inc(v_a_738_);
v___x_740_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_723_, v_tgtRange_724_, v___x_739_, v_a_738_, v_f_725_, v_canonicalOnly_726_);
if (lean_obj_tag(v___x_740_) == 1)
{
lean_object* v___x_742_; 
lean_dec_ref(v_f_725_);
lean_dec(v_ctx_x3f_721_);
lean_inc_ref(v___x_740_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_737_);
lean_ctor_set(v___x_735_, 0, v___x_740_);
v___x_742_ = v___x_735_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_737_);
v___x_742_ = v_reuseFailAlloc_753_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_751_; 
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; 
v_unused_752_ = lean_ctor_get(v___x_740_, 0);
lean_dec(v_unused_752_);
v___x_744_ = v___x_740_;
v_isShared_745_ = v_isSharedCheck_751_;
goto v_resetjp_743_;
}
else
{
lean_dec(v___x_740_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_751_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_742_);
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_742_);
v___x_747_ = v_reuseFailAlloc_750_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v_snd_733_);
v___x_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
}
}
else
{
lean_object* v___x_754_; size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
lean_dec(v___x_740_);
lean_del_object(v___x_735_);
lean_dec(v_snd_733_);
v___x_754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1));
v___x_755_ = ((size_t)1ULL);
v___x_756_ = lean_usize_add(v_i_729_, v___x_755_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_721_, v_i_722_, v_kind_723_, v_tgtRange_724_, v_f_725_, v_canonicalOnly_726_, v_as_727_, v_sz_728_, v___x_756_, v___x_754_);
return v___x_757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(lean_object* v_ctx_x3f_760_, lean_object* v_i_761_, lean_object* v_kind_762_, lean_object* v_tgtRange_763_, lean_object* v_f_764_, uint8_t v_canonicalOnly_765_, lean_object* v_t_766_, lean_object* v_init_767_){
_start:
{
lean_object* v_root_768_; lean_object* v_tail_769_; lean_object* v___x_770_; 
v_root_768_ = lean_ctor_get(v_t_766_, 0);
v_tail_769_ = lean_ctor_get(v_t_766_, 1);
lean_inc_ref(v_f_764_);
lean_inc(v_ctx_x3f_760_);
lean_inc_ref(v_init_767_);
v___x_770_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_767_, v_ctx_x3f_760_, v_i_761_, v_kind_762_, v_tgtRange_763_, v_f_764_, v_canonicalOnly_765_, v_root_768_, v_init_767_);
lean_dec_ref(v_init_767_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_771_; 
lean_dec_ref(v_f_764_);
lean_dec(v_ctx_x3f_760_);
v___x_771_ = lean_box(0);
return v___x_771_;
}
else
{
lean_object* v_val_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_796_; 
v_val_772_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_796_ == 0)
{
v___x_774_ = v___x_770_;
v_isShared_775_ = v_isSharedCheck_796_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_val_772_);
lean_dec(v___x_770_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_796_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
if (lean_obj_tag(v_val_772_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; 
lean_dec_ref(v_f_764_);
lean_dec(v_ctx_x3f_760_);
v_a_776_ = lean_ctor_get(v_val_772_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v_val_772_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v_a_776_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_781_; lean_object* v___x_782_; size_t v_sz_783_; size_t v___x_784_; lean_object* v___x_785_; 
lean_del_object(v___x_774_);
v_a_780_ = lean_ctor_get(v_val_772_, 0);
lean_inc(v_a_780_);
lean_dec_ref(v_val_772_);
v___x_781_ = lean_box(0);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_a_780_);
v_sz_783_ = lean_array_size(v_tail_769_);
v___x_784_ = ((size_t)0ULL);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_760_, v_i_761_, v_kind_762_, v_tgtRange_763_, v_f_764_, v_canonicalOnly_765_, v_tail_769_, v_sz_783_, v___x_784_, v___x_782_);
if (lean_obj_tag(v___x_785_) == 0)
{
return v___x_781_;
}
else
{
lean_object* v_val_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_795_; 
v_val_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_795_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_795_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_val_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_795_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_fst_790_; 
v_fst_790_ = lean_ctor_get(v_val_786_, 0);
if (lean_obj_tag(v_fst_790_) == 0)
{
lean_object* v_snd_791_; lean_object* v___x_793_; 
v_snd_791_ = lean_ctor_get(v_val_786_, 1);
lean_inc(v_snd_791_);
lean_dec(v_val_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_snd_791_);
v___x_793_ = v___x_788_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_snd_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
else
{
lean_inc_ref(v_fst_790_);
lean_del_object(v___x_788_);
lean_dec(v_val_786_);
return v_fst_790_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f(lean_object* v_kind_797_, lean_object* v_tgtRange_798_, lean_object* v_ctx_x3f_799_, lean_object* v_t_800_, lean_object* v_f_801_, uint8_t v_canonicalOnly_802_){
_start:
{
switch(lean_obj_tag(v_t_800_))
{
case 0:
{
lean_object* v_i_803_; lean_object* v_t_804_; lean_object* v___x_805_; 
v_i_803_ = lean_ctor_get(v_t_800_, 0);
lean_inc_ref(v_i_803_);
v_t_804_ = lean_ctor_get(v_t_800_, 1);
lean_inc_ref(v_t_804_);
lean_dec_ref(v_t_800_);
v___x_805_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_803_, v_ctx_x3f_799_);
v_ctx_x3f_799_ = v___x_805_;
v_t_800_ = v_t_804_;
goto _start;
}
case 1:
{
lean_object* v_i_807_; lean_object* v_children_808_; 
v_i_807_ = lean_ctor_get(v_t_800_, 0);
v_children_808_ = lean_ctor_get(v_t_800_, 1);
if (lean_obj_tag(v_ctx_x3f_799_) == 1)
{
lean_object* v_val_815_; uint8_t v___y_817_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_val_815_ = lean_ctor_get(v_ctx_x3f_799_, 0);
v___x_829_ = l_Lean_Elab_Info_stx(v_i_807_);
v___x_830_ = l_Lean_Syntax_getRange_x3f(v___x_829_, v_canonicalOnly_802_);
if (lean_obj_tag(v___x_830_) == 1)
{
lean_object* v_val_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_val_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_val_831_);
lean_dec_ref(v___x_830_);
v___x_832_ = l_Lean_Syntax_getKind(v___x_829_);
v___x_833_ = lean_name_eq(v___x_832_, v_kind_797_);
lean_dec(v___x_832_);
if (v___x_833_ == 0)
{
lean_dec(v_val_831_);
v___y_817_ = v___x_833_;
goto v___jp_816_;
}
else
{
uint8_t v___x_834_; 
v___x_834_ = l_Lean_Syntax_instBEqRange_beq(v_val_831_, v_tgtRange_798_);
lean_dec(v_val_831_);
v___y_817_ = v___x_834_;
goto v___jp_816_;
}
}
else
{
lean_inc_ref(v_children_808_);
lean_inc_ref(v_i_807_);
lean_dec(v___x_830_);
lean_dec(v___x_829_);
lean_dec_ref(v_t_800_);
goto v___jp_809_;
}
v___jp_816_:
{
if (v___y_817_ == 0)
{
lean_inc_ref(v_children_808_);
lean_inc_ref(v_i_807_);
lean_dec_ref(v_t_800_);
goto v___jp_809_;
}
else
{
lean_object* v___x_818_; uint8_t v___x_819_; 
lean_inc_ref(v_f_801_);
lean_inc_ref(v_i_807_);
lean_inc(v_val_815_);
v___x_818_ = lean_apply_2(v_f_801_, v_val_815_, v_i_807_);
v___x_819_ = lean_unbox(v___x_818_);
if (v___x_819_ == 0)
{
lean_inc_ref(v_children_808_);
lean_inc_ref(v_i_807_);
lean_dec_ref(v_t_800_);
goto v___jp_809_;
}
else
{
lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_827_; 
lean_inc(v_val_815_);
lean_dec_ref(v_f_801_);
v_isSharedCheck_827_ = !lean_is_exclusive(v_ctx_x3f_799_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v_ctx_x3f_799_, 0);
lean_dec(v_unused_828_);
v___x_821_ = v_ctx_x3f_799_;
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
else
{
lean_dec(v_ctx_x3f_799_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v_val_815_);
lean_ctor_set(v___x_823_, 1, v_t_800_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
}
else
{
lean_inc_ref(v_children_808_);
lean_inc_ref(v_i_807_);
lean_dec_ref(v_t_800_);
goto v___jp_809_;
}
v___jp_809_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_810_ = lean_box(0);
v___x_811_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0));
v___x_812_ = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(v_ctx_x3f_799_, v_i_807_, v_kind_797_, v_tgtRange_798_, v_f_801_, v_canonicalOnly_802_, v_children_808_, v___x_811_);
lean_dec_ref(v_children_808_);
lean_dec_ref(v_i_807_);
if (lean_obj_tag(v___x_812_) == 0)
{
return v___x_810_;
}
else
{
lean_object* v_val_813_; lean_object* v_fst_814_; 
v_val_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_val_813_);
lean_dec_ref(v___x_812_);
v_fst_814_ = lean_ctor_get(v_val_813_, 0);
lean_inc(v_fst_814_);
lean_dec(v_val_813_);
if (lean_obj_tag(v_fst_814_) == 0)
{
return v___x_810_;
}
else
{
return v_fst_814_;
}
}
}
}
default: 
{
lean_object* v___x_835_; 
lean_dec_ref(v_f_801_);
lean_dec_ref(v_t_800_);
lean_dec(v_ctx_x3f_799_);
v___x_835_ = lean_box(0);
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_ctx_x3f_845_, lean_object* v_i_846_, lean_object* v_kind_847_, lean_object* v_tgtRange_848_, lean_object* v_f_849_, uint8_t v_canonicalOnly_850_, lean_object* v_as_851_, size_t v_sz_852_, size_t v_i_853_, lean_object* v_b_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = lean_usize_dec_lt(v_i_853_, v_sz_852_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_dec_ref(v_f_849_);
lean_dec(v_ctx_x3f_845_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v_b_854_);
return v___x_856_;
}
else
{
lean_object* v_snd_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_883_; 
v_snd_857_ = lean_ctor_get(v_b_854_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_b_854_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; 
v_unused_884_ = lean_ctor_get(v_b_854_, 0);
lean_dec(v_unused_884_);
v___x_859_ = v_b_854_;
v_isShared_860_ = v_isSharedCheck_883_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_snd_857_);
lean_dec(v_b_854_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_883_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_861_ = lean_box(0);
v_a_862_ = lean_array_uget_borrowed(v_as_851_, v_i_853_);
lean_inc(v_ctx_x3f_845_);
v___x_863_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_845_, v_i_846_);
lean_inc_ref(v_f_849_);
lean_inc(v_a_862_);
v___x_864_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_847_, v_tgtRange_848_, v___x_863_, v_a_862_, v_f_849_, v_canonicalOnly_850_);
if (lean_obj_tag(v___x_864_) == 1)
{
lean_object* v___x_866_; 
lean_dec_ref(v_f_849_);
lean_dec(v_ctx_x3f_845_);
lean_inc_ref(v___x_864_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v___x_861_);
lean_ctor_set(v___x_859_, 0, v___x_864_);
v___x_866_ = v___x_859_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_861_);
v___x_866_ = v_reuseFailAlloc_878_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_876_; 
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; 
v_unused_877_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_877_);
v___x_868_ = v___x_864_;
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
else
{
lean_dec(v___x_864_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_866_);
v___x_871_ = v_reuseFailAlloc_875_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v_snd_857_);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
}
}
}
else
{
lean_object* v___x_879_; size_t v___x_880_; size_t v___x_881_; 
lean_dec(v___x_864_);
lean_del_object(v___x_859_);
lean_dec(v_snd_857_);
v___x_879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_add(v_i_853_, v___x_880_);
v_i_853_ = v___x_881_;
v_b_854_ = v___x_879_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(lean_object* v_ctx_x3f_885_, lean_object* v_i_886_, lean_object* v_kind_887_, lean_object* v_tgtRange_888_, lean_object* v_f_889_, uint8_t v_canonicalOnly_890_, lean_object* v_as_891_, size_t v_sz_892_, size_t v_i_893_, lean_object* v_b_894_){
_start:
{
uint8_t v___x_895_; 
v___x_895_ = lean_usize_dec_lt(v_i_893_, v_sz_892_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec_ref(v_f_889_);
lean_dec(v_ctx_x3f_885_);
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_b_894_);
return v___x_896_;
}
else
{
lean_object* v_snd_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_923_; 
v_snd_897_ = lean_ctor_get(v_b_894_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v_b_894_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v_b_894_, 0);
lean_dec(v_unused_924_);
v___x_899_ = v_b_894_;
v_isShared_900_ = v_isSharedCheck_923_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_snd_897_);
lean_dec(v_b_894_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_923_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v_a_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_901_ = lean_box(0);
v_a_902_ = lean_array_uget_borrowed(v_as_891_, v_i_893_);
lean_inc(v_ctx_x3f_885_);
v___x_903_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_885_, v_i_886_);
lean_inc_ref(v_f_889_);
lean_inc(v_a_902_);
v___x_904_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_887_, v_tgtRange_888_, v___x_903_, v_a_902_, v_f_889_, v_canonicalOnly_890_);
if (lean_obj_tag(v___x_904_) == 1)
{
lean_object* v___x_906_; 
lean_dec_ref(v_f_889_);
lean_dec(v_ctx_x3f_885_);
lean_inc_ref(v___x_904_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v___x_901_);
lean_ctor_set(v___x_899_, 0, v___x_904_);
v___x_906_ = v___x_899_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v___x_901_);
v___x_906_ = v_reuseFailAlloc_918_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_916_; 
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v___x_904_, 0);
lean_dec(v_unused_917_);
v___x_908_ = v___x_904_;
v_isShared_909_ = v_isSharedCheck_916_;
goto v_resetjp_907_;
}
else
{
lean_dec(v___x_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_916_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_906_);
v___x_911_ = v_reuseFailAlloc_915_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v_snd_897_);
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
}
}
else
{
lean_object* v___x_919_; size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; 
lean_dec(v___x_904_);
lean_del_object(v___x_899_);
lean_dec(v_snd_897_);
v___x_919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0));
v___x_920_ = ((size_t)1ULL);
v___x_921_ = lean_usize_add(v_i_893_, v___x_920_);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_885_, v_i_886_, v_kind_887_, v_tgtRange_888_, v_f_889_, v_canonicalOnly_890_, v_as_891_, v_sz_892_, v___x_921_, v___x_919_);
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(lean_object* v_init_925_, lean_object* v_ctx_x3f_926_, lean_object* v_i_927_, lean_object* v_kind_928_, lean_object* v_tgtRange_929_, lean_object* v_f_930_, uint8_t v_canonicalOnly_931_, lean_object* v_n_932_, lean_object* v_b_933_){
_start:
{
if (lean_obj_tag(v_n_932_) == 0)
{
lean_object* v_cs_934_; lean_object* v___x_935_; lean_object* v___x_936_; size_t v_sz_937_; size_t v___x_938_; lean_object* v___x_939_; 
v_cs_934_ = lean_ctor_get(v_n_932_, 0);
v___x_935_ = lean_box(0);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v_b_933_);
v_sz_937_ = lean_array_size(v_cs_934_);
v___x_938_ = ((size_t)0ULL);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_925_, v_ctx_x3f_926_, v_i_927_, v_kind_928_, v_tgtRange_929_, v_f_930_, v_canonicalOnly_931_, v_cs_934_, v_sz_937_, v___x_938_, v___x_936_);
if (lean_obj_tag(v___x_939_) == 0)
{
return v___x_935_;
}
else
{
lean_object* v_val_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_950_; 
v_val_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_950_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_950_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_val_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_950_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_fst_944_; 
v_fst_944_ = lean_ctor_get(v_val_940_, 0);
if (lean_obj_tag(v_fst_944_) == 0)
{
lean_object* v_snd_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v_snd_945_ = lean_ctor_get(v_val_940_, 1);
lean_inc(v_snd_945_);
lean_dec(v_val_940_);
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v_snd_945_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_946_);
v___x_948_ = v___x_942_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
else
{
lean_inc_ref(v_fst_944_);
lean_del_object(v___x_942_);
lean_dec(v_val_940_);
return v_fst_944_;
}
}
}
}
else
{
lean_object* v_vs_951_; lean_object* v___x_952_; lean_object* v___x_953_; size_t v_sz_954_; size_t v___x_955_; lean_object* v___x_956_; 
v_vs_951_ = lean_ctor_get(v_n_932_, 0);
v___x_952_ = lean_box(0);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set(v___x_953_, 1, v_b_933_);
v_sz_954_ = lean_array_size(v_vs_951_);
v___x_955_ = ((size_t)0ULL);
v___x_956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_926_, v_i_927_, v_kind_928_, v_tgtRange_929_, v_f_930_, v_canonicalOnly_931_, v_vs_951_, v_sz_954_, v___x_955_, v___x_953_);
if (lean_obj_tag(v___x_956_) == 0)
{
return v___x_952_;
}
else
{
lean_object* v_val_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_967_; 
v_val_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_967_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_val_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_fst_961_; 
v_fst_961_ = lean_ctor_get(v_val_957_, 0);
if (lean_obj_tag(v_fst_961_) == 0)
{
lean_object* v_snd_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v_snd_962_ = lean_ctor_get(v_val_957_, 1);
lean_inc(v_snd_962_);
lean_dec(v_val_957_);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v_snd_962_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_963_);
v___x_965_ = v___x_959_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
lean_inc_ref(v_fst_961_);
lean_del_object(v___x_959_);
lean_dec(v_val_957_);
return v_fst_961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(lean_object* v_init_968_, lean_object* v_ctx_x3f_969_, lean_object* v_i_970_, lean_object* v_kind_971_, lean_object* v_tgtRange_972_, lean_object* v_f_973_, uint8_t v_canonicalOnly_974_, lean_object* v_as_975_, size_t v_sz_976_, size_t v_i_977_, lean_object* v_b_978_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = lean_usize_dec_lt(v_i_977_, v_sz_976_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
lean_dec_ref(v_f_973_);
lean_dec(v_ctx_x3f_969_);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v_b_978_);
return v___x_980_;
}
else
{
lean_object* v_snd_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1008_; 
v_snd_981_ = lean_ctor_get(v_b_978_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_b_978_);
if (v_isSharedCheck_1008_ == 0)
{
lean_object* v_unused_1009_; 
v_unused_1009_ = lean_ctor_get(v_b_978_, 0);
lean_dec(v_unused_1009_);
v___x_983_ = v_b_978_;
v_isShared_984_ = v_isSharedCheck_1008_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_snd_981_);
lean_dec(v_b_978_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1008_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_a_985_; lean_object* v___x_986_; 
v_a_985_ = lean_array_uget_borrowed(v_as_975_, v_i_977_);
lean_inc(v_snd_981_);
lean_inc_ref(v_f_973_);
lean_inc(v_ctx_x3f_969_);
v___x_986_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_968_, v_ctx_x3f_969_, v_i_970_, v_kind_971_, v_tgtRange_972_, v_f_973_, v_canonicalOnly_974_, v_a_985_, v_snd_981_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v___x_987_; 
lean_del_object(v___x_983_);
lean_dec(v_snd_981_);
lean_dec_ref(v_f_973_);
lean_dec(v_ctx_x3f_969_);
v___x_987_ = lean_box(0);
return v___x_987_;
}
else
{
lean_object* v_val_988_; 
v_val_988_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_val_988_);
if (lean_obj_tag(v_val_988_) == 0)
{
lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref(v_f_973_);
lean_dec(v_ctx_x3f_969_);
v_isSharedCheck_998_ = !lean_is_exclusive(v_val_988_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v_val_988_, 0);
lean_dec(v_unused_999_);
v___x_990_ = v_val_988_;
v_isShared_991_ = v_isSharedCheck_998_;
goto v_resetjp_989_;
}
else
{
lean_dec(v_val_988_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_998_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_986_);
v___x_993_ = v___x_983_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_snd_981_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 1);
lean_ctor_set(v___x_990_, 0, v___x_993_);
v___x_995_ = v___x_990_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
lean_dec_ref(v___x_986_);
lean_dec(v_snd_981_);
v_a_1000_ = lean_ctor_get(v_val_988_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v_val_988_);
v___x_1001_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v_a_1000_);
lean_ctor_set(v___x_983_, 0, v___x_1001_);
v___x_1003_ = v___x_983_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_a_1000_);
v___x_1003_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
size_t v___x_1004_; size_t v___x_1005_; 
v___x_1004_ = ((size_t)1ULL);
v___x_1005_ = lean_usize_add(v_i_977_, v___x_1004_);
v_i_977_ = v___x_1005_;
v_b_978_ = v___x_1003_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1010_, lean_object* v_ctx_x3f_1011_, lean_object* v_i_1012_, lean_object* v_kind_1013_, lean_object* v_tgtRange_1014_, lean_object* v_f_1015_, lean_object* v_canonicalOnly_1016_, lean_object* v_as_1017_, lean_object* v_sz_1018_, lean_object* v_i_1019_, lean_object* v_b_1020_){
_start:
{
uint8_t v_canonicalOnly_boxed_1021_; size_t v_sz_boxed_1022_; size_t v_i_boxed_1023_; lean_object* v_res_1024_; 
v_canonicalOnly_boxed_1021_ = lean_unbox(v_canonicalOnly_1016_);
v_sz_boxed_1022_ = lean_unbox_usize(v_sz_1018_);
lean_dec(v_sz_1018_);
v_i_boxed_1023_ = lean_unbox_usize(v_i_1019_);
lean_dec(v_i_1019_);
v_res_1024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_1010_, v_ctx_x3f_1011_, v_i_1012_, v_kind_1013_, v_tgtRange_1014_, v_f_1015_, v_canonicalOnly_boxed_1021_, v_as_1017_, v_sz_boxed_1022_, v_i_boxed_1023_, v_b_1020_);
lean_dec_ref(v_as_1017_);
lean_dec_ref(v_tgtRange_1014_);
lean_dec(v_kind_1013_);
lean_dec_ref(v_i_1012_);
lean_dec_ref(v_init_1010_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0___boxed(lean_object* v_ctx_x3f_1025_, lean_object* v_i_1026_, lean_object* v_kind_1027_, lean_object* v_tgtRange_1028_, lean_object* v_f_1029_, lean_object* v_canonicalOnly_1030_, lean_object* v_t_1031_, lean_object* v_init_1032_){
_start:
{
uint8_t v_canonicalOnly_boxed_1033_; lean_object* v_res_1034_; 
v_canonicalOnly_boxed_1033_ = lean_unbox(v_canonicalOnly_1030_);
v_res_1034_ = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(v_ctx_x3f_1025_, v_i_1026_, v_kind_1027_, v_tgtRange_1028_, v_f_1029_, v_canonicalOnly_boxed_1033_, v_t_1031_, v_init_1032_);
lean_dec_ref(v_t_1031_);
lean_dec_ref(v_tgtRange_1028_);
lean_dec(v_kind_1027_);
lean_dec_ref(v_i_1026_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___boxed(lean_object* v_ctx_x3f_1035_, lean_object* v_i_1036_, lean_object* v_kind_1037_, lean_object* v_tgtRange_1038_, lean_object* v_f_1039_, lean_object* v_canonicalOnly_1040_, lean_object* v_as_1041_, lean_object* v_sz_1042_, lean_object* v_i_1043_, lean_object* v_b_1044_){
_start:
{
uint8_t v_canonicalOnly_boxed_1045_; size_t v_sz_boxed_1046_; size_t v_i_boxed_1047_; lean_object* v_res_1048_; 
v_canonicalOnly_boxed_1045_ = lean_unbox(v_canonicalOnly_1040_);
v_sz_boxed_1046_ = lean_unbox_usize(v_sz_1042_);
lean_dec(v_sz_1042_);
v_i_boxed_1047_ = lean_unbox_usize(v_i_1043_);
lean_dec(v_i_1043_);
v_res_1048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_1035_, v_i_1036_, v_kind_1037_, v_tgtRange_1038_, v_f_1039_, v_canonicalOnly_boxed_1045_, v_as_1041_, v_sz_boxed_1046_, v_i_boxed_1047_, v_b_1044_);
lean_dec_ref(v_as_1041_);
lean_dec_ref(v_tgtRange_1038_);
lean_dec(v_kind_1037_);
lean_dec_ref(v_i_1036_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_ctx_x3f_1049_, lean_object* v_i_1050_, lean_object* v_kind_1051_, lean_object* v_tgtRange_1052_, lean_object* v_f_1053_, lean_object* v_canonicalOnly_1054_, lean_object* v_as_1055_, lean_object* v_sz_1056_, lean_object* v_i_1057_, lean_object* v_b_1058_){
_start:
{
uint8_t v_canonicalOnly_boxed_1059_; size_t v_sz_boxed_1060_; size_t v_i_boxed_1061_; lean_object* v_res_1062_; 
v_canonicalOnly_boxed_1059_ = lean_unbox(v_canonicalOnly_1054_);
v_sz_boxed_1060_ = lean_unbox_usize(v_sz_1056_);
lean_dec(v_sz_1056_);
v_i_boxed_1061_ = lean_unbox_usize(v_i_1057_);
lean_dec(v_i_1057_);
v_res_1062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_1049_, v_i_1050_, v_kind_1051_, v_tgtRange_1052_, v_f_1053_, v_canonicalOnly_boxed_1059_, v_as_1055_, v_sz_boxed_1060_, v_i_boxed_1061_, v_b_1058_);
lean_dec_ref(v_as_1055_);
lean_dec_ref(v_tgtRange_1052_);
lean_dec(v_kind_1051_);
lean_dec_ref(v_i_1050_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_ctx_x3f_1063_, lean_object* v_i_1064_, lean_object* v_kind_1065_, lean_object* v_tgtRange_1066_, lean_object* v_f_1067_, lean_object* v_canonicalOnly_1068_, lean_object* v_as_1069_, lean_object* v_sz_1070_, lean_object* v_i_1071_, lean_object* v_b_1072_){
_start:
{
uint8_t v_canonicalOnly_boxed_1073_; size_t v_sz_boxed_1074_; size_t v_i_boxed_1075_; lean_object* v_res_1076_; 
v_canonicalOnly_boxed_1073_ = lean_unbox(v_canonicalOnly_1068_);
v_sz_boxed_1074_ = lean_unbox_usize(v_sz_1070_);
lean_dec(v_sz_1070_);
v_i_boxed_1075_ = lean_unbox_usize(v_i_1071_);
lean_dec(v_i_1071_);
v_res_1076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_1063_, v_i_1064_, v_kind_1065_, v_tgtRange_1066_, v_f_1067_, v_canonicalOnly_boxed_1073_, v_as_1069_, v_sz_boxed_1074_, v_i_boxed_1075_, v_b_1072_);
lean_dec_ref(v_as_1069_);
lean_dec_ref(v_tgtRange_1066_);
lean_dec(v_kind_1065_);
lean_dec_ref(v_i_1064_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_ctx_x3f_1077_, lean_object* v_i_1078_, lean_object* v_kind_1079_, lean_object* v_tgtRange_1080_, lean_object* v_f_1081_, lean_object* v_canonicalOnly_1082_, lean_object* v_as_1083_, lean_object* v_sz_1084_, lean_object* v_i_1085_, lean_object* v_b_1086_){
_start:
{
uint8_t v_canonicalOnly_boxed_1087_; size_t v_sz_boxed_1088_; size_t v_i_boxed_1089_; lean_object* v_res_1090_; 
v_canonicalOnly_boxed_1087_ = lean_unbox(v_canonicalOnly_1082_);
v_sz_boxed_1088_ = lean_unbox_usize(v_sz_1084_);
lean_dec(v_sz_1084_);
v_i_boxed_1089_ = lean_unbox_usize(v_i_1085_);
lean_dec(v_i_1085_);
v_res_1090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_1077_, v_i_1078_, v_kind_1079_, v_tgtRange_1080_, v_f_1081_, v_canonicalOnly_boxed_1087_, v_as_1083_, v_sz_boxed_1088_, v_i_boxed_1089_, v_b_1086_);
lean_dec_ref(v_as_1083_);
lean_dec_ref(v_tgtRange_1080_);
lean_dec(v_kind_1079_);
lean_dec_ref(v_i_1078_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0___boxed(lean_object* v_init_1091_, lean_object* v_ctx_x3f_1092_, lean_object* v_i_1093_, lean_object* v_kind_1094_, lean_object* v_tgtRange_1095_, lean_object* v_f_1096_, lean_object* v_canonicalOnly_1097_, lean_object* v_n_1098_, lean_object* v_b_1099_){
_start:
{
uint8_t v_canonicalOnly_boxed_1100_; lean_object* v_res_1101_; 
v_canonicalOnly_boxed_1100_ = lean_unbox(v_canonicalOnly_1097_);
v_res_1101_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_1091_, v_ctx_x3f_1092_, v_i_1093_, v_kind_1094_, v_tgtRange_1095_, v_f_1096_, v_canonicalOnly_boxed_1100_, v_n_1098_, v_b_1099_);
lean_dec_ref(v_n_1098_);
lean_dec_ref(v_tgtRange_1095_);
lean_dec(v_kind_1094_);
lean_dec_ref(v_i_1093_);
lean_dec_ref(v_init_1091_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f___boxed(lean_object* v_kind_1102_, lean_object* v_tgtRange_1103_, lean_object* v_ctx_x3f_1104_, lean_object* v_t_1105_, lean_object* v_f_1106_, lean_object* v_canonicalOnly_1107_){
_start:
{
uint8_t v_canonicalOnly_boxed_1108_; lean_object* v_res_1109_; 
v_canonicalOnly_boxed_1108_ = lean_unbox(v_canonicalOnly_1107_);
v_res_1109_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_1102_, v_tgtRange_1103_, v_ctx_x3f_1104_, v_t_1105_, v_f_1106_, v_canonicalOnly_boxed_1108_);
lean_dec_ref(v_tgtRange_1103_);
lean_dec(v_kind_1102_);
return v_res_1109_;
}
}
static lean_object* _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_1111_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_1111_, 0, lean_box(0));
lean_closure_set(v___x_1111_, 1, lean_box(0));
lean_closure_set(v___x_1111_, 2, v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(lean_object* v_msg_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v___f_1116_; lean_object* v___x_4027__overap_1117_; lean_object* v___x_1118_; 
v___x_1115_ = lean_obj_once(&l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0, &l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0_once, _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0);
v___f_1116_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1116_, 0, v___x_1115_);
v___x_4027__overap_1117_ = lean_panic_fn_borrowed(v___f_1116_, v_msg_1112_);
lean_dec_ref(v___f_1116_);
lean_inc_ref(v___y_1113_);
v___x_1118_ = lean_apply_2(v___x_4027__overap_1117_, v___y_1113_, lean_box(0));
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___boxed(lean_object* v_msg_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v_msg_1119_, v___y_1120_);
lean_dec_ref(v___y_1120_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0(lean_object* v___x_1123_, lean_object* v___x_1124_, lean_object* v_ctx_1125_, lean_object* v_node_1126_, lean_object* v_result_1127_){
_start:
{
uint8_t v___y_1129_; 
if (lean_obj_tag(v_node_1126_) == 1)
{
lean_object* v_i_1132_; 
v_i_1132_ = lean_ctor_get(v_node_1126_, 0);
if (lean_obj_tag(v_i_1132_) == 3)
{
lean_object* v_i_1133_; lean_object* v_stx_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; 
v_i_1133_ = lean_ctor_get(v_i_1132_, 0);
v_stx_1134_ = lean_ctor_get(v_i_1133_, 1);
v___x_1135_ = 1;
v___x_1136_ = l_Lean_Syntax_getPos_x3f(v_stx_1134_, v___x_1135_);
if (lean_obj_tag(v___x_1136_) == 1)
{
lean_object* v_val_1137_; lean_object* v___x_1138_; 
v_val_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_val_1137_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1134_, v___x_1135_);
if (lean_obj_tag(v___x_1138_) == 1)
{
lean_object* v_val_1139_; uint8_t v___x_1140_; 
v_val_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_val_1139_);
lean_dec_ref(v___x_1138_);
v___x_1140_ = lean_nat_dec_le(v_val_1137_, v___x_1123_);
lean_dec(v_val_1137_);
if (v___x_1140_ == 0)
{
lean_dec(v_val_1139_);
v___y_1129_ = v___x_1140_;
goto v___jp_1128_;
}
else
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_nat_dec_le(v___x_1124_, v_val_1139_);
lean_dec(v_val_1139_);
v___y_1129_ = v___x_1141_;
goto v___jp_1128_;
}
}
else
{
lean_dec(v___x_1138_);
lean_dec(v_val_1137_);
lean_dec_ref(v_node_1126_);
lean_dec_ref(v_ctx_1125_);
return v_result_1127_;
}
}
else
{
lean_dec(v___x_1136_);
lean_dec_ref(v_node_1126_);
lean_dec_ref(v_ctx_1125_);
return v_result_1127_;
}
}
else
{
lean_dec_ref(v_node_1126_);
lean_dec_ref(v_ctx_1125_);
return v_result_1127_;
}
}
else
{
lean_dec_ref(v_node_1126_);
lean_dec_ref(v_ctx_1125_);
return v_result_1127_;
}
v___jp_1128_:
{
if (v___y_1129_ == 0)
{
lean_dec_ref(v_node_1126_);
lean_dec_ref(v_ctx_1125_);
return v_result_1127_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_ctx_1125_);
lean_ctor_set(v___x_1130_, 1, v_node_1126_);
v___x_1131_ = lean_array_push(v_result_1127_, v___x_1130_);
return v___x_1131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed(lean_object* v___x_1142_, lean_object* v___x_1143_, lean_object* v_ctx_1144_, lean_object* v_node_1145_, lean_object* v_result_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_CodeAction_cmdCodeActionProvider___lam__0(v___x_1142_, v___x_1143_, v_ctx_1144_, v_node_1145_, v_result_1146_);
lean_dec(v___x_1143_);
lean_dec(v___x_1142_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(lean_object* v_params_1148_, lean_object* v_snap_1149_, lean_object* v_fst_1150_, lean_object* v_snd_1151_, lean_object* v_as_1152_, size_t v_sz_1153_, size_t v_i_1154_, lean_object* v_b_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_snd_1159_; uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_lt(v_i_1154_, v_sz_1153_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
lean_dec_ref(v_snd_1151_);
lean_dec_ref(v_fst_1150_);
lean_dec_ref(v_snap_1149_);
lean_dec_ref(v_params_1148_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_b_1155_);
return v___x_1164_;
}
else
{
lean_object* v___x_4661__overap_1165_; lean_object* v___x_1166_; 
v___x_4661__overap_1165_ = lean_array_uget_borrowed(v_as_1152_, v_i_1154_);
lean_inc(v___x_4661__overap_1165_);
lean_inc_ref(v___y_1156_);
lean_inc_ref(v_snd_1151_);
lean_inc_ref(v_fst_1150_);
lean_inc_ref(v_snap_1149_);
lean_inc_ref(v_params_1148_);
v___x_1166_ = lean_apply_6(v___x_4661__overap_1165_, v_params_1148_, v_snap_1149_, v_fst_1150_, v_snd_1151_, v___y_1156_, lean_box(0));
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1168_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref(v___x_1166_);
v___x_1168_ = l_Array_append___redArg(v_b_1155_, v_a_1167_);
lean_dec(v_a_1167_);
v_snd_1159_ = v___x_1168_;
goto v___jp_1158_;
}
else
{
lean_dec_ref(v___x_1166_);
v_snd_1159_ = v_b_1155_;
goto v___jp_1158_;
}
}
v___jp_1158_:
{
size_t v___x_1160_; size_t v___x_1161_; 
v___x_1160_ = ((size_t)1ULL);
v___x_1161_ = lean_usize_add(v_i_1154_, v___x_1160_);
v_i_1154_ = v___x_1161_;
v_b_1155_ = v_snd_1159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1___boxed(lean_object* v_params_1169_, lean_object* v_snap_1170_, lean_object* v_fst_1171_, lean_object* v_snd_1172_, lean_object* v_as_1173_, lean_object* v_sz_1174_, lean_object* v_i_1175_, lean_object* v_b_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
size_t v_sz_boxed_1179_; size_t v_i_boxed_1180_; lean_object* v_res_1181_; 
v_sz_boxed_1179_ = lean_unbox_usize(v_sz_1174_);
lean_dec(v_sz_1174_);
v_i_boxed_1180_ = lean_unbox_usize(v_i_1175_);
lean_dec(v_i_1175_);
v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1169_, v_snap_1170_, v_fst_1171_, v_snd_1172_, v_as_1173_, v_sz_boxed_1179_, v_i_boxed_1180_, v_b_1176_, v___y_1177_);
lean_dec_ref(v___y_1177_);
lean_dec_ref(v_as_1173_);
return v_res_1181_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2));
v___x_1186_ = lean_unsigned_to_nat(48u);
v___x_1187_ = lean_unsigned_to_nat(185u);
v___x_1188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1));
v___x_1189_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0));
v___x_1190_ = l_mkPanicMessageWithDecl(v___x_1189_, v___x_1188_, v___x_1187_, v___x_1186_, v___x_1185_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(lean_object* v___x_1191_, lean_object* v_params_1192_, lean_object* v_snap_1193_, lean_object* v_as_1194_, size_t v_sz_1195_, size_t v_i_1196_, lean_object* v_b_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_a_1201_; lean_object* v___y_1206_; uint8_t v___x_1217_; 
v___x_1217_ = lean_usize_dec_lt(v_i_1196_, v_sz_1195_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
lean_dec_ref(v_snap_1193_);
lean_dec_ref(v_params_1192_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_b_1197_);
return v___x_1218_;
}
else
{
lean_object* v_a_1219_; lean_object* v_snd_1220_; 
v_a_1219_ = lean_array_uget_borrowed(v_as_1194_, v_i_1196_);
v_snd_1220_ = lean_ctor_get(v_a_1219_, 1);
if (lean_obj_tag(v_snd_1220_) == 1)
{
lean_object* v_i_1221_; 
v_i_1221_ = lean_ctor_get(v_snd_1220_, 0);
if (lean_obj_tag(v_i_1221_) == 3)
{
lean_object* v_fst_1222_; lean_object* v_i_1223_; lean_object* v_onAnyCmd_1224_; lean_object* v_onCmd_1225_; lean_object* v_out_1227_; lean_object* v___y_1228_; lean_object* v_stx_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_fst_1222_ = lean_ctor_get(v_a_1219_, 0);
v_i_1223_ = lean_ctor_get(v_i_1221_, 0);
v_onAnyCmd_1224_ = lean_ctor_get(v___x_1191_, 0);
v_onCmd_1225_ = lean_ctor_get(v___x_1191_, 1);
v_stx_1233_ = lean_ctor_get(v_i_1223_, 1);
lean_inc(v_stx_1233_);
v___x_1234_ = l_Lean_Syntax_getKind(v_stx_1233_);
v___x_1235_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_1225_, v___x_1234_);
lean_dec(v___x_1234_);
if (lean_obj_tag(v___x_1235_) == 1)
{
lean_object* v_val_1236_; size_t v_sz_1237_; size_t v___x_1238_; lean_object* v___x_1239_; 
v_val_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_val_1236_);
lean_dec_ref(v___x_1235_);
v_sz_1237_ = lean_array_size(v_val_1236_);
v___x_1238_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1220_);
lean_inc(v_fst_1222_);
lean_inc_ref(v_snap_1193_);
lean_inc_ref(v_params_1192_);
v___x_1239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1192_, v_snap_1193_, v_fst_1222_, v_snd_1220_, v_val_1236_, v_sz_1237_, v___x_1238_, v_b_1197_, v___y_1198_);
lean_dec(v_val_1236_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref(v___x_1239_);
v_out_1227_ = v_a_1240_;
v___y_1228_ = v___y_1198_;
goto v___jp_1226_;
}
else
{
lean_dec_ref(v_snap_1193_);
lean_dec_ref(v_params_1192_);
return v___x_1239_;
}
}
else
{
lean_dec(v___x_1235_);
v_out_1227_ = v_b_1197_;
v___y_1228_ = v___y_1198_;
goto v___jp_1226_;
}
v___jp_1226_:
{
size_t v_sz_1229_; size_t v___x_1230_; lean_object* v___x_1231_; 
v_sz_1229_ = lean_array_size(v_onAnyCmd_1224_);
v___x_1230_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1220_);
lean_inc(v_fst_1222_);
lean_inc_ref(v_snap_1193_);
lean_inc_ref(v_params_1192_);
v___x_1231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1192_, v_snap_1193_, v_fst_1222_, v_snd_1220_, v_onAnyCmd_1224_, v_sz_1229_, v___x_1230_, v_out_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1231_);
v_a_1201_ = v_a_1232_;
goto v___jp_1200_;
}
else
{
lean_dec_ref(v_snap_1193_);
lean_dec_ref(v_params_1192_);
return v___x_1231_;
}
}
}
else
{
v___y_1206_ = v___y_1198_;
goto v___jp_1205_;
}
}
else
{
v___y_1206_ = v___y_1198_;
goto v___jp_1205_;
}
}
v___jp_1200_:
{
size_t v___x_1202_; size_t v___x_1203_; 
v___x_1202_ = ((size_t)1ULL);
v___x_1203_ = lean_usize_add(v_i_1196_, v___x_1202_);
v_i_1196_ = v___x_1203_;
v_b_1197_ = v_a_1201_;
goto _start;
}
v___jp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
v___x_1208_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v___x_1207_, v___y_1206_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_dec_ref(v___x_1208_);
v_a_1201_ = v_b_1197_;
goto v___jp_1200_;
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v_b_1197_);
lean_dec_ref(v_snap_1193_);
lean_dec_ref(v_params_1192_);
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___boxed(lean_object* v___x_1241_, lean_object* v_params_1242_, lean_object* v_snap_1243_, lean_object* v_as_1244_, lean_object* v_sz_1245_, lean_object* v_i_1246_, lean_object* v_b_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
size_t v_sz_boxed_1250_; size_t v_i_boxed_1251_; lean_object* v_res_1252_; 
v_sz_boxed_1250_ = lean_unbox_usize(v_sz_1245_);
lean_dec(v_sz_1245_);
v_i_boxed_1251_ = lean_unbox_usize(v_i_1246_);
lean_dec(v_i_1246_);
v_res_1252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_1241_, v_params_1242_, v_snap_1243_, v_as_1244_, v_sz_boxed_1250_, v_i_boxed_1251_, v_b_1247_, v___y_1248_);
lean_dec_ref(v___y_1248_);
lean_dec_ref(v_as_1244_);
lean_dec_ref(v___x_1241_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(lean_object* v_params_1253_, lean_object* v_snap_1254_, lean_object* v___x_1255_, lean_object* v_as_1256_, size_t v_sz_1257_, size_t v_i_1258_, lean_object* v_b_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_a_1263_; lean_object* v___y_1268_; uint8_t v___x_1279_; 
v___x_1279_ = lean_usize_dec_lt(v_i_1258_, v_sz_1257_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_dec_ref(v_snap_1254_);
lean_dec_ref(v_params_1253_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v_b_1259_);
return v___x_1280_;
}
else
{
lean_object* v_a_1281_; lean_object* v_snd_1282_; 
v_a_1281_ = lean_array_uget_borrowed(v_as_1256_, v_i_1258_);
v_snd_1282_ = lean_ctor_get(v_a_1281_, 1);
if (lean_obj_tag(v_snd_1282_) == 1)
{
lean_object* v_i_1283_; 
v_i_1283_ = lean_ctor_get(v_snd_1282_, 0);
if (lean_obj_tag(v_i_1283_) == 3)
{
lean_object* v_fst_1284_; lean_object* v_i_1285_; lean_object* v_onAnyCmd_1286_; lean_object* v_onCmd_1287_; lean_object* v_out_1289_; lean_object* v___y_1290_; lean_object* v_stx_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_fst_1284_ = lean_ctor_get(v_a_1281_, 0);
v_i_1285_ = lean_ctor_get(v_i_1283_, 0);
v_onAnyCmd_1286_ = lean_ctor_get(v___x_1255_, 0);
v_onCmd_1287_ = lean_ctor_get(v___x_1255_, 1);
v_stx_1295_ = lean_ctor_get(v_i_1285_, 1);
lean_inc(v_stx_1295_);
v___x_1296_ = l_Lean_Syntax_getKind(v_stx_1295_);
v___x_1297_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_1287_, v___x_1296_);
lean_dec(v___x_1296_);
if (lean_obj_tag(v___x_1297_) == 1)
{
lean_object* v_val_1298_; size_t v_sz_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v_val_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_val_1298_);
lean_dec_ref(v___x_1297_);
v_sz_1299_ = lean_array_size(v_val_1298_);
v___x_1300_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1282_);
lean_inc(v_fst_1284_);
lean_inc_ref(v_snap_1254_);
lean_inc_ref(v_params_1253_);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1253_, v_snap_1254_, v_fst_1284_, v_snd_1282_, v_val_1298_, v_sz_1299_, v___x_1300_, v_b_1259_, v___y_1260_);
lean_dec(v_val_1298_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref(v___x_1301_);
v_out_1289_ = v_a_1302_;
v___y_1290_ = v___y_1260_;
goto v___jp_1288_;
}
else
{
lean_dec_ref(v_snap_1254_);
lean_dec_ref(v_params_1253_);
return v___x_1301_;
}
}
else
{
lean_dec(v___x_1297_);
v_out_1289_ = v_b_1259_;
v___y_1290_ = v___y_1260_;
goto v___jp_1288_;
}
v___jp_1288_:
{
size_t v_sz_1291_; size_t v___x_1292_; lean_object* v___x_1293_; 
v_sz_1291_ = lean_array_size(v_onAnyCmd_1286_);
v___x_1292_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1282_);
lean_inc(v_fst_1284_);
lean_inc_ref(v_snap_1254_);
lean_inc_ref(v_params_1253_);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1253_, v_snap_1254_, v_fst_1284_, v_snd_1282_, v_onAnyCmd_1286_, v_sz_1291_, v___x_1292_, v_out_1289_, v___y_1290_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref(v___x_1293_);
v_a_1263_ = v_a_1294_;
goto v___jp_1262_;
}
else
{
lean_dec_ref(v_snap_1254_);
lean_dec_ref(v_params_1253_);
return v___x_1293_;
}
}
}
else
{
v___y_1268_ = v___y_1260_;
goto v___jp_1267_;
}
}
else
{
v___y_1268_ = v___y_1260_;
goto v___jp_1267_;
}
}
v___jp_1262_:
{
size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = ((size_t)1ULL);
v___x_1265_ = lean_usize_add(v_i_1258_, v___x_1264_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_1255_, v_params_1253_, v_snap_1254_, v_as_1256_, v_sz_1257_, v___x_1265_, v_a_1263_, v___y_1260_);
return v___x_1266_;
}
v___jp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
v___x_1270_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v___x_1269_, v___y_1268_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_dec_ref(v___x_1270_);
v_a_1263_ = v_b_1259_;
goto v___jp_1262_;
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v_b_1259_);
lean_dec_ref(v_snap_1254_);
lean_dec_ref(v_params_1253_);
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2___boxed(lean_object* v_params_1303_, lean_object* v_snap_1304_, lean_object* v___x_1305_, lean_object* v_as_1306_, lean_object* v_sz_1307_, lean_object* v_i_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
size_t v_sz_boxed_1312_; size_t v_i_boxed_1313_; lean_object* v_res_1314_; 
v_sz_boxed_1312_ = lean_unbox_usize(v_sz_1307_);
lean_dec(v_sz_1307_);
v_i_boxed_1313_ = lean_unbox_usize(v_i_1308_);
lean_dec(v_i_1308_);
v_res_1314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_1303_, v_snap_1304_, v___x_1305_, v_as_1306_, v_sz_boxed_1312_, v_i_boxed_1313_, v_b_1309_, v___y_1310_);
lean_dec_ref(v___y_1310_);
lean_dec_ref(v_as_1306_);
lean_dec_ref(v___x_1305_);
return v_res_1314_;
}
}
static lean_object* _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0(void){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Array_instInhabited(lean_box(0));
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = l_Lean_CodeAction_instInhabitedCommandCodeActions_default;
v___x_1317_ = lean_obj_once(&l_Lean_CodeAction_cmdCodeActionProvider___closed__0, &l_Lean_CodeAction_cmdCodeActionProvider___closed__0_once, _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0);
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v___x_1316_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider(lean_object* v_params_1321_, lean_object* v_snap_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v___x_1325_; lean_object* v_a_1326_; lean_object* v_toEditableDocumentCore_1327_; lean_object* v_meta_1328_; lean_object* v_range_1329_; lean_object* v_text_1330_; lean_object* v_start_1331_; lean_object* v_end_1332_; lean_object* v___x_1333_; lean_object* v_toEnvExtension_1334_; lean_object* v_asyncMode_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v_snd_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___f_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; size_t v_sz_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1325_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v_a_1323_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1325_);
v_toEditableDocumentCore_1327_ = lean_ctor_get(v_a_1326_, 0);
lean_inc_ref(v_toEditableDocumentCore_1327_);
lean_dec(v_a_1326_);
v_meta_1328_ = lean_ctor_get(v_toEditableDocumentCore_1327_, 0);
lean_inc_ref(v_meta_1328_);
lean_dec_ref(v_toEditableDocumentCore_1327_);
v_range_1329_ = lean_ctor_get(v_params_1321_, 3);
v_text_1330_ = lean_ctor_get(v_meta_1328_, 3);
lean_inc_ref(v_text_1330_);
lean_dec_ref(v_meta_1328_);
v_start_1331_ = lean_ctor_get(v_range_1329_, 0);
v_end_1332_ = lean_ctor_get(v_range_1329_, 1);
v___x_1333_ = l_Lean_CodeAction_cmdCodeActionExt;
v_toEnvExtension_1334_ = lean_ctor_get(v___x_1333_, 0);
v_asyncMode_1335_ = lean_ctor_get(v_toEnvExtension_1334_, 2);
v___x_1336_ = lean_obj_once(&l_Lean_CodeAction_cmdCodeActionProvider___closed__1, &l_Lean_CodeAction_cmdCodeActionProvider___closed__1_once, _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1);
v___x_1337_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1322_);
v___x_1338_ = lean_box(0);
v___x_1339_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1336_, v___x_1333_, v___x_1337_, v_asyncMode_1335_, v___x_1338_);
v_snd_1340_ = lean_ctor_get(v___x_1339_, 1);
lean_inc(v_snd_1340_);
lean_dec(v___x_1339_);
lean_inc_ref(v_start_1331_);
v___x_1341_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1330_, v_start_1331_);
lean_inc_ref(v_end_1332_);
v___x_1342_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1330_, v_end_1332_);
lean_dec_ref(v_text_1330_);
v___f_1343_ = lean_alloc_closure((void*)(l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1343_, 0, v___x_1342_);
lean_closure_set(v___f_1343_, 1, v___x_1341_);
v___x_1344_ = ((lean_object*)(l_Lean_CodeAction_cmdCodeActionProvider___closed__2));
lean_inc_ref(v_snap_1322_);
v___x_1345_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_1322_);
v___x_1346_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v___x_1344_, v___f_1343_, v___x_1345_);
v_sz_1347_ = lean_array_size(v___x_1346_);
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_1321_, v_snap_1322_, v_snd_1340_, v___x_1346_, v_sz_1347_, v___x_1348_, v___x_1344_, v_a_1323_);
lean_dec(v___x_1346_);
lean_dec(v_snd_1340_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___boxed(lean_object* v_params_1350_, lean_object* v_snap_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_CodeAction_cmdCodeActionProvider(v_params_1350_, v_snap_1351_, v_a_1352_);
lean_dec_ref(v_a_1352_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1(){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1));
v___x_1362_ = lean_alloc_closure((void*)(l_Lean_CodeAction_cmdCodeActionProvider___boxed), 4, 0);
v___x_1363_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_1361_, v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___boxed(lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
return v_res_1365_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Producers_Range(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_StepSize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinTerm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_BuiltinNotation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_CodeActions_Attr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_CodeActions_Provider(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
