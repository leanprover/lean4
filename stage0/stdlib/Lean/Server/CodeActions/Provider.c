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
lean_inc_ref(v_root_768_);
v_tail_769_ = lean_ctor_get(v_t_766_, 1);
lean_inc_ref(v_tail_769_);
lean_dec_ref(v_t_766_);
lean_inc_ref(v_f_764_);
lean_inc(v_ctx_x3f_760_);
lean_inc_ref(v_init_767_);
v___x_770_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_767_, v_ctx_x3f_760_, v_i_761_, v_kind_762_, v_tgtRange_763_, v_f_764_, v_canonicalOnly_765_, v_root_768_, v_init_767_);
lean_dec_ref(v_init_767_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_771_; 
lean_dec_ref(v_tail_769_);
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
lean_dec_ref(v_tail_769_);
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
lean_dec_ref(v_tail_769_);
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
lean_object* v_cs_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_956_; 
v_cs_934_ = lean_ctor_get(v_n_932_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_n_932_);
if (v_isSharedCheck_956_ == 0)
{
v___x_936_ = v_n_932_;
v_isShared_937_ = v_isSharedCheck_956_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_cs_934_);
lean_dec(v_n_932_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_956_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_939_; size_t v_sz_940_; size_t v___x_941_; lean_object* v___x_942_; 
v___x_938_ = lean_box(0);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v_b_933_);
v_sz_940_ = lean_array_size(v_cs_934_);
v___x_941_ = ((size_t)0ULL);
v___x_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_925_, v_ctx_x3f_926_, v_i_927_, v_kind_928_, v_tgtRange_929_, v_f_930_, v_canonicalOnly_931_, v_cs_934_, v_sz_940_, v___x_941_, v___x_939_);
lean_dec_ref(v_cs_934_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_del_object(v___x_936_);
return v___x_938_;
}
else
{
lean_object* v_val_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_955_; 
v_val_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_955_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_955_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_val_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_955_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_fst_947_; 
v_fst_947_ = lean_ctor_get(v_val_943_, 0);
if (lean_obj_tag(v_fst_947_) == 0)
{
lean_object* v_snd_948_; lean_object* v___x_950_; 
v_snd_948_ = lean_ctor_get(v_val_943_, 1);
lean_inc(v_snd_948_);
lean_dec(v_val_943_);
if (v_isShared_937_ == 0)
{
lean_ctor_set_tag(v___x_936_, 1);
lean_ctor_set(v___x_936_, 0, v_snd_948_);
v___x_950_ = v___x_936_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_snd_948_);
v___x_950_ = v_reuseFailAlloc_954_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_952_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_950_);
v___x_952_ = v___x_945_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
else
{
lean_inc_ref(v_fst_947_);
lean_del_object(v___x_945_);
lean_dec(v_val_943_);
lean_del_object(v___x_936_);
return v_fst_947_;
}
}
}
}
}
else
{
lean_object* v_vs_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_979_; 
v_vs_957_ = lean_ctor_get(v_n_932_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v_n_932_);
if (v_isSharedCheck_979_ == 0)
{
v___x_959_ = v_n_932_;
v_isShared_960_ = v_isSharedCheck_979_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_vs_957_);
lean_dec(v_n_932_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_979_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_962_; size_t v_sz_963_; size_t v___x_964_; lean_object* v___x_965_; 
v___x_961_ = lean_box(0);
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v_b_933_);
v_sz_963_ = lean_array_size(v_vs_957_);
v___x_964_ = ((size_t)0ULL);
v___x_965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_926_, v_i_927_, v_kind_928_, v_tgtRange_929_, v_f_930_, v_canonicalOnly_931_, v_vs_957_, v_sz_963_, v___x_964_, v___x_962_);
lean_dec_ref(v_vs_957_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_del_object(v___x_959_);
return v___x_961_;
}
else
{
lean_object* v_val_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_978_; 
v_val_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_978_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_978_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_val_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_978_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v_fst_970_; 
v_fst_970_ = lean_ctor_get(v_val_966_, 0);
if (lean_obj_tag(v_fst_970_) == 0)
{
lean_object* v_snd_971_; lean_object* v___x_973_; 
v_snd_971_ = lean_ctor_get(v_val_966_, 1);
lean_inc(v_snd_971_);
lean_dec(v_val_966_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v_snd_971_);
v___x_973_ = v___x_959_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_snd_971_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_973_);
v___x_975_ = v___x_968_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
lean_inc_ref(v_fst_970_);
lean_del_object(v___x_968_);
lean_dec(v_val_966_);
lean_del_object(v___x_959_);
return v_fst_970_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(lean_object* v_init_980_, lean_object* v_ctx_x3f_981_, lean_object* v_i_982_, lean_object* v_kind_983_, lean_object* v_tgtRange_984_, lean_object* v_f_985_, uint8_t v_canonicalOnly_986_, lean_object* v_as_987_, size_t v_sz_988_, size_t v_i_989_, lean_object* v_b_990_){
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
lean_inc(v_a_997_);
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
lean_dec_ref(v___x_998_);
lean_dec(v_snd_993_);
v_a_1012_ = lean_ctor_get(v_val_1000_, 0);
lean_inc(v_a_1012_);
lean_dec_ref(v_val_1000_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1022_, lean_object* v_ctx_x3f_1023_, lean_object* v_i_1024_, lean_object* v_kind_1025_, lean_object* v_tgtRange_1026_, lean_object* v_f_1027_, lean_object* v_canonicalOnly_1028_, lean_object* v_as_1029_, lean_object* v_sz_1030_, lean_object* v_i_1031_, lean_object* v_b_1032_){
_start:
{
uint8_t v_canonicalOnly_boxed_1033_; size_t v_sz_boxed_1034_; size_t v_i_boxed_1035_; lean_object* v_res_1036_; 
v_canonicalOnly_boxed_1033_ = lean_unbox(v_canonicalOnly_1028_);
v_sz_boxed_1034_ = lean_unbox_usize(v_sz_1030_);
lean_dec(v_sz_1030_);
v_i_boxed_1035_ = lean_unbox_usize(v_i_1031_);
lean_dec(v_i_1031_);
v_res_1036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_1022_, v_ctx_x3f_1023_, v_i_1024_, v_kind_1025_, v_tgtRange_1026_, v_f_1027_, v_canonicalOnly_boxed_1033_, v_as_1029_, v_sz_boxed_1034_, v_i_boxed_1035_, v_b_1032_);
lean_dec_ref(v_as_1029_);
lean_dec_ref(v_tgtRange_1026_);
lean_dec(v_kind_1025_);
lean_dec_ref(v_i_1024_);
lean_dec_ref(v_init_1022_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0___boxed(lean_object* v_ctx_x3f_1037_, lean_object* v_i_1038_, lean_object* v_kind_1039_, lean_object* v_tgtRange_1040_, lean_object* v_f_1041_, lean_object* v_canonicalOnly_1042_, lean_object* v_t_1043_, lean_object* v_init_1044_){
_start:
{
uint8_t v_canonicalOnly_boxed_1045_; lean_object* v_res_1046_; 
v_canonicalOnly_boxed_1045_ = lean_unbox(v_canonicalOnly_1042_);
v_res_1046_ = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(v_ctx_x3f_1037_, v_i_1038_, v_kind_1039_, v_tgtRange_1040_, v_f_1041_, v_canonicalOnly_boxed_1045_, v_t_1043_, v_init_1044_);
lean_dec_ref(v_tgtRange_1040_);
lean_dec(v_kind_1039_);
lean_dec_ref(v_i_1038_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___boxed(lean_object* v_ctx_x3f_1047_, lean_object* v_i_1048_, lean_object* v_kind_1049_, lean_object* v_tgtRange_1050_, lean_object* v_f_1051_, lean_object* v_canonicalOnly_1052_, lean_object* v_as_1053_, lean_object* v_sz_1054_, lean_object* v_i_1055_, lean_object* v_b_1056_){
_start:
{
uint8_t v_canonicalOnly_boxed_1057_; size_t v_sz_boxed_1058_; size_t v_i_boxed_1059_; lean_object* v_res_1060_; 
v_canonicalOnly_boxed_1057_ = lean_unbox(v_canonicalOnly_1052_);
v_sz_boxed_1058_ = lean_unbox_usize(v_sz_1054_);
lean_dec(v_sz_1054_);
v_i_boxed_1059_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_res_1060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_1047_, v_i_1048_, v_kind_1049_, v_tgtRange_1050_, v_f_1051_, v_canonicalOnly_boxed_1057_, v_as_1053_, v_sz_boxed_1058_, v_i_boxed_1059_, v_b_1056_);
lean_dec_ref(v_as_1053_);
lean_dec_ref(v_tgtRange_1050_);
lean_dec(v_kind_1049_);
lean_dec_ref(v_i_1048_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_ctx_x3f_1061_, lean_object* v_i_1062_, lean_object* v_kind_1063_, lean_object* v_tgtRange_1064_, lean_object* v_f_1065_, lean_object* v_canonicalOnly_1066_, lean_object* v_as_1067_, lean_object* v_sz_1068_, lean_object* v_i_1069_, lean_object* v_b_1070_){
_start:
{
uint8_t v_canonicalOnly_boxed_1071_; size_t v_sz_boxed_1072_; size_t v_i_boxed_1073_; lean_object* v_res_1074_; 
v_canonicalOnly_boxed_1071_ = lean_unbox(v_canonicalOnly_1066_);
v_sz_boxed_1072_ = lean_unbox_usize(v_sz_1068_);
lean_dec(v_sz_1068_);
v_i_boxed_1073_ = lean_unbox_usize(v_i_1069_);
lean_dec(v_i_1069_);
v_res_1074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_1061_, v_i_1062_, v_kind_1063_, v_tgtRange_1064_, v_f_1065_, v_canonicalOnly_boxed_1071_, v_as_1067_, v_sz_boxed_1072_, v_i_boxed_1073_, v_b_1070_);
lean_dec_ref(v_as_1067_);
lean_dec_ref(v_tgtRange_1064_);
lean_dec(v_kind_1063_);
lean_dec_ref(v_i_1062_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_ctx_x3f_1075_, lean_object* v_i_1076_, lean_object* v_kind_1077_, lean_object* v_tgtRange_1078_, lean_object* v_f_1079_, lean_object* v_canonicalOnly_1080_, lean_object* v_as_1081_, lean_object* v_sz_1082_, lean_object* v_i_1083_, lean_object* v_b_1084_){
_start:
{
uint8_t v_canonicalOnly_boxed_1085_; size_t v_sz_boxed_1086_; size_t v_i_boxed_1087_; lean_object* v_res_1088_; 
v_canonicalOnly_boxed_1085_ = lean_unbox(v_canonicalOnly_1080_);
v_sz_boxed_1086_ = lean_unbox_usize(v_sz_1082_);
lean_dec(v_sz_1082_);
v_i_boxed_1087_ = lean_unbox_usize(v_i_1083_);
lean_dec(v_i_1083_);
v_res_1088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_1075_, v_i_1076_, v_kind_1077_, v_tgtRange_1078_, v_f_1079_, v_canonicalOnly_boxed_1085_, v_as_1081_, v_sz_boxed_1086_, v_i_boxed_1087_, v_b_1084_);
lean_dec_ref(v_as_1081_);
lean_dec_ref(v_tgtRange_1078_);
lean_dec(v_kind_1077_);
lean_dec_ref(v_i_1076_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_ctx_x3f_1089_, lean_object* v_i_1090_, lean_object* v_kind_1091_, lean_object* v_tgtRange_1092_, lean_object* v_f_1093_, lean_object* v_canonicalOnly_1094_, lean_object* v_as_1095_, lean_object* v_sz_1096_, lean_object* v_i_1097_, lean_object* v_b_1098_){
_start:
{
uint8_t v_canonicalOnly_boxed_1099_; size_t v_sz_boxed_1100_; size_t v_i_boxed_1101_; lean_object* v_res_1102_; 
v_canonicalOnly_boxed_1099_ = lean_unbox(v_canonicalOnly_1094_);
v_sz_boxed_1100_ = lean_unbox_usize(v_sz_1096_);
lean_dec(v_sz_1096_);
v_i_boxed_1101_ = lean_unbox_usize(v_i_1097_);
lean_dec(v_i_1097_);
v_res_1102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_1089_, v_i_1090_, v_kind_1091_, v_tgtRange_1092_, v_f_1093_, v_canonicalOnly_boxed_1099_, v_as_1095_, v_sz_boxed_1100_, v_i_boxed_1101_, v_b_1098_);
lean_dec_ref(v_as_1095_);
lean_dec_ref(v_tgtRange_1092_);
lean_dec(v_kind_1091_);
lean_dec_ref(v_i_1090_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0___boxed(lean_object* v_init_1103_, lean_object* v_ctx_x3f_1104_, lean_object* v_i_1105_, lean_object* v_kind_1106_, lean_object* v_tgtRange_1107_, lean_object* v_f_1108_, lean_object* v_canonicalOnly_1109_, lean_object* v_n_1110_, lean_object* v_b_1111_){
_start:
{
uint8_t v_canonicalOnly_boxed_1112_; lean_object* v_res_1113_; 
v_canonicalOnly_boxed_1112_ = lean_unbox(v_canonicalOnly_1109_);
v_res_1113_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_1103_, v_ctx_x3f_1104_, v_i_1105_, v_kind_1106_, v_tgtRange_1107_, v_f_1108_, v_canonicalOnly_boxed_1112_, v_n_1110_, v_b_1111_);
lean_dec_ref(v_tgtRange_1107_);
lean_dec(v_kind_1106_);
lean_dec_ref(v_i_1105_);
lean_dec_ref(v_init_1103_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_findInfoTree_x3f___boxed(lean_object* v_kind_1114_, lean_object* v_tgtRange_1115_, lean_object* v_ctx_x3f_1116_, lean_object* v_t_1117_, lean_object* v_f_1118_, lean_object* v_canonicalOnly_1119_){
_start:
{
uint8_t v_canonicalOnly_boxed_1120_; lean_object* v_res_1121_; 
v_canonicalOnly_boxed_1120_ = lean_unbox(v_canonicalOnly_1119_);
v_res_1121_ = l_Lean_CodeAction_findInfoTree_x3f(v_kind_1114_, v_tgtRange_1115_, v_ctx_x3f_1116_, v_t_1117_, v_f_1118_, v_canonicalOnly_boxed_1120_);
lean_dec_ref(v_tgtRange_1115_);
lean_dec(v_kind_1114_);
return v_res_1121_;
}
}
static lean_object* _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_1123_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_1123_, 0, lean_box(0));
lean_closure_set(v___x_1123_, 1, lean_box(0));
lean_closure_set(v___x_1123_, 2, v___x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(lean_object* v_msg_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v___f_1128_; lean_object* v___x_4027__overap_1129_; lean_object* v___x_1130_; 
v___x_1127_ = lean_obj_once(&l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0, &l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0_once, _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0);
v___f_1128_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1128_, 0, v___x_1127_);
v___x_4027__overap_1129_ = lean_panic_fn_borrowed(v___f_1128_, v_msg_1124_);
lean_dec_ref(v___f_1128_);
lean_inc_ref(v___y_1125_);
v___x_1130_ = lean_apply_2(v___x_4027__overap_1129_, v___y_1125_, lean_box(0));
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___boxed(lean_object* v_msg_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v_msg_1131_, v___y_1132_);
lean_dec_ref(v___y_1132_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0(lean_object* v___x_1135_, lean_object* v___x_1136_, lean_object* v_ctx_1137_, lean_object* v_node_1138_, lean_object* v_result_1139_){
_start:
{
uint8_t v___y_1141_; 
if (lean_obj_tag(v_node_1138_) == 1)
{
lean_object* v_i_1144_; 
v_i_1144_ = lean_ctor_get(v_node_1138_, 0);
if (lean_obj_tag(v_i_1144_) == 3)
{
lean_object* v_i_1145_; lean_object* v_stx_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; 
v_i_1145_ = lean_ctor_get(v_i_1144_, 0);
v_stx_1146_ = lean_ctor_get(v_i_1145_, 1);
v___x_1147_ = 1;
v___x_1148_ = l_Lean_Syntax_getPos_x3f(v_stx_1146_, v___x_1147_);
if (lean_obj_tag(v___x_1148_) == 1)
{
lean_object* v_val_1149_; lean_object* v___x_1150_; 
v_val_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_val_1149_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1146_, v___x_1147_);
if (lean_obj_tag(v___x_1150_) == 1)
{
lean_object* v_val_1151_; uint8_t v___x_1152_; 
v_val_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_val_1151_);
lean_dec_ref(v___x_1150_);
v___x_1152_ = lean_nat_dec_le(v_val_1149_, v___x_1135_);
lean_dec(v_val_1149_);
if (v___x_1152_ == 0)
{
lean_dec(v_val_1151_);
v___y_1141_ = v___x_1152_;
goto v___jp_1140_;
}
else
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_nat_dec_le(v___x_1136_, v_val_1151_);
lean_dec(v_val_1151_);
v___y_1141_ = v___x_1153_;
goto v___jp_1140_;
}
}
else
{
lean_dec(v___x_1150_);
lean_dec(v_val_1149_);
lean_dec_ref(v_node_1138_);
lean_dec_ref(v_ctx_1137_);
return v_result_1139_;
}
}
else
{
lean_dec(v___x_1148_);
lean_dec_ref(v_node_1138_);
lean_dec_ref(v_ctx_1137_);
return v_result_1139_;
}
}
else
{
lean_dec_ref(v_node_1138_);
lean_dec_ref(v_ctx_1137_);
return v_result_1139_;
}
}
else
{
lean_dec_ref(v_node_1138_);
lean_dec_ref(v_ctx_1137_);
return v_result_1139_;
}
v___jp_1140_:
{
if (v___y_1141_ == 0)
{
lean_dec_ref(v_node_1138_);
lean_dec_ref(v_ctx_1137_);
return v_result_1139_;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_ctx_1137_);
lean_ctor_set(v___x_1142_, 1, v_node_1138_);
v___x_1143_ = lean_array_push(v_result_1139_, v___x_1142_);
return v___x_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed(lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v_ctx_1156_, lean_object* v_node_1157_, lean_object* v_result_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_CodeAction_cmdCodeActionProvider___lam__0(v___x_1154_, v___x_1155_, v_ctx_1156_, v_node_1157_, v_result_1158_);
lean_dec(v___x_1155_);
lean_dec(v___x_1154_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(lean_object* v_params_1160_, lean_object* v_snap_1161_, lean_object* v_fst_1162_, lean_object* v_snd_1163_, lean_object* v_as_1164_, size_t v_sz_1165_, size_t v_i_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_snd_1171_; uint8_t v___x_1175_; 
v___x_1175_ = lean_usize_dec_lt(v_i_1166_, v_sz_1165_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
lean_dec_ref(v_snd_1163_);
lean_dec_ref(v_fst_1162_);
lean_dec_ref(v_snap_1161_);
lean_dec_ref(v_params_1160_);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_b_1167_);
return v___x_1176_;
}
else
{
lean_object* v___x_4661__overap_1177_; lean_object* v___x_1178_; 
v___x_4661__overap_1177_ = lean_array_uget_borrowed(v_as_1164_, v_i_1166_);
lean_inc(v___x_4661__overap_1177_);
lean_inc_ref(v___y_1168_);
lean_inc_ref(v_snd_1163_);
lean_inc_ref(v_fst_1162_);
lean_inc_ref(v_snap_1161_);
lean_inc_ref(v_params_1160_);
v___x_1178_ = lean_apply_6(v___x_4661__overap_1177_, v_params_1160_, v_snap_1161_, v_fst_1162_, v_snd_1163_, v___y_1168_, lean_box(0));
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1180_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref(v___x_1178_);
v___x_1180_ = l_Array_append___redArg(v_b_1167_, v_a_1179_);
lean_dec(v_a_1179_);
v_snd_1171_ = v___x_1180_;
goto v___jp_1170_;
}
else
{
lean_dec_ref(v___x_1178_);
v_snd_1171_ = v_b_1167_;
goto v___jp_1170_;
}
}
v___jp_1170_:
{
size_t v___x_1172_; size_t v___x_1173_; 
v___x_1172_ = ((size_t)1ULL);
v___x_1173_ = lean_usize_add(v_i_1166_, v___x_1172_);
v_i_1166_ = v___x_1173_;
v_b_1167_ = v_snd_1171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1___boxed(lean_object* v_params_1181_, lean_object* v_snap_1182_, lean_object* v_fst_1183_, lean_object* v_snd_1184_, lean_object* v_as_1185_, lean_object* v_sz_1186_, lean_object* v_i_1187_, lean_object* v_b_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
size_t v_sz_boxed_1191_; size_t v_i_boxed_1192_; lean_object* v_res_1193_; 
v_sz_boxed_1191_ = lean_unbox_usize(v_sz_1186_);
lean_dec(v_sz_1186_);
v_i_boxed_1192_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1181_, v_snap_1182_, v_fst_1183_, v_snd_1184_, v_as_1185_, v_sz_boxed_1191_, v_i_boxed_1192_, v_b_1188_, v___y_1189_);
lean_dec_ref(v___y_1189_);
lean_dec_ref(v_as_1185_);
return v_res_1193_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2));
v___x_1198_ = lean_unsigned_to_nat(48u);
v___x_1199_ = lean_unsigned_to_nat(185u);
v___x_1200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1));
v___x_1201_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0));
v___x_1202_ = l_mkPanicMessageWithDecl(v___x_1201_, v___x_1200_, v___x_1199_, v___x_1198_, v___x_1197_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(lean_object* v___x_1203_, lean_object* v_params_1204_, lean_object* v_snap_1205_, lean_object* v_as_1206_, size_t v_sz_1207_, size_t v_i_1208_, lean_object* v_b_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_a_1213_; lean_object* v___y_1218_; uint8_t v___x_1229_; 
v___x_1229_ = lean_usize_dec_lt(v_i_1208_, v_sz_1207_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; 
lean_dec_ref(v_snap_1205_);
lean_dec_ref(v_params_1204_);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v_b_1209_);
return v___x_1230_;
}
else
{
lean_object* v_a_1231_; lean_object* v_snd_1232_; 
v_a_1231_ = lean_array_uget_borrowed(v_as_1206_, v_i_1208_);
v_snd_1232_ = lean_ctor_get(v_a_1231_, 1);
if (lean_obj_tag(v_snd_1232_) == 1)
{
lean_object* v_i_1233_; 
v_i_1233_ = lean_ctor_get(v_snd_1232_, 0);
if (lean_obj_tag(v_i_1233_) == 3)
{
lean_object* v_fst_1234_; lean_object* v_i_1235_; lean_object* v_onAnyCmd_1236_; lean_object* v_onCmd_1237_; lean_object* v_out_1239_; lean_object* v___y_1240_; lean_object* v_stx_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_fst_1234_ = lean_ctor_get(v_a_1231_, 0);
v_i_1235_ = lean_ctor_get(v_i_1233_, 0);
v_onAnyCmd_1236_ = lean_ctor_get(v___x_1203_, 0);
v_onCmd_1237_ = lean_ctor_get(v___x_1203_, 1);
v_stx_1245_ = lean_ctor_get(v_i_1235_, 1);
lean_inc(v_stx_1245_);
v___x_1246_ = l_Lean_Syntax_getKind(v_stx_1245_);
v___x_1247_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_1237_, v___x_1246_);
lean_dec(v___x_1246_);
if (lean_obj_tag(v___x_1247_) == 1)
{
lean_object* v_val_1248_; size_t v_sz_1249_; size_t v___x_1250_; lean_object* v___x_1251_; 
v_val_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_val_1248_);
lean_dec_ref(v___x_1247_);
v_sz_1249_ = lean_array_size(v_val_1248_);
v___x_1250_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1232_);
lean_inc(v_fst_1234_);
lean_inc_ref(v_snap_1205_);
lean_inc_ref(v_params_1204_);
v___x_1251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1204_, v_snap_1205_, v_fst_1234_, v_snd_1232_, v_val_1248_, v_sz_1249_, v___x_1250_, v_b_1209_, v___y_1210_);
lean_dec(v_val_1248_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1251_);
v_out_1239_ = v_a_1252_;
v___y_1240_ = v___y_1210_;
goto v___jp_1238_;
}
else
{
lean_dec_ref(v_snap_1205_);
lean_dec_ref(v_params_1204_);
return v___x_1251_;
}
}
else
{
lean_dec(v___x_1247_);
v_out_1239_ = v_b_1209_;
v___y_1240_ = v___y_1210_;
goto v___jp_1238_;
}
v___jp_1238_:
{
size_t v_sz_1241_; size_t v___x_1242_; lean_object* v___x_1243_; 
v_sz_1241_ = lean_array_size(v_onAnyCmd_1236_);
v___x_1242_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1232_);
lean_inc(v_fst_1234_);
lean_inc_ref(v_snap_1205_);
lean_inc_ref(v_params_1204_);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1204_, v_snap_1205_, v_fst_1234_, v_snd_1232_, v_onAnyCmd_1236_, v_sz_1241_, v___x_1242_, v_out_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref(v___x_1243_);
v_a_1213_ = v_a_1244_;
goto v___jp_1212_;
}
else
{
lean_dec_ref(v_snap_1205_);
lean_dec_ref(v_params_1204_);
return v___x_1243_;
}
}
}
else
{
v___y_1218_ = v___y_1210_;
goto v___jp_1217_;
}
}
else
{
v___y_1218_ = v___y_1210_;
goto v___jp_1217_;
}
}
v___jp_1212_:
{
size_t v___x_1214_; size_t v___x_1215_; 
v___x_1214_ = ((size_t)1ULL);
v___x_1215_ = lean_usize_add(v_i_1208_, v___x_1214_);
v_i_1208_ = v___x_1215_;
v_b_1209_ = v_a_1213_;
goto _start;
}
v___jp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
v___x_1220_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v___x_1219_, v___y_1218_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_dec_ref(v___x_1220_);
v_a_1213_ = v_b_1209_;
goto v___jp_1212_;
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v_b_1209_);
lean_dec_ref(v_snap_1205_);
lean_dec_ref(v_params_1204_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___boxed(lean_object* v___x_1253_, lean_object* v_params_1254_, lean_object* v_snap_1255_, lean_object* v_as_1256_, lean_object* v_sz_1257_, lean_object* v_i_1258_, lean_object* v_b_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
size_t v_sz_boxed_1262_; size_t v_i_boxed_1263_; lean_object* v_res_1264_; 
v_sz_boxed_1262_ = lean_unbox_usize(v_sz_1257_);
lean_dec(v_sz_1257_);
v_i_boxed_1263_ = lean_unbox_usize(v_i_1258_);
lean_dec(v_i_1258_);
v_res_1264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_1253_, v_params_1254_, v_snap_1255_, v_as_1256_, v_sz_boxed_1262_, v_i_boxed_1263_, v_b_1259_, v___y_1260_);
lean_dec_ref(v___y_1260_);
lean_dec_ref(v_as_1256_);
lean_dec_ref(v___x_1253_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(lean_object* v_params_1265_, lean_object* v_snap_1266_, lean_object* v___x_1267_, lean_object* v_as_1268_, size_t v_sz_1269_, size_t v_i_1270_, lean_object* v_b_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_a_1275_; lean_object* v___y_1280_; uint8_t v___x_1291_; 
v___x_1291_ = lean_usize_dec_lt(v_i_1270_, v_sz_1269_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
lean_dec_ref(v_snap_1266_);
lean_dec_ref(v_params_1265_);
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v_b_1271_);
return v___x_1292_;
}
else
{
lean_object* v_a_1293_; lean_object* v_snd_1294_; 
v_a_1293_ = lean_array_uget_borrowed(v_as_1268_, v_i_1270_);
v_snd_1294_ = lean_ctor_get(v_a_1293_, 1);
if (lean_obj_tag(v_snd_1294_) == 1)
{
lean_object* v_i_1295_; 
v_i_1295_ = lean_ctor_get(v_snd_1294_, 0);
if (lean_obj_tag(v_i_1295_) == 3)
{
lean_object* v_fst_1296_; lean_object* v_i_1297_; lean_object* v_onAnyCmd_1298_; lean_object* v_onCmd_1299_; lean_object* v_out_1301_; lean_object* v___y_1302_; lean_object* v_stx_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_fst_1296_ = lean_ctor_get(v_a_1293_, 0);
v_i_1297_ = lean_ctor_get(v_i_1295_, 0);
v_onAnyCmd_1298_ = lean_ctor_get(v___x_1267_, 0);
v_onCmd_1299_ = lean_ctor_get(v___x_1267_, 1);
v_stx_1307_ = lean_ctor_get(v_i_1297_, 1);
lean_inc(v_stx_1307_);
v___x_1308_ = l_Lean_Syntax_getKind(v_stx_1307_);
v___x_1309_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_1299_, v___x_1308_);
lean_dec(v___x_1308_);
if (lean_obj_tag(v___x_1309_) == 1)
{
lean_object* v_val_1310_; size_t v_sz_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v_val_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_val_1310_);
lean_dec_ref(v___x_1309_);
v_sz_1311_ = lean_array_size(v_val_1310_);
v___x_1312_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1294_);
lean_inc(v_fst_1296_);
lean_inc_ref(v_snap_1266_);
lean_inc_ref(v_params_1265_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1265_, v_snap_1266_, v_fst_1296_, v_snd_1294_, v_val_1310_, v_sz_1311_, v___x_1312_, v_b_1271_, v___y_1272_);
lean_dec(v_val_1310_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref(v___x_1313_);
v_out_1301_ = v_a_1314_;
v___y_1302_ = v___y_1272_;
goto v___jp_1300_;
}
else
{
lean_dec_ref(v_snap_1266_);
lean_dec_ref(v_params_1265_);
return v___x_1313_;
}
}
else
{
lean_dec(v___x_1309_);
v_out_1301_ = v_b_1271_;
v___y_1302_ = v___y_1272_;
goto v___jp_1300_;
}
v___jp_1300_:
{
size_t v_sz_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v_sz_1303_ = lean_array_size(v_onAnyCmd_1298_);
v___x_1304_ = ((size_t)0ULL);
lean_inc_ref(v_snd_1294_);
lean_inc(v_fst_1296_);
lean_inc_ref(v_snap_1266_);
lean_inc_ref(v_params_1265_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_1265_, v_snap_1266_, v_fst_1296_, v_snd_1294_, v_onAnyCmd_1298_, v_sz_1303_, v___x_1304_, v_out_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref(v___x_1305_);
v_a_1275_ = v_a_1306_;
goto v___jp_1274_;
}
else
{
lean_dec_ref(v_snap_1266_);
lean_dec_ref(v_params_1265_);
return v___x_1305_;
}
}
}
else
{
v___y_1280_ = v___y_1272_;
goto v___jp_1279_;
}
}
else
{
v___y_1280_ = v___y_1272_;
goto v___jp_1279_;
}
}
v___jp_1274_:
{
size_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = lean_usize_add(v_i_1270_, v___x_1276_);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_1267_, v_params_1265_, v_snap_1266_, v_as_1268_, v_sz_1269_, v___x_1277_, v_a_1275_, v___y_1272_);
return v___x_1278_;
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
v___x_1282_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v___x_1281_, v___y_1280_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_dec_ref(v___x_1282_);
v_a_1275_ = v_b_1271_;
goto v___jp_1274_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec_ref(v_b_1271_);
lean_dec_ref(v_snap_1266_);
lean_dec_ref(v_params_1265_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2___boxed(lean_object* v_params_1315_, lean_object* v_snap_1316_, lean_object* v___x_1317_, lean_object* v_as_1318_, lean_object* v_sz_1319_, lean_object* v_i_1320_, lean_object* v_b_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
size_t v_sz_boxed_1324_; size_t v_i_boxed_1325_; lean_object* v_res_1326_; 
v_sz_boxed_1324_ = lean_unbox_usize(v_sz_1319_);
lean_dec(v_sz_1319_);
v_i_boxed_1325_ = lean_unbox_usize(v_i_1320_);
lean_dec(v_i_1320_);
v_res_1326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_1315_, v_snap_1316_, v___x_1317_, v_as_1318_, v_sz_boxed_1324_, v_i_boxed_1325_, v_b_1321_, v___y_1322_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v_as_1318_);
lean_dec_ref(v___x_1317_);
return v_res_1326_;
}
}
static lean_object* _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0(void){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Array_instInhabited(lean_box(0));
return v___x_1327_;
}
}
static lean_object* _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = l_Lean_CodeAction_instInhabitedCommandCodeActions_default;
v___x_1329_ = lean_obj_once(&l_Lean_CodeAction_cmdCodeActionProvider___closed__0, &l_Lean_CodeAction_cmdCodeActionProvider___closed__0_once, _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0);
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
lean_ctor_set(v___x_1330_, 1, v___x_1328_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider(lean_object* v_params_1333_, lean_object* v_snap_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v_toEditableDocumentCore_1339_; lean_object* v_meta_1340_; lean_object* v_range_1341_; lean_object* v_text_1342_; lean_object* v_start_1343_; lean_object* v_end_1344_; lean_object* v___x_1345_; lean_object* v_toEnvExtension_1346_; lean_object* v_asyncMode_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v_snd_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___f_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; size_t v_sz_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1337_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v_a_1335_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1337_);
v_toEditableDocumentCore_1339_ = lean_ctor_get(v_a_1338_, 0);
lean_inc_ref(v_toEditableDocumentCore_1339_);
lean_dec(v_a_1338_);
v_meta_1340_ = lean_ctor_get(v_toEditableDocumentCore_1339_, 0);
lean_inc_ref(v_meta_1340_);
lean_dec_ref(v_toEditableDocumentCore_1339_);
v_range_1341_ = lean_ctor_get(v_params_1333_, 3);
v_text_1342_ = lean_ctor_get(v_meta_1340_, 3);
lean_inc_ref(v_text_1342_);
lean_dec_ref(v_meta_1340_);
v_start_1343_ = lean_ctor_get(v_range_1341_, 0);
v_end_1344_ = lean_ctor_get(v_range_1341_, 1);
v___x_1345_ = l_Lean_CodeAction_cmdCodeActionExt;
v_toEnvExtension_1346_ = lean_ctor_get(v___x_1345_, 0);
v_asyncMode_1347_ = lean_ctor_get(v_toEnvExtension_1346_, 2);
v___x_1348_ = lean_obj_once(&l_Lean_CodeAction_cmdCodeActionProvider___closed__1, &l_Lean_CodeAction_cmdCodeActionProvider___closed__1_once, _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1);
v___x_1349_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1334_);
v___x_1350_ = lean_box(0);
v___x_1351_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1348_, v___x_1345_, v___x_1349_, v_asyncMode_1347_, v___x_1350_);
v_snd_1352_ = lean_ctor_get(v___x_1351_, 1);
lean_inc(v_snd_1352_);
lean_dec(v___x_1351_);
lean_inc_ref(v_start_1343_);
v___x_1353_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1342_, v_start_1343_);
lean_inc_ref(v_end_1344_);
v___x_1354_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1342_, v_end_1344_);
lean_dec_ref(v_text_1342_);
v___f_1355_ = lean_alloc_closure((void*)(l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1355_, 0, v___x_1354_);
lean_closure_set(v___f_1355_, 1, v___x_1353_);
v___x_1356_ = ((lean_object*)(l_Lean_CodeAction_cmdCodeActionProvider___closed__2));
lean_inc_ref(v_snap_1334_);
v___x_1357_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_1334_);
v___x_1358_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v___x_1356_, v___f_1355_, v___x_1357_);
v_sz_1359_ = lean_array_size(v___x_1358_);
v___x_1360_ = ((size_t)0ULL);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_1333_, v_snap_1334_, v_snd_1352_, v___x_1358_, v_sz_1359_, v___x_1360_, v___x_1356_, v_a_1335_);
lean_dec(v___x_1358_);
lean_dec(v_snd_1352_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_CodeAction_cmdCodeActionProvider___boxed(lean_object* v_params_1362_, lean_object* v_snap_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_CodeAction_cmdCodeActionProvider(v_params_1362_, v_snap_1363_, v_a_1364_);
lean_dec_ref(v_a_1364_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1(){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = ((lean_object*)(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1));
v___x_1374_ = lean_alloc_closure((void*)(l_Lean_CodeAction_cmdCodeActionProvider___boxed), 4, 0);
v___x_1375_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_1373_, v___x_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___boxed(lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
return v_res_1377_;
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
